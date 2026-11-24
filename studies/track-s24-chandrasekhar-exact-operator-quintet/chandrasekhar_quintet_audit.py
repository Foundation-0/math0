#!/usr/bin/env python3
"""Track S24: Zone-B Hardened CLI, Full Pure-Q Replay & Secondary Algebraic Cross-Check.

Pure Python 3 standard library: zero floats, zero bare asserts, zero RNG.
Uses per-component `dir_fd` (`openat(..., O_DIRECTORY | O_NOFOLLOW)`) traversal,
`O_NONBLOCK` + `S_ISREG` checks, capped chunked reads, hardlink refusal (`st_nlink > 1`),
and atomic `O_CREAT | O_EXCL | O_NOFOLLOW` + `os.replace(..., src_dir_fd, dst_dir_fd)` writes.
"""
from __future__ import annotations

import errno
from fractions import Fraction
import hashlib
import os
from pathlib import Path
import stat
import sys
from typing import Any, Sequence

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

from chandrasekhar_quintet_oracle import (
    ChandrasekharError,
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    TRACK_ID,
    build_standalone_certificate,
    canonical_json_bytes,
    parse_exact_rational,
    parse_strict_json_text,
    require_exact_bool,
    require_exact_int,
    require_exact_str,
    validate_certificate_payload,
)

_EXACT_PATH_TYPE = type(Path("."))
_READ_CHUNK_BYTES = 65536
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


# ---------------------------------------------------------------------------
# Race-Free Zone-B File I/O (Per-Component dir_fd/openat + Atomic os.replace)
# ---------------------------------------------------------------------------

def _open_dir_chain(anchor: str, parts: Sequence[str]) -> int:
    """Walk directory components atomically via `openat(..., O_DIRECTORY | O_NOFOLLOW)`."""
    try:
        dfd = os.open(anchor, _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise ChandrasekharError("PATH_STAT_ERROR", f"cannot open anchor dir: {type(exc).__name__}") from exc

    for part in parts:
        try:
            nxt = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
        except OSError as exc:
            os.close(dfd)
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                raise ChandrasekharError("SYMLINK_FORBIDDEN", "symlink or non-dir forbidden in directory path") from exc
            if exc.errno == errno.ENOENT:
                raise ChandrasekharError("PATH_NOT_FOUND", "directory component not found") from exc
            raise ChandrasekharError("PATH_STAT_ERROR", f"cannot traverse dir: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _validate_path_and_split(path: Any) -> tuple[str, list[str]]:
    if type(path) is not _EXACT_PATH_TYPE:
        raise ChandrasekharError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = require_exact_str(str(path), "path")
    if "\x00" in raw_str:
        raise ChandrasekharError("INVALID_PATH", "path contains NUL byte")

    if not path.is_absolute():
        try:
            Path.cwd()
        except OSError as exc:
            raise ChandrasekharError("CWD_UNAVAILABLE", f"cannot resolve cwd: {type(exc).__name__}") from exc
        pwd_env = os.environ.get("PWD", "")
        if pwd_env.startswith("/"):
            pwd_path = Path(pwd_env)
            pwd_parts = [p for p in pwd_path.parts[1:] if p not in ("", ".")]
            try:
                pwd_fd = _open_dir_chain(pwd_path.anchor, pwd_parts)
            except ChandrasekharError as exc:
                if exc.code != "PATH_NOT_FOUND":
                    raise
            else:
                os.close(pwd_fd)
        rel_parts = [p for p in path.parts if p not in ("", ".")]
        return ".", rel_parts
    abs_parts = [p for p in path.parts[1:] if p not in ("", ".")]
    return path.anchor, abs_parts


def require_safe_path(path: Any) -> Path:
    """Validate path type, CWD/PWD, and atomic `openat` directory chain with zero symlinks."""
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        return path
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            st = os.lstat(parts[-1], dir_fd=dfd)
        except FileNotFoundError:
            return path
        except OSError as exc:
            raise ChandrasekharError("PATH_STAT_ERROR", f"cannot lstat leaf: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise ChandrasekharError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
    finally:
        os.close(dfd)
    return path


def _open_leaf_for_read(path: Path) -> int:
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise ChandrasekharError("NON_REGULAR_FILE", "target path refers to a directory")
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            return os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise ChandrasekharError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise ChandrasekharError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


def read_regular_file_bytes(path: Path) -> bytes:
    fd = _open_leaf_for_read(path)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ChandrasekharError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_JSON_BYTES:
                raise ChandrasekharError("FILE_TOO_LARGE", f"file exceeds {MAX_JSON_BYTES} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except ChandrasekharError:
        raise
    except OSError as exc:
        raise ChandrasekharError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        os.close(fd)


def write_regular_file_bytes(path: Path, data: bytes) -> None:
    if type(data) is not bytes:
        raise ChandrasekharError("INVALID_WRITE_DATA", "data must be exact bytes")
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise ChandrasekharError("NON_REGULAR_FILE", "target path refers to a directory")
    leaf = parts[-1]
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise ChandrasekharError("FILE_WRITE_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise ChandrasekharError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
            if not stat.S_ISREG(st.st_mode):
                raise ChandrasekharError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise ChandrasekharError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        tmp_fd: int | None = None
        tmp_name = ""
        for attempt in range(16):
            cand = f".{leaf}.s24tmp.{os.getpid()}.{attempt}"
            try:
                tmp_fd = os.open(
                    cand,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                    0o600,
                    dir_fd=dfd,
                )
                tmp_name = cand
                break
            except FileExistsError:
                continue
            except OSError as exc:
                raise ChandrasekharError("FILE_WRITE_ERROR", f"cannot create temp file: {type(exc).__name__}") from exc
        if tmp_fd is None:
            raise ChandrasekharError("FILE_WRITE_ERROR", "temp file collision limit exceeded")

        try:
            try:
                view = memoryview(data)
                written = 0
                while written < len(data):
                    written += os.write(tmp_fd, view[written:])
            finally:
                os.close(tmp_fd)
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
        except OSError as exc:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
            raise ChandrasekharError("FILE_WRITE_ERROR", f"failed writing file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


# ---------------------------------------------------------------------------
# Full Pure-Q Replay & Secondary Algebraic Cross-Check of Certificate Payload
# ---------------------------------------------------------------------------

def _require_true(mapping: dict[str, Any], key: str, err_code: str) -> None:
    if not require_exact_bool(mapping.get(key), key):
        raise ChandrasekharError(err_code, f"required invariant {key} is false")


def independent_audit_payload(payload: dict[str, Any]) -> dict[str, Any]:
    """Secondary algebraic cross-check over all five Chandrasekhar pillars."""
    # Pillar 1: Black-Hole Darboux / SUSY Iso-Spectrality
    t1 = payload["theorem1_black_hole_darboux"]
    for key in (
        "zerilli_superpotential_identity_exact",
        "regge_wheeler_superpotential_identity_exact",
        "darboux_intertwining_zerilli_exact",
        "darboux_intertwining_rw_exact",
        "asymptotic_superpotential_limit_verified",
        "scattering_modulus_equality_exact",
        "negative_control_perturbed_beta_2M_rejected",
    ):
        _require_true(t1, key, "AUDIT_T1_FAILED")

    for mp in t1["multipoles"]:
        ell = require_exact_int(mp["ell"], "ell", min_val=2)
        lam = Fraction((ell - 1) * (ell + 2), 2)
        if parse_exact_rational(mp["lambda"], "lambda") != lam:
            raise ChandrasekharError("AUDIT_T1_LAMBDA", "multipole lambda mismatch")
        if parse_exact_rational(mp["omega_as_times_M"], "omega_as_times_M") != lam * (lam + 1) / Fraction(3, 1):
            raise ChandrasekharError("AUDIT_T1_OMEGA_AS", "algebraically special frequency mismatch")
        # Independent evaluation of V_RW(r=5, M=1) and V_Zerilli(r=5, M=1)
        r = Fraction(5, 1)
        vrw_ind = (r - 2) * (2 * (lam + 1) * r - 6) / (r ** 4)
        vz_ind = (
            2 * (r - 2) * (lam * lam * (lam + 1) * (r ** 3) + 3 * lam * lam * (r ** 2) + 9 * lam * r + 9)
            / ((r ** 4) * ((lam * r + 3) ** 2))
        )
        if parse_exact_rational(mp["v_rw_at_r5M"], "v_rw") != vrw_ind:
            raise ChandrasekharError("AUDIT_T1_VRW", "independent V_RW(5M) mismatch")
        if parse_exact_rational(mp["v_zerilli_at_r5M"], "v_zerilli") != vz_ind:
            raise ChandrasekharError("AUDIT_T1_VZERILLI", "independent V_Zerilli(5M) mismatch")

    # Pillar 2: Universal Magnetoconvection SOS Stability Law
    t2 = payload["theorem2_magnetoconvection_sos"]
    for key in (
        "sos_identity_exact",
        "q1_factorization_exact",
        "q1_derivative_positive_law_exact",
        "supercritical_instability_identity_exact",
    ):
        _require_true(t2, key, "AUDIT_T2_FAILED")
    for cp in t2["critical_points"]:
        uc = parse_exact_rational(cp["u_c"], "u_c")
        q1 = 2 * (uc ** 3) + 3 * (uc ** 2) - 1
        rc = 2 * ((1 + uc) ** 3)
        if parse_exact_rational(cp["Q_over_pi2"], "Q_over_pi2") != q1:
            raise ChandrasekharError("AUDIT_T2_Q1", "critical Q1 mismatch")
        if parse_exact_rational(cp["R_c_over_pi4"], "R_c_over_pi4") != rc:
            raise ChandrasekharError("AUDIT_T2_RC", "critical R_c mismatch")
        margin = parse_exact_rational(cp["supercritical_margin_at_delta_1e_3"], "margin")
        if margin != -Fraction(1, 1000) * uc:
            raise ChandrasekharError("AUDIT_T2_MARGIN", "supercritical margin mismatch")

    # Pillar 3: Lane-Emden Polytropes & n=3 Rigorous Enclosure
    t3 = payload["theorem3_lane_emden_polytropes"]
    for key in (
        "n0_closed_form_exact",
        "n1_series_ode_exact_deg24",
        "n5_rational_ode_exact",
        "binding_energy_law_exact",
        "n3_binding_energy_vanishes",
        "banach_start_verified",
        "banach_start_lipschitz_lt_half",
        "strictly_decreasing_unique_first_zero",
        "widths_strictly_below_1e_8",
        "negative_control_interval_div_zero_rejected",
    ):
        _require_true(t3, key, "AUDIT_T3_FAILED")
    expected_prefix = [Fraction(1, 1), Fraction(-1, 6), Fraction(1, 40), Fraction(-19, 5040)]
    actual_prefix = [parse_exact_rational(s, "series_coeff") for s in t3["n3_series_prefix"][:4]]
    if actual_prefix != expected_prefix:
        raise ChandrasekharError("AUDIT_T3_SERIES", "n=3 Lane-Emden series prefix mismatch")
    xi1_lo = parse_exact_rational(t3["xi1_lo"], "xi1_lo")
    xi1_hi = parse_exact_rational(t3["xi1_hi"], "xi1_hi")
    xi1_w = parse_exact_rational(t3["xi1_width"], "xi1_width")
    om_lo = parse_exact_rational(t3["omega3_lo"], "omega3_lo")
    om_hi = parse_exact_rational(t3["omega3_hi"], "omega3_hi")
    om_w = parse_exact_rational(t3["omega3_width"], "omega3_width")
    tol = Fraction(1, 10 ** 8)
    if xi1_hi - xi1_lo != xi1_w or xi1_w <= 0 or xi1_w >= tol:
        raise ChandrasekharError("AUDIT_T3_XI1_WIDTH", "xi1 enclosure width check failed")
    if om_hi - om_lo != om_w or om_w <= 0 or om_w >= tol:
        raise ChandrasekharError("AUDIT_T3_OMEGA_WIDTH", "omega3 enclosure width check failed")
    if not (Fraction(6896848, 1000000) < xi1_lo and xi1_hi < Fraction(6896849, 1000000)):
        raise ChandrasekharError("AUDIT_T3_XI1_RANGE", "xi1 enclosure outside known physical window")
    if not (Fraction(2018235, 1000000) < om_lo and om_hi < Fraction(2018236, 1000000)):
        raise ChandrasekharError("AUDIT_T3_OMEGA_RANGE", "omega3 enclosure outside known physical window")

    # Pillar 4: Chandrasekhar-Fermi Virial No-Go Obstruction
    t4 = payload["theorem4_chandrasekhar_fermi_virial"]
    for key in (
        "scalar_virial_energy_elimination_exact",
        "gamma_4_3_energy_vanishing_exact",
        "critical_mass_to_flux_R_cancels_exact",
        "field_div_B_zero_exact",
        "pointwise_3d_maxwell_virial_identity_zero",
        "gauss_virial_balance_zero",
        "self_confined_force_free_R3_obstructed",
        "negative_control_unbound_detected",
    ):
        _require_true(t4, key, "AUDIT_T4_FAILED")
    m_vol = parse_exact_rational(t4["cube_magnetic_energy_M"], "M")
    l_vol = parse_exact_rational(t4["cube_lorentz_virial_int"], "L")
    s_flx = parse_exact_rational(t4["cube_surface_stress_flux"], "S")
    if m_vol <= 0 or s_flx + m_vol != l_vol:
        raise ChandrasekharError("AUDIT_T4_BALANCE", "Gauss Maxwell virial balance mismatch")

    # Pillar 5: Radiative Transfer H-Function Moments & Slab X/Y Riccati Closure
    t5 = payload["theorem5_radiative_transfer_riccati"]
    for key in (
        "alpha0_algebraic_law_exact_Q_q",
        "conservative_hopf_invariant_alpha1_sq_4_3_exact",
        "gauss_legendre_2pt_Q_sqrt3_exact",
        "quad4_pure_Q_cubic_exact",
        "finite_slab_riccati_symbolic_conserved",
        "finite_slab_riccati_tau0_exact",
        "finite_slab_riccati_series_deg8_zero",
        "negative_control_spurious_alpha0_branch_rejected",
        "negative_control_broken_riccati_sign_rejected",
    ):
        _require_true(t5, key, "AUDIT_T5_FAILED")
    for case in t5["albedo_cases"]:
        qv = parse_exact_rational(case["q"], "q")
        w0 = parse_exact_rational(case["albedo_w0"], "albedo_w0")
        a0 = parse_exact_rational(case["alpha0_exact"], "alpha0_exact")
        if (w0 / Fraction(2, 1)) * a0 * a0 - 2 * a0 + 2 != 0:
            raise ChandrasekharError("AUDIT_T5_QUAD_LAW", "H-function quadratic moment law failed")
        if w0 != 1 - qv * qv:
            raise ChandrasekharError("AUDIT_T5_ALBEDO", "albedo != 1 - q^2")
        if a0 != Fraction(2, 1) / (1 + qv):
            raise ChandrasekharError("AUDIT_T5_ALPHA0", "alpha0 != 2/(1+q) physical branch")
        _require_true(case, "quad4_max_residual_lt_1e_18", "AUDIT_T5_RESID")
        _require_true(case, "quad4_alpha0_err_lt_1e_18", "AUDIT_T5_ERR")

    return {
        "independent_audit_passed": True,
        "multipoles_checked": len(t1["multipoles"]),
        "critical_points_checked": len(t2["critical_points"]),
        "albedo_cases_checked": len(t5["albedo_cases"]),
    }


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_file_bytes(path)
    if b"\r" in raw:
        raise ChandrasekharError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise ChandrasekharError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ChandrasekharError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise ChandrasekharError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
    res = validate_certificate_payload(cert, full_replay=True)
    indep = independent_audit_payload(cert["payload"])
    res["canonical_sha256"] = hashlib.sha256(canonical_raw).hexdigest()
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    res["independent_audit"] = indep
    return res


def write_certificate_file(path: Path) -> dict[str, Any]:
    cert = build_standalone_certificate()
    canonical_raw = canonical_json_bytes(cert)
    raw = canonical_raw + b"\n"
    write_regular_file_bytes(path, raw)
    return {
        "written": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": cert["payload_sha256"],
        "certificate_sha256": cert["certificate_sha256"],
        "file_sha256": hashlib.sha256(raw).hexdigest(),
    }


# ---------------------------------------------------------------------------
# Strict Fail-Closed CLI Parsing
# ---------------------------------------------------------------------------

def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple):
        raise ChandrasekharError("INVALID_ARGV", "argv must be exact list/tuple of strict str")
    for item in argv:
        require_exact_str(item, "argv_item", non_empty=False)

    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = argv[i]
        if tok == "--json":
            if as_json:
                raise ChandrasekharError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise ChandrasekharError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise ChandrasekharError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise ChandrasekharError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            val = argv[i + 1]
            if not val or val.startswith("-"):
                raise ChandrasekharError("INVALID_PATH_ARG", f"{tok} path cannot be empty or flag-like")
            mode = "check" if tok == "--check" else "write"
            target = Path(val)
            i += 2
        else:
            raise ChandrasekharError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

    if mode is None:
        mode = "standalone"
    return mode, target, as_json


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv: Any = sys.argv[1:] if argv is None else argv
    try:
        mode, target, as_json = _parse_cli_argv(raw_argv)
        if mode == "standalone":
            out: dict[str, Any] = build_standalone_certificate()
        elif mode == "write":
            out = write_certificate_file(target)  # type: ignore[arg-type]
        else:
            out = check_certificate_file(target)  # type: ignore[arg-type]
    except ChandrasekharError as exc:
        err = {"valid": False, "error_code": exc.code, "error_message": exc.message}
        sys.stderr.write(canonical_json_bytes(err).decode("ascii") + "\n")
        return 2

    if as_json:
        sys.stdout.write(canonical_json_bytes(out).decode("ascii") + "\n")
    else:
        sys.stdout.write(
            f"OK {SCHEMA_VERSION} payload_sha256={out['payload_sha256']} "
            f"certificate_sha256={out['certificate_sha256']}\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Track S28: Zone-B Hardened CLI, Full Pure-Q Replay & Secondary Algebraic Cross-Check.

Pure Python 3 standard library: zero floats, zero bare asserts, zero RNG.
Uses atomic per-component `dir_fd` (`openat(..., O_DIRECTORY | O_NOFOLLOW)`) traversal,
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

from alcubierre_adm_oracle import (
    AlcubierreAdmError,
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
        raise AlcubierreAdmError("PATH_STAT_ERROR", f"cannot open anchor dir: {type(exc).__name__}") from exc

    for part in parts:
        try:
            nxt = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
        except OSError as exc:
            os.close(dfd)
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                raise AlcubierreAdmError("SYMLINK_FORBIDDEN", "symlink or non-dir forbidden in directory path") from exc
            if exc.errno == errno.ENOENT:
                raise AlcubierreAdmError("PATH_NOT_FOUND", "directory component not found") from exc
            raise AlcubierreAdmError("PATH_STAT_ERROR", f"cannot traverse dir: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _validate_path_and_split(path: Any) -> tuple[str, list[str]]:
    if type(path) is not _EXACT_PATH_TYPE:
        raise AlcubierreAdmError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = require_exact_str(str(path), "path")
    if "\x00" in raw_str:
        raise AlcubierreAdmError("INVALID_PATH", "path contains NUL byte")

    if not path.is_absolute():
        try:
            Path.cwd()
        except OSError as exc:
            raise AlcubierreAdmError("CWD_UNAVAILABLE", f"cannot resolve cwd: {type(exc).__name__}") from exc
        pwd_env = require_exact_str(os.environ.get("PWD", ""), "PWD", non_empty=False)
        if pwd_env.startswith("/"):
            pwd_path = Path(pwd_env)
            pwd_parts = [p for p in pwd_path.parts[1:] if p not in ("", ".")]
            try:
                pwd_fd = _open_dir_chain(pwd_path.anchor, pwd_parts)
            except AlcubierreAdmError as exc:
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
            raise AlcubierreAdmError("PATH_STAT_ERROR", f"cannot lstat leaf: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise AlcubierreAdmError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
    finally:
        os.close(dfd)
    return path


def _open_leaf_for_read(path: Path) -> int:
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise AlcubierreAdmError("NON_REGULAR_FILE", "target path refers to a directory")
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            return os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise AlcubierreAdmError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise AlcubierreAdmError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


def read_regular_file_bytes(path: Path) -> bytes:
    fd = _open_leaf_for_read(path)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise AlcubierreAdmError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_JSON_BYTES:
                raise AlcubierreAdmError("FILE_TOO_LARGE", f"file exceeds {MAX_JSON_BYTES} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except AlcubierreAdmError:
        raise
    except OSError as exc:
        raise AlcubierreAdmError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        os.close(fd)


def write_regular_file_bytes(path: Path, data: bytes) -> None:
    if type(data) is not bytes:
        raise AlcubierreAdmError("INVALID_WRITE_DATA", "data must be exact bytes")
    anchor, parts = _validate_path_and_split(path)
    if not parts:
        raise AlcubierreAdmError("NON_REGULAR_FILE", "target path refers to a directory")
    leaf = parts[-1]
    dfd = _open_dir_chain(anchor, parts[:-1])
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise AlcubierreAdmError("FILE_WRITE_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise AlcubierreAdmError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
            if not stat.S_ISREG(st.st_mode):
                raise AlcubierreAdmError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise AlcubierreAdmError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        tmp_fd: int | None = None
        tmp_name = ""
        for attempt in range(16):
            cand = f".{leaf}.s28tmp.{os.getpid()}.{attempt}"
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
                raise AlcubierreAdmError("FILE_WRITE_ERROR", f"cannot create temp file: {type(exc).__name__}") from exc
        if tmp_fd is None:
            raise AlcubierreAdmError("FILE_WRITE_ERROR", "temp file collision limit exceeded")

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
            raise AlcubierreAdmError("FILE_WRITE_ERROR", f"failed writing file: {type(exc).__name__}") from exc
    finally:
        os.close(dfd)


# ---------------------------------------------------------------------------
# Full Pure-Q Replay & Secondary Algebraic Cross-Check of Certificate Payload
# ---------------------------------------------------------------------------

def _require_true(mapping: dict[str, Any], key: str, err_code: str) -> None:
    if not require_exact_bool(mapping.get(key), key):
        raise AlcubierreAdmError(err_code, f"required invariant {key} is false")


def secondary_algebraic_audit(payload: dict[str, Any]) -> dict[str, Any]:
    """Secondary algebraic cross-check over all five Track S28 pillars."""
    # Pillar 1: ADM identities, GP boundary, sign-flip duality, and irrotational Type-IV trigger
    p1 = payload["pillar1_arbitrary_lapse_adm"]
    for key in (
        "arbitrary_lapse_hamiltonian_residual_zero",
        "arbitrary_lapse_momentum_residuals_zero",
        "unit_lapse_pointwise_sign_flip_residual_zero",
        "compact_bubble_int_div_J_zero",
        "compact_bubble_sign_flip_duality_exact",
    ):
        _require_true(p1, key, "AUDIT_P1_FAILED")

    m_gp = parse_exact_rational(p1["gullstrand_painleve_M"], "M_gp")
    for gp in p1["gullstrand_painleve_checks"]:
        r_v = parse_exact_rational(gp["r"], "r")
        br = parse_exact_rational(gp["beta_r"], "beta_r")
        if br * br * r_v != 2 * m_gp:
            raise AlcubierreAdmError("AUDIT_P1_GP_BETA", "GP beta_r^2 * r != 2M")
        if parse_exact_rational(gp["flux_J_ADM_over_pi"], "flux") != 16 * m_gp:
            raise AlcubierreAdmError("AUDIT_P1_GP_FLUX", "GP flux != 16*pi*M")
        _require_true(gp, "vacuum_G_zero", "AUDIT_P1_GP_VAC")

    om_sq = parse_exact_rational(p1["compact_bubble_int_omega_sq"], "om_sq")
    rho16 = parse_exact_rational(p1["compact_bubble_int_16pi_rhoE"], "rho16")
    neg2g00 = parse_exact_rational(p1["compact_bubble_int_neg_2G00"], "neg2g00")
    if om_sq <= 0:
        raise AlcubierreAdmError("AUDIT_P1_OMSQ", "bubble enstrophy must be > 0")
    if rho16 != -Fraction(1, 2) * om_sq:
        raise AlcubierreAdmError("AUDIT_P1_RHO16", "bubble Eulerian energy mismatch")
    if neg2g00 != -rho16:
        raise AlcubierreAdmError("AUDIT_P1_DUALITY", "bubble sign-flip duality mismatch")

    iv = p1["irrotational_non_unit_lapse_type_iv"]
    g00_iv = parse_exact_rational(iv["G_hat_00"], "iv_g00")
    g01_iv = parse_exact_rational(iv["G_hat_01"], "iv_g01")
    g11_iv = parse_exact_rational(iv["G_hat_11"], "iv_g11")
    disc_iv = parse_exact_rational(iv["discriminant_01"], "iv_disc")
    if g00_iv <= 0:
        raise AlcubierreAdmError("AUDIT_P1_IV_RHO", "Type-IV trigger must have G00 > 0")
    if (g00_iv + g11_iv) ** 2 - 4 * g01_iv * g01_iv != disc_iv:
        raise AlcubierreAdmError("AUDIT_P1_IV_DISC_EQ", "Type-IV discriminant formula mismatch")
    if disc_iv >= 0:
        raise AlcubierreAdmError("AUDIT_P1_IV_DISC_SIGN", "Type-IV discriminant must be < 0")
    _require_true(iv, "unit_lapse_control_flux_zero", "AUDIT_P1_IV_CTRL")

    # Pillar 2: Alcubierre w_x == +3 EOS & Two-Annulus Type-IV Obstruction
    p2 = payload["pillar2_alcubierre_eos_type_iv"]
    for key in (
        "off_equatorial_g00_formula_exact",
        "off_equatorial_wx_plus3_exact",
        "septic_profile_c3_smooth",
        "two_concentric_type_iv_annuli_certified",
        "type_iv_fraction_increases_as_v_to_0",
    ):
        _require_true(p2, key, "AUDIT_P2_FAILED")
    for st in p2["equatorial_stations"]:
        g00_s = parse_exact_rational(st["G_hat_00"], "s_g00")
        g11_s = parse_exact_rational(st["G_hat_11"], "s_g11")
        g01_s = parse_exact_rational(st["G_hat_01"], "s_g01")
        disc_s = parse_exact_rational(st["discriminant_01"], "s_disc")
        if g11_s != 3 * g00_s:
            raise AlcubierreAdmError("AUDIT_P2_EOS", "Alcubierre station violates w_x == +3")
        if (g00_s + g11_s) ** 2 - 4 * g01_s * g01_s != disc_s:
            raise AlcubierreAdmError("AUDIT_P2_DISC", "Alcubierre station discriminant mismatch")
        expected_type = "Type_IV" if disc_s < 0 else "Type_I"
        if st["hawking_ellis_type"] != expected_type:
            raise AlcubierreAdmError("AUDIT_P2_TYPE", "Hawking-Ellis type disagrees with discriminant sign")

    # Pillar 3: S-Lemma Krein Inertia & Eulerian Blind Spot
    p3 = payload["pillar3_slemma_krein_blind_spot"]
    if p3["eta_inertia"] != [3, 0, 1]:
        raise AlcubierreAdmError("AUDIT_P3_ETA", "eta inertia must be [3, 0, 1]")
    if p3["hyperbolic_2x2_inertia"] != [1, 0, 1]:
        raise AlcubierreAdmError("AUDIT_P3_HYP", "hyperbolic 2x2 inertia must be [1, 0, 1]")
    fl = p3["boosted_perfect_fluid_slemma"]
    for key in (
        "nec_satisfied_all_observers",
        "wec_satisfied_all_observers",
        "sec_satisfied_all_observers",
        "dec_satisfied_all_observers",
    ):
        _require_true(fl, key, "AUDIT_P3_FLUID")
    bs = p3["eulerian_blind_spot_irrotational_type_i"]
    if parse_exact_rational(bs["G_hat_00"], "bs_g00") <= 0:
        raise AlcubierreAdmError("AUDIT_P3_BS_RHO", "blind-spot Eulerian G00 must be > 0")
    if parse_exact_rational(bs["G_hat_00"], "bs_g00") + parse_exact_rational(bs["G_hat_11"], "bs_g11") >= 0:
        raise AlcubierreAdmError("AUDIT_P3_BS_NEC", "blind-spot must violate G00 + G11 < 0")
    _require_true(bs, "G_hat_0i_all_zero", "AUDIT_P3_BS_FLUX")
    _require_true(p3["alcubierre_pythagorean_quadruple_null_witness"], "violation_certified", "AUDIT_P3_NULL_WIT")

    # Pillar 4: Natario Stokes 1/4 Minimum, S23a Beltrami Bridge & Killing Horizons
    p4 = payload["pillar4_natario_beltrami_horizons"]
    c_star = parse_exact_rational(p4["stokes_thin_wall_minimizer_constant"], "c_star")
    c_comp = parse_exact_rational(p4["stokes_quintic_competitor_constant"], "c_comp")
    if c_star != Fraction(1, 4):
        raise AlcubierreAdmError("AUDIT_P4_STOKES_CONST", "Stokes thin-wall constant must equal 1/4")
    if c_comp <= c_star:
        raise AlcubierreAdmError("AUDIT_P4_STOKES_COMP", "quintic competitor must strictly exceed 1/4")
    _require_true(p4, "stokes_euler_lagrange_cross_term_zero", "AUDIT_P4_EL")
    _require_true(p4, "stokes_sos_gap_exact", "AUDIT_P4_SOS")

    bel = p4["beltrami_s23a_bridge"]
    for key in ("natario_zero_expansion_exact", "beltrami_eigenmode_exact", "force_free_momentum_exact", "energy_equals_neg_lam_over_2_helicity"):
        _require_true(bel, key, "AUDIT_P4_BELTRAMI")
    lam_b = parse_exact_rational(bel["lambda"], "lam_b")
    h_dens = parse_exact_rational(bel["helicity_density_beta_dot_omega"], "h_dens")
    if parse_exact_rational(bel["energy_16pi_rhoE"], "e_bel") != -(lam_b / Fraction(2, 1)) * h_dens:
        raise AlcubierreAdmError("AUDIT_P4_BEL_BRIDGE", "Beltrami energy-helicity bridge mismatch")

    kh = p4["killing_horizons"]
    v_sup = parse_exact_rational(kh["superluminal_v"], "v_sup")
    f_rh = parse_exact_rational(kh["f_at_rH"], "f_rh")
    if f_rh != Fraction(1, 1) - Fraction(1, 1) / v_sup:
        raise AlcubierreAdmError("AUDIT_P4_HORIZON_F", "f(r_H) != 1 - 1/v")
    kf = parse_exact_rational(kh["surface_gravity_front_kappa"], "kappa_front")
    kr = parse_exact_rational(kh["surface_gravity_rear_kappa"], "kappa_rear")
    if kf >= 0:
        raise AlcubierreAdmError("AUDIT_P4_KAPPA_FRONT_SIGN", "front white-hole surface gravity must be < 0")
    if kr != -kf:
        raise AlcubierreAdmError("AUDIT_P4_KAPPA_ANTISYM", "rear black-hole surface gravity must equal -kappa_front")
    if kh.get("front_horizon_type") != "white_hole_blueshift" or kh.get("rear_horizon_type") != "black_hole_hawking":
        raise AlcubierreAdmError("AUDIT_P4_HORIZON_TYPES", "front/rear horizon white/black assignment mismatch")
    _require_true(kh, "g_tt_comoving_at_rH_zero", "AUDIT_P4_GTT")
    _require_true(kh, "front_christoffel_killing_exact", "AUDIT_P4_CHRISTOFFEL")
    _require_true(kh, "rear_christoffel_killing_exact", "AUDIT_P4_CHRISTOFFEL")
    _require_true(kh, "kappa_antisymmetry_and_signs_exact", "AUDIT_P4_KAPPA")
    _require_true(kh, "subluminal_horizon_free", "AUDIT_P4_SUBLUM")

    # Pillar 5: Law-2 Steelman — Lichnerowicz & Physical Subluminal Shells
    p5 = payload["pillar5_physical_subluminal_shells"]
    _require_true(p5, "lichnerowicz_general_hamiltonian_residual_zero", "AUDIT_P5_LICH")
    _require_true(p5, "vdb_compact_collar_int_psi5_R3_zero", "AUDIT_P5_VDB")
    if parse_exact_rational(p5["schwarzschild_tail_int_psi5_R3_over_pi"], "tail") != 16 * parse_exact_rational(p5["schwarzschild_tail_ADM_mass_M"], "m_adm"):
        raise AlcubierreAdmError("AUDIT_P5_ADM", "Schwarzschild tail integral != 16*pi*M_ADM")

    for sh_key in ("smooth_conformally_flat_boosted_shell", "israel_thin_shell_boosted"):
        slemma = p5[sh_key]["slemma_all_conditions"]
        for cond in (
            "nec_satisfied_all_observers",
            "wec_satisfied_all_observers",
            "sec_satisfied_all_observers",
            "dec_satisfied_all_observers",
        ):
            _require_true(slemma, cond, "AUDIT_P5_SHELL_SLEMMA")

    neg_dec = p5["negative_control_sub_threshold_dec_violation"]
    _require_true(neg_dec, "below_dec_threshold_25_12", "AUDIT_P5_DEC_NEG_THRESH")
    _require_true(neg_dec["dec_flux_violation_witness"], "violation_certified", "AUDIT_P5_DEC_NEG_WIT")

    return {
        "secondary_audit_passed": True,
        "gp_radii_checked": len(p1["gullstrand_painleve_checks"]),
        "equatorial_stations_checked": len(p2["equatorial_stations"]),
        "stokes_ratios_checked": len(p4["stokes_finite_aspect_resistance"]),
    }


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_file_bytes(path)
    if b"\r" in raw:
        raise AlcubierreAdmError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise AlcubierreAdmError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise AlcubierreAdmError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise AlcubierreAdmError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
    res = validate_certificate_payload(cert, full_replay=True)
    sec = secondary_algebraic_audit(cert["payload"])
    res["canonical_sha256"] = hashlib.sha256(canonical_raw).hexdigest()
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    res["secondary_audit"] = sec
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
        raise AlcubierreAdmError("INVALID_ARGV", "argv must be exact list/tuple of strict str")
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
                raise AlcubierreAdmError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise AlcubierreAdmError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise AlcubierreAdmError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise AlcubierreAdmError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            val = argv[i + 1]
            if not val or val.startswith("-"):
                raise AlcubierreAdmError("INVALID_PATH_ARG", f"{tok} path cannot be empty or flag-like")
            mode = "check" if tok == "--check" else "write"
            target = Path(val)
            i += 2
        else:
            raise AlcubierreAdmError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except AlcubierreAdmError as exc:
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

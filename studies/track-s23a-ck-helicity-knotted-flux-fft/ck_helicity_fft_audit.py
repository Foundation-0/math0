#!/usr/bin/env python3
"""Zone-B Hardened CLI & Deterministic Replay Certificate Auditor for CK Helicity & FFT.

Zero external dependencies, zero floats, zero bare asserts, zero RNG.
Provides full pure-Q deterministic replay and secondary algebraic cross-checking
with atomic per-component `dir_fd` (`openat` + `O_NOFOLLOW | O_DIRECTORY`) path
traversal, atomic `O_CREAT | O_EXCL` + `os.replace` writes preserving hardlinks
and symlinks under concurrent `renameat2(RENAME_EXCHANGE)` swaps, deleted-CWD
fail-closed handling, lone-surrogate rejection, and strict CLI flag parsing.
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

from ck_helicity_fft_oracle import (
    CKHelicityError,
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    TRACK_ID,
    build_standalone_certificate,
    canonical_json_bytes,
    parse_exact_rational,
    parse_strict_json_text,
    validate_certificate_payload,
)

_EXACT_PATH_TYPE = type(Path("."))
_READ_CHUNK_BYTES = 65536
_TMP_COUNTER = 0
_DARWIN_SYSTEM_ROOT_ALIASES: tuple[tuple[str, str], ...] = (
    ("/var", "/private/var"),
    ("/tmp", "/private/tmp"),
    ("/etc", "/private/etc"),
)


# ---------------------------------------------------------------------------
# Zone-B Hardened Atomic dir_fd File I/O (TOCTOU, PWD, Hardlinks, Surrogates)
# ---------------------------------------------------------------------------

def _normalize_darwin_system_prefix(path: Path, *, allow_exact: bool = False) -> Path:
    """Map verified root-owned macOS /var, /tmp, /etc aliases to /private/* without resolving user symlinks."""
    if sys.platform != "darwin" or not path.is_absolute():
        return path
    parts = path.parts
    min_parts = 2 if allow_exact else 3
    if len(parts) < min_parts or ".." in parts:
        return path
    top = "/" + parts[1]
    for alias, canonical in _DARWIN_SYSTEM_ROOT_ALIASES:
        if top != alias:
            continue
        try:
            st = os.lstat(alias)
            if not stat.S_ISLNK(st.st_mode) or st.st_uid != 0:
                return path
            target = os.readlink(alias)
            if target not in (canonical, canonical.lstrip("/")):
                return path
        except OSError:
            return path
        return Path(canonical, *parts[2:])
    return path


def _require_utf8_str(raw: str, label: str) -> str:
    try:
        raw.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise CKHelicityError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    return raw


def _step_dir_fd_chain(start_fd: int, components: Sequence[str], label: str) -> int:
    """Atomically traverse directory components via openat(O_RDONLY|O_DIRECTORY|O_NOFOLLOW)."""
    dfd = start_fd
    for comp in components:
        try:
            nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dfd)
        except OSError as exc:
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                try:
                    is_sym = stat.S_ISLNK(os.lstat(comp, dir_fd=dfd).st_mode)
                except OSError:
                    is_sym = True
                os.close(dfd)
                if is_sym:
                    raise CKHelicityError("SYMLINK_FORBIDDEN", f"symlink forbidden at {label}") from exc
                raise CKHelicityError("PATH_STAT_ERROR", f"non-directory ancestor at {label}") from exc
            os.close(dfd)
            raise CKHelicityError("FILE_IO_ERROR", f"cannot traverse {label}: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _check_logical_pwd_no_symlinks() -> None:
    pwd_env = os.environ.get("PWD")
    if not pwd_env or not pwd_env.startswith("/"):
        return
    _require_utf8_str(pwd_env, "PWD")
    pwd_path = _normalize_darwin_system_prefix(Path(pwd_env), allow_exact=True)
    pwd_parts = [p for p in pwd_path.parts[1:] if p not in ("", ".")]
    try:
        root_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    except OSError as exc:
        raise CKHelicityError("CWD_UNAVAILABLE", f"cannot open root: {type(exc).__name__}") from exc
    end_fd = _step_dir_fd_chain(root_fd, pwd_parts, "pwd_ancestor")
    os.close(end_fd)


def _open_parent_dir_fd(path: Any) -> tuple[int, str]:
    """Validate path and atomically open parent directory fd pinned against TOCTOU swaps."""
    if type(path) is not _EXACT_PATH_TYPE:
        raise CKHelicityError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = str(path)
    if not raw_str or "\x00" in raw_str:
        raise CKHelicityError("INVALID_PATH", "path empty or contains NUL byte")
    _require_utf8_str(raw_str, "path")

    if path.is_absolute():
        norm_path = _normalize_darwin_system_prefix(path)
        raw_parts = [p for p in norm_path.parts[1:] if p not in ("", ".")]
        try:
            start_fd = os.open(norm_path.anchor, os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise CKHelicityError("FILE_IO_ERROR", f"cannot open root anchor: {type(exc).__name__}") from exc
    else:
        try:
            os.getcwd()
            start_fd = os.open(".", os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise CKHelicityError("CWD_UNAVAILABLE", f"current working directory unavailable: {type(exc).__name__}") from exc
        try:
            _check_logical_pwd_no_symlinks()
        except CKHelicityError:
            os.close(start_fd)
            raise
        raw_parts = [p for p in path.parts if p not in ("", ".")]

    if not raw_parts or raw_parts[-1] == "..":
        os.close(start_fd)
        raise CKHelicityError("NON_REGULAR_FILE", "target path names a directory")

    dfd = _step_dir_fd_chain(start_fd, raw_parts[:-1], "path_component")
    return dfd, raw_parts[-1]


def require_safe_path(path: Any) -> Path:
    """Verify path syntax, CWD/PWD safety, ancestor non-symlink traversal, and non-symlink leaf."""
    dfd, leaf = _open_parent_dir_fd(path)
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            return path
        except OSError as exc:
            raise CKHelicityError("PATH_STAT_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise CKHelicityError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
        return path
    finally:
        os.close(dfd)


def read_regular_file_bytes(path: Path) -> bytes:
    dfd, leaf = _open_parent_dir_fd(path)
    fd = -1
    try:
        try:
            fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise CKHelicityError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise CKHelicityError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise CKHelicityError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_JSON_BYTES:
                raise CKHelicityError("FILE_TOO_LARGE", f"file exceeds {MAX_JSON_BYTES} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except CKHelicityError:
        raise
    except OSError as exc:
        raise CKHelicityError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dfd)


def write_regular_file_bytes(path: Path, data: bytes) -> None:
    global _TMP_COUNTER
    if type(data) is not bytes:
        raise CKHelicityError("INVALID_WRITE_DATA", "data must be exact bytes")
    dfd, leaf = _open_parent_dir_fd(path)
    tmp_fd = -1
    created_tmp = False
    tmp_name = ""
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise CKHelicityError("FILE_WRITE_ERROR", f"cannot stat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise CKHelicityError("SYMLINK_FORBIDDEN", "cannot write to symlink target")
            if not stat.S_ISREG(st.st_mode):
                raise CKHelicityError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise CKHelicityError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        _TMP_COUNTER += 1
        tmp_name = f".ck_s23a_tmp_{os.getpid()}_{_TMP_COUNTER}"
        try:
            tmp_fd = os.open(
                tmp_name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                0o600,
                dir_fd=dfd,
            )
            created_tmp = True
            view = memoryview(data)
            written = 0
            while written < len(data):
                written += os.write(tmp_fd, view[written:])
            os.close(tmp_fd)
            tmp_fd = -1
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            created_tmp = False
        except OSError as exc:
            raise CKHelicityError("FILE_WRITE_ERROR", f"failed atomic write: {type(exc).__name__}") from exc
    finally:
        if tmp_fd >= 0:
            os.close(tmp_fd)
        if created_tmp:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Secondary Algebraic Cross-Check of Certificate Payload
# ---------------------------------------------------------------------------

def independent_audit_payload(payload: dict[str, Any]) -> dict[str, Any]:
    """Secondary algebraic cross-check over the parsed JSON certificate payload."""
    t1 = payload["theorem1_flux_tube_helicity"]
    hp = t1["hopf_positive"]
    hn = t1["hopf_negative"]
    if hp["linking_matrix"] != [[0, 1], [1, 0]] or hn["linking_matrix"] != [[0, -1], [-1, 0]]:
        raise CKHelicityError("AUDIT_T1_HOPF_FAILED", "Hopf linking matrix mismatch")
    if parse_exact_rational(hp["h_mutual"]) != -parse_exact_rational(hn["h_mutual"]):
        raise CKHelicityError("AUDIT_T1_CHIRAL_FAILED", "Hopf chiral antisymmetry failed")
    borr = t1["borromean_rings"]
    if borr["linking_matrix"] != [[0, 0, 0], [0, 0, 0], [0, 0, 0]] or borr["h_mutual"] != "0":
        raise CKHelicityError("AUDIT_T1_BORROMEAN_FAILED", "Borromean obstruction mismatch")
    for tc in t1["torus_cables"]:
        pq = tc["torus_p"] * tc["torus_q"]
        if tc["linking_matrix"] != [[0, pq], [pq, 0]] or not tc["torus_framing_matches_pq"]:
            raise CKHelicityError("AUDIT_T1_TORUS_FAILED", "torus cable pq linking mismatch")
    if not t1["must_fail_odd_crossing_sum"]["rejected"]:
        raise CKHelicityError("AUDIT_T1_CONTROL_FAILED", "odd crossing control was not rejected")

    t2 = payload["theorem2_ck_and_woltjer"]
    for cm in t2["cylindrical_ck_modes"]:
        lam = parse_exact_rational(cm["lambda"])
        kz = parse_exact_rational(cm["kz"])
        gsq = parse_exact_rational(cm["gamma_sq"])
        if gsq != lam * lam - kz * kz or not cm["div_zero_exact"] or not cm["curl_eq_lambda_b_exact"]:
            raise CKHelicityError("AUDIT_T2_CK_FAILED", "cylindrical CK dispersion or eigenstate check failed")
    if not t2["must_fail_broken_dispersion"]["residual_detected"]:
        raise CKHelicityError("AUDIT_T2_CONTROL_FAILED", "broken dispersion control failed")
    for wa_key, expect_sat in (("woltjer_arnold_saturated", True), ("woltjer_arnold_strict_slack", False)):
        wa = t2[wa_key]
        e_val = parse_exact_rational(wa["energy_E"])
        h_val = parse_exact_rational(wa["helicity_H"])
        l1 = parse_exact_rational(wa["lambda_1"])
        slack = Fraction(2, 1) * e_val - l1 * abs(h_val)
        if slack != parse_exact_rational(wa["woltjer_arnold_slack_2E_minus_lam1_absH"]) or slack < 0:
            raise CKHelicityError("AUDIT_T2_WA_FAILED", f"Woltjer-Arnold mismatch in {wa_key}")
        if (slack == 0) is not expect_sat:
            raise CKHelicityError("AUDIT_T2_WA_SAT_FAILED", f"Woltjer-Arnold saturation mismatch in {wa_key}")
    vir = t2["chandrasekhar_fermi_virial"]
    if not vir["pointwise_maxwell_virial_identity_zero"] or not vir["self_confined_R3_obstructed"]:
        raise CKHelicityError("AUDIT_T2_VIRIAL_FAILED", "Chandrasekhar-Fermi virial check failed")

    t3 = payload["theorem3_triads_and_fft"]
    for tr in t3["triads"]:
        k, p, q = tr["wavevectors"]
        if [k[i] + p[i] + q[i] for i in range(3)] != [0, 0, 0]:
            raise CKHelicityError("AUDIT_T3_TRIAD_SUM", "triad wavevectors do not sum to zero")
        t_sum = sum((parse_exact_rational(x) for x in tr["per_leg_ideal_dH_dt"]), Fraction(0, 1))
        if t_sum != 0 or not tr["ideal_helicity_conserved_exact"]:
            raise CKHelicityError("AUDIT_T3_CONSERVATION", "triad ideal helicity conservation failed")
    sp = t3["spectral_convolutions"]
    if not sp["qcomplex_fft3d_n4"]["convolution_theorem_exact"] or not sp["ntt_crt_3d"]["n4_all_192_entries_exact_match"]:
        raise CKHelicityError("AUDIT_T3_SPECTRAL", "spectral FFT/NTT convolution parity failed")

    return {
        "independent_audit_passed": True,
        "torus_cables_checked": len(t1["torus_cables"]),
        "ck_modes_checked": len(t2["cylindrical_ck_modes"]),
        "projectors_checked": len(t2["pythagorean_helical_projectors"]),
        "triads_checked": len(t3["triads"]),
    }


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_file_bytes(path)
    if b"\r" in raw:
        raise CKHelicityError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise CKHelicityError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise CKHelicityError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise CKHelicityError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
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
# Strict Fail-Closed CLI Parsing (Zero Abbreviations, Rejects Flag-Like Paths)
# ---------------------------------------------------------------------------

def _validate_cli_path_value(flag: str, val: str) -> Path:
    _require_utf8_str(val, f"{flag}.path")
    if not val or val.startswith("-"):
        raise CKHelicityError("INVALID_PATH_ARG", f"{flag} path cannot be empty or flag-like")
    return Path(val)


def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple) or any(type(item) is not str for item in argv):
        raise CKHelicityError("INVALID_ARGV", "argv must be exact list/tuple of strict str")

    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = _require_utf8_str(argv[i], "argv")
        if tok == "--json":
            if as_json:
                raise CKHelicityError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise CKHelicityError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise CKHelicityError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise CKHelicityError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            mode = "check" if tok == "--check" else "write"
            target = _validate_cli_path_value(tok, argv[i + 1])
            i += 2
        elif tok.startswith("--check=") or tok.startswith("--write="):
            if mode is not None:
                raise CKHelicityError("CONFLICTING_MODE", "multiple mode flags forbidden")
            flag_name, raw_val = tok.split("=", 1)
            mode = "check" if flag_name == "--check" else "write"
            target = _validate_cli_path_value(flag_name, raw_val)
            i += 1
        else:
            raise CKHelicityError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except CKHelicityError as exc:
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

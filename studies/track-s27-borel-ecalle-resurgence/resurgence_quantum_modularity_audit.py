#!/usr/bin/env python3
"""Fail-closed standalone CLI & certificate verifier for Borel-Ecalle resurgence & quantum modularity.

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero
mathematical RNG (CSPRNG secrets.token_hex used exclusively for temp filenames).
Fail-closed I/O & certificate verification invariants:
  - Concrete pathlib.Path check + NUL-byte and lone UTF-16 surrogate path refusal
  - Deleted-CWD OSError wrapping -> CWD_UNAVAILABLE (rc=2)
  - Atomic dir_fd PWD symlink ancestor verification (O_DIRECTORY | O_NOFOLLOW)
  - Atomic per-component dir_fd openat (O_RDONLY | O_DIRECTORY | O_NOFOLLOW, ELOOP & ENOTDIR)
  - Leaf dir_fd O_RDONLY | O_NOFOLLOW | O_NONBLOCK + fstat S_ISREG + 64 KiB streaming
    reads under strict cap (1 <= max_bytes <= 64 MiB)
  - Thread-safe durable atomic writer: type(payload) is bytes before dir_fd open,
    target lstat (SYMLINK_FORBIDDEN, NOT_A_REGULAR_FILE, st_nlink <= 1 HARDLINK_FORBIDDEN),
    threading.Lock + counter + secrets.token_hex(8) + EEXIST retry, 0o600 temp mode,
    os.fsync(fd), pre-replace fstat(fd).st_nlink == 1, atomic os.replace(..., dir_fd),
    and os.fsync(dfd)
  - Strict RFC 8259 ASCII-only JSON int parser (rejects Unicode digits, leading zeros, -0)
    + canonical_json_bytes full tree & bit-cap validation
  - Strict 64-char lowercase ASCII hex check BEFORE hmac.compare_digest + full-keyset
    and full-leaf secondary_audit_payload with iterative JSON-tree validation
"""
from __future__ import annotations

import errno
import hashlib
import hmac
import json
import os
from pathlib import Path
import secrets
import stat
import sys
import threading
from typing import Any

_ROOT_DIR = str(Path(__file__).resolve().parent)
if _ROOT_DIR not in sys.path:
    sys.path.insert(0, _ROOT_DIR)

import resurgence_quantum_modularity_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_READ_CAP_BYTES = 64 * 1024 * 1024
READ_CHUNK_BYTES = 65_536
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = 1_001
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
DEFAULT_CERT_NAME = "resurgence_quantum_modularity_certificate.json"

_TMP_LOCK = threading.Lock()
_TMP_SEQ = 0


def _next_tmp_tag() -> str:
    global _TMP_SEQ
    with _TMP_LOCK:
        _TMP_SEQ += 1
        seq = _TMP_SEQ
    return f"{os.getpid()}_{seq}_{secrets.token_hex(8)}"


def _require_utf8_no_surrogate(text: str, label: str) -> None:
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise oracle.ResurgenceError("INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden") from exc


def _require_concrete_path(path: Any, label: str) -> Path:
    oracle.require_ok(
        type(path) in _EXACT_PATH_TYPES,
        "INVALID_PATH_TYPE",
        f"{label}: concrete pathlib.Path required",
    )
    raw_s = str(path)
    oracle.require_ok("\x00" not in raw_s, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    _require_utf8_no_surrogate(raw_s, label)
    return path


_DARWIN_SYSTEM_ROOT_ALIASES: tuple[tuple[str, str], ...] = (
    ("/var", "/private/var"),
    ("/tmp", "/private/tmp"),
    ("/etc", "/private/etc"),
)


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
            link_target = os.readlink(alias)
            if link_target not in (canonical, canonical.lstrip("/")):
                return path
        except OSError:
            return path
        return Path(canonical, *parts[2:])
    return path


def _safe_cwd(label: str) -> Path:
    try:
        return Path.cwd()
    except OSError as exc:
        raise oracle.ResurgenceError("CWD_UNAVAILABLE", f"{label}: CWD unavailable ({exc})") from exc


def _check_pwd_no_symlinks(label: str) -> None:
    """Atomically verify PWD ancestor components contain no symlinks via dir_fd O_DIRECTORY|O_NOFOLLOW."""
    pwd = os.environ.get("PWD")
    if pwd and os.path.isabs(pwd):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_parts = _normalize_darwin_system_prefix(Path(pwd), allow_exact=True).parts[1:]
        dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        try:
            dfd = os.open("/", dir_flags)
        except OSError as exc:
            raise oracle.ResurgenceError("FILE_READ_ERROR", f"{label}: cannot open root for PWD ({exc})") from exc
        try:
            for part in pwd_parts:
                if part == ".":
                    continue
                try:
                    nfd = os.open(part, dir_flags, dir_fd=dfd)
                except OSError as exc:
                    if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                        try:
                            is_lnk = stat.S_ISLNK(os.lstat(part, dir_fd=dfd).st_mode)
                        except OSError:
                            is_lnk = exc.errno == errno.ELOOP
                        if is_lnk:
                            raise oracle.ResurgenceError(
                                "SYMLINK_ANCESTOR_FORBIDDEN", f"{label}: symlink PWD ancestor forbidden"
                            ) from exc
                    break
                os.close(dfd)
                dfd = nfd
        finally:
            os.close(dfd)


def _open_dir_chain(target: Path, label: str, *, create_parents: bool) -> tuple[int, str]:
    """Open ancestor directory chain atomically via dir_fd + O_DIRECTORY | O_NOFOLLOW."""
    if target.is_absolute():
        parts = _normalize_darwin_system_prefix(target).parts[1:]
    else:
        cwd = _normalize_darwin_system_prefix(_safe_cwd(label), allow_exact=True)
        _check_pwd_no_symlinks(label)
        parts = cwd.parts[1:] + target.parts
    oracle.require_ok(
        len(parts) >= 1 and parts[-1] not in ("", ".", ".."),
        "NOT_A_REGULAR_FILE",
        f"{label}: path does not name a regular file leaf",
    )
    parent_parts = parts[:-1]
    leaf = parts[-1]
    dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    err_code = "FILE_WRITE_ERROR" if create_parents else "FILE_READ_ERROR"
    try:
        dfd = os.open("/", dir_flags)
    except OSError as exc:
        raise oracle.ResurgenceError(err_code, f"{label}: cannot open root ({exc})") from exc
    try:
        for part in parent_parts:
            if part == ".":
                continue
            try:
                next_fd = os.open(part, dir_flags, dir_fd=dfd)
            except OSError as exc:
                if create_parents and exc.errno == errno.ENOENT:
                    try:
                        os.mkdir(part, 0o755, dir_fd=dfd)
                    except FileExistsError:
                        pass
                    except OSError as mk_exc:
                        raise oracle.ResurgenceError("FILE_WRITE_ERROR", f"{label}: mkdir failed ({mk_exc})") from mk_exc
                    try:
                        next_fd = os.open(part, dir_flags, dir_fd=dfd)
                    except OSError as reopen_exc:
                        raise oracle.ResurgenceError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({reopen_exc})"
                        ) from reopen_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    try:
                        is_lnk = stat.S_ISLNK(os.lstat(part, dir_fd=dfd).st_mode)
                    except OSError:
                        is_lnk = exc.errno == errno.ELOOP
                    if is_lnk:
                        raise oracle.ResurgenceError("SYMLINK_FORBIDDEN", f"{label}: symlink component forbidden") from exc
                    raise oracle.ResurgenceError(err_code, f"{label}: non-directory ancestor ({exc})") from exc
                else:
                    raise oracle.ResurgenceError(err_code, f"{label}: cannot open ancestor ({exc})") from exc
            os.close(dfd)
            dfd = next_fd
        return dfd, leaf
    except BaseException:
        os.close(dfd)
        raise


def read_regular_bytes_capped(path: Path, label: str, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes under strict cap using atomic dir_fd openat + 64 KiB streaming reads."""
    target = _require_concrete_path(path, label)
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_READ_CAP_BYTES)
    dfd, leaf = _open_dir_chain(target, label, create_parents=False)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            fd = os.open(leaf, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise oracle.ResurgenceError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.ResurgenceError("FILE_READ_ERROR", f"{label}: cannot open ({exc})") from exc
    finally:
        os.close(dfd)
    chunks: list[bytes] = []
    total = 0
    try:
        st_f = os.fstat(fd)
        oracle.require_ok(stat.S_ISREG(st_f.st_mode), "NOT_A_REGULAR_FILE", f"{label}: not a regular file")
        while total <= max_bytes:
            chunk = os.read(fd, min(READ_CHUNK_BYTES, max_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
    except oracle.ResurgenceError:
        raise
    except OSError as exc:
        raise oracle.ResurgenceError("FILE_READ_ERROR", f"{label}: read failed ({exc})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str) -> None:
    """Thread-safe durable atomic write via 0o600 O_EXCL temp + fsync + pre-replace st_nlink==1 + os.replace + dir fsync."""
    target = _require_concrete_path(path, label)
    oracle.require_ok(type(payload) is bytes, "INVALID_PAYLOAD_TYPE", f"{label}: payload must be exact bytes")
    dfd, leaf = _open_dir_chain(target, label, create_parents=True)
    tmp_name: str | None = None
    try:
        try:
            st_existing = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st_existing = None
        except OSError as exc:
            raise oracle.ResurgenceError("FILE_WRITE_ERROR", f"{label}: stat failed ({exc})") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")
        for _ in range(32):
            cand = f".{leaf}.s27_tmp_{_next_tmp_tag()}"
            try:
                fd = os.open(
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
                raise oracle.ResurgenceError("FILE_WRITE_ERROR", f"{label}: create temp failed ({exc})") from exc
        else:
            raise oracle.ResurgenceError("FILE_WRITE_ERROR", f"{label}: exhausted temp file slots")
        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(st_tmp.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: temp file hardlinked before replace")
        except oracle.ResurgenceError:
            raise
        except OSError as exc:
            raise oracle.ResurgenceError("FILE_WRITE_ERROR", f"{label}: write/fsync failed ({exc})") from exc
        finally:
            os.close(fd)
        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.ResurgenceError("FILE_WRITE_ERROR", f"{label}: atomic replace failed ({exc})") from exc
    finally:
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


def require_hex64_lower_ascii(val: Any, label: str) -> str:
    oracle.require_ok(
        type(val) is str and len(val) == 64,
        "INVALID_HEX64",
        f"{label}: expected 64-char lowercase ASCII hex",
    )
    for ch in val:
        oracle.require_ok(ch in _HEX_LOWER, "INVALID_HEX64", f"{label}: non-hex-lowercase character")
    return val


def _reject_dup_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        oracle.require_ok(k not in out, "DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def _parse_bounded_int(token: str) -> int:
    oracle.require_ok(type(token) is str, "INVALID_JSON_INT", "JSON int token must be exact str")
    neg = token.startswith("-")
    digits = token[1:] if neg else token
    oracle.require_ok(
        len(digits) >= 1 and all(ch in _ASCII_DIGITS for ch in digits),
        "INVALID_JSON_INT",
        "JSON int token must contain ASCII digits only",
    )
    oracle.require_ok(not (len(digits) > 1 and digits[0] == "0"), "INVALID_JSON_INT", "leading zero forbidden")
    oracle.require_ok(not (neg and digits == "0"), "INVALID_JSON_INT", "negative zero forbidden")
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    val = int(token)
    oracle.require_ok(val.bit_length() <= oracle.MAX_INT_BITS, "INT_BIT_LIMIT", "JSON int exceeds bit cap")
    return val


def _reject_nonfinite(token: str) -> Any:
    raise oracle.ResurgenceError("NONFINITE_JSON", f"non-finite JSON constant {token!r}")


def _reject_float(token: str) -> Any:
    raise oracle.ResurgenceError("FLOAT_FORBIDDEN", f"JSON float token forbidden: {token!r}")


def _validate_json_tree(root: Any, label: str) -> None:
    stack: list[tuple[Any, int]] = [(root, 0)]
    while stack:
        node, depth = stack.pop()
        oracle.require_ok(depth <= MAX_JSON_DEPTH, "MAX_DEPTH_EXCEEDED", f"{label}: depth > {MAX_JSON_DEPTH}")
        t = type(node)
        if t is str:
            oracle.require_ok("\x00" not in node, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte in string")
            _require_utf8_no_surrogate(node, label)
        elif t is dict:
            for k, v in node.items():
                oracle.require_ok(type(k) is str, "INVALID_JSON_KEY", f"{label}: dict keys must be exact str")
                stack.append((k, depth + 1))
                stack.append((v, depth + 1))
        elif t is list:
            for item in node:
                stack.append((item, depth + 1))
        elif t is int:
            oracle.require_ok(
                node.bit_length() <= oracle.MAX_INT_BITS,
                "INT_BIT_LIMIT",
                f"{label}: integer exceeds {oracle.MAX_INT_BITS} bits",
            )
        elif t is bool or node is None:
            pass
        else:
            raise oracle.ResurgenceError("INVALID_JSON_VALUE", f"{label}: unsupported type {t.__name__}")


def parse_strict_json_text(
    text: str,
    label: str,
    *,
    require_object: bool = True,
    max_bytes: int = MAX_JSON_BYTES,
) -> Any:
    oracle.require_ok(type(text) is str, "INVALID_JSON_TEXT", f"{label}: text must be exact str")
    oracle.require_exact_bool(require_object, "require_object")
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_READ_CAP_BYTES)
    oracle.require_ok(not text.startswith("\ufeff"), "BOM_FORBIDDEN", f"{label}: UTF-8 BOM forbidden")
    oracle.require_ok("\x00" not in text, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    _require_utf8_no_surrogate(text, label)
    oracle.require_ok(
        len(text.encode("utf-8")) <= max_bytes,
        "JSON_TOO_LARGE",
        f"{label}: JSON text exceeds {max_bytes} bytes",
    )
    try:
        parsed = json.loads(
            text,
            object_pairs_hook=_reject_dup_keys,
            parse_int=_parse_bounded_int,
            parse_constant=_reject_nonfinite,
            parse_float=_reject_float,
        )
    except oracle.ResurgenceError:
        raise
    except (ValueError, RecursionError) as exc:
        raise oracle.ResurgenceError("INVALID_JSON", f"{label}: {exc}") from exc
    if require_object:
        oracle.require_ok(type(parsed) is dict, "JSON_ROOT_NOT_OBJECT", f"{label}: JSON root must be dict")
    _validate_json_tree(parsed, label)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    _validate_json_tree(obj, "canonical_json")
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n").encode("utf-8")


def build_certificate() -> dict[str, Any]:
    payload = oracle.compute_s27_payload()
    payload_sha = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    envelope = {
        "schema_version": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = hashlib.sha256(canonical_json_bytes(envelope)).hexdigest()
    return {
        "schema_version": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


_EXPECTED_S27_PAYLOAD: dict[str, Any] = {
    "track_id": "TRACK-S27-BOREL-ECALLE-QUANTUM-MODULARITY",
    "novelty_class": "N1",
    "oracle_class": "exact",
    "pillar1_borel_euler": {
        "all_verified": True,
        "borel_convolution_associative": True,
        "borel_convolution_commutative": True,
        "borel_convolution_homomorphism_exact": True,
        "borel_derivative_rule_exact": True,
        "borel_geometric_series_exact": True,
        "borel_inverse_roundtrip_exact": True,
        "borel_pole_closure_exact": True,
        "borel_pole_location": "-1",
        "borel_pole_residue": "1",
        "euler_ode_residual_zero": True,
        "euler_order_N": 20,
        "superasymptotic_truncation_z_1_10": {
            "minimal_at_n9_and_n10": True,
            "n_star": 10,
            "term_8_mag": "63/1562500",
            "term_9_mag": "567/15625000",
            "term_10_mag": "567/15625000",
            "term_11_mag": "6237/156250000",
            "z": "1/10",
        },
    },
    "pillar2_alien_bridge_stokes": {
        "alien_leibniz_rule_exact": True,
        "all_verified": True,
        "linear_euler_bridge_and_stokes_exact": True,
        "riccati_c1_exact_polynomial_control": True,
        "riccati_c_half": {
            "a0_first_8": ["1", "-1/2", "1/2", "-7/8", "19/8", "-143/16", "689/16", "-32299/128"],
            "all_3_sector_ode_residuals_zero": True,
            "c": "1/2",
            "exact_neg_psi1_1": "1/2",
            "inv_pi_6dp": "0.318309",
            "large_order_d1_n20_6dp": "0.538088",
            "large_order_d1_n25_6dp": "0.527473",
            "large_order_d1_n30_6dp": "0.521527",
            "monotone_convergence_verified": True,
            "order_N": 30,
            "psi1_first_6": ["1", "-1/2", "3/8", "-7/16", "103/128", "-567/256"],
            "psi2_first_5": ["-1/2", "0", "-3/4", "-11/8", "-237/32"],
            "richardson_R1_n30_6dp": "0.495277",
            "stokes_C_est_n30_6dp": "0.318310",
            "stokes_C_matches_inv_pi_within_1e5": True,
            "stokes_automorphism_3sector_exact": True,
        },
    },
    "pillar3_bernoulli_stirling_eisenstein": {
        "all_verified": True,
        "bernoulli_even_B2_to_B24": {
            "B_2": "1/6",
            "B_4": "-1/30",
            "B_6": "1/42",
            "B_8": "-1/30",
            "B_10": "5/66",
            "B_12": "-691/2730",
            "B_14": "7/6",
            "B_16": "-3617/510",
            "B_18": "43867/798",
            "B_20": "-174611/330",
            "B_22": "854513/138",
            "B_24": "-236364091/2730",
        },
        "borel_pole_lattice_2pi_i_bounds_exact": True,
        "divergence_lower_bound_k4_6dp": "1.396673",
        "divergence_lower_bound_k4_gt_1": True,
        "eisenstein_bridge_s22a": {
            "E4_squared_equals_E8_mod_q13": True,
            "prefactors_E2_E4_E6_E8": ["-24", "240", "-504", "480"],
        },
        "euler_maclaurin_power_sums_p1_to_5_exact": True,
        "odd_bernoulli_vanish_B3_to_B23": True,
        "stirling_c1_to_c6": ["1/12", "-1/360", "1/1260", "-1/1680", "1/1188", "-691/360360"],
        "stirling_ratio_crosses_1_at_k4_to_5": True,
        "stirling_ratio_k4_to_5": "140/99",
        "stirling_ratio_k11_to_12": "236364091/20197580",
        "stirling_sign_alternation_exact": True,
    },
    "pillar4_zagier_quantum_modularity": {
        "all_verified": True,
        "fishburn_A022493_0_to_10": [1, 1, 2, 5, 15, 53, 217, 1014, 5335, 31240, 201608],
        "kontsevich_roots_of_unity": {
            "F_1": [1, 0],
            "F_i_in_Z_i": [8, -3],
            "F_minus1": [3, 0],
            "F_omega_in_Z_omega": [5, -1],
            "F_zeta6_in_Z_omega": [4, -13],
        },
        "trefoil_habiro_s23b_bridge": {
            "J2_coeffs": {"1": 1, "3": 1, "4": -1},
            "J2_matches_S23b_V31": True,
            "J3_coeffs": {"2": 1, "5": 1, "7": -1, "8": 1, "9": -1, "10": -1, "11": 1},
            "J4_coeffs": {
                "3": 1, "7": 1, "10": -1, "11": 1, "13": -1, "14": -1,
                "15": 1, "17": -1, "19": 1, "20": 1, "21": -1,
            },
            "kashaev_collapse_N2_N3_N4": [True, True, True],
            "s23b_SU2_levels_k1_k2_k4_match": True,
            "s23b_k4_norm_sq": 3,
        },
        "zagier_radial_F_exp_minus_t_0_to_6": ["1", "1", "3/2", "19/6", "69/8", "3451/120", "27221/240"],
        "zagier_strange_identity_C0_to_C9": [
            1, 23, 1681, 257543, 67637281, 27138236663, 15442193173681,
            11828536957233383, 11735529528739490881, 14639678925928297567703,
        ],
        "zagier_strange_identity_L_match_all_10": True,
    },
}


def _exact_json_tree_equal(actual: Any, expected: Any) -> bool:
    """Iterative strict-type, exact-keyset JSON tree equality (rejects bool-for-int, subclasses, and extra keys)."""
    stack: list[tuple[Any, Any]] = [(actual, expected)]
    while stack:
        a, b = stack.pop()
        ta = type(a)
        if ta is not type(b):
            return False
        if ta is dict:
            if set(a.keys()) != set(b.keys()):
                return False
            for k, bv in b.items():
                stack.append((a[k], bv))
        elif ta is list:
            if len(a) != len(b):
                return False
            for av, bv in zip(a, b):
                stack.append((av, bv))
        elif a != b:
            return False
    return True


def secondary_audit_payload(payload: Any) -> None:
    """Schema-safe fail-closed full-keyset & full-leaf secondary cross-check (bool/float/subclass-proof)."""
    oracle.require_ok(type(payload) is dict, "ALGEBRAIC_CROSSCHECK_FAILED", "payload must be exact dict")
    _validate_json_tree(payload, "payload")
    oracle.require_ok(
        _exact_json_tree_equal(payload, _EXPECTED_S27_PAYLOAD),
        "ALGEBRAIC_CROSSCHECK_FAILED",
        "secondary algebraic cross-check failed",
    )


def verify_certificate_dict(
    cert: Any,
    *,
    expected: dict[str, Any] | None = None,
    full_replay: bool = True,
) -> dict[str, Any]:
    """Fail-closed in-memory certificate verifier (works under both full_replay=True and full_replay=False)."""
    oracle.require_exact_bool(full_replay, "full_replay")
    oracle.require_ok(type(cert) is dict, "INVALID_CERT_TYPE", "certificate must be exact dict")
    oracle.require_ok(set(cert.keys()) == _CERT_KEYS, "INVALID_CERT_KEYS", "unexpected or missing cert keys")
    _validate_json_tree(cert, "cert")
    oracle.require_ok(cert["schema_version"] == oracle.SCHEMA_VERSION, "INVALID_SCHEMA", "schema_version mismatch")
    oracle.require_ok(cert["track_id"] == oracle.TRACK_ID, "INVALID_TRACK_ID", "track_id mismatch")
    got_psha = require_hex64_lower_ascii(cert["payload_sha256"], "payload_sha256")
    got_csha = require_hex64_lower_ascii(cert["certificate_sha256"], "certificate_sha256")

    # Always verify self-consistent payload & envelope digests + secondary algebraic cross-check
    calc_psha = hashlib.sha256(canonical_json_bytes(cert["payload"])).hexdigest()
    oracle.require_ok(
        hmac.compare_digest(got_psha, calc_psha),
        "PAYLOAD_SHA_MISMATCH",
        "payload_sha256 does not match payload bytes",
    )
    envelope = {
        "schema_version": cert["schema_version"],
        "track_id": cert["track_id"],
        "payload_sha256": got_psha,
        "payload": cert["payload"],
    }
    calc_csha = hashlib.sha256(canonical_json_bytes(envelope)).hexdigest()
    oracle.require_ok(
        hmac.compare_digest(got_csha, calc_csha),
        "CERTIFICATE_SHA_MISMATCH",
        "certificate_sha256 does not match envelope bytes",
    )
    secondary_audit_payload(cert["payload"])

    if full_replay:
        exp = build_certificate() if expected is None else expected
        oracle.require_ok(
            hmac.compare_digest(got_psha, exp["payload_sha256"]),
            "PAYLOAD_SHA_MISMATCH",
            "payload_sha256 mismatch against oracle replay",
        )
        oracle.require_ok(
            hmac.compare_digest(got_csha, exp["certificate_sha256"]),
            "CERTIFICATE_SHA_MISMATCH",
            "certificate_sha256 mismatch against oracle replay",
        )
        oracle.require_ok(
            hmac.compare_digest(canonical_json_bytes(cert), canonical_json_bytes(exp)),
            "CERTIFICATE_MISMATCH",
            "certificate does not match freshly computed exact oracle output",
        )
    return {
        "valid": True,
        "full_replay": full_replay,
        "payload_sha256": got_psha,
        "certificate_sha256": got_csha,
    }


def verify_certificate_file(cert_path: Path, *, full_replay: bool = True) -> dict[str, Any]:
    """Fail-closed file certificate verifier (atomic dir_fd read + LF-only canonical bytes + replay)."""
    oracle.require_exact_bool(full_replay, "full_replay")
    raw = read_regular_bytes_capped(cert_path, "certificate")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise oracle.ResurgenceError("INVALID_UTF8", f"certificate: invalid UTF-8 ({exc})") from exc
    oracle.require_ok("\r" not in text, "CRLF_FORBIDDEN", "certificate: CRLF line endings forbidden")
    parsed = parse_strict_json_text(text, "certificate", require_object=True)
    res = verify_certificate_dict(parsed, full_replay=full_replay)
    oracle.require_ok(
        hmac.compare_digest(raw, canonical_json_bytes(parsed)),
        "CERTIFICATE_BYTE_MISMATCH",
        "certificate bytes are non-canonical",
    )
    return res


def _validate_cli_argv(argv: Any) -> list[str]:
    oracle.require_ok(type(argv) is list, "INVALID_ARGV", "argv must be exact list")
    for item in argv:
        oracle.require_ok(type(item) is str, "INVALID_ARGV", "argv entries must be exact str")
        oracle.require_ok("\x00" not in item, "NUL_BYTE_FORBIDDEN", "NUL byte forbidden in argv")
        _require_utf8_no_surrogate(item, "argv")
    return argv


def _validate_cli_path_arg(arg: str, flag: str) -> Path:
    oracle.require_ok(
        len(arg) > 0 and not arg.startswith("-"),
        "INVALID_PATH_ARG",
        f"{flag}: path argument must be non-empty and must not start with '-'",
    )
    return Path(arg)


def main(argv: list[str] | None = None) -> int:
    try:
        args = _validate_cli_argv(list(sys.argv[1:]) if argv is None else argv)
        if args in ([], ["--standalone", "--json"]):
            cert = build_certificate()
            sys.stdout.buffer.write(canonical_json_bytes(cert))
            sys.stdout.buffer.flush()
            return 0
        if len(args) == 2 and args[0] == "--write":
            out_path = _validate_cli_path_arg(args[1], "--write")
            cert = build_certificate()
            write_regular_bytes_safe(out_path, canonical_json_bytes(cert), "certificate")
            return 0
        if len(args) == 2 and args[0] == "--check":
            chk_path = _validate_cli_path_arg(args[1], "--check")
            res = verify_certificate_file(chk_path)
            sys.stdout.write(json.dumps(res, sort_keys=True, separators=(",", ":")) + "\n")
            return 0
        raise oracle.ResurgenceError(
            "INVALID_CLI_ARGS",
            "usage: resurgence_quantum_modularity_audit.py (--standalone --json | --write <path> | --check <path>)",
        )
    except oracle.ResurgenceError as exc:
        sys.stderr.write(f"[FAIL] {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

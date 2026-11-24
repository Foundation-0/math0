#!/usr/bin/env python3
"""Zone-B hardened standalone CLI & certificate verifier for Track S22c (Portal 14, Leg 3).

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero .isdigit(),
zero mathematical RNG. First-pass R2-grade Zone-B hardening:
  - Concrete pathlib.Path check + NUL-byte and lone UTF-16 surrogate path refusal
  - Deleted-CWD OSError wrapping -> CWD_UNAVAILABLE (rc=2)
  - Relative-path atomic dir_fd PWD walk + atomic per-component dir_fd openat
    (O_RDONLY | O_DIRECTORY | O_NOFOLLOW, ELOOP/ENOTDIR handling)
  - Leaf dir_fd O_RDONLY | O_NOFOLLOW | O_NONBLOCK + fstat S_ISREG + streaming
    64 KiB capped os.read (strict cap max_bytes <= 64 MiB)
  - Atomic write: type(payload) is bytes BEFORE dir/temp open -> dir_fd lstat
    (SYMLINK_FORBIDDEN, NOT_A_REGULAR_FILE, HARDLINK_FORBIDDEN on st_nlink > 1)
    -> thread-locked CSPRNG O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_NONBLOCK (0o600)
    temp file in same dfd -> os.fsync(tmp_fd) -> pre-replace os.fstat(tmp_fd).st_nlink == 1
    -> atomic os.replace(tmp, leaf, src_dir_fd=dfd, dst_dir_fd=dfd) -> os.fsync(dfd)
  - Strict ASCII-only 0-9 integer (no -0, no leading zeros) and canonical exact
    rational parsers (zero .isdigit(), zero bare ValueError)
  - Strict canonical_json_bytes tree validation (int bit cap, depth cap, no floats/cycles)
  - Strict exact-str argv validation, space- & equals-syntax flag-like/empty CLI
    path refusal (--write --json, --write=--json, --check=--json -> rc=2, 0 files)
  - Strict 64-char lowercase ASCII hex check BEFORE hmac.compare_digest +
    self-consistent SHA-256 + schema-safe fail-closed exact-int secondary_audit_payload
    (even with full_replay=False) + default full pure-Z/Q deterministic replay
"""
from __future__ import annotations

import errno
from fractions import Fraction
import hashlib
import hmac
import json
import math
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

import f2x_perfect_poly_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = 1_234
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PAYLOAD_KEYS = frozenset(
    {
        "track_id",
        "schema_version",
        "oracle_class",
        "novelty_label",
        "prior_art_quarantine_n0",
        "pillar1_f2x_ring_and_sigma",
        "pillar2_splitting_perfect_characterization",
        "pillar3_canaday_11_and_deg14_census",
        "pillar4_odd_perfect_obstruction_frontier",
        "all_pillars_verified",
    }
)
_P1_KEYS = frozenset(
    {
        "irred_counts_deg_1_to_12",
        "rabin_vs_sieve_checked_deg_1_to_8",
        "rabin_vs_sieve_matches_deg_1_to_8",
        "multiplicativity_and_divisor_checks",
        "geometric_sigma_identity_checks",
        "canaday_anchor_x_xp1",
        "all_verified",
    }
)
_P1_ANCHOR_KEYS = frozenset(
    {
        "mask",
        "poly",
        "sigma_x_mask",
        "sigma_xp1_mask",
        "sigma_a_mask",
        "proper_divisor_sum_char2",
    }
)
_P2_KEYS = frozenset(
    {
        "max_exponent_checked",
        "nonconstant_pairs_checked",
        "perfect_splitting_pairs",
        "characterization_a_eq_b_eq_2n_minus_1",
        "duality_witnesses_n_1_to_6",
        "negative_controls",
        "all_verified",
    }
)
_P2_DUAL_KEYS = frozenset({"n", "exponent_2n_minus_1", "degree", "duality_exact"})
_P2_NEG_KEYS = frozenset({"a", "b", "is_perfect"})
_P3_KEYS = frozenset(
    {
        "exhaustive_max_deg",
        "total_monic_polys_deg_1_to_14",
        "perfect_count_deg_1_to_14",
        "splitting_count_deg_1_to_14",
        "sporadic_count_deg_1_to_14",
        "density_deg_1_to_14_q",
        "density_deg_1_to_14_dec6",
        "neg_zero_normalization_witness",
        "census_deg_1_to_14",
        "canaday_11_sporadic_count",
        "canaday_11_verified_count",
        "canaday_direct_divisor_cross_checks",
        "canaday_conjugate_twin_pairs",
        "canaday_self_symmetric_masks",
        "canaday_11_sporadic",
        "all_verified",
    }
)
_P3_CENSUS_KEYS = frozenset({"mask", "degree", "is_splitting", "shift_x_plus_1_mask", "factorization"})
_P3_CANADAY_KEYS = frozenset({"mask", "degree", "omega", "shift_x_plus_1_mask", "self_symmetric", "factorization"})
_P4_KEYS = frozenset(
    {
        "direct_odd_max_deg",
        "direct_odd_at_deg_16",
        "direct_odd_checked_deg_2_to_16",
        "direct_odd_perfect_found",
        "odd_irreducibles_tested_deg_2_to_8",
        "theorem_4a_even_exponent_witnesses",
        "theorem_4a_every_odd_perfect_is_square",
        "theorem_4b_char2_derivative_witnesses",
        "theorem_4b_sigma_p2a_never_square",
        "theorem_4b_unconditional_omega_ge_3",
        "square_lifted_max_root_deg",
        "square_lifted_max_poly_deg",
        "square_lifted_odd_squares_checked",
        "square_lifted_total_odd_polys_covered_deg_2_to_24",
        "square_lifted_odd_perfect_found",
        "all_verified",
    }
)
_EXPECTED_PRIOR_ART_N0: tuple[str, ...] = (
    "Canaday (1941) Duke Math. J. — F2[x] perfect polynomials & 11 sporadic solutions",
    "Beard, O'Connell & West (1977) — splitting perfect polynomials over GF(q)",
    "Gallardo & Rahavandrainy (2007-2025) — odd perfect polynomial obstructions over F2[x]",
)
_EXPECTED_NEG_CONTROL_PAIRS: tuple[tuple[int, int], ...] = (
    (2, 1),
    (1, 2),
    (2, 2),
    (3, 1),
    (4, 4),
)
_EXPECTED_CENSUS_MASKS_14: tuple[int, ...] = (6, 36, 54, 120, 2470, 2640, 3144, 3780, 32640)
_TEMP_NAME_LOCK = threading.Lock()
DEFAULT_CERT_NAME = "f2x_perfect_poly_certificate.json"


def _require_utf8_no_surrogate(text: str, label: str) -> None:
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise oracle.F2xPerfectError("INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden") from exc


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


def _safe_cwd(label: str) -> Path:
    try:
        return Path.cwd()
    except OSError as exc:
        raise oracle.F2xPerfectError("CWD_UNAVAILABLE", f"{label}: CWD unavailable ({exc})") from exc


def _check_pwd_no_symlinks(label: str) -> None:
    pwd = os.environ.get("PWD")
    if pwd and os.path.isabs(pwd):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_path = Path(pwd)
        dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        try:
            dfd = os.open("/", dir_flags)
        except OSError as exc:
            raise oracle.F2xPerfectError("CWD_UNAVAILABLE", f"{label}: cannot open root for PWD ({exc})") from exc
        try:
            for part in pwd_path.parts[1:]:
                try:
                    next_fd = os.open(part, dir_flags, dir_fd=dfd)
                except OSError as exc:
                    if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                        raise oracle.F2xPerfectError(
                            "SYMLINK_ANCESTOR_FORBIDDEN",
                            f"{label}: symlink PWD ancestor forbidden",
                        ) from exc
                    raise oracle.F2xPerfectError(
                        "CWD_UNAVAILABLE",
                        f"{label}: PWD ancestor unavailable ({exc})",
                    ) from exc
                os.close(dfd)
                dfd = next_fd
        finally:
            os.close(dfd)


def _open_dir_chain(target: Path, label: str, *, create_parents: bool) -> tuple[int, str]:
    """Open ancestor directory chain atomically via dir_fd + O_DIRECTORY | O_NOFOLLOW."""
    if target.is_absolute():
        parts = target.parts[1:]
    else:
        cwd = _safe_cwd(label)
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
        raise oracle.F2xPerfectError(err_code, f"{label}: cannot open root ({exc})") from exc
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
                        raise oracle.F2xPerfectError("FILE_WRITE_ERROR", f"{label}: mkdir failed ({mk_exc})") from mk_exc
                    try:
                        next_fd = os.open(part, dir_flags, dir_fd=dfd)
                    except OSError as reopen_exc:
                        raise oracle.F2xPerfectError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({reopen_exc})"
                        ) from reopen_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    try:
                        is_lnk = stat.S_ISLNK(os.lstat(part, dir_fd=dfd).st_mode)
                    except OSError:
                        is_lnk = exc.errno == errno.ELOOP
                    if is_lnk:
                        raise oracle.F2xPerfectError("SYMLINK_FORBIDDEN", f"{label}: symlink component forbidden") from exc
                    raise oracle.F2xPerfectError(err_code, f"{label}: non-directory ancestor ({exc})") from exc
                else:
                    raise oracle.F2xPerfectError(err_code, f"{label}: cannot open ancestor ({exc})") from exc
            os.close(dfd)
            dfd = next_fd
        return dfd, leaf
    except BaseException:
        os.close(dfd)
        raise


def read_regular_bytes_capped(path: Path, label: str, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes under strict cap using atomic dir_fd openat O_NOFOLLOW|O_NONBLOCK + fstat S_ISREG."""
    target = _require_concrete_path(path, label)
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_ALLOWED_CAP_BYTES)
    dfd, leaf = _open_dir_chain(target, label, create_parents=False)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            fd = os.open(leaf, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise oracle.F2xPerfectError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.F2xPerfectError("FILE_READ_ERROR", f"{label}: cannot open ({exc})") from exc
    finally:
        os.close(dfd)
    chunks: list[bytes] = []
    total = 0
    try:
        st_f = os.fstat(fd)
        oracle.require_ok(stat.S_ISREG(st_f.st_mode), "NOT_A_REGULAR_FILE", f"{label}: not a regular file")
        while total <= max_bytes:
            chunk = os.read(fd, min(_READ_CHUNK_BYTES, max_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
    except oracle.F2xPerfectError:
        raise
    except OSError as exc:
        raise oracle.F2xPerfectError("FILE_READ_ERROR", f"{label}: read failed ({exc})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str) -> None:
    """Write bytes atomically via dir_fd O_CREAT|O_EXCL|O_NOFOLLOW (0o600) + fsync + os.replace + dir fsync."""
    oracle.require_ok(type(payload) is bytes, "INVALID_PAYLOAD_BYTES", f"{label}: payload must be exact bytes")
    target = _require_concrete_path(path, label)
    dfd, leaf = _open_dir_chain(target, label, create_parents=True)
    tmp_name: str | None = None
    try:
        try:
            st_existing = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st_existing = None
        except OSError as exc:
            raise oracle.F2xPerfectError("FILE_WRITE_ERROR", f"{label}: stat failed ({exc})") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")
        pid = os.getpid()
        for _ in range(64):
            with _TEMP_NAME_LOCK:
                cand = f".s22c.{pid}.{secrets.token_hex(8)}.tmp"
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
                raise oracle.F2xPerfectError("FILE_WRITE_ERROR", f"{label}: create temp failed ({exc})") from exc
        else:
            raise oracle.F2xPerfectError("FILE_WRITE_ERROR", f"{label}: exhausted temp file slots")
        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(st_tmp.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: temp file link count altered")
        except OSError as exc:
            raise oracle.F2xPerfectError("FILE_WRITE_ERROR", f"{label}: write failed ({exc})") from exc
        finally:
            os.close(fd)
        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.F2xPerfectError("FILE_WRITE_ERROR", f"{label}: atomic replace failed ({exc})") from exc
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


def _parse_bounded_int(token: str) -> int:
    """Strict ASCII-only 0-9 signed integer parser (zero .isdigit(), zero bare ValueError)."""
    oracle.require_ok(type(token) is str, "INVALID_JSON_INT", "JSON int token must be exact str")
    oracle.require_ok(token != "-0", "INVALID_JSON_INT", "negative zero forbidden")
    digits = token[1:] if token.startswith("-") else token
    oracle.require_ok(len(digits) >= 1, "INVALID_JSON_INT", "JSON int token has no digits")
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    oracle.require_ok(digits == "0" or not digits.startswith("0"), "INVALID_JSON_INT", "leading zero forbidden")
    for ch in digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_JSON_INT", "JSON int token must contain ASCII digits 0-9 only")
    return int(token)


def parse_exact_rational(token: Any, label: str = "rational") -> Fraction:
    """Strict ASCII-only canonical exact rational parser for 'n' or reduced 'n/d' (d >= 2)."""
    oracle.require_ok(type(token) is str, "INVALID_RATIONAL", f"{label}: rational token must be exact str")
    parts = token.split("/")
    oracle.require_ok(len(parts) in (1, 2), "INVALID_RATIONAL", f"{label}: expected 'n' or 'n/d'")
    num_s = parts[0]
    oracle.require_ok(num_s != "-0", "INVALID_RATIONAL", f"{label}: negative zero forbidden")
    num_digits = num_s[1:] if num_s.startswith("-") else num_s
    oracle.require_ok(len(num_digits) >= 1, "INVALID_RATIONAL", f"{label}: empty numerator")
    oracle.require_ok(len(num_digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", f"{label}: numerator too long")
    oracle.require_ok(num_digits == "0" or not num_digits.startswith("0"), "INVALID_RATIONAL", f"{label}: leading zero")
    for ch in num_digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_RATIONAL", f"{label}: non-ASCII digit in numerator")
    num = int(num_s)
    oracle.require_ok(num.bit_length() <= oracle.MAX_JSON_INT_BITS, "INT_BIT_LIMIT", f"{label}: numerator bit limit")
    if len(parts) == 1:
        return Fraction(num, 1)
    den_s = parts[1]
    oracle.require_ok(len(den_s) >= 1, "INVALID_RATIONAL", f"{label}: empty denominator")
    oracle.require_ok(len(den_s) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", f"{label}: denominator too long")
    oracle.require_ok(not den_s.startswith("0"), "INVALID_RATIONAL", f"{label}: leading zero in denominator")
    for ch in den_s:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_RATIONAL", f"{label}: non-ASCII digit in denominator")
    den = int(den_s)
    oracle.require_ok(den.bit_length() <= oracle.MAX_JSON_INT_BITS, "INT_BIT_LIMIT", f"{label}: denominator bit limit")
    oracle.require_ok(den >= 2, "INVALID_RATIONAL", f"{label}: denominator must be >= 2")
    oracle.require_ok(math.gcd(num, den) == 1, "INVALID_RATIONAL", f"{label}: non-reduced rational forbidden")
    return Fraction(num, den)


def _reject_dup_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        oracle.require_ok(k not in out, "DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def _reject_nonfinite(token: str) -> Any:
    raise oracle.F2xPerfectError("NONFINITE_JSON", f"non-finite JSON constant {token!r}")


def _reject_float(token: str) -> Any:
    raise oracle.F2xPerfectError("FLOAT_FORBIDDEN", f"JSON float token forbidden: {token!r}")


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
                node.bit_length() <= oracle.MAX_JSON_INT_BITS,
                "INT_BIT_LIMIT",
                f"{label}: integer exceeds {oracle.MAX_JSON_INT_BITS} bits",
            )
        elif t is bool or node is None:
            pass
        else:
            raise oracle.F2xPerfectError("INVALID_JSON_VALUE", f"{label}: unsupported type {t.__name__}")


def parse_strict_json_text(text: str, label: str, *, require_object: bool = True) -> Any:
    oracle.require_ok(type(text) is str, "INVALID_JSON_TEXT", f"{label}: text must be exact str")
    oracle.require_exact_bool(require_object, "require_object")
    oracle.require_ok(not text.startswith("\ufeff"), "BOM_FORBIDDEN", f"{label}: UTF-8 BOM forbidden")
    oracle.require_ok("\x00" not in text, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    _require_utf8_no_surrogate(text, label)
    oracle.require_ok(len(text.encode("utf-8")) <= MAX_JSON_BYTES, "FILE_TOO_LARGE", f"{label}: JSON text exceeds byte cap")
    try:
        parsed = json.loads(
            text,
            object_pairs_hook=_reject_dup_keys,
            parse_int=_parse_bounded_int,
            parse_constant=_reject_nonfinite,
            parse_float=_reject_float,
        )
    except oracle.F2xPerfectError:
        raise
    except (ValueError, RecursionError) as exc:
        raise oracle.F2xPerfectError("INVALID_JSON", f"{label}: {exc}") from exc
    if require_object:
        oracle.require_ok(type(parsed) is dict, "JSON_ROOT_NOT_OBJECT", f"{label}: JSON root must be dict")
    _validate_json_tree(parsed, label)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    _validate_json_tree(obj, "canonical_json")
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n").encode("utf-8")


def build_certificate() -> dict[str, Any]:
    payload = oracle.compute_s22c_payload()
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


def _req_dict(obj: Any, label: str) -> dict[str, Any]:
    oracle.require_ok(type(obj) is dict, "SECONDARY_AUDIT_SCHEMA_ERROR", f"{label}: expected exact dict")
    return obj


def _req_exact_dict(obj: Any, expected_keys: frozenset[str], label: str) -> dict[str, Any]:
    d = _req_dict(obj, label)
    oracle.require_ok(set(d.keys()) == expected_keys, "SECONDARY_AUDIT_SCHEMA_ERROR", f"{label}: unexpected or missing keys")
    return d


def _req_list(obj: Any, label: str) -> list[Any]:
    oracle.require_ok(type(obj) is list, "SECONDARY_AUDIT_SCHEMA_ERROR", f"{label}: expected exact list")
    return obj


def _req_int_fields(d: dict[str, Any], keys: tuple[str, ...], label: str) -> None:
    for k in keys:
        oracle.require_exact_int(d[k], f"{label}.{k}")


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Schema-safe fail-closed strict-keyset & algebraic secondary audit on ANY crafted payload."""
    pl = _req_exact_dict(payload, _PAYLOAD_KEYS, "payload")
    _validate_json_tree(pl, "payload")
    prior_list = _req_list(pl["prior_art_quarantine_n0"], "payload.prior_art")
    p1 = _req_exact_dict(pl["pillar1_f2x_ring_and_sigma"], _P1_KEYS, "p1")
    p2 = _req_exact_dict(pl["pillar2_splitting_perfect_characterization"], _P2_KEYS, "p2")
    p3 = _req_exact_dict(pl["pillar3_canaday_11_and_deg14_census"], _P3_KEYS, "p3")
    p4 = _req_exact_dict(pl["pillar4_odd_perfect_obstruction_frontier"], _P4_KEYS, "p4")

    # P1 exact-int checks
    _req_int_fields(
        p1,
        (
            "rabin_vs_sieve_checked_deg_1_to_8",
            "rabin_vs_sieve_matches_deg_1_to_8",
            "multiplicativity_and_divisor_checks",
            "geometric_sigma_identity_checks",
        ),
        "p1",
    )
    irred_list = _req_list(p1["irred_counts_deg_1_to_12"], "p1.irreds")
    for idx, val in enumerate(irred_list):
        oracle.require_exact_int(val, f"p1.irreds[{idx}]")
    p1_anchor = _req_exact_dict(p1["canaday_anchor_x_xp1"], _P1_ANCHOR_KEYS, "p1.anchor")
    _req_int_fields(p1_anchor, ("mask", "sigma_x_mask", "sigma_xp1_mask", "sigma_a_mask", "proper_divisor_sum_char2"), "p1.anchor")

    # P2 exact-int & algebraic checks
    _req_int_fields(p2, ("max_exponent_checked", "nonconstant_pairs_checked"), "p2")
    split_pairs = _req_list(p2["perfect_splitting_pairs"], "p2.pairs")
    for idx, pair in enumerate(split_pairs):
        pr = _req_list(pair, f"p2.pairs[{idx}]")
        oracle.require_ok(len(pr) == 2, "SECONDARY_AUDIT_SCHEMA_ERROR", "splitting pair must have len 2")
        oracle.require_exact_int(pr[0], f"p2.pairs[{idx}][0]")
        oracle.require_exact_int(pr[1], f"p2.pairs[{idx}][1]")
    dual_list = _req_list(p2["duality_witnesses_n_1_to_6"], "p2.duality")
    dual_dicts = [_req_exact_dict(dw, _P2_DUAL_KEYS, f"p2.duality[{idx}]") for idx, dw in enumerate(dual_list)]
    for idx, dwd in enumerate(dual_dicts):
        _req_int_fields(dwd, ("n", "exponent_2n_minus_1", "degree"), f"p2.duality[{idx}]")
    dual_ok = len(dual_dicts) == 6
    if dual_ok:
        for idx, dwd in enumerate(dual_dicts):
            exp_n = idx + 1
            exp_e = (1 << exp_n) - 1
            if not all(
                (
                    dwd["n"] == exp_n,
                    dwd["exponent_2n_minus_1"] == exp_e,
                    dwd["degree"] == 2 * exp_e,
                    dwd["duality_exact"] is True,
                )
            ):
                dual_ok = False
    neg_list = _req_list(p2["negative_controls"], "p2.neg")
    neg_dicts = [_req_exact_dict(nc, _P2_NEG_KEYS, f"p2.neg[{idx}]") for idx, nc in enumerate(neg_list)]
    for idx, ncd in enumerate(neg_dicts):
        _req_int_fields(ncd, ("a", "b"), f"p2.neg[{idx}]")
    neg_ok = len(neg_dicts) == len(_EXPECTED_NEG_CONTROL_PAIRS)
    if neg_ok:
        for ncd, (exp_a, exp_b) in zip(neg_dicts, _EXPECTED_NEG_CONTROL_PAIRS):
            if not all(
                (
                    ncd["a"] == exp_a,
                    ncd["b"] == exp_b,
                    ncd["is_perfect"] is False,
                    oracle.sigma_from_factors({2: exp_a, 3: exp_b})
                    != oracle.poly_mul(oracle.poly_pow(2, exp_a), oracle.poly_pow(3, exp_b)),
                )
            ):
                neg_ok = False

    # P3 exact-int, rational & exact algebraic factorization checks
    _req_int_fields(
        p3,
        (
            "exhaustive_max_deg",
            "total_monic_polys_deg_1_to_14",
            "perfect_count_deg_1_to_14",
            "splitting_count_deg_1_to_14",
            "sporadic_count_deg_1_to_14",
            "canaday_11_sporadic_count",
            "canaday_11_verified_count",
            "canaday_direct_divisor_cross_checks",
            "canaday_conjugate_twin_pairs",
        ),
        "p3",
    )
    dens_q = parse_exact_rational(p3["density_deg_1_to_14_q"], "density_deg_1_to_14_q")
    spf4, cof4 = oracle.build_f2_spf_sieve(4)
    census_list = _req_list(p3["census_deg_1_to_14"], "p3.census")
    census_dicts = [_req_exact_dict(rec, _P3_CENSUS_KEYS, f"p3.census[{idx}]") for idx, rec in enumerate(census_list)]
    for idx, rd in enumerate(census_dicts):
        _req_int_fields(rd, ("mask", "degree", "shift_x_plus_1_mask"), f"p3.census[{idx}]")
    census_ok = len(census_dicts) == len(_EXPECTED_CENSUS_MASKS_14)
    if census_ok:
        for rd, exp_m in zip(census_dicts, _EXPECTED_CENSUS_MASKS_14):
            m_val = rd["mask"]
            if m_val != exp_m:
                census_ok = False
                continue
            facs = oracle.factor_with_sieve(m_val, spf4, cof4)
            if not all(
                (
                    oracle.sigma_from_factors(facs) == m_val,
                    rd["degree"] == oracle.poly_deg(m_val),
                    rd["is_splitting"] is (set(facs.keys()) <= {2, 3}),
                    rd["shift_x_plus_1_mask"] == oracle.poly_shift_x_plus_1(m_val),
                    rd["factorization"] == oracle.format_factorization_f2(facs),
                )
            ):
                census_ok = False
    can_list = _req_list(p3["canaday_11_sporadic"], "p3.canaday")
    can_dicts = [_req_exact_dict(rec, _P3_CANADAY_KEYS, f"p3.canaday[{idx}]") for idx, rec in enumerate(can_list)]
    for idx, rd in enumerate(can_dicts):
        _req_int_fields(rd, ("mask", "degree", "omega", "shift_x_plus_1_mask"), f"p3.canaday[{idx}]")
    can_ok = len(can_dicts) == len(oracle.CANADAY_11_SPORADIC_MASKS)
    if can_ok:
        for rd, exp_m in zip(can_dicts, oracle.CANADAY_11_SPORADIC_MASKS):
            m_val = rd["mask"]
            if m_val != exp_m:
                can_ok = False
                continue
            facs = oracle.factor_with_sieve(m_val, spf4, cof4)
            sh_val = oracle.poly_shift_x_plus_1(m_val)
            if not all(
                (
                    oracle.sigma_from_factors(facs) == m_val,
                    not (set(facs.keys()) <= {2, 3}),
                    rd["degree"] == oracle.poly_deg(m_val),
                    rd["omega"] == len(facs),
                    rd["shift_x_plus_1_mask"] == sh_val,
                    rd["self_symmetric"] is (sh_val == m_val),
                    rd["factorization"] == oracle.format_factorization_f2(facs),
                )
            ):
                can_ok = False
    self_sym = _req_list(p3["canaday_self_symmetric_masks"], "p3.self_sym")
    for idx, val in enumerate(self_sym):
        oracle.require_exact_int(val, f"p3.self_sym[{idx}]")

    # P4 exact-int checks
    _req_int_fields(
        p4,
        (
            "direct_odd_max_deg",
            "direct_odd_at_deg_16",
            "direct_odd_checked_deg_2_to_16",
            "direct_odd_perfect_found",
            "odd_irreducibles_tested_deg_2_to_8",
            "theorem_4a_even_exponent_witnesses",
            "theorem_4b_char2_derivative_witnesses",
            "square_lifted_max_root_deg",
            "square_lifted_max_poly_deg",
            "square_lifted_odd_squares_checked",
            "square_lifted_total_odd_polys_covered_deg_2_to_24",
            "square_lifted_odd_perfect_found",
        ),
        "p4",
    )

    ok_all = all(
        (
            pl["track_id"] == oracle.TRACK_ID,
            pl["schema_version"] == oracle.SCHEMA_VERSION,
            pl["oracle_class"] == "exact",
            pl["novelty_label"] == "N1",
            tuple(prior_list) == _EXPECTED_PRIOR_ART_N0,
            pl["all_pillars_verified"] is True,
            p1["all_verified"] is True,
            p2["all_verified"] is True,
            p3["all_verified"] is True,
            p4["all_verified"] is True,
            tuple(irred_list) == oracle.EXPECTED_IRRED_COUNTS_1_TO_12,
            p1["rabin_vs_sieve_checked_deg_1_to_8"] == 510,
            p1["rabin_vs_sieve_matches_deg_1_to_8"] == 510,
            p1["multiplicativity_and_divisor_checks"] == 6,
            p1["geometric_sigma_identity_checks"] == 36,
            p1_anchor["mask"] == 6,
            p1_anchor["poly"] == "x^2+x",
            p1_anchor["sigma_x_mask"] == 3,
            p1_anchor["sigma_xp1_mask"] == 2,
            p1_anchor["sigma_a_mask"] == 6,
            p1_anchor["proper_divisor_sum_char2"] == 0,
            p2["max_exponent_checked"] == oracle.MAX_SPLITTING_EXP,
            p2["nonconstant_pairs_checked"] == 288,
            split_pairs == [[1, 1], [3, 3], [7, 7], [15, 15]],
            p2["characterization_a_eq_b_eq_2n_minus_1"] is True,
            dual_ok,
            neg_ok,
            p3["exhaustive_max_deg"] == oracle.MAX_ALL_CENSUS_DEG,
            p3["total_monic_polys_deg_1_to_14"] == 32_766,
            p3["perfect_count_deg_1_to_14"] == 9,
            p3["splitting_count_deg_1_to_14"] == 3,
            p3["sporadic_count_deg_1_to_14"] == 6,
            p3["splitting_count_deg_1_to_14"] + p3["sporadic_count_deg_1_to_14"] == p3["perfect_count_deg_1_to_14"],
            dens_q * p3["total_monic_polys_deg_1_to_14"] == p3["perfect_count_deg_1_to_14"],
            p3["density_deg_1_to_14_dec6"] == oracle.format_decimal_rounded(dens_q, digits=6),
            p3["neg_zero_normalization_witness"] == "0.000000",
            census_ok,
            p3["canaday_11_sporadic_count"] == 11,
            p3["canaday_11_verified_count"] == 11,
            p3["canaday_direct_divisor_cross_checks"] == 6,
            can_ok,
            p3["canaday_conjugate_twin_pairs"] == 5,
            self_sym == [67184],
            p4["direct_odd_max_deg"] == oracle.MAX_ODD_DIRECT_DEG,
            p4["direct_odd_at_deg_16"] == 16_384,
            p4["direct_odd_checked_deg_2_to_16"] == 32_767,
            p4["direct_odd_perfect_found"] == 0,
            p4["odd_irreducibles_tested_deg_2_to_8"] == 69,
            p4["theorem_4a_even_exponent_witnesses"] == 276,
            p4["theorem_4a_every_odd_perfect_is_square"] is True,
            p4["theorem_4b_char2_derivative_witnesses"] == 276,
            p4["theorem_4b_sigma_p2a_never_square"] is True,
            p4["theorem_4b_unconditional_omega_ge_3"] is True,
            p4["square_lifted_max_root_deg"] == oracle.MAX_ODD_SQUARE_ROOT_DEG,
            p4["square_lifted_max_poly_deg"] == 24,
            p4["square_lifted_odd_squares_checked"] == 2_047,
            p4["square_lifted_total_odd_polys_covered_deg_2_to_24"] == 8_388_607,
            p4["square_lifted_odd_perfect_found"] == 0,
        )
    )
    oracle.require_ok(ok_all, "SECONDARY_AUDIT_FAILED", "secondary algebraic cross-check failed")
    return {"secondary_audit_passed": True}


def verify_certificate_dict(
    cert: Any,
    *,
    expected: dict[str, Any] | None = None,
    full_replay: bool = True,
) -> dict[str, Any]:
    """Fail-closed in-memory certificate verifier (schema + SHA-256 + secondary audit + optional full replay)."""
    oracle.require_exact_bool(full_replay, "full_replay")
    oracle.require_ok(type(cert) is dict, "INVALID_CERT_TYPE", "certificate must be exact dict")
    oracle.require_ok(set(cert.keys()) == _CERT_KEYS, "INVALID_CERT_KEYS", "unexpected or missing cert keys")
    _validate_json_tree(cert, "cert")
    oracle.require_ok(cert["schema_version"] == oracle.SCHEMA_VERSION, "INVALID_SCHEMA_VERSION", "schema_version mismatch")
    oracle.require_ok(cert["track_id"] == oracle.TRACK_ID, "INVALID_TRACK_ID", "track_id mismatch")
    got_psha = require_hex64_lower_ascii(cert["payload_sha256"], "payload_sha256")
    got_csha = require_hex64_lower_ascii(cert["certificate_sha256"], "certificate_sha256")
    calc_psha = hashlib.sha256(canonical_json_bytes(cert["payload"])).hexdigest()
    oracle.require_ok(
        hmac.compare_digest(got_psha, calc_psha),
        "PAYLOAD_SHA_MISMATCH",
        "payload_sha256 does not match payload",
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
        "certificate_sha256 does not match envelope",
    )
    secondary_audit_payload(cert["payload"])
    if full_replay:
        exp = build_certificate() if expected is None else expected
        oracle.require_ok(
            hmac.compare_digest(canonical_json_bytes(cert), canonical_json_bytes(exp)),
            "CERTIFICATE_MISMATCH",
            "certificate does not match freshly computed exact oracle output",
        )
    return {
        "valid": True,
        "payload_sha256": got_psha,
        "certificate_sha256": got_csha,
    }


def verify_certificate_file(cert_path: Path) -> dict[str, Any]:
    """Fail-closed file certificate verifier (atomic dir_fd read + LF-only canonical bytes + replay)."""
    raw = read_regular_bytes_capped(cert_path, "certificate")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise oracle.F2xPerfectError("INVALID_UTF8", f"certificate: invalid UTF-8 ({exc})") from exc
    oracle.require_ok("\r" not in text, "CRLF_FORBIDDEN", "certificate: CRLF line endings forbidden")
    parsed = parse_strict_json_text(text, "certificate", require_object=True)
    expected = build_certificate()
    res = verify_certificate_dict(parsed, expected=expected)
    oracle.require_ok(
        hmac.compare_digest(raw, canonical_json_bytes(expected)),
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
            sys.stdout.write(canonical_json_bytes(cert).decode("ascii"))
            return 0
        if len(args) == 2 and args[0] == "--write":
            out_path = _validate_cli_path_arg(args[1], "--write")
            cert = build_certificate()
            raw = canonical_json_bytes(cert)
            write_regular_bytes_safe(out_path, raw, "--write")
            summary = {
                "written": True,
                "file_sha256": hashlib.sha256(raw).hexdigest(),
                "payload_sha256": cert["payload_sha256"],
                "certificate_sha256": cert["certificate_sha256"],
            }
            sys.stdout.write(canonical_json_bytes(summary).decode("ascii"))
            return 0
        if len(args) == 2 and args[0] == "--check":
            cert_path = _validate_cli_path_arg(args[1], "--check")
            res = verify_certificate_file(cert_path)
            sys.stdout.write(canonical_json_bytes(res).decode("ascii"))
            return 0
        raise oracle.F2xPerfectError(
            "INVALID_CLI_ARGS",
            "usage: f2x_perfect_poly_audit.py [--standalone --json | --write <path> | --check <path>]",
        )
    except oracle.F2xPerfectError as exc:
        err_obj = {"valid": False, "error_code": exc.code, "detail": exc.detail}
        sys.stderr.write(canonical_json_bytes(err_obj).decode("ascii"))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

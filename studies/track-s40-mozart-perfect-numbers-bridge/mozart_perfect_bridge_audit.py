#!/usr/bin/env python3
"""Zone-B R2-grade hardened standalone CLI, full pure-Z/Q replay & deep secondary auditor
for Track S40 (Portal 38: Mozart Patterns -> Perfect Numbers Exact-Operator Bridge).

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero .isdigit(),
zero mathematical RNG (secrets.token_hex used strictly for atomic temp filename uniqueness).
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
from typing import Any, Sequence

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import mozart_perfect_bridge_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = oracle.MAX_INT_DIGITS  # 1,000 digits <-> aligned 3,321 bits
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PAYLOAD_KEYS = frozenset(
    {
        "track_id",
        "portal_id",
        "novelty_class",
        "pillar1_frobenius_canaday_euclid",
        "pillar2_cyclotomic_opn_obstruction",
        "pillar3_nyquist_pentagonal_ramanujan",
        "pillar4_anti_numerology_control",
        "summary",
    }
)
_P1_KEYS = frozenset(
    {
        "mozart_2n_nilpotence",
        "canaday_splitting_perfect_n1_to_n6",
        "euclid_euler_even_perfect_p2_to_p19",
        "composite_exponent_m4_contrast",
        "all_verified",
    }
)
_P2_KEYS = frozenset(
    {
        "cyclotomic_mozart_obstructions",
        "cyclotomic_sigma_factorization",
        "f2_odd_perfect_square_theorem",
        "z_carry_propagation_obstruction",
        "all_verified",
    }
)
_P3_KEYS = frozenset(
    {
        "spectral_prism_comparison",
        "sigma_raw_R2_to_R5_all_gt_17_over_5",
        "sigma_ms_R2_to_R5_all_gt_18_over_5",
        "strict_nyquist_ordering_verified",
        "euler_pentagonal_annihilator",
        "ramanujan_e2_e4_convolution",
        "all_verified",
    }
)
_P4_KEYS = frozenset(
    {
        "transposition_invariance_control",
        "radix_invariance_control",
        "golden_ratio_bar_count_refutation",
        "all_verified",
    }
)
_SUMMARY_KEYS = frozenset(
    {
        "pillar_count",
        "all_four_pillars_verified",
        "integer_opn_conjecture_remains_open",
        "float_count_on_trust_path",
        "bare_assert_count",
        "rng_calls",
    }
)
_P1_MOZART_KEYS = frozenset(
    {"case_id", "exponent_n", "f2_annihilation_rem", "f2_frobenius_exact", "length", "outcome", "steps_to_zero", "verified"}
)
_P1_CANADAY_KEYS = frozenset(
    {
        "degree",
        "direct_divisor_sum_checked",
        "direct_divisor_sum_exact",
        "exponent_2n_minus_1",
        "frobenius_identity_exact",
        "n",
        "quotient_by_x_plus_1_exact",
        "sigma_An_eq_An",
        "sigma_x_eq_xp1_pow",
        "sigma_xp1_eq_x_pow",
        "verified",
    }
)
_P1_EUCLID_KEYS = frozenset(
    {
        "Mp_is_prime",
        "direct_divisor_sum_checked",
        "direct_divisor_sum_exact",
        "even_perfect_N",
        "mersenne_Mp",
        "p",
        "sigma_2pm1_eq_Mp",
        "sigma_N_eq_2N",
        "verified",
    }
)
_P1_M4_KEYS = frozenset(
    {
        "f2_A2_perfect_verified",
        "f2_x4_plus_1_eq_xp1_pow4",
        "m",
        "verified",
        "z_2powm_minus_1",
        "z_abundant_excess",
        "z_candidate_N",
        "z_factors",
        "z_is_prime",
        "z_sigma_N",
        "z_two_N",
    }
)
_P2_CYC_OBS_KEYS = frozenset(
    {"L", "case_id", "divisors", "ducci_cycle_period", "ducci_outcome", "factorization_exact", "odd_cyclotomic_coprime_to_delta_f2", "verified"}
)
_P2_CYC_SIG_KEYS = frozenset({"f2_prime_power_checks", "f2_prime_power_exact", "verified", "z_prime_power_checks", "z_prime_power_exact"})
_P2_SQ_THM_KEYS = frozenset(
    {
        "every_f2_odd_perfect_poly_must_be_square",
        "non_square_odd_composites_blocked",
        "non_square_odd_composites_checked",
        "odd_irreducibles_deg2_to_6_count",
        "odd_prime_power_cases_checked",
        "odd_prime_power_divisible_by_x_xp1",
    }
)
_P2_CARRY_KEYS = frozenset(
    {"euler_primes_1_mod_4", "f2_parity_collapse_does_not_prove_integer_opn", "integer_opn_conjecture_remains_open", "mod3_control_primes", "verified"}
)
_P2_EULER_P_KEYS = frozenset({"exact_single_factor_of_2", "phi2_q", "q", "q_mod_4", "v2_sigma_q1", "v2_sigma_q5"})
_P2_MOD3_P_KEYS = frozenset({"blocked_by_4_div_q_plus_1", "q", "q_mod_4", "v2_sigma_q1"})
_P3_PRISM_KEYS = frozenset(
    {"energies_E1_to_E5", "length", "ms_ratios_R2_to_R5_dec6", "ms_ratios_R2_to_R5_q", "name", "ratios_R2_to_R5_dec6", "ratios_R2_to_R5_q"}
)
_P3_EP_KEYS = frozenset(
    {
        "delta2_pent_minus_const_3",
        "delta2_pent_plus_const_3",
        "delta3_pent_minus_zero",
        "delta3_pent_plus_zero",
        "n_checked",
        "sign_seq_period4_alberti_s2_plus_I_zero",
        "sign_seq_period4_alberti_s4_minus_I_zero",
        "verified",
        "zero_residual_count",
    }
)
_P3_RAM_KEYS = frozenset(
    {"general_e2_e4_zero_residual_count", "n_checked_1_to_64", "perfect_number_witnesses", "perfect_specialization_hits_1_to_64", "verified"}
)
_P3_RAM_W_KEYS = frozenset({"lhs_12_conv", "n", "rhs_general_e2_e4", "rhs_perfect_2n_1m6n", "sigma_1", "sigma_3", "verified"})
_P4_TC_KEYS = frozenset({"cases", "stage_b_invariant_stage_a_broken"})
_P4_TC_ROW_KEYS = frozenset(
    {"semitone_shift", "stage_a_c_pitch_class_count", "stage_a_histogram_preserved", "stage_b_energies_identical", "stage_b_ratios_identical"}
)
_P4_RC_KEYS = frozenset({"cases", "stage_b_invariant_base10_artifact_broken"})
_P4_RC_ROW_KEYS = frozenset(
    {"base", "digit_sums_6_28_496", "ends_in_6_or_8_in_this_base", "last_digits_6_28_496", "stage_b_sigma_eq_2N_all_3"}
)
_P4_GC_KEYS = frozenset({"all_reject_golden_numerology", "cases", "phi_inv_bracket_verified"})
_P4_GC_ROW_KEYS = frozenset({"a", "a_over_b_q", "b", "exact_golden_defect_Z", "min_deviation_exceeds_2pct", "nonzero_defect", "sonata"})
_EXPECTED_P1_MOZART: tuple[tuple[str, int, int, int], ...] = (
    ("K551_4note_CDFE", 4, 2, 4),
    ("K545_Alberti_4", 4, 2, 4),
    ("K551_8note", 8, 3, 7),
    ("K550_8note", 8, 3, 8),
)
_EXPECTED_EUCLID_PS: tuple[int, ...] = (2, 3, 5, 7, 13, 17, 19)
_EXPECTED_CYC_OBS: tuple[tuple[str, int, int, list[int]], ...] = (
    ("K550_3note_sigh", 3, 3, [1, 3]),
    ("F2_impulse_L5", 5, 15, [1, 5]),
    ("K331_6_8_bar", 6, 6, [1, 2, 3, 6]),
)
_EXPECTED_EULER_PRIMES: tuple[int, ...] = (5, 13, 17, 29, 37, 41)
_EXPECTED_MOD3_PRIMES: tuple[int, ...] = (3, 7, 11, 19)
_EXPECTED_PRISM_SPECS: tuple[tuple[str, int, list[int]], ...] = (
    ("quadratic_n2_1_to_32", 32, [43679, 120, 0, 0, 0]),
    ("K550_phrase_20", 20, [87, 161, 441, 1359, 4486]),
    ("K545_Alberti_16", 16, [415, 1432, 5248, 19584, 72384]),
    ("sigma_1_to_32", 32, [10016, 35739, 127326, 446996, 1558662]),
)
_EXPECTED_TRANSP_ROWS: tuple[tuple[int, int], ...] = ((0, 4), (1, 0), (5, 8), (7, 0), (12, 4))
_EXPECTED_RADIX_BASES: tuple[int, ...] = (2, 8, 10, 12, 16)
_EXPECTED_GOLDEN_ROWS: tuple[tuple[str, int, int], ...] = (
    ("K.282_I", 15, 21),
    ("K.283_I", 53, 67),
    ("K.332_I", 93, 136),
    ("K.576_I", 58, 102),
)
_PRISM_NAMES = frozenset({"quadratic_n2_1_to_32", "K550_phrase_20", "K545_Alberti_16", "sigma_1_to_32"})
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
_TEMP_NAME_LOCK = threading.Lock()
_TEMP_COUNTER = 0


# ============================================================================
# 1. Zone-B Path, CWD, Atomic dir_fd Traversal & Durable Atomic Write
# ============================================================================

def _require_utf8_no_surrogate(text: Any, label: str) -> str:
    if type(text) is not str:
        raise oracle.MozartPerfectBridgeError("INVALID_STR", f"{label}: exact str required")
    oracle.require_ok("\x00" not in text, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise oracle.MozartPerfectBridgeError(
            "INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden"
        ) from exc
    return text


def _require_concrete_path(path: Any, label: str) -> Path:
    oracle.require_ok(
        type(path) in _EXACT_PATH_TYPES,
        "INVALID_PATH_TYPE",
        f"{label}: concrete pathlib.Path required",
    )
    _require_utf8_no_surrogate(str(path), label)
    return path


def _safe_cwd(label: str) -> Path:
    try:
        return Path.cwd()
    except OSError as exc:
        raise oracle.MozartPerfectBridgeError(
            "CWD_UNAVAILABLE", f"{label}: CWD unavailable ({type(exc).__name__})"
        ) from exc


def _check_pwd_no_symlinks(label: str) -> None:
    pwd = os.environ.get("PWD", "")
    if pwd.startswith("/"):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_path = Path(pwd)
        try:
            dfd = os.open("/", _DIR_OPEN_FLAGS)
        except OSError as exc:
            raise oracle.MozartPerfectBridgeError("CWD_UNAVAILABLE", f"{label}: cannot open root for PWD") from exc
        try:
            for part in pwd_path.parts[1:]:
                if part == ".":
                    continue
                try:
                    next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
                except OSError as exc:
                    if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                        raise oracle.MozartPerfectBridgeError(
                            "SYMLINK_ANCESTOR_FORBIDDEN", f"{label}: symlink PWD ancestor forbidden"
                        ) from exc
                    raise oracle.MozartPerfectBridgeError(
                        "CWD_UNAVAILABLE", f"{label}: PWD ancestor unavailable ({type(exc).__name__})"
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
    err_code = "FILE_WRITE_ERROR" if create_parents else "FILE_READ_ERROR"
    try:
        dfd = os.open("/", _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise oracle.MozartPerfectBridgeError(err_code, f"{label}: cannot open root") from exc
    try:
        for part in parent_parts:
            if part == ".":
                continue
            try:
                next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
            except OSError as exc:
                if create_parents and exc.errno == errno.ENOENT:
                    try:
                        os.mkdir(part, 0o755, dir_fd=dfd)
                    except FileExistsError:
                        pass
                    except OSError as mk_exc:
                        raise oracle.MozartPerfectBridgeError(
                            "FILE_WRITE_ERROR", f"{label}: mkdir failed ({type(mk_exc).__name__})"
                        ) from mk_exc
                    try:
                        next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
                    except OSError as re_exc:
                        raise oracle.MozartPerfectBridgeError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({type(re_exc).__name__})"
                        ) from re_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise oracle.MozartPerfectBridgeError(
                        "SYMLINK_FORBIDDEN", f"{label}: symlink or non-directory ancestor forbidden"
                    ) from exc
                else:
                    raise oracle.MozartPerfectBridgeError(
                        err_code, f"{label}: cannot traverse ancestor ({type(exc).__name__})"
                    ) from exc
            os.close(dfd)
            dfd = next_fd
        return dfd, leaf
    except BaseException:
        os.close(dfd)
        raise


def read_regular_bytes_capped(path: Path, label: str = "file", max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes under strict cap using atomic dir_fd openat + fstat S_ISREG + 64 KiB chunks."""
    target = _require_concrete_path(path, label)
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_ALLOWED_CAP_BYTES)
    dfd, leaf = _open_dir_chain(target, label, create_parents=False)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            fd = os.open(leaf, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise oracle.MozartPerfectBridgeError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.MozartPerfectBridgeError(
                "FILE_READ_ERROR", f"{label}: cannot open ({type(exc).__name__})"
            ) from exc
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
    except oracle.MozartPerfectBridgeError:
        raise
    except OSError as exc:
        raise oracle.MozartPerfectBridgeError("FILE_READ_ERROR", f"{label}: read failed ({type(exc).__name__})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str = "output") -> None:
    """Durable atomic dir_fd write: 0o600 temp, lock+counter+CSPRNG+EEXIST retry, fsync, st_nlink==1, os.replace, dir fsync."""
    global _TEMP_COUNTER
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
            raise oracle.MozartPerfectBridgeError(
                "FILE_WRITE_ERROR", f"{label}: lstat failed ({type(exc).__name__})"
            ) from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")

        pid = os.getpid()
        for _ in range(64):
            with _TEMP_NAME_LOCK:
                _TEMP_COUNTER += 1
                seq_num = _TEMP_COUNTER
                cand = f".s40.{pid}.{seq_num}.{secrets.token_hex(8)}.tmp"
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
                raise oracle.MozartPerfectBridgeError(
                    "FILE_WRITE_ERROR", f"{label}: create temp failed ({type(exc).__name__})"
                ) from exc
        else:
            raise oracle.MozartPerfectBridgeError("FILE_WRITE_ERROR", f"{label}: exhausted temp file slots")

        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(st_tmp.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: temp link count altered")
        except oracle.MozartPerfectBridgeError:
            raise
        except OSError as exc:
            raise oracle.MozartPerfectBridgeError(
                "FILE_WRITE_ERROR", f"{label}: write failed ({type(exc).__name__})"
            ) from exc
        finally:
            os.close(fd)

        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.MozartPerfectBridgeError(
                "FILE_WRITE_ERROR", f"{label}: atomic replace failed ({type(exc).__name__})"
            ) from exc
    finally:
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ============================================================================
# 2. Strict ASCII Parsers, Aligned 3,321-Bit Validation & Canonical JSON
# ============================================================================

def require_hex64_lower_ascii(val: Any, label: str = "sha256") -> str:
    s = _require_utf8_no_surrogate(val, label)
    oracle.require_ok(len(s) == 64, "INVALID_HEX64", f"{label}: expected 64-char lowercase ASCII hex")
    for ch in s:
        oracle.require_ok(ch in _HEX_LOWER, "INVALID_HEX64", f"{label}: non-hex-lowercase char")
    return s


def _parse_bounded_int(token: str) -> int:
    """Strict ASCII-only 0-9 signed integer parser aligned with 3,321-bit / 1,000-digit cap."""
    s = _require_utf8_no_surrogate(token, "json_int")
    oracle.require_ok(s != "-0", "INVALID_JSON_INT", "negative zero forbidden")
    digits = s[1:] if s.startswith("-") else s
    oracle.require_ok(len(digits) >= 1, "INVALID_JSON_INT", "JSON int has no digits")
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    oracle.require_ok(digits == "0" or not digits.startswith("0"), "INVALID_JSON_INT", "leading zero forbidden")
    for ch in digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_JSON_INT", "non-ASCII digit forbidden")
    val = int(s)
    oracle.require_ok(val.bit_length() <= oracle.MAX_INT_BITS, "INT_BIT_LIMIT", "JSON int exceeds 3,321-bit cap")
    return val


def parse_exact_rational(token: Any, label: str = "rational") -> Fraction:
    """Strict ASCII-only canonical exact rational parser ('n' or reduced 'n/d' with d >= 2)."""
    s = _require_utf8_no_surrogate(token, label)
    parts = s.split("/")
    oracle.require_ok(len(parts) in (1, 2), "INVALID_RATIONAL", f"{label}: expected 'n' or 'n/d'")
    num = _parse_bounded_int(parts[0])
    if len(parts) == 1:
        return oracle.require_exact_fraction(Fraction(num, 1), label)
    den = _parse_bounded_int(parts[1])
    oracle.require_ok(den >= 2, "INVALID_RATIONAL", f"{label}: denominator must be >= 2")
    oracle.require_ok(math.gcd(abs(num), den) == 1, "NON_CANONICAL_RATIONAL", f"{label}: not in lowest terms")
    return oracle.require_exact_fraction(Fraction(num, den), label)


def _validate_json_tree(root: Any, label: str = "json") -> None:
    """Iterative validator: depth cap (blocks cycles), aligned 3,321-bit cap, UTF-8 surrogates, zero floats."""
    stack: list[tuple[Any, int]] = [(root, 0)]
    while stack:
        node, depth = stack.pop()
        oracle.require_ok(depth <= MAX_JSON_DEPTH, "JSON_DEPTH_LIMIT", f"{label}: nesting exceeds {MAX_JSON_DEPTH}")
        t = type(node)
        if node is None or t is bool:
            continue
        if t is int:
            oracle.require_ok(node.bit_length() <= oracle.MAX_INT_BITS, "INT_BIT_LIMIT", f"{label}: int exceeds 3,321 bits")
            continue
        if t is str:
            _require_utf8_no_surrogate(node, label)
            continue
        if t is list:
            nxt = depth + 1
            for item in node:
                stack.append((item, nxt))
            continue
        if t is dict:
            nxt = depth + 1
            for k, v in node.items():
                _require_utf8_no_surrogate(k, f"{label}.key")
                stack.append((v, nxt))
            continue
        raise oracle.MozartPerfectBridgeError("FORBIDDEN_JSON_TYPE", f"{label}: unsupported type {t.__name__}")


def _reject_float(token: str) -> Any:
    raise oracle.MozartPerfectBridgeError("FLOAT_LITERAL_FORBIDDEN", f"float literal forbidden: {token}")


def _reject_constant(token: str) -> Any:
    raise oracle.MozartPerfectBridgeError("NONFINITE_LITERAL_FORBIDDEN", f"non-finite constant forbidden: {token}")


def _strict_pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        _require_utf8_no_surrogate(k, "json_key")
        oracle.require_ok(k not in out, "DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def parse_strict_json_text(
    text: Any,
    *,
    require_object: bool = True,
    max_bytes: int = MAX_JSON_BYTES,
) -> Any:
    s = _require_utf8_no_surrogate(text, "json_text")
    oracle.require_exact_bool(require_object, "require_object")
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_ALLOWED_CAP_BYTES)
    oracle.require_ok(len(s.encode("utf-8")) <= max_bytes, "JSON_TOO_LARGE", "JSON text exceeds byte cap")
    try:
        parsed = json.loads(
            s,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            parse_int=_parse_bounded_int,
            object_pairs_hook=_strict_pairs_hook,
        )
    except oracle.MozartPerfectBridgeError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise oracle.MozartPerfectBridgeError("JSON_PARSE_ERROR", f"invalid JSON ({type(exc).__name__})") from exc
    _validate_json_tree(parsed, "parsed_json")
    if require_object and type(parsed) is not dict:
        raise oracle.MozartPerfectBridgeError("JSON_ROOT_NOT_OBJECT", "JSON root must be an object")
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    _validate_json_tree(obj, "canonical_json")
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _sha256_canonical(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


# ============================================================================
# 3. Deep Schema-Safe Secondary Auditor (Full Enforcement Under full_replay=False)
# ============================================================================

def _req_dict(val: Any, label: str, expected_keys: frozenset[str] | None = None) -> dict[str, Any]:
    oracle.require_ok(type(val) is dict, "INVALID_SCHEMA_DICT", f"{label}: exact dict required")
    if expected_keys is not None:
        oracle.require_ok(frozenset(val.keys()) == expected_keys, "INVALID_SCHEMA_KEYS", f"{label}: key set mismatch")
    return val


def _req_list(val: Any, label: str, exact_len: int) -> list[Any]:
    oracle.require_ok(type(val) is list and len(val) == exact_len, "INVALID_SCHEMA_LIST", f"{label}: list len {exact_len} required")
    return val


def _req_int_f(obj: dict[str, Any], key: str, label: str) -> int:
    oracle.require_ok(key in obj, "MISSING_FIELD", f"{label}: missing {key!r}")
    return oracle.require_exact_int(obj[key], f"{label}.{key}")


def _req_bool_f(obj: dict[str, Any], key: str, label: str) -> bool:
    oracle.require_ok(key in obj, "MISSING_FIELD", f"{label}: missing {key!r}")
    return oracle.require_exact_bool(obj[key], f"{label}.{key}")


def _req_int_list(val: Any, label: str, exact_len: int) -> list[int]:
    items = _req_list(val, label, exact_len)
    return [oracle.require_exact_int(v, f"{label}[{i}]") for i, v in enumerate(items)]


def _v2_pos(val: int) -> int:
    return (val & -val).bit_length() - 1


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Schema-safe fail-closed strict-keyset & algebraic secondary cross-check across ALL 4 pillars."""
    pl = _req_dict(payload, "payload", _PAYLOAD_KEYS)
    _validate_json_tree(pl, "payload")
    p1 = _req_dict(pl["pillar1_frobenius_canaday_euclid"], "p1", _P1_KEYS)
    p2 = _req_dict(pl["pillar2_cyclotomic_opn_obstruction"], "p2", _P2_KEYS)
    p3 = _req_dict(pl["pillar3_nyquist_pentagonal_ramanujan"], "p3", _P3_KEYS)
    p4 = _req_dict(pl["pillar4_anti_numerology_control"], "p4", _P4_KEYS)
    summ = _req_dict(pl["summary"], "summary", _SUMMARY_KEYS)

    # Pillar 1: Mozart 2^n nilpotence, Canaday n=1..6, Euclid-Euler p=2..19, m=4 contrast
    m_nil = _req_list(p1["mozart_2n_nilpotence"], "p1.mozart", 4)
    p1_moz_ok = True
    for i, (row, (exp_cid, exp_ln, exp_en, exp_st)) in enumerate(zip(m_nil, _EXPECTED_P1_MOZART)):
        rd = _req_dict(row, f"p1.mozart[{i}]", _P1_MOZART_KEYS)
        cid = _require_utf8_no_surrogate(rd["case_id"], f"p1.mozart[{i}].case_id")
        ln = _req_int_f(rd, "length", f"p1.mozart[{i}]")
        en = _req_int_f(rd, "exponent_n", f"p1.mozart[{i}]")
        st = _req_int_f(rd, "steps_to_zero", f"p1.mozart[{i}]")
        rem = _req_int_f(rd, "f2_annihilation_rem", f"p1.mozart[{i}]")
        out_s = _require_utf8_no_surrogate(rd["outcome"], f"p1.mozart[{i}].outcome")
        b_frob = _req_bool_f(rd, "f2_frobenius_exact", f"p1.mozart[{i}]")
        b_ver = _req_bool_f(rd, "verified", f"p1.mozart[{i}]")
        if en != exp_en:
            p1_moz_ok = False
            continue
        if not all(
            (
                cid == exp_cid,
                ln == exp_ln,
                ln == (1 << en),
                st == exp_st,
                0 < st <= ln,
                rem == 0,
                out_s == "ZERO",
                b_frob,
                b_ver,
            )
        ):
            p1_moz_ok = False

    can_rows = _req_list(p1["canaday_splitting_perfect_n1_to_n6"], "p1.canaday", 6)
    can_degs: list[int] = []
    p1_can_ok = True
    for i, row in enumerate(can_rows):
        rd = _req_dict(row, f"p1.canaday[{i}]", _P1_CANADAY_KEYS)
        nv = _req_int_f(rd, "n", f"p1.canaday[{i}]")
        ev = _req_int_f(rd, "exponent_2n_minus_1", f"p1.canaday[{i}]")
        dv = _req_int_f(rd, "degree", f"p1.canaday[{i}]")
        b_frob = _req_bool_f(rd, "frobenius_identity_exact", f"p1.canaday[{i}]")
        b_quot = _req_bool_f(rd, "quotient_by_x_plus_1_exact", f"p1.canaday[{i}]")
        b_sx = _req_bool_f(rd, "sigma_x_eq_xp1_pow", f"p1.canaday[{i}]")
        b_sxp = _req_bool_f(rd, "sigma_xp1_eq_x_pow", f"p1.canaday[{i}]")
        b_sa = _req_bool_f(rd, "sigma_An_eq_An", f"p1.canaday[{i}]")
        b_dc = _req_bool_f(rd, "direct_divisor_sum_checked", f"p1.canaday[{i}]")
        b_de = _req_bool_f(rd, "direct_divisor_sum_exact", f"p1.canaday[{i}]")
        b_ver = _req_bool_f(rd, "verified", f"p1.canaday[{i}]")
        can_degs.append(dv)
        if nv != i + 1:
            p1_can_ok = False
            continue
        if not all(
            (
                ev == (1 << nv) - 1,
                dv == 2 * ev,
                b_frob,
                b_quot,
                b_sx,
                b_sxp,
                b_sa,
                b_dc is (nv <= 3),
                b_de,
                b_ver,
            )
        ):
            p1_can_ok = False

    euc_rows = _req_list(p1["euclid_euler_even_perfect_p2_to_p19"], "p1.euclid", 7)
    euc_ps: list[int] = []
    p1_euc_ok = True
    for i, (row, exp_p) in enumerate(zip(euc_rows, _EXPECTED_EUCLID_PS)):
        rd = _req_dict(row, f"p1.euclid[{i}]", _P1_EUCLID_KEYS)
        pv = _req_int_f(rd, "p", f"p1.euclid[{i}]")
        mp = _req_int_f(rd, "mersenne_Mp", f"p1.euclid[{i}]")
        np = _req_int_f(rd, "even_perfect_N", f"p1.euclid[{i}]")
        b_mp = _req_bool_f(rd, "Mp_is_prime", f"p1.euclid[{i}]")
        b_s2 = _req_bool_f(rd, "sigma_2pm1_eq_Mp", f"p1.euclid[{i}]")
        b_sn = _req_bool_f(rd, "sigma_N_eq_2N", f"p1.euclid[{i}]")
        b_dc = _req_bool_f(rd, "direct_divisor_sum_checked", f"p1.euclid[{i}]")
        b_de = _req_bool_f(rd, "direct_divisor_sum_exact", f"p1.euclid[{i}]")
        b_ver = _req_bool_f(rd, "verified", f"p1.euclid[{i}]")
        euc_ps.append(pv)
        if pv != exp_p:
            p1_euc_ok = False
            continue
        exp_mp = (1 << pv) - 1
        if mp != exp_mp:
            p1_euc_ok = False
            continue
        if not all(
            (
                np == (1 << (pv - 1)) * mp,
                oracle.is_prime_exact(mp),
                b_mp,
                b_s2,
                b_sn,
                b_dc is (pv <= 7),
                b_de,
                b_ver,
            )
        ):
            p1_euc_ok = False

    cc = _req_dict(p1["composite_exponent_m4_contrast"], "p1.m4", _P1_M4_KEYS)
    p1_cc_ok = all(
        (
            _req_int_f(cc, "m", "p1.m4") == 4,
            _req_int_f(cc, "z_2powm_minus_1", "p1.m4") == 15,
            _req_int_list(cc["z_factors"], "p1.m4.z_factors", 2) == [3, 5],
            _req_bool_f(cc, "z_is_prime", "p1.m4") is False,
            _req_int_f(cc, "z_candidate_N", "p1.m4") == 120,
            _req_int_f(cc, "z_two_N", "p1.m4") == 240,
            _req_int_f(cc, "z_sigma_N", "p1.m4") == 360,
            _req_int_f(cc, "z_abundant_excess", "p1.m4") == 120,
            _req_bool_f(cc, "f2_x4_plus_1_eq_xp1_pow4", "p1.m4") is True,
            _req_bool_f(cc, "f2_A2_perfect_verified", "p1.m4") is True,
            _req_bool_f(cc, "verified", "p1.m4") is True,
        )
    )

    # Pillar 2: Cyclotomic obstructions, sigma factorization, F_2[x] square theorem, Z carry obstruction
    cyc_obs = _req_list(p2["cyclotomic_mozart_obstructions"], "p2.cyc_obs", 3)
    cyc_periods: list[int] = []
    p2_cyc_ok = True
    for i, (row, (exp_cid, exp_l, exp_per, exp_divs)) in enumerate(zip(cyc_obs, _EXPECTED_CYC_OBS)):
        rd = _req_dict(row, f"p2.cyc_obs[{i}]", _P2_CYC_OBS_KEYS)
        cid = _require_utf8_no_surrogate(rd["case_id"], f"p2.cyc_obs[{i}].case_id")
        l_val = _req_int_f(rd, "L", f"p2.cyc_obs[{i}]")
        per_val = _req_int_f(rd, "ducci_cycle_period", f"p2.cyc_obs[{i}]")
        divs_val = _req_int_list(rd["divisors"], f"p2.cyc_obs[{i}].divisors", len(exp_divs))
        out_val = _require_utf8_no_surrogate(rd["ducci_outcome"], f"p2.cyc_obs[{i}].outcome")
        cyc_periods.append(per_val)
        if not all(
            (
                cid == exp_cid,
                l_val == exp_l,
                per_val == exp_per,
                divs_val == exp_divs,
                out_val == "CYCLE",
                _req_bool_f(rd, "factorization_exact", f"p2.cyc_obs[{i}]"),
                _req_bool_f(rd, "odd_cyclotomic_coprime_to_delta_f2", f"p2.cyc_obs[{i}]"),
                _req_bool_f(rd, "verified", f"p2.cyc_obs[{i}]"),
            )
        ):
            p2_cyc_ok = False

    cyc_sig = _req_dict(p2["cyclotomic_sigma_factorization"], "p2.cyc_sig", _P2_CYC_SIG_KEYS)
    sq_thm = _req_dict(p2["f2_odd_perfect_square_theorem"], "p2.sq_thm", _P2_SQ_THM_KEYS)
    carry = _req_dict(p2["z_carry_propagation_obstruction"], "p2.carry", _P2_CARRY_KEYS)
    eul_p = _req_list(carry["euler_primes_1_mod_4"], "p2.carry.euler", 6)
    mod3_p = _req_list(carry["mod3_control_primes"], "p2.carry.mod3", 4)
    p2_carry_rows_ok = True
    for i, (row, exp_q) in enumerate(zip(eul_p, _EXPECTED_EULER_PRIMES)):
        rd = _req_dict(row, f"p2.carry.euler[{i}]", _P2_EULER_P_KEYS)
        qv = _req_int_f(rd, "q", f"p2.carry.euler[{i}]")
        qm4 = _req_int_f(rd, "q_mod_4", f"p2.carry.euler[{i}]")
        phi2 = _req_int_f(rd, "phi2_q", f"p2.carry.euler[{i}]")
        v2_1 = _req_int_f(rd, "v2_sigma_q1", f"p2.carry.euler[{i}]")
        v2_5 = _req_int_f(rd, "v2_sigma_q5", f"p2.carry.euler[{i}]")
        b_sf = _req_bool_f(rd, "exact_single_factor_of_2", f"p2.carry.euler[{i}]")
        if qv != exp_q:
            p2_carry_rows_ok = False
            continue
        if not all(
            (
                oracle.is_prime_exact(qv),
                qv % 4 == 1,
                qm4 == 1,
                phi2 == qv + 1,
                v2_1 == _v2_pos(qv + 1),
                v2_1 == 1,
                v2_5 == _v2_pos(sum(qv**k for k in range(6))),
                v2_5 == 1,
                b_sf,
            )
        ):
            p2_carry_rows_ok = False
    for i, (row, exp_q) in enumerate(zip(mod3_p, _EXPECTED_MOD3_PRIMES)):
        rd = _req_dict(row, f"p2.carry.mod3[{i}]", _P2_MOD3_P_KEYS)
        qv = _req_int_f(rd, "q", f"p2.carry.mod3[{i}]")
        qm4 = _req_int_f(rd, "q_mod_4", f"p2.carry.mod3[{i}]")
        v2_1 = _req_int_f(rd, "v2_sigma_q1", f"p2.carry.mod3[{i}]")
        b_blk = _req_bool_f(rd, "blocked_by_4_div_q_plus_1", f"p2.carry.mod3[{i}]")
        if qv != exp_q:
            p2_carry_rows_ok = False
            continue
        if not all(
            (
                oracle.is_prime_exact(qv),
                qv % 4 == 3,
                qm4 == 3,
                v2_1 == _v2_pos(qv + 1),
                v2_1 >= 2,
                b_blk,
            )
        ):
            p2_carry_rows_ok = False

    # Pillar 3: Nyquist-4 spectral prism, Euler pentagonal, Ramanujan E2<->E4
    prism_rows = _req_list(p3["spectral_prism_comparison"], "p3.prism", 4)
    r2_vals: dict[str, Fraction] = {}
    p3_prism_ratios_ok = True
    p3_sigma_raw_gt_3_4 = False
    p3_sigma_ms_gt_3_6 = False
    for i, (row, (exp_nm, exp_ln, exp_es)) in enumerate(zip(prism_rows, _EXPECTED_PRISM_SPECS)):
        rd = _req_dict(row, f"p3.prism[{i}]", _P3_PRISM_KEYS)
        nm = _require_utf8_no_surrogate(rd["name"], f"p3.prism[{i}].name")
        ln = _req_int_f(rd, "length", f"p3.prism[{i}]")
        es = _req_int_list(rd["energies_E1_to_E5"], f"p3.prism[{i}].E", 5)
        rs_raw = _req_list(rd["ratios_R2_to_R5_q"], f"p3.prism[{i}].R", 4)
        ms_raw = _req_list(rd["ms_ratios_R2_to_R5_q"], f"p3.prism[{i}].MS", 4)
        rs_dec = _req_list(rd["ratios_R2_to_R5_dec6"], f"p3.prism[{i}].Rdec", 4)
        ms_dec = _req_list(rd["ms_ratios_R2_to_R5_dec6"], f"p3.prism[{i}].MSdec", 4)
        rs = [parse_exact_rational(r, f"p3.prism[{i}].R[{j}]") for j, r in enumerate(rs_raw)]
        ms = [parse_exact_rational(r, f"p3.prism[{i}].MS[{j}]") for j, r in enumerate(ms_raw)]
        r2_vals[nm] = rs[0]
        if not all((nm == exp_nm, ln == exp_ln, es == exp_es, all(e >= 0 for e in es))):
            p3_prism_ratios_ok = False
            continue
        for j in range(4):
            n_ord = j + 2
            if es[j] == 0:
                if rs[j] != 0:
                    p3_prism_ratios_ok = False
                if ms[j] != 0:
                    p3_prism_ratios_ok = False
            else:
                if Fraction(es[j + 1], es[j]) != rs[j]:
                    p3_prism_ratios_ok = False
                if Fraction(es[j + 1] * (ln - n_ord + 1), es[j] * (ln - n_ord)) != ms[j]:
                    p3_prism_ratios_ok = False
            if rs_dec[j] != oracle.format_decimal(rs[j], 6):
                p3_prism_ratios_ok = False
            if ms_dec[j] != oracle.format_decimal(ms[j], 6):
                p3_prism_ratios_ok = False
        if nm == "sigma_1_to_32":
            p3_sigma_raw_gt_3_4 = all(r > Fraction(17, 5) for r in rs)
            p3_sigma_ms_gt_3_6 = all(r > Fraction(18, 5) for r in ms)

    oracle.require_ok(frozenset(r2_vals.keys()) == _PRISM_NAMES, "INVALID_SCHEMA_KEYS", "p3.prism names mismatch")
    p3_order_ok = (
        r2_vals["quadratic_n2_1_to_32"]
        < 1
        < r2_vals["K550_phrase_20"]
        < 2
        < 3
        < r2_vals["K545_Alberti_16"]
        < r2_vals["sigma_1_to_32"]
        < 4
    )

    ep = _req_dict(p3["euler_pentagonal_annihilator"], "p3.euler_pent", _P3_EP_KEYS)
    ram = _req_dict(p3["ramanujan_e2_e4_convolution"], "p3.ramanujan", _P3_RAM_KEYS)
    ram_hits = _req_int_list(ram["perfect_specialization_hits_1_to_64"], "p3.ram.hits", 2)
    ram_w = _req_list(ram["perfect_number_witnesses"], "p3.ramanujan.witnesses", 3)
    ram_vals: list[tuple[int, int]] = []
    ram_w_ok = True
    for i, row in enumerate(ram_w):
        rd = _req_dict(row, f"p3.ram.w[{i}]", _P3_RAM_W_KEYS)
        nv = _req_int_f(rd, "n", f"p3.ram.w[{i}]")
        s1 = _req_int_f(rd, "sigma_1", f"p3.ram.w[{i}]")
        s3 = _req_int_f(rd, "sigma_3", f"p3.ram.w[{i}]")
        lhs = _req_int_f(rd, "lhs_12_conv", f"p3.ram.w[{i}]")
        rhs_g = _req_int_f(rd, "rhs_general_e2_e4", f"p3.ram.w[{i}]")
        rhs_p = _req_int_f(rd, "rhs_perfect_2n_1m6n", f"p3.ram.w[{i}]")
        ram_vals.append((nv, lhs))
        if not all(
            (
                s1 == 2 * nv,
                rhs_g == 5 * s3 + (1 - 6 * nv) * s1,
                rhs_p == 5 * s3 + 2 * nv * (1 - 6 * nv),
                lhs == rhs_g,
                rhs_g == rhs_p,
                _req_bool_f(rd, "verified", f"p3.ram.w[{i}]"),
            )
        ):
            ram_w_ok = False

    # Pillar 4: Anti-numerology controls
    tc = _req_dict(p4["transposition_invariance_control"], "p4.transp", _P4_TC_KEYS)
    tc_cases = _req_list(tc["cases"], "p4.transp.cases", 5)
    rc = _req_dict(p4["radix_invariance_control"], "p4.radix", _P4_RC_KEYS)
    rc_cases = _req_list(rc["cases"], "p4.radix.cases", 5)
    gc = _req_dict(p4["golden_ratio_bar_count_refutation"], "p4.golden", _P4_GC_KEYS)
    gc_cases = _req_list(gc["cases"], "p4.golden.cases", 4)
    p4_rows_ok = True
    for i, (row, (exp_sh, exp_c_cnt)) in enumerate(zip(tc_cases, _EXPECTED_TRANSP_ROWS)):
        rd = _req_dict(row, f"p4.transp[{i}]", _P4_TC_ROW_KEYS)
        sh = _req_int_f(rd, "semitone_shift", f"p4.transp[{i}]")
        c_cnt = _req_int_f(rd, "stage_a_c_pitch_class_count", f"p4.transp[{i}]")
        if not all(
            (
                sh == exp_sh,
                c_cnt == exp_c_cnt,
                _req_bool_f(rd, "stage_a_histogram_preserved", f"p4.transp[{i}]") is (exp_sh % 12 == 0),
                _req_bool_f(rd, "stage_b_energies_identical", f"p4.transp[{i}]"),
                _req_bool_f(rd, "stage_b_ratios_identical", f"p4.transp[{i}]"),
            )
        ):
            p4_rows_ok = False
    for i, (row, exp_b) in enumerate(zip(rc_cases, _EXPECTED_RADIX_BASES)):
        rd = _req_dict(row, f"p4.radix[{i}]", _P4_RC_ROW_KEYS)
        bv = _req_int_f(rd, "base", f"p4.radix[{i}]")
        last_d = _req_int_list(rd["last_digits_6_28_496"], f"p4.radix[{i}].last", 3)
        d_sums = _req_int_list(rd["digit_sums_6_28_496"], f"p4.radix[{i}].sums", 3)
        if not all(
            (
                bv == exp_b,
                last_d == [6 % exp_b, 28 % exp_b, 496 % exp_b],
                d_sums == [sum(oracle.to_base_digits(nv, exp_b)) for nv in (6, 28, 496)],
                _req_bool_f(rd, "ends_in_6_or_8_in_this_base", f"p4.radix[{i}]") is (exp_b == 10),
                _req_bool_f(rd, "stage_b_sigma_eq_2N_all_3", f"p4.radix[{i}]"),
            )
        ):
            p4_rows_ok = False
    phi_inv_lo = Fraction(618_033, 1_000_000)
    phi_inv_hi = Fraction(618_034, 1_000_000)
    for i, (row, (exp_son, exp_a, exp_b)) in enumerate(zip(gc_cases, _EXPECTED_GOLDEN_ROWS)):
        rd = _req_dict(row, f"p4.golden[{i}]", _P4_GC_ROW_KEYS)
        son = _require_utf8_no_surrogate(rd["sonata"], f"p4.golden[{i}].sonata")
        a_v = _req_int_f(rd, "a", f"p4.golden[{i}]")
        b_v = _req_int_f(rd, "b", f"p4.golden[{i}]")
        df_v = _req_int_f(rd, "exact_golden_defect_Z", f"p4.golden[{i}]")
        ab_q = parse_exact_rational(rd["a_over_b_q"], f"p4.golden[{i}].ab")
        b_nz = _req_bool_f(rd, "nonzero_defect", f"p4.golden[{i}]")
        b_2p = _req_bool_f(rd, "min_deviation_exceeds_2pct", f"p4.golden[{i}]")
        if b_v <= 0:
            p4_rows_ok = False
            continue
        min_dev = (ab_q - phi_inv_hi) if ab_q > phi_inv_hi else (phi_inv_lo - ab_q)
        if not all(
            (
                son == exp_son,
                a_v == exp_a,
                b_v == exp_b,
                df_v == b_v * b_v - a_v * (a_v + b_v),
                df_v != 0,
                ab_q == Fraction(a_v, b_v),
                min_dev > Fraction(1, 50),
                b_nz,
                b_2p,
            )
        ):
            p4_rows_ok = False

    ok_all = all(
        (
            pl["track_id"] == oracle.TRACK_ID,
            pl["portal_id"] == "Portal-38",
            pl["novelty_class"] == "N1",
            _req_bool_f(p1, "all_verified", "p1") is True,
            p1_moz_ok,
            p1_can_ok,
            can_degs == [2, 6, 14, 30, 62, 126],
            p1_euc_ok,
            euc_ps == [2, 3, 5, 7, 13, 17, 19],
            p1_cc_ok,
            _req_bool_f(p2, "all_verified", "p2") is True,
            p2_cyc_ok,
            cyc_periods == [3, 15, 6],
            _req_int_f(cyc_sig, "z_prime_power_checks", "p2.cyc_sig") == 24,
            _req_int_f(cyc_sig, "z_prime_power_exact", "p2.cyc_sig") == 24,
            _req_int_f(cyc_sig, "f2_prime_power_checks", "p2.cyc_sig") == 15,
            _req_int_f(cyc_sig, "f2_prime_power_exact", "p2.cyc_sig") == 15,
            _req_bool_f(cyc_sig, "verified", "p2.cyc_sig") is True,
            _req_int_f(sq_thm, "odd_irreducibles_deg2_to_6_count", "p2.sq_thm") == 21,
            _req_int_f(sq_thm, "odd_prime_power_cases_checked", "p2.sq_thm") == 63,
            _req_int_f(sq_thm, "odd_prime_power_divisible_by_x_xp1", "p2.sq_thm") == 63,
            _req_int_f(sq_thm, "non_square_odd_composites_checked", "p2.sq_thm") == 6,
            _req_int_f(sq_thm, "non_square_odd_composites_blocked", "p2.sq_thm") == 6,
            _req_bool_f(sq_thm, "every_f2_odd_perfect_poly_must_be_square", "p2.sq_thm") is True,
            _req_bool_f(carry, "f2_parity_collapse_does_not_prove_integer_opn", "p2.carry") is True,
            _req_bool_f(carry, "integer_opn_conjecture_remains_open", "p2.carry") is True,
            _req_bool_f(carry, "verified", "p2.carry") is True,
            p2_carry_rows_ok,
            _req_bool_f(p3, "all_verified", "p3") is True,
            p3_prism_ratios_ok,
            p3_sigma_raw_gt_3_4,
            p3_sigma_ms_gt_3_6,
            p3_order_ok,
            _req_bool_f(p3, "sigma_raw_R2_to_R5_all_gt_17_over_5", "p3") is True,
            _req_bool_f(p3, "sigma_ms_R2_to_R5_all_gt_18_over_5", "p3") is True,
            _req_bool_f(p3, "strict_nyquist_ordering_verified", "p3") is True,
            _req_int_f(ep, "n_checked", "p3.ep") == 100,
            _req_int_f(ep, "zero_residual_count", "p3.ep") == 100,
            _req_bool_f(ep, "delta2_pent_plus_const_3", "p3.ep") is True,
            _req_bool_f(ep, "delta2_pent_minus_const_3", "p3.ep") is True,
            _req_bool_f(ep, "delta3_pent_plus_zero", "p3.ep") is True,
            _req_bool_f(ep, "delta3_pent_minus_zero", "p3.ep") is True,
            _req_bool_f(ep, "sign_seq_period4_alberti_s2_plus_I_zero", "p3.ep") is True,
            _req_bool_f(ep, "sign_seq_period4_alberti_s4_minus_I_zero", "p3.ep") is True,
            _req_bool_f(ep, "verified", "p3.ep") is True,
            _req_int_f(ram, "n_checked_1_to_64", "p3.ram") == 64,
            _req_int_f(ram, "general_e2_e4_zero_residual_count", "p3.ram") == 64,
            ram_hits == [6, 28],
            ram_vals == [(6, 840), (28, 116_208), (496, 694_330_560)],
            ram_w_ok,
            _req_bool_f(ram, "verified", "p3.ram") is True,
            _req_bool_f(p4, "all_verified", "p4") is True,
            _req_bool_f(tc, "stage_b_invariant_stage_a_broken", "p4.tc") is True,
            _req_bool_f(rc, "stage_b_invariant_base10_artifact_broken", "p4.rc") is True,
            _req_bool_f(gc, "phi_inv_bracket_verified", "p4.gc") is True,
            _req_bool_f(gc, "all_reject_golden_numerology", "p4.gc") is True,
            p4_rows_ok,
            _req_int_f(summ, "pillar_count", "summary") == 4,
            _req_bool_f(summ, "all_four_pillars_verified", "summary") is True,
            _req_bool_f(summ, "integer_opn_conjecture_remains_open", "summary") is True,
            _req_int_f(summ, "float_count_on_trust_path", "summary") == 0,
            _req_int_f(summ, "bare_assert_count", "summary") == 0,
            _req_int_f(summ, "rng_calls", "summary") == 0,
        )
    )
    oracle.require_ok(ok_all, "SECONDARY_AUDIT_FAILED", "secondary algebraic cross-check failed")
    return {"secondary_audit_passed": True, "pillars_audited": 4}


def build_standalone_certificate() -> dict[str, Any]:
    payload = oracle.build_payload()
    payload_sha = _sha256_canonical(payload)
    outer = {
        "schema_version": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": payload_sha,
        "payload": payload,
    }
    cert_sha = _sha256_canonical(outer)
    return {
        "schema_version": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": payload_sha,
        "certificate_sha256": cert_sha,
        "payload": payload,
    }


def verify_certificate_dict(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    oracle.require_exact_bool(full_replay, "full_replay")
    oracle.require_ok(type(cert) is dict, "INVALID_CERT_TYPE", "certificate must be exact dict")
    _validate_json_tree(cert, "cert")
    oracle.require_ok(frozenset(cert.keys()) == _CERT_KEYS, "INVALID_CERT_KEYS", "certificate keys mismatch")
    oracle.require_ok(cert["schema_version"] == oracle.SCHEMA_VERSION, "INVALID_SCHEMA", "schema_version mismatch")
    oracle.require_ok(cert["track_id"] == oracle.TRACK_ID, "INVALID_TRACK_ID", "track_id mismatch")
    oracle.require_ok(type(cert["payload"]) is dict, "INVALID_PAYLOAD_TYPE", "payload must be exact dict")

    claimed_p = require_hex64_lower_ascii(cert["payload_sha256"], "payload_sha256")
    claimed_c = require_hex64_lower_ascii(cert["certificate_sha256"], "certificate_sha256")

    actual_p = _sha256_canonical(cert["payload"])
    oracle.require_ok(hmac.compare_digest(claimed_p, actual_p), "PAYLOAD_SHA256_MISMATCH", "payload_sha256 mismatch")

    outer = {
        "schema_version": cert["schema_version"],
        "track_id": cert["track_id"],
        "payload_sha256": claimed_p,
        "payload": cert["payload"],
    }
    actual_c = _sha256_canonical(outer)
    oracle.require_ok(hmac.compare_digest(claimed_c, actual_c), "CERT_SHA256_MISMATCH", "certificate_sha256 mismatch")

    sec = secondary_audit_payload(cert["payload"])
    if full_replay:
        ref = build_standalone_certificate()
        oracle.require_ok(hmac.compare_digest(actual_p, ref["payload_sha256"]), "REPLAY_MISMATCH", "replay mismatch")

    return {
        "valid": True,
        "schema_version": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": actual_p,
        "certificate_sha256": actual_c,
        "full_replay": full_replay,
        "secondary_audit": sec,
    }


def check_certificate_file(path: Path, *, full_replay: bool = True) -> dict[str, Any]:
    raw = read_regular_bytes_capped(path, "certificate", MAX_JSON_BYTES)
    oracle.require_ok(b"\r" not in raw, "CRLF_FORBIDDEN", "CRLF line endings forbidden")
    oracle.require_ok(raw.endswith(b"\n"), "MISSING_TRAILING_LF", "certificate must end with LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise oracle.MozartPerfectBridgeError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canon = canonical_json_bytes(cert)
    oracle.require_ok(raw == canon + b"\n", "NON_CANONICAL_BYTES", "certificate is not canonical ASCII JSON + LF")
    res = verify_certificate_dict(cert, full_replay=full_replay)
    res["canonical_sha256"] = hashlib.sha256(canon).hexdigest()
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    return res


def write_certificate_file(path: Path) -> dict[str, Any]:
    cert = build_standalone_certificate()
    canon = canonical_json_bytes(cert)
    raw = canon + b"\n"
    write_regular_bytes_safe(path, raw, "certificate")
    return {
        "written": True,
        "schema_version": oracle.SCHEMA_VERSION,
        "track_id": oracle.TRACK_ID,
        "payload_sha256": cert["payload_sha256"],
        "certificate_sha256": cert["certificate_sha256"],
        "file_sha256": hashlib.sha256(raw).hexdigest(),
    }


# ============================================================================
# 4. Strict Fail-Closed CLI (Space & Equals Flag-Like Rejection)
# ============================================================================

def _reject_bad_path_arg(tok: str, val: str) -> Path:
    oracle.require_ok(bool(val) and not val.startswith("-"), "INVALID_PATH_ARG", f"{tok} path empty or flag-like")
    return Path(val)


def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    oracle.require_ok(type(argv) in (list, tuple), "INVALID_ARGV", "argv must be list or tuple")
    for item in argv:
        _require_utf8_no_surrogate(item, "argv_item")

    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = argv[i]
        if tok == "--json":
            oracle.require_ok(not as_json, "DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            oracle.require_ok(mode is None, "CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            oracle.require_ok(mode is None, "CONFLICTING_MODE", "multiple mode flags forbidden")
            oracle.require_ok(i + 1 < n, "MISSING_PATH_ARG", f"{tok} requires a path argument")
            target = _reject_bad_path_arg(tok, argv[i + 1])
            mode = "check" if tok == "--check" else "write"
            i += 2
        elif tok.startswith("--check=") or tok.startswith("--write="):
            oracle.require_ok(mode is None, "CONFLICTING_MODE", "multiple mode flags forbidden")
            flag_name, val = tok.split("=", 1)
            target = _reject_bad_path_arg(flag_name, val)
            mode = "check" if flag_name == "--check" else "write"
            i += 1
        else:
            raise oracle.MozartPerfectBridgeError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except oracle.MozartPerfectBridgeError as exc:
        err = {"valid": False, "error_code": exc.code, "error_message": exc.detail}
        sys.stderr.write(canonical_json_bytes(err).decode("ascii") + "\n")
        return 2

    if as_json:
        sys.stdout.write(canonical_json_bytes(out).decode("ascii") + "\n")
    else:
        sys.stdout.write(
            f"OK {oracle.SCHEMA_VERSION} payload_sha256={out['payload_sha256']} "
            f"certificate_sha256={out['certificate_sha256']}\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Zone-B R2-grade hardened standalone CLI & certificate verifier for Track S39 (Portal 37).

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero scientific RNG.
Uniform Zone-B Gold Standard (R2-grade built in from R1):
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
    (even with full_replay=False) + default full pure-Q deterministic replay
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

import mozart_nth_diff_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = 1_234
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PRISM_NAMES = frozenset({"Scale", "K.550", "K.331", "K.525", "K.545_Mel", "K.545_Alberti"})
_BOOL_LEAF_KEYS = frozenset(
    {
        "all_120_clean",
        "all_pillars_verified",
        "all_verified",
        "crt_bijection_and_chords_verified",
        "endpoints_match_Sp_minus_I_mod_p",
        "energies_strictly_growing",
        "exact_annihilation_verified",
        "fails_2pct_ab_ratio_test",
        "interior_binomials_zero_mod_p",
        "is_power_of_2",
        "nilpotent_iff_power_of_2_L2_to_L12",
        "operator_probe_identity_exact",
        "phi_inv_bracket_verified",
        "seam_matrix_exact_rank_1",
        "strict_textural_ordering_verified",
        "verified",
    }
)
_PAYLOAD_KEYS = frozenset(
    {
        "track_id",
        "schema_version",
        "oracle_class",
        "novelty_class",
        "pillar1_frobenius_z12",
        "pillar2_spectral_prism",
        "pillar3_ducci_nilpotence",
        "pillar4_combinatorial_invariance_cs13",
        "all_pillars_verified",
    }
)
_P1_KEYS = frozenset(
    {
        "frobenius_prime_checks",
        "frobenius_prime_power_checks",
        "k550_period3_annihilation",
        "k545_alberti_period4_annihilation",
        "crt_z12_decomposition",
        "all_verified",
    }
)
_FROB_KEYS = frozenset(
    {
        "prime_p",
        "exponent_r",
        "order_q",
        "interior_binomials_zero_mod_p",
        "endpoints_match_Sp_minus_I_mod_p",
        "operator_probe_identity_exact",
        "verified",
    }
)
_K550_KEYS = frozenset(
    {
        "opening_midi",
        "delta2_mod3",
        "delta3_raw",
        "delta3_mod3",
        "s3_minus_I_mod3",
        "leap_semitones",
        "exact_annihilation_verified",
    }
)
_K545_KEYS = frozenset(
    {
        "alberti_midi",
        "delta4_mod2",
        "s4_minus_I_exact_Z",
        "integer_energies_E1_to_E5",
        "energies_strictly_growing",
        "exact_annihilation_verified",
    }
)
_CRT_KEYS = frozenset(
    {
        "bijection_table_x_r3_r4",
        "augmented_triads_by_r4",
        "diminished_7ths_by_r3",
        "crt_bijection_and_chords_verified",
    }
)
_P2_KEYS = frozenset(
    {
        "white_noise_variances_n1_to_n5",
        "white_noise_ratios_R1_to_R5_q",
        "random_walk_ratios_R2_to_R5_q",
        "sinusoidal_gain_table",
        "unity_cutoff_lambda",
        "nyquist_ceiling",
        "mozart_corpus_prism",
        "strict_textural_ordering_verified",
        "all_verified",
    }
)
_SIN_KEYS = frozenset(
    {
        "wavelength_lambda",
        "cos_omega_q",
        "gain_exact",
        "eigenwave_energy",
        "eigenwave_diff_energy",
    }
)
_PRISM_KEYS = frozenset(
    {
        "name",
        "length",
        "energies_E1_to_E5",
        "ratios_R2_to_R5_q",
        "ratios_R2_to_R5_dec6",
    }
)
_P3_KEYS = frozenset(
    {
        "mozart_ducci_orbits",
        "f2_impulse_characterization_L2_to_L12",
        "nilpotent_iff_power_of_2_L2_to_L12",
        "all_verified",
    }
)
_DUCCI_MOZART_KEYS = frozenset(
    {
        "case_id",
        "input_midi",
        "length",
        "outcome",
        "steps_to_zero",
        "cycle_entry_step",
        "cycle_period",
        "terminal_state",
    }
)
_DUCCI_F2_KEYS = frozenset(
    {
        "L",
        "is_power_of_2",
        "outcome",
        "steps_to_zero",
        "cycle_entry_step",
        "cycle_period",
    }
)
_P4_KEYS = frozenset(
    {
        "k551_s5_quintuple_counterpoint",
        "k516f_dice_game_invariance",
        "putz_1995_cs13_anti_numerology",
        "all_verified",
    }
)
_S5_KEYS = frozenset(
    {
        "cantus_firmus_v0_pc",
        "valid_model",
        "parallel_5th_counter_model",
        "parallel_8ve_counter_model",
        "verified",
    }
)
_S5_MODEL_KEYS = frozenset(
    {
        "total_permutations",
        "clean_permutations",
        "violating_permutations",
        "all_120_clean",
        "first_violation",
    }
)
_S5_FV_KEYS = frozenset(
    {
        "perm",
        "upper_voice",
        "lower_voice",
        "step_t",
        "interval_mod12",
    }
)
_K516F_KEYS = frozenset(
    {
        "minuets_fixed_bar8",
        "minuets_two_bar8_endings",
        "seam_compatibility_11x11_sum",
        "seam_matrix_exact_rank_1",
        "matrix_product_14bar_paths",
        "broken_chromatic_seam_sum",
        "verified",
    }
)
_PUTZ_KEYS = frozenset(
    {
        "phi_inv_bracket_lo_q",
        "phi_inv_bracket_hi_q",
        "phi_inv_bracket_verified",
        "sonatas_checked",
        "nonzero_exact_defect_count",
        "negative_defect_count",
        "positive_defect_count",
        "fail_2pct_ab_count",
        "max_ab_deviation_lo_q",
        "max_ab_deviation_lo_dec6",
        "range_compression_ba_width_q",
        "range_compression_ab_width_q",
        "range_compression_factor_q",
        "sonata_splits",
        "verified",
    }
)
_PUTZ_ROW_KEYS = frozenset(
    {
        "sonata",
        "a_exposition_bars",
        "b_dev_recap_bars",
        "total_bars",
        "b_over_total_q",
        "b_over_total_dec6",
        "a_over_b_q",
        "a_over_b_dec6",
        "exact_golden_defect_Z",
        "fails_2pct_ab_ratio_test",
    }
)
_EXPECTED_FROB_PRIMES: tuple[tuple[int, int, int, bool, bool, bool, bool], ...] = (
    (2, 1, 2, True, True, True, True),
    (3, 1, 3, True, True, True, True),
    (5, 1, 5, True, True, True, True),
    (7, 1, 7, True, True, True, True),
)
_EXPECTED_FROB_POWERS: tuple[tuple[int, int, int, bool, bool, bool, bool], ...] = (
    (2, 2, 4, True, True, True, True),
    (2, 3, 8, True, True, True, True),
    (3, 2, 9, True, True, True, True),
)
_EXPECTED_SIN_SPEC: tuple[tuple[str, Fraction, int, int, int], ...] = (
    ("inf", Fraction(1, 1), 0, 4, 0),
    ("6", Fraction(1, 2), 1, 12, 12),
    ("4", Fraction(0, 1), 2, 2, 4),
    ("3", Fraction(-1, 2), 3, 6, 18),
    ("2", Fraction(-1, 1), 4, 2, 8),
)
_EXPECTED_PRISM_SPEC: tuple[tuple[str, int, tuple[int, int, int, int, int]], ...] = (
    ("Scale", 16, (48, 8, 23, 67, 198)),
    ("K.550", 20, (87, 161, 441, 1359, 4486)),
    ("K.331", 18, (92, 193, 499, 1385, 3837)),
    ("K.525", 18, (291, 808, 2562, 8292, 27208)),
    ("K.545_Mel", 17, (248, 661, 2187, 7622, 26189)),
    ("K.545_Alberti", 16, (415, 1432, 5248, 19584, 72384)),
)
_EXPECTED_MOZART_DUCCI: tuple[tuple[str, tuple[int, ...], int, str, int, int, int, tuple[int, ...]], ...] = (
    ("K551_4note_CDFE", (60, 62, 65, 64), 4, "ZERO", 4, -1, 0, (0, 0, 0, 0)),
    ("K551_8note_CDFE_EDCB", (72, 74, 77, 76, 76, 74, 72, 71), 8, "ZERO", 7, -1, 0, (0, 0, 0, 0, 0, 0, 0, 0)),
    ("K545_Alberti_L4", (60, 67, 64, 67), 4, "ZERO", 4, -1, 0, (0, 0, 0, 0)),
    ("K550_8note_phrase", (75, 74, 74, 75, 74, 74, 75, 74), 8, "ZERO", 8, -1, 0, (0, 0, 0, 0, 0, 0, 0, 0)),
    ("K550_3note_sigh_L3", (75, 74, 74), 3, "CYCLE", -1, 1, 3, (1, 0, 1)),
    ("K331_6_8_bar_L6", (73, 74, 73, 76, 76, 71), 6, "CYCLE", -1, 4, 6, (1, 1, 0, 0, 1, 1)),
)
_EXPECTED_F2_DUCCI: tuple[tuple[int, bool, str, int, int, int], ...] = (
    (2, True, "ZERO", 2, -1, 0),
    (3, False, "CYCLE", -1, 1, 3),
    (4, True, "ZERO", 4, -1, 0),
    (5, False, "CYCLE", -1, 1, 15),
    (6, False, "CYCLE", -1, 2, 6),
    (7, False, "CYCLE", -1, 1, 7),
    (8, True, "ZERO", 8, -1, 0),
    (9, False, "CYCLE", -1, 1, 63),
    (10, False, "CYCLE", -1, 2, 30),
    (11, False, "CYCLE", -1, 1, 341),
    (12, False, "CYCLE", -1, 4, 12),
)
_TEMP_NAME_LOCK = threading.Lock()
DEFAULT_CERT_NAME = "mozart_nth_diff_certificate.json"


def _require_utf8_no_surrogate(text: str, label: str) -> None:
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise oracle.MozartNthDiffError("INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden") from exc


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
        raise oracle.MozartNthDiffError("CWD_UNAVAILABLE", f"{label}: CWD unavailable ({exc})") from exc


def _check_pwd_no_symlinks(label: str) -> None:
    pwd = os.environ.get("PWD")
    if pwd and os.path.isabs(pwd):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_path = Path(pwd)
        dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        try:
            dfd = os.open("/", dir_flags)
        except OSError as exc:
            raise oracle.MozartNthDiffError("CWD_UNAVAILABLE", f"{label}: cannot open root for PWD ({exc})") from exc
        try:
            for part in pwd_path.parts[1:]:
                try:
                    next_fd = os.open(part, dir_flags, dir_fd=dfd)
                except OSError as exc:
                    if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                        raise oracle.MozartNthDiffError(
                            "SYMLINK_ANCESTOR_FORBIDDEN",
                            f"{label}: symlink PWD ancestor forbidden",
                        ) from exc
                    raise oracle.MozartNthDiffError(
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
        raise oracle.MozartNthDiffError(err_code, f"{label}: cannot open root ({exc})") from exc
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
                        raise oracle.MozartNthDiffError("FILE_WRITE_ERROR", f"{label}: mkdir failed ({mk_exc})") from mk_exc
                    try:
                        next_fd = os.open(part, dir_flags, dir_fd=dfd)
                    except OSError as reopen_exc:
                        raise oracle.MozartNthDiffError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({reopen_exc})"
                        ) from reopen_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    try:
                        is_lnk = stat.S_ISLNK(os.lstat(part, dir_fd=dfd).st_mode)
                    except OSError:
                        is_lnk = exc.errno == errno.ELOOP
                    if is_lnk:
                        raise oracle.MozartNthDiffError("SYMLINK_FORBIDDEN", f"{label}: symlink component forbidden") from exc
                    raise oracle.MozartNthDiffError(err_code, f"{label}: non-directory ancestor ({exc})") from exc
                else:
                    raise oracle.MozartNthDiffError(err_code, f"{label}: cannot open ancestor ({exc})") from exc
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
                raise oracle.MozartNthDiffError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.MozartNthDiffError("FILE_READ_ERROR", f"{label}: cannot open ({exc})") from exc
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
    except oracle.MozartNthDiffError:
        raise
    except OSError as exc:
        raise oracle.MozartNthDiffError("FILE_READ_ERROR", f"{label}: read failed ({exc})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str) -> None:
    """Write bytes atomically via dir_fd O_CREAT|O_EXCL|O_NOFOLLOW (0o600) + pre-replace nlink check + os.replace + dir fsync."""
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
            raise oracle.MozartNthDiffError("FILE_WRITE_ERROR", f"{label}: stat failed ({exc})") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")
        pid = os.getpid()
        for _ in range(64):
            with _TEMP_NAME_LOCK:
                cand = f".s39.{pid}.{secrets.token_hex(8)}.tmp"
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
                raise oracle.MozartNthDiffError("FILE_WRITE_ERROR", f"{label}: create temp failed ({exc})") from exc
        else:
            raise oracle.MozartNthDiffError("FILE_WRITE_ERROR", f"{label}: exhausted temp file slots")
        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(st_tmp.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: temp file link count altered")
        except OSError as exc:
            raise oracle.MozartNthDiffError("FILE_WRITE_ERROR", f"{label}: write failed ({exc})") from exc
        finally:
            os.close(fd)
        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.MozartNthDiffError("FILE_WRITE_ERROR", f"{label}: atomic replace failed ({exc})") from exc
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
    """Strict ASCII-only 0-9 signed integer parser (zero .isdigit(), zero -0/leading zeros)."""
    oracle.require_ok(type(token) is str, "INVALID_JSON_INT", "JSON int token must be exact str")
    oracle.require_ok(token != "-0", "INVALID_JSON_INT", "negative zero forbidden")
    digits = token[1:] if token.startswith("-") else token
    oracle.require_ok(len(digits) >= 1, "INVALID_JSON_INT", "JSON int token has no digits")
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    oracle.require_ok(digits == "0" or not digits.startswith("0"), "INVALID_JSON_INT", "leading zero forbidden")
    for ch in digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_JSON_INT", "JSON int token must contain ASCII digits 0-9 only")
    return oracle.require_exact_int(int(token), "json_int")


def parse_exact_rational(token: Any, label: str = "rational") -> Fraction:
    """Strict ASCII-only canonical exact rational parser for 'n' or reduced 'n/d' (d >= 2)."""
    oracle.require_ok(type(token) is str, "INVALID_RATIONAL", f"{label}: rational token must be exact str")
    parts = token.split("/")
    oracle.require_ok(len(parts) in (1, 2), "INVALID_RATIONAL", f"{label}: expected 'n' or 'n/d'")
    num_s = parts[0]
    oracle.require_ok(num_s != "-0", "INVALID_RATIONAL", f"{label}: negative zero forbidden")
    num_digits = num_s[1:] if num_s.startswith("-") else num_s
    oracle.require_ok(len(num_digits) >= 1, "INVALID_RATIONAL", f"{label}: empty numerator")
    oracle.require_ok(len(num_digits) <= MAX_JSON_INT_DIGITS, "INVALID_RATIONAL", f"{label}: numerator too long")
    oracle.require_ok(num_digits == "0" or not num_digits.startswith("0"), "INVALID_RATIONAL", f"{label}: leading zero")
    for ch in num_digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_RATIONAL", f"{label}: non-ASCII digit in numerator")
    num = int(num_s)
    if len(parts) == 1:
        return oracle.require_exact_fraction(Fraction(num, 1), label)
    den_s = parts[1]
    oracle.require_ok(len(den_s) >= 1, "INVALID_RATIONAL", f"{label}: empty denominator")
    oracle.require_ok(len(den_s) <= MAX_JSON_INT_DIGITS, "INVALID_RATIONAL", f"{label}: denominator too long")
    oracle.require_ok(not den_s.startswith("0"), "INVALID_RATIONAL", f"{label}: leading zero in denominator")
    for ch in den_s:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_RATIONAL", f"{label}: non-ASCII digit in denominator")
    den = int(den_s)
    oracle.require_ok(den >= 2, "INVALID_RATIONAL", f"{label}: denominator must be >= 2")
    oracle.require_ok(math.gcd(num, den) == 1, "INVALID_RATIONAL", f"{label}: non-reduced rational forbidden")
    return oracle.require_exact_fraction(Fraction(num, den), label)


def _reject_dup_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        oracle.require_ok(k not in out, "DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def _reject_nonfinite(token: str) -> Any:
    raise oracle.MozartNthDiffError("NONFINITE_JSON", f"non-finite JSON constant {token!r}")


def _reject_float(token: str) -> Any:
    raise oracle.MozartNthDiffError("FLOAT_FORBIDDEN", f"JSON float token forbidden: {token!r}")


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
            raise oracle.MozartNthDiffError("INVALID_JSON_VALUE", f"{label}: unsupported type {t.__name__}")


def parse_strict_json_text(text: str, label: str, *, require_object: bool = True) -> Any:
    oracle.require_ok(type(text) is str, "INVALID_JSON_TEXT", f"{label}: text must be exact str")
    oracle.require_exact_bool(require_object, "require_object")
    oracle.require_ok(not text.startswith("\ufeff"), "BOM_FORBIDDEN", f"{label}: UTF-8 BOM forbidden")
    oracle.require_ok("\x00" not in text, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    _require_utf8_no_surrogate(text, label)
    try:
        parsed = json.loads(
            text,
            object_pairs_hook=_reject_dup_keys,
            parse_int=_parse_bounded_int,
            parse_constant=_reject_nonfinite,
            parse_float=_reject_float,
        )
    except oracle.MozartNthDiffError:
        raise
    except (ValueError, RecursionError) as exc:
        raise oracle.MozartNthDiffError("INVALID_JSON", f"{label}: {exc}") from exc
    if require_object:
        oracle.require_ok(type(parsed) is dict, "JSON_ROOT_NOT_OBJECT", f"{label}: JSON root must be dict")
    _validate_json_tree(parsed, label)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    _validate_json_tree(obj, "canonical_json")
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n").encode("utf-8")


def build_certificate() -> dict[str, Any]:
    payload = oracle.compute_s39_payload()
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


def _req_exact_dict(obj: Any, expected_keys: frozenset[str], label: str) -> dict[str, Any]:
    oracle.require_ok(type(obj) is dict, "SECONDARY_AUDIT_SCHEMA_ERROR", f"{label}: expected exact dict")
    oracle.require_ok(
        set(obj.keys()) == expected_keys,
        "SECONDARY_AUDIT_SCHEMA_ERROR",
        f"{label}: unexpected or missing keys",
    )
    for k in expected_keys:
        if k in _BOOL_LEAF_KEYS:
            oracle.require_exact_bool(obj[k], f"{label}.{k}")
    return obj


def _req_list(obj: Any, label: str) -> list[Any]:
    oracle.require_ok(type(obj) is list, "SECONDARY_AUDIT_SCHEMA_ERROR", f"{label}: expected exact list")
    return obj


def _req_str(val: Any, label: str) -> str:
    oracle.require_ok(type(val) is str, "SECONDARY_AUDIT_SCHEMA_ERROR", f"{label}: expected exact str")
    return val


def _req_int(val: Any, label: str) -> int:
    return oracle.require_exact_int(val, label)


def _req_int_fields(d: dict[str, Any], keys: tuple[str, ...], label: str) -> None:
    for k in keys:
        _req_int(d[k], f"{label}.{k}")


def _req_int_list(obj: Any, label: str) -> list[int]:
    items = _req_list(obj, label)
    return [_req_int(v, f"{label}[{i}]") for i, v in enumerate(items)]


def _req_str_list(obj: Any, label: str) -> list[str]:
    items = _req_list(obj, label)
    return [_req_str(v, f"{label}[{i}]") for i, v in enumerate(items)]


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Schema-safe fail-closed exact-int/Q secondary algebraic cross-check on ANY crafted payload."""
    pl = _req_exact_dict(payload, _PAYLOAD_KEYS, "payload")
    _validate_json_tree(pl, "payload")
    track_id = _req_str(pl["track_id"], "payload.track_id")
    schema_ver = _req_str(pl["schema_version"], "payload.schema_version")
    oracle_cls = _req_str(pl["oracle_class"], "payload.oracle_class")
    novelty_cls = _req_str(pl["novelty_class"], "payload.novelty_class")
    p1 = _req_exact_dict(pl["pillar1_frobenius_z12"], _P1_KEYS, "p1")
    p2 = _req_exact_dict(pl["pillar2_spectral_prism"], _P2_KEYS, "p2")
    p3 = _req_exact_dict(pl["pillar3_ducci_nilpotence"], _P3_KEYS, "p3")
    p4 = _req_exact_dict(pl["pillar4_combinatorial_invariance_cs13"], _P4_KEYS, "p4")

    # Pillar 1 exact-int, keyset, & algebraic checks
    fp_checks = _req_list(p1["frobenius_prime_checks"], "p1.frobenius_prime_checks")
    fpp_checks = _req_list(p1["frobenius_prime_power_checks"], "p1.frobenius_prime_power_checks")
    frob_parsed: dict[str, list[tuple[int, int, int, bool, bool, bool, bool]]] = {
        "frobenius_prime_checks": [],
        "frobenius_prime_power_checks": [],
    }
    for blk_key, blk_list in (("frobenius_prime_checks", fp_checks), ("frobenius_prime_power_checks", fpp_checks)):
        for idx, item in enumerate(blk_list):
            it = _req_exact_dict(item, _FROB_KEYS, f"p1.{blk_key}[{idx}]")
            _req_int_fields(it, ("prime_p", "exponent_r", "order_q"), f"p1.{blk_key}[{idx}]")
            frob_parsed[blk_key].append(
                (
                    it["prime_p"],
                    it["exponent_r"],
                    it["order_q"],
                    it["interior_binomials_zero_mod_p"],
                    it["endpoints_match_Sp_minus_I_mod_p"],
                    it["operator_probe_identity_exact"],
                    it["verified"],
                )
            )
    k550 = _req_exact_dict(p1["k550_period3_annihilation"], _K550_KEYS, "p1.k550")
    k550_midi = _req_int_list(k550["opening_midi"], "p1.k550.opening_midi")
    k550_d2 = _req_int_list(k550["delta2_mod3"], "p1.k550.delta2_mod3")
    k550_d3_raw = _req_int_list(k550["delta3_raw"], "p1.k550.delta3_raw")
    k550_d3 = _req_int_list(k550["delta3_mod3"], "p1.k550.delta3_mod3")
    k550_s3 = _req_int_list(k550["s3_minus_I_mod3"], "p1.k550.s3_minus_I_mod3")
    k550_leap = _req_int(k550["leap_semitones"], "p1.k550.leap_semitones")

    k545 = _req_exact_dict(p1["k545_alberti_period4_annihilation"], _K545_KEYS, "p1.k545")
    k545_midi = _req_int_list(k545["alberti_midi"], "p1.k545.alberti_midi")
    k545_d4 = _req_int_list(k545["delta4_mod2"], "p1.k545.delta4_mod2")
    k545_s4 = _req_int_list(k545["s4_minus_I_exact_Z"], "p1.k545.s4_minus_I_exact_Z")
    k545_energies = _req_int_list(k545["integer_energies_E1_to_E5"], "p1.k545.energies")

    crt = _req_exact_dict(p1["crt_z12_decomposition"], _CRT_KEYS, "p1.crt")
    crt_table = [
        _req_int_list(row, f"p1.crt.table[{idx}]")
        for idx, row in enumerate(_req_list(crt["bijection_table_x_r3_r4"], "p1.crt.table"))
    ]
    crt_aug = [
        _req_int_list(tri, f"p1.crt.aug[{idx}]")
        for idx, tri in enumerate(_req_list(crt["augmented_triads_by_r4"], "p1.crt.aug"))
    ]
    crt_dim = [
        _req_int_list(ch, f"p1.crt.dim[{idx}]")
        for idx, ch in enumerate(_req_list(crt["diminished_7ths_by_r3"], "p1.crt.dim"))
    ]

    # Pillar 2 exact-int, rational, & spectral-prism checks
    wn_vars = _req_int_list(p2["white_noise_variances_n1_to_n5"], "p2.wn_vars")
    wn_ratios = [
        parse_exact_rational(tok, f"p2.wn_ratios[{idx}]")
        for idx, tok in enumerate(_req_list(p2["white_noise_ratios_R1_to_R5_q"], "p2.wn_ratios"))
    ]
    rw_ratios = [
        parse_exact_rational(tok, f"p2.rw_ratios[{idx}]")
        for idx, tok in enumerate(_req_list(p2["random_walk_ratios_R2_to_R5_q"], "p2.rw_ratios"))
    ]
    _req_int_fields(p2, ("unity_cutoff_lambda", "nyquist_ceiling"), "p2")
    sin_rows = _req_list(p2["sinusoidal_gain_table"], "p2.sin")
    sin_parsed: list[tuple[str, Fraction, int, int, int]] = []
    for idx, row in enumerate(sin_rows):
        rd = _req_exact_dict(row, _SIN_KEYS, f"p2.sin[{idx}]")
        wl = _req_str(rd["wavelength_lambda"], f"p2.sin[{idx}].wl")
        cos_q = parse_exact_rational(rd["cos_omega_q"], f"p2.sin[{idx}].cos")
        _req_int_fields(rd, ("gain_exact", "eigenwave_energy", "eigenwave_diff_energy"), f"p2.sin[{idx}]")
        sin_parsed.append((wl, cos_q, rd["gain_exact"], rd["eigenwave_energy"], rd["eigenwave_diff_energy"]))

    prism_rows = _req_list(p2["mozart_corpus_prism"], "p2.prism")
    r2_vals: dict[str, Fraction] = {}
    prism_meta: list[tuple[str, int, tuple[int, ...]]] = []
    prism_ratios_ok = True
    for idx, row in enumerate(prism_rows):
        rd = _req_exact_dict(row, _PRISM_KEYS, f"p2.prism[{idx}]")
        nm = _req_str(rd["name"], f"p2.prism[{idx}].name")
        ln = _req_int(rd["length"], f"p2.prism[{idx}].length")
        energies = _req_int_list(rd["energies_E1_to_E5"], f"p2.prism[{idx}].E")
        oracle.require_ok(len(energies) == 5, "SECONDARY_AUDIT_SCHEMA_ERROR", f"p2.prism[{idx}].E: expected 5 energies")
        r_list = _req_list(rd["ratios_R2_to_R5_q"], f"p2.prism[{idx}].R")
        oracle.require_ok(len(r_list) == 4, "SECONDARY_AUDIT_SCHEMA_ERROR", f"p2.prism[{idx}].R: expected 4 ratios")
        r_parsed = [parse_exact_rational(r, f"p2.prism[{idx}].R[{j}]") for j, r in enumerate(r_list)]
        dec_list = _req_str_list(rd["ratios_R2_to_R5_dec6"], f"p2.prism[{idx}].dec6")
        if not all(energies[j] * r_parsed[j] == energies[j + 1] for j in range(4)):
            prism_ratios_ok = False
        if dec_list != [oracle.format_decimal_rounded(r, 6) for r in r_parsed]:
            prism_ratios_ok = False
        prism_meta.append((nm, ln, tuple(energies)))
        r2_vals[nm] = r_parsed[0]

    # Pillar 3 exact-int & Ducci checks
    moz_ducci = _req_list(p3["mozart_ducci_orbits"], "p3.mozart")
    moz_parsed: list[tuple[str, tuple[int, ...], int, str, int, int, int, tuple[int, ...]]] = []
    for idx, row in enumerate(moz_ducci):
        rd = _req_exact_dict(row, _DUCCI_MOZART_KEYS, f"p3.mozart[{idx}]")
        cid = _req_str(rd["case_id"], f"p3.mozart[{idx}].case_id")
        out = _req_str(rd["outcome"], f"p3.mozart[{idx}].outcome")
        _req_int_fields(rd, ("length", "steps_to_zero", "cycle_entry_step", "cycle_period"), f"p3.mozart[{idx}]")
        in_midi = _req_int_list(rd["input_midi"], f"p3.mozart[{idx}].in")
        term = _req_int_list(rd["terminal_state"], f"p3.mozart[{idx}].term")
        moz_parsed.append(
            (
                cid,
                tuple(in_midi),
                rd["length"],
                out,
                rd["steps_to_zero"],
                rd["cycle_entry_step"],
                rd["cycle_period"],
                tuple(term),
            )
        )
    f2_rows = _req_list(p3["f2_impulse_characterization_L2_to_L12"], "p3.f2")
    f2_parsed: list[tuple[int, bool, str, int, int, int]] = []
    for idx, row in enumerate(f2_rows):
        rd = _req_exact_dict(row, _DUCCI_F2_KEYS, f"p3.f2[{idx}]")
        out = _req_str(rd["outcome"], f"p3.f2[{idx}].outcome")
        _req_int_fields(rd, ("L", "steps_to_zero", "cycle_entry_step", "cycle_period"), f"p3.f2[{idx}]")
        f2_parsed.append(
            (
                rd["L"],
                rd["is_power_of_2"],
                out,
                rd["steps_to_zero"],
                rd["cycle_entry_step"],
                rd["cycle_period"],
            )
        )

    # Pillar 4 exact-int, rational, & invariance checks
    s5 = _req_exact_dict(p4["k551_s5_quintuple_counterpoint"], _S5_KEYS, "p4.s5")
    s5_cf = _req_int_list(s5["cantus_firmus_v0_pc"], "p4.s5.cf")
    s5_val = _req_exact_dict(s5["valid_model"], _S5_MODEL_KEYS, "p4.s5.valid")
    s5_p5 = _req_exact_dict(s5["parallel_5th_counter_model"], _S5_MODEL_KEYS, "p4.s5.p5")
    s5_p8 = _req_exact_dict(s5["parallel_8ve_counter_model"], _S5_MODEL_KEYS, "p4.s5.p8")
    for m_lbl, md in (("s5.valid", s5_val), ("s5.p5", s5_p5), ("s5.p8", s5_p8)):
        _req_int_fields(md, ("total_permutations", "clean_permutations", "violating_permutations"), m_lbl)
        fv = md["first_violation"]
        if fv is not None:
            fvd = _req_exact_dict(fv, _S5_FV_KEYS, f"{m_lbl}.fv")
            _req_int_list(fvd["perm"], f"{m_lbl}.fv.perm")
            _req_int_fields(fvd, ("upper_voice", "lower_voice", "step_t", "interval_mod12"), f"{m_lbl}.fv")

    k516f = _req_exact_dict(p4["k516f_dice_game_invariance"], _K516F_KEYS, "p4.k516f")
    _req_int_fields(
        k516f,
        (
            "minuets_fixed_bar8",
            "minuets_two_bar8_endings",
            "seam_compatibility_11x11_sum",
            "matrix_product_14bar_paths",
            "broken_chromatic_seam_sum",
        ),
        "p4.k516f",
    )

    putz = _req_exact_dict(p4["putz_1995_cs13_anti_numerology"], _PUTZ_KEYS, "p4.putz")
    phi_lo = parse_exact_rational(putz["phi_inv_bracket_lo_q"], "p4.putz.phi_lo")
    phi_hi = parse_exact_rational(putz["phi_inv_bracket_hi_q"], "p4.putz.phi_hi")
    _req_int_fields(
        putz,
        ("sonatas_checked", "nonzero_exact_defect_count", "negative_defect_count", "positive_defect_count", "fail_2pct_ab_count"),
        "p4.putz",
    )
    max_dev_q = parse_exact_rational(putz["max_ab_deviation_lo_q"], "p4.putz.max_dev")
    max_dev_dec6 = _req_str(putz["max_ab_deviation_lo_dec6"], "p4.putz.max_dev_dec6")
    ba_width = parse_exact_rational(putz["range_compression_ba_width_q"], "p4.putz.ba_w")
    ab_width = parse_exact_rational(putz["range_compression_ab_width_q"], "p4.putz.ab_w")
    comp_fac = parse_exact_rational(putz["range_compression_factor_q"], "p4.putz.comp")
    putz_splits = _req_list(putz["sonata_splits"], "p4.putz.splits")
    putz_meta: list[tuple[str, int, int]] = []
    putz_rows_ok = True
    tol_2pct = Fraction(1, 50)
    for idx, row in enumerate(putz_splits):
        rd = _req_exact_dict(row, _PUTZ_ROW_KEYS, f"p4.putz.splits[{idx}]")
        sname = _req_str(rd["sonata"], f"p4.putz.splits[{idx}].sonata")
        _req_int_fields(
            rd,
            ("a_exposition_bars", "b_dev_recap_bars", "total_bars", "exact_golden_defect_Z"),
            f"p4.putz.splits[{idx}]",
        )
        a_b = rd["a_exposition_bars"]
        b_b = rd["b_dev_recap_bars"]
        tot_b = rd["total_bars"]
        bt_q = parse_exact_rational(rd["b_over_total_q"], f"p4.putz.splits[{idx}].bt")
        bt_dec6 = _req_str(rd["b_over_total_dec6"], f"p4.putz.splits[{idx}].bt_dec6")
        ab_q = parse_exact_rational(rd["a_over_b_q"], f"p4.putz.splits[{idx}].ab")
        ab_dec6 = _req_str(rd["a_over_b_dec6"], f"p4.putz.splits[{idx}].ab_dec6")
        if ab_q > phi_hi:
            err_lo = ab_q - phi_hi
        elif ab_q < phi_lo:
            err_lo = phi_lo - ab_q
        else:
            err_lo = Fraction(0, 1)
        row_ok = all(
            (
                a_b + b_b == tot_b,
                tot_b * bt_q == b_b,
                bt_dec6 == oracle.format_decimal_rounded(bt_q, 6),
                b_b * ab_q == a_b,
                ab_dec6 == oracle.format_decimal_rounded(ab_q, 6),
                rd["exact_golden_defect_Z"] == b_b * b_b - a_b * tot_b,
                rd["fails_2pct_ab_ratio_test"] is (err_lo > tol_2pct),
            )
        )
        if not row_ok:
            putz_rows_ok = False
        putz_meta.append((sname, a_b, b_b))

    oracle.require_ok(set(r2_vals.keys()) == _PRISM_NAMES, "SECONDARY_AUDIT_SCHEMA_ERROR", "p2.prism: missing or unexpected names")
    prism_order_ok = (
        r2_vals["Scale"]
        < 1
        < r2_vals["K.550"]
        < 2
        < r2_vals["K.331"]
        < r2_vals["K.545_Mel"]
        < r2_vals["K.525"]
        < r2_vals["K.545_Alberti"]
        < 4
    )
    ok_all = all(
        (
            track_id == oracle.TRACK_ID,
            schema_ver == oracle.SCHEMA_VERSION,
            oracle_cls == "exact",
            novelty_cls == "N1",
            pl["all_pillars_verified"] is True,
            p1["all_verified"] is True,
            p2["all_verified"] is True,
            p3["all_verified"] is True,
            p4["all_verified"] is True,
            frob_parsed["frobenius_prime_checks"] == list(_EXPECTED_FROB_PRIMES),
            frob_parsed["frobenius_prime_power_checks"] == list(_EXPECTED_FROB_POWERS),
            k550_midi == list(oracle.K550_OPENING_10),
            k550_d2 == [1, 1, 1, 1, 1, 1, 1, 2],
            k550_d3_raw == [0, -3, 3, 0, -3, 3, 7],
            k550_d3 == [0, 0, 0, 0, 0, 0, 1],
            k550_s3 == [0, 0, 0, 0, 0, 0, 1],
            k550_leap == 8,
            k550["exact_annihilation_verified"] is True,
            k545_midi == list(oracle.K545_ALBERTI_16),
            k545_d4 == [0] * 12,
            k545_s4 == [0] * 12,
            k545_energies == [415, 1432, 5248, 19584, 72384],
            k545["energies_strictly_growing"] is True,
            k545["exact_annihilation_verified"] is True,
            crt_table == [[x, x % 3, x % 4] for x in range(12)],
            crt_aug == [[r4, r4 + 4, r4 + 8] for r4 in range(4)],
            crt_dim == [[r3, r3 + 3, r3 + 6, r3 + 9] for r3 in range(3)],
            crt["crt_bijection_and_chords_verified"] is True,
            wn_vars == [2, 6, 20, 70, 252],
            wn_ratios == [Fraction(2, 1), Fraction(3, 1), Fraction(10, 3), Fraction(7, 2), Fraction(18, 5)],
            rw_ratios == [Fraction(2, 1), Fraction(3, 1), Fraction(10, 3), Fraction(7, 2)],
            p2["unity_cutoff_lambda"] == 6,
            p2["nyquist_ceiling"] == 4,
            sin_parsed == list(_EXPECTED_SIN_SPEC),
            prism_meta == list(_EXPECTED_PRISM_SPEC),
            prism_ratios_ok,
            prism_order_ok,
            p2["strict_textural_ordering_verified"] is True,
            moz_parsed == list(_EXPECTED_MOZART_DUCCI),
            f2_parsed == list(_EXPECTED_F2_DUCCI),
            p3["nilpotent_iff_power_of_2_L2_to_L12"] is True,
            s5_cf == [0, 2, 5, 4],
            s5["verified"] is True,
            s5_val == {
                "total_permutations": 120,
                "clean_permutations": 120,
                "violating_permutations": 0,
                "all_120_clean": True,
                "first_violation": None,
            },
            s5_p5 == {
                "total_permutations": 120,
                "clean_permutations": 60,
                "violating_permutations": 60,
                "all_120_clean": False,
                "first_violation": {
                    "perm": [0, 1, 2, 3, 4],
                    "upper_voice": 1,
                    "lower_voice": 0,
                    "step_t": 0,
                    "interval_mod12": 7,
                },
            },
            s5_p8 == {
                "total_permutations": 120,
                "clean_permutations": 0,
                "violating_permutations": 120,
                "all_120_clean": False,
                "first_violation": {
                    "perm": [0, 1, 2, 3, 4],
                    "upper_voice": 1,
                    "lower_voice": 0,
                    "step_t": 0,
                    "interval_mod12": 0,
                },
            },
            k516f["minuets_fixed_bar8"] == 11**14,
            k516f["minuets_two_bar8_endings"] == 2 * (11**14),
            k516f["seam_compatibility_11x11_sum"] == 121,
            k516f["seam_matrix_exact_rank_1"] is True,
            k516f["matrix_product_14bar_paths"] == 11**14,
            k516f["broken_chromatic_seam_sum"] == 110,
            k516f["verified"] is True,
            phi_lo == Fraction(618_033, 1_000_000),
            phi_hi == Fraction(309_017, 500_000),
            putz["phi_inv_bracket_verified"] is True,
            putz["sonatas_checked"] == 15,
            putz_meta == list(oracle.PUTZ_1995_MOZART_SPLITS),
            putz_rows_ok,
            putz["nonzero_exact_defect_count"] == 15,
            putz["negative_defect_count"] == 8,
            putz["positive_defect_count"] == 7,
            putz["fail_2pct_ab_count"] == 9,
            max_dev_q == Fraction(5_795_861, 33_500_000),
            max_dev_dec6 == oracle.format_decimal_rounded(max_dev_q, 6),
            ba_width == Fraction(1, 10),
            ab_width == Fraction(40, 143),
            comp_fac == Fraction(400, 143),
            putz["verified"] is True,
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
    """Fail-closed in-memory certificate verifier (schema + self-consistent SHA-256 + secondary audit + optional full pure-Q replay)."""
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
        raise oracle.MozartNthDiffError("INVALID_UTF8", f"certificate: invalid UTF-8 ({exc})") from exc
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
        raise oracle.MozartNthDiffError(
            "INVALID_CLI_ARGS",
            "usage: mozart_nth_diff_audit.py [--standalone --json | --write <path> | --check <path>]",
        )
    except oracle.MozartNthDiffError as exc:
        err_obj = {"valid": False, "error_code": exc.code, "detail": exc.detail}
        sys.stderr.write(canonical_json_bytes(err_obj).decode("ascii"))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

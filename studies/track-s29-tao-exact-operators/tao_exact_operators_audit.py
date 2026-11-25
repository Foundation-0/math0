#!/usr/bin/env python3
"""Zone-B hardened standalone CLI & certificate verifier for Track S29.

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero mathematical RNG
(CSPRNG secrets.token_hex used exclusively for collision-free atomic temp filenames).
Uniform Zone-B Gold Standard:
  - Concrete pathlib.Path check + NUL-byte and lone UTF-16 surrogate path refusal
  - Deleted-CWD OSError wrapping -> CWD_UNAVAILABLE (rc=2)
  - Atomic dir_fd PWD symlink ancestor walk + atomic per-component dir_fd openat
    (O_RDONLY | O_DIRECTORY | O_NOFOLLOW, handling ELOOP & ENOTDIR)
  - Leaf dir_fd O_RDONLY | O_NOFOLLOW | O_NONBLOCK + fstat S_ISREG + 65,536-byte
    streaming os.read under strict cap (1 <= max_bytes <= 64 MiB)
  - Durable atomic writer: dir_fd lstat (SYMLINK_FORBIDDEN, NOT_A_REGULAR_FILE,
    HARDLINK_FORBIDDEN) -> threading.Lock + secrets.token_hex(8) 32-retry 0o600 temp
    in SAME dfd -> os.fsync(fd) -> pre-replace fstat(fd).st_nlink == 1 ->
    atomic os.replace(tmp, leaf, src_dir_fd=dfd, dst_dir_fd=dfd) -> os.fsync(dfd)
  - Strict RFC 8259 ASCII-only JSON int parser (rejects -0, leading zeros, Unicode digits)
  - Strict exact-str argv validation, flag-like & equals-syntax CLI path refusal
  - Strict 64-char lowercase ASCII hex check BEFORE hmac.compare_digest + full
    pure-Q deterministic replay + division-free algebraic & 402-leaf schema cross-check
"""
from __future__ import annotations

import errno
from fractions import Fraction
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

import tao_exact_operators_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_READ_CAP_BYTES = 64 * 1024 * 1024
READ_CHUNK_BYTES = 65_536
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = 1_205
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
DEFAULT_CERT_NAME = "tao_exact_operators_certificate.json"

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
        raise oracle.TaoOperatorsError("INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden") from exc


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
        raise oracle.TaoOperatorsError("CWD_UNAVAILABLE", f"{label}: CWD unavailable ({exc})") from exc


def _check_pwd_no_symlinks(label: str) -> None:
    """Atomically verify absolute PWD ancestors contain no symlinks via dir_fd O_DIRECTORY|O_NOFOLLOW."""
    pwd = os.environ.get("PWD")
    if pwd and os.path.isabs(pwd):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_parts = Path(pwd).parts[1:]
        dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        try:
            dfd = os.open("/", dir_flags)
        except OSError as exc:
            raise oracle.TaoOperatorsError("FILE_READ_ERROR", f"{label}: cannot open root for PWD ({exc})") from exc
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
                            raise oracle.TaoOperatorsError(
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
        raise oracle.TaoOperatorsError(err_code, f"{label}: cannot open root ({exc})") from exc
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
                        raise oracle.TaoOperatorsError("FILE_WRITE_ERROR", f"{label}: mkdir failed ({mk_exc})") from mk_exc
                    try:
                        next_fd = os.open(part, dir_flags, dir_fd=dfd)
                    except OSError as reopen_exc:
                        raise oracle.TaoOperatorsError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({reopen_exc})"
                        ) from reopen_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    try:
                        is_lnk = stat.S_ISLNK(os.lstat(part, dir_fd=dfd).st_mode)
                    except OSError:
                        is_lnk = exc.errno == errno.ELOOP
                    if is_lnk:
                        raise oracle.TaoOperatorsError("SYMLINK_FORBIDDEN", f"{label}: symlink component forbidden") from exc
                    raise oracle.TaoOperatorsError(err_code, f"{label}: non-directory ancestor ({exc})") from exc
                else:
                    raise oracle.TaoOperatorsError(err_code, f"{label}: cannot open ancestor ({exc})") from exc
            os.close(dfd)
            dfd = next_fd
        return dfd, leaf
    except BaseException:
        os.close(dfd)
        raise


def read_regular_bytes_capped(path: Path, label: str, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes under strict cap using atomic dir_fd openat O_NOFOLLOW|O_NONBLOCK + fstat S_ISREG."""
    target = _require_concrete_path(path, label)
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_READ_CAP_BYTES)
    dfd, leaf = _open_dir_chain(target, label, create_parents=False)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            fd = os.open(leaf, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise oracle.TaoOperatorsError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.TaoOperatorsError("FILE_READ_ERROR", f"{label}: cannot open ({exc})") from exc
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
    except oracle.TaoOperatorsError:
        raise
    except OSError as exc:
        raise oracle.TaoOperatorsError("FILE_READ_ERROR", f"{label}: read failed ({exc})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str) -> None:
    """Write bytes atomically via dir_fd O_CREAT|O_EXCL|O_NOFOLLOW + os.replace (zero TOCTOU/hardlink clobber)."""
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
            raise oracle.TaoOperatorsError("FILE_WRITE_ERROR", f"{label}: stat failed ({exc})") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")
        for _ in range(32):
            cand = f".{leaf}.s29_tmp_{_next_tmp_tag()}"
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
                raise oracle.TaoOperatorsError("FILE_WRITE_ERROR", f"{label}: create temp failed ({exc})") from exc
        else:
            raise oracle.TaoOperatorsError("TEMP_EXHAUSTED", f"{label}: exhausted temp file slots")
        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(
                all((stat.S_ISREG(st_tmp.st_mode), st_tmp.st_nlink == 1)),
                "HARDLINK_FORBIDDEN",
                f"{label}: temp file unexpectedly hardlinked before replace",
            )
        except oracle.TaoOperatorsError:
            raise
        except OSError as exc:
            raise oracle.TaoOperatorsError("FILE_WRITE_ERROR", f"{label}: write failed ({exc})") from exc
        finally:
            os.close(fd)
        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.TaoOperatorsError("FILE_WRITE_ERROR", f"{label}: atomic replace failed ({exc})") from exc
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
    oracle.require_ok(
        not (len(digits) > 1 and digits[0] == "0"),
        "INVALID_JSON_INT",
        "JSON int leading zero forbidden",
    )
    oracle.require_ok(
        not (neg and digits == "0"),
        "INVALID_JSON_INT",
        "JSON negative zero forbidden",
    )
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    return int(token)


def _reject_nonfinite(token: str) -> Any:
    raise oracle.TaoOperatorsError("NONFINITE_JSON", f"non-finite JSON constant {token!r}")


def _reject_float(token: str) -> Any:
    raise oracle.TaoOperatorsError("FLOAT_FORBIDDEN", f"JSON float token forbidden: {token!r}")


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
            raise oracle.TaoOperatorsError("INVALID_JSON_VALUE", f"{label}: unsupported type {t.__name__}")


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
    except oracle.TaoOperatorsError:
        raise
    except (ValueError, RecursionError) as exc:
        raise oracle.TaoOperatorsError("INVALID_JSON", f"{label}: {exc}") from exc
    if require_object:
        oracle.require_ok(type(parsed) is dict, "JSON_ROOT_NOT_OBJECT", f"{label}: JSON root must be dict")
    _validate_json_tree(parsed, label)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    _validate_json_tree(obj, "canonical_json")
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n").encode("utf-8")


def build_certificate() -> dict[str, Any]:
    payload = oracle.compute_s29_payload()
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


_PINNED_PAYLOAD: dict[str, Any] = {
    "novelty_class": "N1",
    "oracle_class": "exact",
    "pillar1_katz_tao_entropy": {"all_verified": True, "cross_ratio_invariance": {"all_invariant": True, "cr_0_1_inf_m1": "2", "cr_0_inf_1_m1": "-1", "mobius_maps_verified": 4}, "katz_tao_11_6_certificate": {"cl_ring_equals_cl_Q": True, "copy_step_count": 3, "dual_row_count": 11, "exponent": "11/6", "residual_count": 0, "rhs_weights": ["2/3", "2/3", "1/2"], "ring": "Z"}, "katz_tao_7_4_certificate": {"cl_ring_equals_cl_Q": True, "copy_step_count": 2, "dual_row_count": 6, "exponent": "7/4", "residual_count": 0, "rhs_weights": ["1/2", "1/2", "1/2", "1/4"], "ring": "Z[1/2]"}, "open_seam_probe_honest_status": {"all_glues_tight_at_7_4": True, "beats_7_4_in_2page_rank3_cone": False, "four_slope_2page_best_achieved": "7/4", "four_slope_2page_rank3_glues_probed": 8, "honest_novelty_grade": "N1", "p0_primal_closed_sets_verified": 100, "p0_primal_lower_bound": "7/4", "per_glue_receipts": [{"atoms_2page": 17, "cap": 14, "closed_sets_verified": 506, "glue_mask": 127, "glue_name": "G1_2pair_z0z1", "primal_lower_bound": "7/4", "proof_method": "full_5d_polymatroid", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 17, "cap": 14, "closed_sets_verified": 512, "glue_mask": 911, "glue_name": "G2_2pair_z0z2", "primal_lower_bound": "7/4", "proof_method": "full_5d_polymatroid", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 19, "cap": 13, "closed_sets_verified": 782, "glue_mask": 369, "glue_name": "G3_1pair_z1_y2", "primal_lower_bound": "7/4", "proof_method": "full_5d_polymatroid", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 19, "cap": 13, "closed_sets_verified": 762, "glue_mask": 625, "glue_name": "G4_1pair_z1_t2", "primal_lower_bound": "7/4", "proof_method": "full_5d_polymatroid", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 20, "cap": 12, "glue_mask": 1314, "glue_name": "G5_syz4_y0s1y2s3", "primal_lower_bound": "7/4", "proof_method": "linear_projection_h0", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 20, "cap": 12, "glue_mask": 1352, "glue_name": "G6_syz4_t0t1y2s3", "primal_lower_bound": "7/4", "proof_method": "linear_projection_h0", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 20, "cap": 12, "glue_mask": 1576, "glue_name": "G7_syz4_t0s1t2s3", "primal_lower_bound": "7/4", "proof_method": "linear_projection_h0", "rank_modular_5d": True, "tight_at_7_4": True}, {"atoms_2page": 21, "cap": 12, "glue_mask": 1060, "glue_name": "G8_ind3_s0s1s3", "primal_lower_bound": "7/4", "proof_method": "linear_projection_h0", "rank_modular_5d": True, "tight_at_7_4": True}], "three_slope_published_records_N0": {"farnamfar_18page_std": "2762/1509", "farnamfar_5page_std": "152/83"}}, "ring_closure_separation": {"y_in_Q_span_x_xplus3y": True, "y_in_Z_span_x_xplus2y": False, "y_in_Zhalf_span_x_xplus2y": True, "y_in_Zhalf_span_x_xplus3y": False}, "tao_rational_complexity": [{"D_rational_complexity": 0, "slope": "-1"}, {"D_rational_complexity": 1, "slope": "2"}, {"D_rational_complexity": 2, "slope": "3"}, {"D_rational_complexity": 1, "slope": "-2"}, {"D_rational_complexity": 2, "slope": "3/2"}, {"D_rational_complexity": 3, "slope": "5/3"}, {"D_rational_complexity": 3, "slope": "7/4"}, {"D_rational_complexity": 4, "slope": "13/8"}], "trivial_2_mono_certificate": {"cl_ring_equals_cl_Q": True, "copy_step_count": 0, "dual_row_count": 2, "exponent": "2", "residual_count": 0, "rhs_weights": ["1", "1"], "ring": "Z"}},
    "pillar2_von_mangoldt_chains": {"all_verified": True, "hit_180_omega2_log_approx": "7925799930620659238/9872377837458467625", "hit_180_omega2_uniform": "23/30", "hit_210_omega2_log_approx": "1", "hit_210_omega2_uniform": "1", "odd_banks_martin_Q357": {"beta_weights": {"3": "3", "5": "5/3", "7": "7/5"}, "f_N1_gt_f_N2_certified": True, "f_N2_gt_f_N3_certified": True, "subinvariance_eq62_max_upper_bound_le_1": True}, "perfect_antichain_hit_from_10416": "83/420", "primitive_abundant_antichain_hit_from_3780": "229/420", "smooth_2_to_120_count": 49, "two_in_Q_obstruction": {"beta_2_denominator_p_minus_2": 0, "full_monotonicity_failure_note": "N0: Lichtman (1909.00804) proved f(N_k) fails monotonicity at k=6 on all primes; 2605.00301 Lemma 6.1 beta_p=p/(p-2) hits an exact pole at p=2.", "remark63_k1_erdos_strong_Q23_holds": True, "three_nu0_upper_lt_1": True, "two_nu0_lower_gt_1": True}, "von_mangoldt_kernel_identity_ok": True},
    "pillar3_syracuse_and_gilbreath": {"all_verified": True, "chase_hunter_tao_witnesses": {"long_zero_block_left_diag": [2, 1, 1, 1, 1, 1, 1, 1, 7], "shallow_0_2_block_left_diag": [2, 1, 3, 1, 1, 1, 1], "shallow_0_3_block_left_diag": [2, 1, 5, 2, 2, 2, 2]}, "geometric_contraction_ratio": "3/4", "gilbreath_first_500_primes": {"left_diagonal_all_ones": True, "p_500": 3571}, "logarithmic_density_note": "N0: Tao (1909.03562) proves almost all orbits attain bounded values in logarithmic density; full Collatz remains open.", "negative_17_cycle": {"orbit": [-17, -25, -37, -55, -41, -61, -91], "rational_formula_exact": True, "valuations": [1, 1, 1, 2, 1, 1, 4]}, "negative_short_cycles": [[-5, 2], [-1, 1]], "positive_short_cycles": [[1, 1]], "short_circuit_compositions_checked": 350, "syracuse_2adic_haar_drift": {"asymptotic_haar_ev2": "2", "asymptotic_haar_geometric_drift": "3/4", "odd_residues_checked": 128, "precision_bits_m": 8, "strictly_contractive": True, "telescoping_identity_exact": True, "truncated_ev2_mod256": "255/128", "truncated_formula_matches": True}, "syracuse_3adic_mod27": {"m": 3, "max_to_min_ratio": "23285/799", "modulus": 27, "ord_2_mod_3m": 18, "row_stochastic_exact": True, "state_count": 18, "stationary_max": "46570/262143", "stationary_min": "1598/262143", "stationary_pi_mod9": {}, "stationary_residual_zero": True, "tv_distance_from_uniform": "181409/524286"}, "syracuse_3adic_mod9": {"m": 2, "max_to_min_ratio": "11", "modulus": 9, "ord_2_mod_3m": 6, "row_stochastic_exact": True, "state_count": 6, "stationary_max": "22/63", "stationary_min": "2/63", "stationary_pi_mod9": {"1": "8/63", "2": "16/63", "4": "11/63", "5": "4/63", "7": "2/63", "8": "22/63"}, "stationary_residual_zero": True, "tv_distance_from_uniform": "5/18"}, "two_adic_parity_bijection_k1_to_8": True},
    "pillar4_sidon_gowers_ruzsa": {"all_verified": True, "gowers_f2_4": {"bent_wht_all_abs_4": True, "bent_x0x1_plus_x2x3": {"U2_4": "1/16", "U3_8": "1", "U4_16": "1"}, "cubic_x0x1x2": {"U2_4": "11/32", "U3_8": "11/32", "U4_16": "1"}, "linear_x0": {"U2_4": "1", "U3_8": "1", "U4_16": "1"}}, "ruzsa_and_plunnecke": {"doubling_constant_K": "5/2", "plunnecke_ruzsa_K3_A_bound": "375/4", "ruzsa_triangle_lhs": 125, "ruzsa_triangle_rhs": 238, "size_2A_minus_A": 28}, "singer_sidon_sets": [{"carter_obryant_tao_bound_ok": True, "diameter": 5, "duplicate_nonzero_differences": 0, "k": 3, "modulus": 7, "projective_points_covered": 7, "q": 2, "sidon_set": [0, 1, 5]}, {"carter_obryant_tao_bound_ok": True, "diameter": 11, "duplicate_nonzero_differences": 0, "k": 4, "modulus": 13, "projective_points_covered": 13, "q": 3, "sidon_set": [0, 1, 5, 11]}, {"carter_obryant_tao_bound_ok": True, "diameter": 16, "duplicate_nonzero_differences": 0, "k": 5, "modulus": 21, "projective_points_covered": 21, "q": 4, "sidon_set": [0, 1, 4, 14, 16]}, {"carter_obryant_tao_bound_ok": True, "diameter": 29, "duplicate_nonzero_differences": 0, "k": 6, "modulus": 31, "projective_points_covered": 31, "q": 5, "sidon_set": [0, 1, 14, 20, 24, 29]}, {"carter_obryant_tao_bound_ok": True, "diameter": 52, "duplicate_nonzero_differences": 0, "k": 8, "modulus": 57, "projective_points_covered": 57, "q": 7, "sidon_set": [0, 1, 4, 12, 14, 30, 37, 52]}], "two_golomb_ruler_witness": {"max_difference_multiplicity": 2, "set": [0, 1, 2, 5, 7]}},
    "pillar5_dyadic_ns_dptz_etp": {"all_verified": True, "dptz_eigenvector_eigenvalue": {"matrix_3x3": {"adjugate_schur_crosscheck_exact": True, "dptz_all_exact": True, "eigenpair_minor_pairs_checked": 9, "eigenvalues": [1, 4, 9], "n": 3}, "matrix_4x4": {"adjugate_schur_crosscheck_exact": True, "dptz_all_exact": True, "eigenpair_minor_pairs_checked": 16, "eigenvalues": [1, 3, 7, 13], "n": 4}}, "dyadic_ns_barrier": {"energy_conservation_exact": True, "lambda": "2", "lyapunov_growth_rates": ["67621/53900", "10379/200"], "mu": "3/2", "positive_cone_inward_exact": True, "weighted_lyapunov_identity_exact": True}, "etp_magma_countermodels": {"affine_medial_order3": {"associative": False, "associative_refutation": [0, 0, 1], "commutative": True, "commutative_refutation": None, "idempotent": True, "idempotent_refutation": None, "law1689_central_groupoid": False, "law1689_refutation": [0, 0, 1], "medial": True, "medial_refutation": None, "order": 3}, "central_groupoid_order4": {"associative": False, "associative_refutation": [0, 0, 2], "commutative": False, "commutative_refutation": [0, 1], "idempotent": False, "idempotent_refutation": [1], "law1689_central_groupoid": True, "law1689_refutation": None, "medial": False, "medial_refutation": [0, 0, 1, 0], "order": 4}, "cyclic_group_Z3": {"associative": True, "associative_refutation": None, "commutative": True, "commutative_refutation": None, "idempotent": False, "idempotent_refutation": [1], "law1689_central_groupoid": False, "law1689_refutation": [0, 0, 1], "medial": True, "medial_refutation": None, "order": 3}, "left_projection_order3": {"associative": True, "associative_refutation": None, "commutative": False, "commutative_refutation": [0, 1], "idempotent": True, "idempotent_refutation": None, "law1689_central_groupoid": False, "law1689_refutation": [0, 1, 0], "medial": True, "medial_refutation": None, "order": 3}}},
    "track_id": "TRACK-S29-AUDIT-129",
}
_PAYLOAD_KEYS = frozenset(_PINNED_PAYLOAD.keys())


def _parse_exact_frac(val: Any) -> Fraction | None:
    if type(val) is not str:
        return None
    parts = val.split("/")
    if len(parts) > 2:
        return None
    try:
        num = _parse_bounded_int(parts[0])
        den = 1 if len(parts) == 1 else _parse_bounded_int(parts[1])
    except oracle.TaoOperatorsError:
        return None
    if den <= 0:
        return None
    return Fraction(num, den)


def _get_dict(parent: dict[str, Any], key: str) -> dict[str, Any]:
    val = parent.get(key)
    return val if type(val) is dict else {}


def _check_division_free_algebraic_laws(payload: dict[str, Any]) -> bool:
    """Verify division-free cross-multiplied algebraic laws directly from parsed payload fields."""
    p1 = _get_dict(payload, "pillar1_katz_tao_entropy")
    p2 = _get_dict(payload, "pillar2_von_mangoldt_chains")
    p3 = _get_dict(payload, "pillar3_syracuse_and_gilbreath")
    p4 = _get_dict(payload, "pillar4_sidon_gowers_ruzsa")
    p5 = _get_dict(payload, "pillar5_dyadic_ns_dptz_etp")

    # Pillar 1: dual-weight sums match certified exponents; 2-page probe consistency
    for cert_k in ("katz_tao_11_6_certificate", "katz_tao_7_4_certificate", "trivial_2_mono_certificate"):
        sub = _get_dict(p1, cert_k)
        exp_q = _parse_exact_frac(sub.get("exponent"))
        ws = sub.get("rhs_weights")
        if any((exp_q is None, type(ws) is not list)):
            return False
        w_sum = Fraction(0, 1)
        for item in ws:
            wq = _parse_exact_frac(item)
            if wq is None:
                return False
            w_sum += wq
        if any(
            (
                w_sum != exp_q,
                type(sub.get("residual_count")) is not int,
                sub.get("residual_count") != 0,
                sub.get("cl_ring_equals_cl_Q") is not True,
            )
        ):
            return False
    probe = _get_dict(p1, "open_seam_probe_honest_status")
    receipts = probe.get("per_glue_receipts")
    if any(
        (
            type(receipts) is not list,
            len(receipts) != 8 if type(receipts) is list else True,
            probe.get("beats_7_4_in_2page_rank3_cone") is not False,
            probe.get("all_glues_tight_at_7_4") is not True,
        )
    ):
        return False
    for row in receipts:
        if any(
            (
                type(row) is not dict,
                row.get("tight_at_7_4") is not True if type(row) is dict else True,
                row.get("rank_modular_5d") is not True if type(row) is dict else True,
                _parse_exact_frac(row.get("primal_lower_bound")) != Fraction(7, 4) if type(row) is dict else True,
            )
        ):
            return False

    # Pillar 2: beta_p * (p - 2) == p (division-free) and kernel/subinvariance flags
    obm = _get_dict(p2, "odd_banks_martin_Q357")
    bw = _get_dict(obm, "beta_weights")
    two_obs = _get_dict(p2, "two_in_Q_obstruction")
    for p_str, p_int in (("3", 3), ("5", 5), ("7", 7)):
        bq = _parse_exact_frac(bw.get(p_str))
        if any((bq is None, (bq * (p_int - 2) != Fraction(p_int, 1)) if bq is not None else True)):
            return False
    if any(
        (
            type(two_obs.get("beta_2_denominator_p_minus_2")) is not int,
            two_obs.get("beta_2_denominator_p_minus_2") != 0,
            p2.get("von_mangoldt_kernel_identity_ok") is not True,
            obm.get("subinvariance_eq62_max_upper_bound_le_1") is not True,
        )
    ):
        return False

    # Pillar 3: mod-9 stationary sum == 1; cross-multiplied max == ratio * min (mod 9 & 27); Haar drift 4 * d == 3
    m9 = _get_dict(p3, "syracuse_3adic_mod9")
    m27 = _get_dict(p3, "syracuse_3adic_mod27")
    haar = _get_dict(p3, "syracuse_2adic_haar_drift")
    pi9 = _get_dict(m9, "stationary_pi_mod9")
    pi_sum = Fraction(0, 1)
    for pv in pi9.values():
        pq = _parse_exact_frac(pv)
        if pq is None:
            return False
        pi_sum += pq
    if pi_sum != Fraction(1, 1):
        return False
    for mod_d in (m9, m27):
        smin = _parse_exact_frac(mod_d.get("stationary_min"))
        smax = _parse_exact_frac(mod_d.get("stationary_max"))
        srat = _parse_exact_frac(mod_d.get("max_to_min_ratio"))
        if any(
            (
                smin is None,
                smax is None,
                srat is None,
                (smax != srat * smin) if all((smin is not None, smax is not None, srat is not None)) else True,
                mod_d.get("stationary_residual_zero") is not True,
            )
        ):
            return False
    drift_q = _parse_exact_frac(haar.get("asymptotic_haar_geometric_drift"))
    trunc_q = _parse_exact_frac(haar.get("truncated_ev2_mod256"))
    if any(
        (
            drift_q is None,
            trunc_q is None,
            (4 * drift_q != Fraction(3, 1)) if drift_q is not None else True,
            (128 * trunc_q != Fraction(255, 1)) if trunc_q is not None else True,
            p3.get("two_adic_parity_bijection_k1_to_8") is not True,
        )
    ):
        return False

    # Pillar 4: Singer projective-plane identities & Ruzsa/Plunnecke cross-multiplied bounds
    singers = p4.get("singer_sidon_sets")
    rp = _get_dict(p4, "ruzsa_and_plunnecke")
    if any((type(singers) is not list, len(singers) != 5 if type(singers) is list else True)):
        return False
    for srow in singers:
        if type(srow) is not dict:
            return False
        q_v, k_v, mod_v, dia_v, dup_v = (
            srow.get("q"),
            srow.get("k"),
            srow.get("modulus"),
            srow.get("diameter"),
            srow.get("duplicate_nonzero_differences"),
        )
        sset = srow.get("sidon_set")
        if any(
            (
                any(type(x) is not int for x in (q_v, k_v, mod_v, dia_v, dup_v)),
                type(sset) is not list,
                len(sset) < 1 if type(sset) is list else True,
                len(sset) != k_v if type(sset) is list else True,
                any(type(x) is not int for x in sset) if type(sset) is list else True,
            )
        ):
            return False
        if any(
            (
                mod_v != q_v * q_v + q_v + 1,
                k_v != q_v + 1,
                dup_v != 0,
                dia_v != sset[-1] - sset[0],
                srow.get("carter_obryant_tao_bound_ok") is not True,
            )
        ):
            return False
    k_q = _parse_exact_frac(rp.get("doubling_constant_K"))
    k3a_q = _parse_exact_frac(rp.get("plunnecke_ruzsa_K3_A_bound"))
    rlhs, rrhs, s2a = rp.get("ruzsa_triangle_lhs"), rp.get("ruzsa_triangle_rhs"), rp.get("size_2A_minus_A")
    if any(
        (
            k_q is None,
            k3a_q is None,
            any(type(x) is not int for x in (rlhs, rrhs, s2a)),
            (rlhs > rrhs) if all((type(rlhs) is int, type(rrhs) is int)) else True,
            (k_q * k_q * k_q * 6 != k3a_q) if all((k_q is not None, k3a_q is not None)) else True,
            (Fraction(s2a, 1) > k3a_q) if all((type(s2a) is int, k3a_q is not None)) else True,
        )
    ):
        return False

    # Pillar 5: Dyadic NS positivity & DPTZ n^2 minor-pair identities
    dns = _get_dict(p5, "dyadic_ns_barrier")
    dptz = _get_dict(p5, "dptz_eigenvector_eigenvalue")
    m3 = _get_dict(dptz, "matrix_3x3")
    m4 = _get_dict(dptz, "matrix_4x4")
    lam_q = _parse_exact_frac(dns.get("lambda"))
    mu_q = _parse_exact_frac(dns.get("mu"))
    rates = dns.get("lyapunov_growth_rates")
    if any(
        (
            lam_q is None,
            mu_q is None,
            type(rates) is not list,
            len(rates) != 2 if type(rates) is list else True,
            (lam_q <= 1) if lam_q is not None else True,
            (mu_q <= 1) if mu_q is not None else True,
            dns.get("energy_conservation_exact") is not True,
        )
    ):
        return False
    for r_tok in rates:
        rq = _parse_exact_frac(r_tok)
        if any((rq is None, rq <= 0 if rq is not None else True)):
            return False
    for md in (m3, m4):
        n_v, pairs_v = md.get("n"), md.get("eigenpair_minor_pairs_checked")
        if any(
            (
                type(n_v) is not int,
                type(pairs_v) is not int,
                (pairs_v != n_v * n_v) if all((type(n_v) is int, type(pairs_v) is int)) else True,
                md.get("dptz_all_exact") is not True,
                md.get("adjugate_schur_crosscheck_exact") is not True,
            )
        ):
            return False
    return True


def _strict_typed_equal(actual: Any, expected: Any) -> bool:
    """Iterative exact-type equality enforcing exact nested dict key-sets and all 402 leaves."""
    stack: list[tuple[Any, Any]] = [(actual, expected)]
    while stack:
        a, b = stack.pop()
        if type(a) is not type(b):
            return False
        if type(b) is dict:
            if len(a) != len(b):
                return False
            for k, bv in b.items():
                if k not in a:
                    return False
                stack.append((a[k], bv))
        elif type(b) is list:
            if len(a) != len(b):
                return False
            for av, bv in zip(a, b):
                stack.append((av, bv))
        elif a != b:
            return False
    return True


def _secondary_algebraic_crosscheck(payload: Any) -> None:
    """Fail-closed schema, nested key-set, 402-leaf pinning, and division-free algebraic cross-check."""
    _validate_json_tree(payload, "payload")
    oracle.require_ok(
        type(payload) is dict and set(payload.keys()) == _PAYLOAD_KEYS,
        "ALGEBRAIC_CROSSCHECK_FAILED",
        "payload must be exact dict with expected top-level keys",
    )
    oracle.require_ok(
        _check_division_free_algebraic_laws(payload),
        "ALGEBRAIC_IDENTITY_FAILED",
        "division-free algebraic identity cross-check failed",
    )
    oracle.require_ok(
        _strict_typed_equal(payload, _PINNED_PAYLOAD),
        "ALGEBRAIC_CROSSCHECK_FAILED",
        "secondary schema/leaf cross-check failed",
    )


def verify_certificate_dict(
    cert: Any,
    *,
    expected: dict[str, Any] | None = None,
    full_replay: bool = True,
) -> dict[str, Any]:
    """Fail-closed in-memory certificate verifier (hex64 + self-consistency + secondary + full pure-Q replay)."""
    oracle.require_exact_bool(full_replay, "full_replay")
    oracle.require_ok(type(cert) is dict, "INVALID_CERT_TYPE", "certificate must be exact dict")
    oracle.require_ok(set(cert.keys()) == _CERT_KEYS, "INVALID_CERT_KEYS", "unexpected or missing cert keys")
    _validate_json_tree(cert, "cert")
    oracle.require_ok(cert["schema_version"] == oracle.SCHEMA_VERSION, "INVALID_SCHEMA", "schema_version mismatch")
    oracle.require_ok(cert["track_id"] == oracle.TRACK_ID, "INVALID_TRACK_ID", "track_id mismatch")
    got_psha = require_hex64_lower_ascii(cert["payload_sha256"], "payload_sha256")
    got_csha = require_hex64_lower_ascii(cert["certificate_sha256"], "certificate_sha256")

    calc_psha = hashlib.sha256(canonical_json_bytes(cert["payload"])).hexdigest()
    oracle.require_ok(
        hmac.compare_digest(got_psha, calc_psha),
        "PAYLOAD_SHA_MISMATCH",
        "payload_sha256 mismatch",
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
        "certificate_sha256 mismatch",
    )
    _secondary_algebraic_crosscheck(cert["payload"])

    if full_replay:
        exp = build_certificate() if expected is None else expected
        oracle.require_ok(
            all(
                (
                    hmac.compare_digest(got_psha, exp["payload_sha256"]),
                    hmac.compare_digest(got_csha, exp["certificate_sha256"]),
                    hmac.compare_digest(canonical_json_bytes(cert), canonical_json_bytes(exp)),
                )
            ),
            "CERTIFICATE_MISMATCH",
            "certificate does not match freshly computed exact oracle output",
        )
    return {
        "valid": True,
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
        raise oracle.TaoOperatorsError("INVALID_UTF8", f"certificate: invalid UTF-8 ({exc})") from exc
    oracle.require_ok("\r" not in text, "CRLF_FORBIDDEN", "certificate: CRLF line endings forbidden")
    parsed = parse_strict_json_text(text, "certificate", require_object=True)
    oracle.require_ok(
        hmac.compare_digest(raw, canonical_json_bytes(parsed)),
        "CERTIFICATE_BYTE_MISMATCH",
        "certificate bytes are non-canonical",
    )
    return verify_certificate_dict(parsed, full_replay=full_replay)


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
        raise oracle.TaoOperatorsError(
            "INVALID_CLI_ARGS",
            "usage: tao_exact_operators_audit.py (--standalone --json | --write <path> | --check <path>)",
        )
    except oracle.TaoOperatorsError as exc:
        sys.stderr.write(f"[FAIL] {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

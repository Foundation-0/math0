#!/usr/bin/env python3
"""Zone-B hardened standalone CLI, full pure-Q replay & secondary auditor for Track S35.

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

import geometric_lineage_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = 1_000
_TEN_POW_JSON_INT = 10**MAX_JSON_INT_DIGITS
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_TEMP_NAME_LOCK = threading.Lock()
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


# ---------------------------------------------------------------------------
# Zone-B Path, CWD, Atomic dir_fd Traversal & Atomic Write
# ---------------------------------------------------------------------------

def _require_utf8_no_surrogate(text: str, label: str) -> str:
    if type(text) is not str:
        raise oracle.GeometricLineageError("INVALID_STR", f"{label}: exact str required")
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise oracle.GeometricLineageError("INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden") from exc
    return text


def _require_concrete_path(path: Any, label: str) -> Path:
    oracle.require_ok(
        type(path) in _EXACT_PATH_TYPES,
        "INVALID_PATH_TYPE",
        f"{label}: concrete pathlib.Path required",
    )
    raw_s = _require_utf8_no_surrogate(str(path), label)
    oracle.require_ok("\x00" not in raw_s, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    return path


def _safe_cwd(label: str) -> Path:
    try:
        return Path.cwd()
    except OSError as exc:
        raise oracle.GeometricLineageError("CWD_UNAVAILABLE", f"{label}: CWD unavailable ({type(exc).__name__})") from exc


def _check_pwd_no_symlinks(label: str) -> None:
    pwd = os.environ.get("PWD", "")
    if pwd.startswith("/"):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_path = Path(pwd)
        try:
            dfd = os.open("/", _DIR_OPEN_FLAGS)
        except OSError as exc:
            raise oracle.GeometricLineageError("CWD_UNAVAILABLE", f"{label}: cannot open root for PWD") from exc
        try:
            for part in pwd_path.parts[1:]:
                if part == ".":
                    continue
                try:
                    next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
                except OSError as exc:
                    if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                        raise oracle.GeometricLineageError(
                            "SYMLINK_ANCESTOR_FORBIDDEN",
                            f"{label}: symlink PWD ancestor forbidden",
                        ) from exc
                    raise oracle.GeometricLineageError(
                        "CWD_UNAVAILABLE",
                        f"{label}: PWD ancestor unavailable ({type(exc).__name__})",
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
        raise oracle.GeometricLineageError(err_code, f"{label}: cannot open root") from exc
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
                        raise oracle.GeometricLineageError(
                            "FILE_WRITE_ERROR", f"{label}: mkdir failed ({type(mk_exc).__name__})"
                        ) from mk_exc
                    try:
                        next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
                    except OSError as re_exc:
                        raise oracle.GeometricLineageError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({type(re_exc).__name__})"
                        ) from re_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise oracle.GeometricLineageError(
                        "SYMLINK_FORBIDDEN", f"{label}: symlink or non-directory ancestor forbidden"
                    ) from exc
                else:
                    raise oracle.GeometricLineageError(
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
                raise oracle.GeometricLineageError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.GeometricLineageError("FILE_READ_ERROR", f"{label}: cannot open ({type(exc).__name__})") from exc
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
    except oracle.GeometricLineageError:
        raise
    except OSError as exc:
        raise oracle.GeometricLineageError("FILE_READ_ERROR", f"{label}: read failed ({type(exc).__name__})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str = "output") -> None:
    """Atomic dir_fd write: 0o600 temp, lock+CSPRNG+EEXIST retry, fsync, st_nlink==1, os.replace, dir fsync."""
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
            raise oracle.GeometricLineageError("FILE_WRITE_ERROR", f"{label}: lstat failed ({type(exc).__name__})") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")

        pid = os.getpid()
        for _ in range(64):
            with _TEMP_NAME_LOCK:
                cand = f".s35.{pid}.{secrets.token_hex(8)}.tmp"
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
                raise oracle.GeometricLineageError(
                    "FILE_WRITE_ERROR", f"{label}: create temp failed ({type(exc).__name__})"
                ) from exc
        else:
            raise oracle.GeometricLineageError("FILE_WRITE_ERROR", f"{label}: exhausted temp file slots")

        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(st_tmp.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: temp link count altered")
        except oracle.GeometricLineageError:
            raise
        except OSError as exc:
            raise oracle.GeometricLineageError("FILE_WRITE_ERROR", f"{label}: write failed ({type(exc).__name__})") from exc
        finally:
            os.close(fd)

        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.GeometricLineageError("FILE_WRITE_ERROR", f"{label}: atomic replace failed ({type(exc).__name__})") from exc
    finally:
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Strict ASCII Parsers, Iterative Tree Validation & Canonical JSON
# ---------------------------------------------------------------------------

def require_hex64_lower_ascii(val: Any, label: str = "sha256") -> str:
    s = _require_utf8_no_surrogate(val, label)
    oracle.require_ok(len(s) == 64, "INVALID_HEX64", f"{label}: expected 64-char lowercase ASCII hex")
    for ch in s:
        oracle.require_ok(ch in _HEX_LOWER, "INVALID_HEX64", f"{label}: non-hex-lowercase char")
    return s


def _parse_bounded_int(token: str) -> int:
    """Strict ASCII-only 0-9 signed integer parser (rejects '-0', '007', Unicode digits, huge ints)."""
    s = _require_utf8_no_surrogate(token, "json_int")
    oracle.require_ok(s != "-0", "INVALID_JSON_INT", "negative zero forbidden")
    digits = s[1:] if s.startswith("-") else s
    oracle.require_ok(len(digits) >= 1, "INVALID_JSON_INT", "JSON int has no digits")
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    oracle.require_ok(digits == "0" or not digits.startswith("0"), "INVALID_JSON_INT", "leading zero forbidden")
    for ch in digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_JSON_INT", "non-ASCII digit forbidden")
    return int(s)


def parse_exact_rational(token: Any, label: str = "rational") -> Fraction:
    """Strict ASCII-only canonical exact rational parser ('n' or reduced 'n/d' with d >= 2)."""
    s = _require_utf8_no_surrogate(token, label)
    parts = s.split("/")
    oracle.require_ok(len(parts) in (1, 2), "INVALID_RATIONAL", f"{label}: expected 'n' or 'n/d'")
    num = _parse_bounded_int(parts[0])
    if len(parts) == 1:
        return oracle.require_fraction(Fraction(num, 1), label)
    den = _parse_bounded_int(parts[1])
    oracle.require_ok(den >= 2, "INVALID_RATIONAL", f"{label}: denominator must be >= 2")
    oracle.require_ok(math.gcd(abs(num), den) == 1, "NON_CANONICAL_RATIONAL", f"{label}: not in lowest terms")
    return oracle.require_fraction(Fraction(num, den), label)


def _validate_json_tree(root: Any, label: str = "json") -> None:
    """Iterative validator: depth cap (blocks cycles), int digit cap, UTF-8 surrogate check, zero floats."""
    stack: list[tuple[Any, int]] = [(root, 0)]
    while stack:
        node, depth = stack.pop()
        oracle.require_ok(depth <= MAX_JSON_DEPTH, "JSON_DEPTH_LIMIT", f"{label}: nesting exceeds {MAX_JSON_DEPTH}")
        t = type(node)
        if node is None or t is bool:
            continue
        if t is int:
            if node >= _TEN_POW_JSON_INT or node <= -_TEN_POW_JSON_INT:
                raise oracle.GeometricLineageError("INT_DIGIT_LIMIT", f"{label}: int exceeds {MAX_JSON_INT_DIGITS} digits")
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
        raise oracle.GeometricLineageError("FORBIDDEN_JSON_TYPE", f"{label}: unsupported type {t.__name__}")


def _reject_float(token: str) -> Any:
    raise oracle.GeometricLineageError("FLOAT_LITERAL_FORBIDDEN", f"float literal forbidden: {token}")


def _reject_constant(token: str) -> Any:
    raise oracle.GeometricLineageError("NONFINITE_LITERAL_FORBIDDEN", f"non-finite constant forbidden: {token}")


def _strict_pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        _require_utf8_no_surrogate(k, "json_key")
        oracle.require_ok(k not in out, "DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def parse_strict_json_text(text: Any, *, require_object: bool = True) -> Any:
    s = _require_utf8_no_surrogate(text, "json_text")
    oracle.require_bool(require_object, "require_object")
    oracle.require_ok(len(s.encode("utf-8")) <= MAX_JSON_BYTES, "JSON_TOO_LARGE", "JSON text exceeds size cap")
    try:
        parsed = json.loads(
            s,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            parse_int=_parse_bounded_int,
            object_pairs_hook=_strict_pairs_hook,
        )
    except oracle.GeometricLineageError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise oracle.GeometricLineageError("JSON_PARSE_ERROR", f"invalid JSON ({type(exc).__name__})") from exc
    _validate_json_tree(parsed, "parsed_json")
    if require_object and type(parsed) is not dict:
        raise oracle.GeometricLineageError("JSON_ROOT_NOT_OBJECT", "JSON root must be an object")
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


# ---------------------------------------------------------------------------
# Certificate Builder, Schema-Safe Secondary Audit & Verifier
# ---------------------------------------------------------------------------

def _require_dict_key(container: Any, key: str, label: str) -> dict[str, Any]:
    oracle.require_ok(type(container) is dict, "INVALID_SCHEMA_DICT", f"{label}: dict required")
    oracle.require_ok(key in container, "MISSING_FIELD", f"{label}: missing key {key!r}")
    val = container[key]
    oracle.require_ok(type(val) is dict, "INVALID_SCHEMA_DICT", f"{label}.{key}: dict required")
    return val


def _require_list_key(container: dict[str, Any], key: str, label: str, min_len: int = 1) -> list[Any]:
    oracle.require_ok(key in container, "MISSING_FIELD", f"{label}: missing key {key!r}")
    val = container[key]
    oracle.require_ok(type(val) is list and len(val) >= min_len, "INVALID_SCHEMA_LIST", f"{label}.{key}: list len >= {min_len} required")
    return val


def _req_int_field(obj: dict[str, Any], key: str, label: str) -> int:
    oracle.require_ok(key in obj, "MISSING_FIELD", f"{label}: missing {key!r}")
    return oracle.require_exact_int(obj[key], f"{label}.{key}")


def _req_bool_field(obj: dict[str, Any], key: str, label: str) -> bool:
    oracle.require_ok(key in obj, "MISSING_FIELD", f"{label}: missing {key!r}")
    return oracle.require_bool(obj[key], f"{label}.{key}")


_EXPECTED_PAYLOAD: dict[str, Any] = {
    "lineage_arc": "Uccello -> Piero -> Durer -> Mondrian -> Riley -> Sol LeWitt",
    "portal_id": "Portal-32",
    "pillar1_uccello_gauss_bonnet_stellated": {
        "all_verified": True,
        "embedded_4x4_torus_verified": True,
        "mazzocchio_tori": [
            {
                "E": 32, "F": 16, "M": 4, "N": 4, "V": 16, "chi": 0,
                "gauss_bonnet_matches_chi": True, "gauss_bonnet_sum_over_2pi": "0",
                "inner_vertex_defect_over_pi": "-1/2", "outer_vertex_defect_over_pi": "1/2",
                "total_inner_defect_over_pi": "-4", "total_outer_defect_over_pi": "4",
            },
            {
                "E": 64, "F": 32, "M": 4, "N": 8, "V": 32, "chi": 0,
                "gauss_bonnet_matches_chi": True, "gauss_bonnet_sum_over_2pi": "0",
                "inner_vertex_defect_over_pi": "-1/4", "outer_vertex_defect_over_pi": "1/4",
                "total_inner_defect_over_pi": "-4", "total_outer_defect_over_pi": "4",
            },
            {
                "E": 192, "F": 96, "M": 8, "N": 12, "V": 96, "chi": 0,
                "gauss_bonnet_matches_chi": True, "gauss_bonnet_sum_over_2pi": "0",
                "inner_vertex_defect_over_pi": "-1/12", "outer_vertex_defect_over_pi": "1/12",
                "total_inner_defect_over_pi": "-4", "total_outer_defect_over_pi": "4",
            },
            {
                "E": 384, "F": 192, "M": 16, "N": 12, "V": 192, "chi": 0,
                "gauss_bonnet_matches_chi": True, "gauss_bonnet_sum_over_2pi": "0",
                "inner_vertex_defect_over_pi": "-1/24", "outer_vertex_defect_over_pi": "1/24",
                "total_inner_defect_over_pi": "-4", "total_outer_defect_over_pi": "4",
            },
        ],
        "platonic_dodecahedron_contrast": {
            "E": 30, "F": 12, "V": 20, "chi": 2, "genus": 0, "schlafli": "{5, 3}",
        },
        "small_stellated_dodecahedron": {
            "E": 30, "F": 12, "V": 12,
            "all_edges_incidence_2": True, "all_vertices_degree_5": True,
            "chi": -6, "genus": 4, "schlafli": "{5/2, 5}",
        },
    },
    "pillar2_piero_cayley_menger_cross_ratio": {
        "all_verified": True,
        "cayley_menger": {
            "coplanar_control_det": "0",
            "general_matches_triple_product": True,
            "general_tetrahedron_det": "5000",
            "impossible_metric_control_det": "-19400",
            "impossible_metric_negative": True,
            "orthogonal_345_V2": "100",
            "orthogonal_345_det": "28800",
            "unit_tetrahedron_V2": "1/72",
            "unit_tetrahedron_det": "4",
        },
        "perspective_cross_ratio_cases": [
            {
                "affine_ratio_2d": "2", "affine_ratio_3d": "3",
                "affine_ratio_broken_by_perspective": True, "collinear_2d": True,
                "cross_ratio_2d": "9/7", "cross_ratio_3d": "9/7",
                "cross_ratio_residual": "0", "label": "oblique_foreshortened_line_1",
            },
            {
                "affine_ratio_2d": "2", "affine_ratio_3d": "4",
                "affine_ratio_broken_by_perspective": True, "collinear_2d": True,
                "cross_ratio_2d": "6/5", "cross_ratio_3d": "6/5",
                "cross_ratio_residual": "0", "label": "steep_depth_line_2",
            },
        ],
    },
    "pillar3_durer_melencolia_net_pentagon": {
        "all_verified": True,
        "melencolia_magic_square": {
            "D_times_v": [0, 0, 0, 0],
            "all_16_sums_equal_34": True,
            "det": 0,
            "exact_rank": 3,
            "nullspace_basis": [1, -3, 3, -1],
            "top_left_3x3_minor_det": 136,
            "trace": 34,
            "year_encoding": [15, 14],
        },
        "pentagon_1525_error_proof": {
            "P_at_lo": "102601/10000",
            "P_at_separator": "-671/256",
            "bracket_lo": "-13/10",
            "durer_cos_strictly_lt_cos108_proved": True,
            "minimal_poly_4cos_durer": [1, -12, 56, -48, -176],
            "nine_fourths_sq_vs_five": ["81/16", "5"],
            "poly_division_remainder_neg8u_minus_16_exact": True,
            "rational_separator": "-5/4",
            "strictly_monotone_on_nonpositive_axis": True,
        },
        "truncated_trapezohedron_net": {
            "E": 18, "F": 8, "V": 12,
            "all_28_pairs_disjoint_interiors": True,
            "all_8_faces_isometric_q_sqrt3": True,
            "chi": 2, "cut_edges": 11, "face_pairs_checked_sat": 28,
            "hinge_edges": 7, "hinge_spanning_tree_valid": True,
        },
    },
    "pillar4_mondrian_oeis_a276523": {
        "all_verified": True,
        "exhaustive_bb_lower_bounds_n3_to_n5": [
            {"bb_nodes_explored": 28, "certified_impossible": True, "n": 3, "tested_defect_ceiling": 1},
            {"bb_nodes_explored": 700, "certified_impossible": True, "n": 4, "tested_defect_ceiling": 3},
            {"bb_nodes_explored": 2308, "certified_impossible": True, "n": 5, "tested_defect_ceiling": 3},
        ],
        "guillotine_vs_nonguillotine_witnesses": {
            "n10_pinwheel_nonguillotine_opt": {"defect": 8, "is_guillotine": False},
            "n7_guillotine_opt": {"defect": 5, "is_guillotine": True},
            "n7_nonguillotine_opt": {"defect": 5, "is_guillotine": False, "tile_count": 8},
            "n8_guillotine_opt": {"defect": 6, "is_guillotine": True},
            "n8_nonguillotine_opt": {"defect": 6, "is_guillotine": False, "tile_count": 7},
        },
        "oeis_A276523_sequence": [2, 4, 4, 5, 5, 6, 6, 8],
        "optimal_tilings_n3_to_n10": [
            {
                "achieved_defect": 2, "expected_M_n": 2, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 3, "tile_count": 3,
                "tiles": [[0, 0, 3, 1], [0, 1, 2, 2], [2, 1, 1, 2]],
            },
            {
                "achieved_defect": 4, "expected_M_n": 4, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 4, "tile_count": 4,
                "tiles": [[0, 0, 4, 1], [0, 1, 2, 3], [2, 1, 2, 2], [2, 3, 2, 1]],
            },
            {
                "achieved_defect": 4, "expected_M_n": 4, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 5, "tile_count": 3,
                "tiles": [[0, 0, 5, 2], [0, 2, 3, 3], [3, 2, 2, 3]],
            },
            {
                "achieved_defect": 5, "expected_M_n": 5, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 6, "tile_count": 5,
                "tiles": [[0, 0, 5, 2], [5, 0, 1, 6], [0, 2, 3, 3], [3, 2, 2, 3], [0, 5, 5, 1]],
            },
            {
                "achieved_defect": 5, "expected_M_n": 5, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 7, "tile_count": 5,
                "tiles": [[0, 0, 6, 2], [6, 0, 1, 7], [0, 2, 4, 3], [4, 2, 2, 5], [0, 5, 4, 2]],
            },
            {
                "achieved_defect": 6, "expected_M_n": 6, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 8, "tile_count": 6,
                "tiles": [[0, 0, 7, 2], [7, 0, 1, 8], [0, 2, 3, 4], [3, 2, 2, 4], [5, 2, 2, 6], [0, 6, 5, 2]],
            },
            {
                "achieved_defect": 6, "expected_M_n": 6, "is_guillotine": True,
                "matches_oeis_A276523": True, "n": 9, "tile_count": 3,
                "tiles": [[0, 0, 6, 5], [6, 0, 3, 9], [0, 5, 6, 4]],
            },
            {
                "achieved_defect": 8, "expected_M_n": 8, "is_guillotine": False,
                "matches_oeis_A276523": True, "n": 10, "tile_count": 6,
                "tiles": [[0, 0, 10, 2], [0, 2, 3, 6], [3, 2, 7, 2], [3, 4, 5, 4], [8, 4, 2, 6], [0, 8, 8, 2]],
            },
        ],
    },
    "pillar5_riley_structure_tensor_moire": {
        "all_verified": True,
        "moire_n12_q_sqrt3": {
            "N": 12,
            "beat_frequency_abs_f1_minus_f2": 1,
            "exact_beat_and_alias_identity": True,
            "exact_mode_projections": {"0": "0", "1": "1", "2": "0", "3": "1", "4": "0", "5": "0", "6": "0"},
            "f1": 5, "f2": 4, "nyquist": 6, "sub_nyquist_fold_N_minus_sum": 3,
        },
        "structure_tensor_cases": [
            {
                "Jxx": 1024, "Jxy": 0, "Jyy": 0,
                "axis_aligned_Jxy_zero": True, "coherence_num": 1048576,
                "coherence_strictly_exceeds_axis_diff_sq": False, "diff_sq": 1048576,
                "matches_expectation": True, "name": "rectilinear_stripes_central",
                "nonzero_shear_tilt": False, "operator": "central_diff", "tan_2theta_exact": "0",
            },
            {
                "Jxx": 4096, "Jxy": 0, "Jyy": 4096,
                "axis_aligned_Jxy_zero": True, "coherence_num": 0,
                "coherence_strictly_exceeds_axis_diff_sq": False, "diff_sq": 0,
                "matches_expectation": True, "name": "rectilinear_checker_sobel",
                "nonzero_shear_tilt": False, "operator": "sobel_3x3", "tan_2theta_exact": "0",
            },
            {
                "Jxx": 3072, "Jxy": -1024, "Jyy": 1024,
                "axis_aligned_Jxy_zero": False, "coherence_num": 8388608,
                "coherence_strictly_exceeds_axis_diff_sq": True, "diff_sq": 4194304,
                "matches_expectation": True, "name": "riley_cafewall_sobel",
                "nonzero_shear_tilt": True, "operator": "sobel_3x3", "tan_2theta_exact": "-1",
            },
            {
                "Jxx": 1024, "Jxy": -512, "Jyy": 512,
                "axis_aligned_Jxy_zero": False, "coherence_num": 1310720,
                "coherence_strictly_exceeds_axis_diff_sq": True, "diff_sq": 262144,
                "matches_expectation": True, "name": "riley_pinched_shear_central",
                "nonzero_shear_tilt": True, "operator": "central_diff", "tan_2theta_exact": "-2",
            },
        ],
    },
    "pillar6_lewitt_burnside_kolmogorov": {
        "all_verified": True,
        "incomplete_open_cubes": {
            "O_burnside_fix_sum": 2928, "O_burnside_matches": True, "O_group_order": 24,
            "O_orbits_by_edges": {"10": 5, "11": 1, "3": 3, "4": 5, "5": 14, "6": 24, "7": 32, "8": 25, "9": 13},
            "O_orbits_total": 122,
            "Oh_burnside_fix_sum": 3696, "Oh_burnside_matches": True, "Oh_group_order": 48,
            "Oh_orbits_by_edges": {"10": 4, "11": 1, "3": 2, "4": 3, "5": 9, "6": 14, "7": 19, "8": 16, "9": 9},
            "Oh_orbits_total": 77,
            "achiral_forms": 32, "chiral_enantiomorphic_pairs": 45,
            "connected_3d_spanning_proper": 2366, "total_q3_subgraphs_searched": 4096,
        },
        "wall_drawing_compression": {
            "wd118_doubling_ratio_100_over_50": "198/49",
            "wd118_n50_segments": 1225,
            "wd118_scaling": [
                {"n_points": 10, "output_segments_C_n_2": 45, "rule_bits_O1": 64, "segments_per_rule_bit": "45/64", "segments_per_rule_bit_dec": "0.7031"},
                {"n_points": 25, "output_segments_C_n_2": 300, "rule_bits_O1": 64, "segments_per_rule_bit": "75/16", "segments_per_rule_bit_dec": "4.6875"},
                {"n_points": 50, "output_segments_C_n_2": 1225, "rule_bits_O1": 64, "segments_per_rule_bit": "1225/64", "segments_per_rule_bit_dec": "19.1406"},
                {"n_points": 100, "output_segments_C_n_2": 4950, "rule_bits_O1": 64, "segments_per_rule_bit": "2475/32", "segments_per_rule_bit_dec": "77.3438"},
            ],
            "wd260_nonempty_subsets_4dirs": 15,
        },
    },
    "summary": {
        "all_six_pillars_verified": True,
        "bare_assert_count": 0,
        "float_count_on_trust_path": 0,
        "pillar_count": 6,
        "rng_calls": 0,
    },
}


def _verify_exact_payload_tree(actual: Any, expected: Any, root_label: str) -> None:
    """Iterative bijective verifier: exact types, exact frozenset keysets, exact list lengths, exact leaf values."""
    stack: list[tuple[Any, Any, str]] = [(actual, expected, root_label)]
    while stack:
        act, exp, path = stack.pop()
        oracle.require_ok(type(act) is type(exp), "INVALID_SCHEMA_TYPE", f"{path}: exact type mismatch")
        t = type(exp)
        if t is dict:
            oracle.require_ok(
                frozenset(act.keys()) == frozenset(exp.keys()),
                "INVALID_SCHEMA_KEYS",
                f"{path}: exact keyset mismatch",
            )
            for k, exp_v in exp.items():
                stack.append((act[k], exp_v, f"{path}.{k}"))
        elif t is list:
            oracle.require_ok(
                len(act) == len(exp),
                "INVALID_SCHEMA_LIST",
                f"{path}: list length mismatch",
            )
            for idx, (act_i, exp_i) in enumerate(zip(act, exp)):
                stack.append((act_i, exp_i, f"{path}[{idx}]"))
        else:
            oracle.require_ok(act == exp, "SCHEMA_VALUE_MISMATCH", f"{path}: pinned leaf mismatch")


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Schema-safe secondary algebraic cross-check enforcing exact tree types, keysets, lengths, and all leaves."""
    oracle.require_ok(type(payload) is dict, "INVALID_PAYLOAD", "payload must be exact dict")
    _validate_json_tree(payload, "payload")

    # Pillar 1: Uccello
    p1 = _require_dict_key(payload, "pillar1_uccello_gauss_bonnet_stellated", "payload")
    tori = _require_list_key(p1, "mazzocchio_tori", "p1", min_len=4)
    for row in tori:
        oracle.require_ok(type(row) is dict, "INVALID_SCHEMA_DICT", "p1.torus")
        v_i = _req_int_field(row, "V", "p1.torus")
        e_i = _req_int_field(row, "E", "p1.torus")
        f_i = _req_int_field(row, "F", "p1.torus")
        chi_i = _req_int_field(row, "chi", "p1.torus")
        oracle.require_ok(v_i - e_i + f_i == 0 and chi_i == 0, "AUDIT_P1_TORUS_CHI", "Mazzocchio Euler != 0")
        oracle.require_ok(parse_exact_rational(row.get("gauss_bonnet_sum_over_2pi"), "p1.gb") == 0, "AUDIT_P1_GB", "Gauss-Bonnet != 0")
    ssd = _require_dict_key(p1, "small_stellated_dodecahedron", "p1")
    oracle.require_ok(
        _req_int_field(ssd, "V", "p1.ssd") - _req_int_field(ssd, "E", "p1.ssd") + _req_int_field(ssd, "F", "p1.ssd") == -6
        and _req_int_field(ssd, "genus", "p1.ssd") == 4,
        "AUDIT_P1_SSD",
        "small stellated dodecahedron chi=-6 / genus=4 failed",
    )
    dod = _require_dict_key(p1, "platonic_dodecahedron_contrast", "p1")
    oracle.require_ok(_req_int_field(dod, "genus", "p1.dod") == 0, "AUDIT_P1_DOD", "Platonic genus != 0")

    # Pillar 2: Piero
    p2 = _require_dict_key(payload, "pillar2_piero_cayley_menger_cross_ratio", "payload")
    cm = _require_dict_key(p2, "cayley_menger", "p2")
    oracle.require_ok(parse_exact_rational(cm.get("unit_tetrahedron_det"), "p2.unit") == Fraction(4), "AUDIT_P2_UNIT", "unit CM det != 4")
    oracle.require_ok(parse_exact_rational(cm.get("orthogonal_345_det"), "p2.orth") == Fraction(28800), "AUDIT_P2_ORTH", "345 CM det != 28800")
    oracle.require_ok(parse_exact_rational(cm.get("coplanar_control_det"), "p2.cop") == Fraction(0), "AUDIT_P2_COP", "coplanar CM det != 0")
    for pc in _require_list_key(p2, "perspective_cross_ratio_cases", "p2", min_len=2):
        oracle.require_ok(type(pc) is dict, "INVALID_SCHEMA_DICT", "p2.persp")
        oracle.require_ok(parse_exact_rational(pc.get("cross_ratio_residual"), "p2.cr") == 0, "AUDIT_P2_CR", "cross-ratio residual != 0")
        oracle.require_ok(_req_bool_field(pc, "affine_ratio_broken_by_perspective", "p2.persp"), "AUDIT_P2_AFF", "affine break false")

    # Pillar 3: Durer
    p3 = _require_dict_key(payload, "pillar3_durer_melencolia_net_pentagon", "payload")
    ms = _require_dict_key(p3, "melencolia_magic_square", "p3")
    oracle.require_ok(_req_int_field(ms, "det", "p3.ms") == 0, "AUDIT_P3_DET", "Melencolia det != 0")
    oracle.require_ok(_req_int_field(ms, "top_left_3x3_minor_det", "p3.ms") == 136, "AUDIT_P3_MINOR", "3x3 minor != 136")
    oracle.require_ok(_req_int_field(ms, "exact_rank", "p3.ms") == 3, "AUDIT_P3_RANK", "rank != 3")
    oracle.require_ok(_req_int_field(ms, "trace", "p3.ms") == 34, "AUDIT_P3_TRACE", "trace != 34")
    net = _require_dict_key(p3, "truncated_trapezohedron_net", "p3")
    oracle.require_ok(_req_int_field(net, "face_pairs_checked_sat", "p3.net") == 28, "AUDIT_P3_NET_PAIRS", "SAT pairs != 28")
    oracle.require_ok(_req_bool_field(net, "all_28_pairs_disjoint_interiors", "p3.net"), "AUDIT_P3_NET_DISJ", "net overlap")
    pent = _require_dict_key(p3, "pentagon_1525_error_proof", "p3")
    oracle.require_ok(parse_exact_rational(pent.get("P_at_lo"), "p3.plo") > 0, "AUDIT_P3_PENT_LO", "P_at_lo <= 0")
    oracle.require_ok(parse_exact_rational(pent.get("P_at_separator"), "p3.psep") < 0, "AUDIT_P3_PENT_SEP", "P_at_sep >= 0")

    # Pillar 4: Mondrian
    p4 = _require_dict_key(payload, "pillar4_mondrian_oeis_a276523", "payload")
    seq_raw = _require_list_key(p4, "oeis_A276523_sequence", "p4", min_len=8)
    seq_ints = [oracle.require_exact_int(x, "p4.seq") for x in seq_raw]
    oracle.require_ok(seq_ints == [2, 4, 4, 5, 5, 6, 6, 8], "AUDIT_P4_SEQ", "OEIS A276523 mismatch")
    for lb in _require_list_key(p4, "exhaustive_bb_lower_bounds_n3_to_n5", "p4", min_len=3):
        oracle.require_ok(type(lb) is dict, "INVALID_SCHEMA_DICT", "p4.lb")
        _req_int_field(lb, "n", "p4.lb")
        _req_int_field(lb, "bb_nodes_explored", "p4.lb")
        oracle.require_ok(_req_bool_field(lb, "certified_impossible", "p4.lb"), "AUDIT_P4_LB", "B&B lower bound failed")

    # Pillar 5: Riley
    p5 = _require_dict_key(payload, "pillar5_riley_structure_tensor_moire", "payload")
    t_cases = _require_list_key(p5, "structure_tensor_cases", "p5", min_len=4)
    for idx_t, tc in enumerate(t_cases):
        oracle.require_ok(type(tc) is dict, "INVALID_SCHEMA_DICT", "p5.tc")
        jxy_i = _req_int_field(tc, "Jxy", "p5.tc")
        expect_zero = idx_t < 2
        oracle.require_ok((jxy_i == 0) is expect_zero, "AUDIT_P5_JXY", "Riley Jxy axis/shear mismatch")
    moire = _require_dict_key(p5, "moire_n12_q_sqrt3", "p5")
    oracle.require_ok(_req_int_field(moire, "beat_frequency_abs_f1_minus_f2", "p5.moire") == 1, "AUDIT_P5_BEAT", "beat != 1")
    oracle.require_ok(_req_int_field(moire, "sub_nyquist_fold_N_minus_sum", "p5.moire") == 3, "AUDIT_P5_ALIAS", "alias != 3")

    # Pillar 6: Sol LeWitt
    p6 = _require_dict_key(payload, "pillar6_lewitt_burnside_kolmogorov", "payload")
    ioc = _require_dict_key(p6, "incomplete_open_cubes", "p6")
    oracle.require_ok(_req_int_field(ioc, "total_q3_subgraphs_searched", "p6.ioc") == 4096, "AUDIT_P6_TOTAL", "searched != 4096")
    oracle.require_ok(_req_int_field(ioc, "connected_3d_spanning_proper", "p6.ioc") == 2366, "AUDIT_P6_VALID", "valid != 2366")
    oracle.require_ok(_req_int_field(ioc, "O_orbits_total", "p6.ioc") == 122, "AUDIT_P6_O", "O orbits != 122")
    oracle.require_ok(_req_int_field(ioc, "Oh_orbits_total", "p6.ioc") == 77, "AUDIT_P6_OH", "Oh orbits != 77")
    oracle.require_ok(_req_int_field(ioc, "chiral_enantiomorphic_pairs", "p6.ioc") == 45, "AUDIT_P6_CHIRAL", "chiral != 45")
    oracle.require_ok(_req_int_field(ioc, "O_burnside_fix_sum", "p6.ioc") == 2928, "AUDIT_P6_BURN_O", "O Burnside != 2928")
    oracle.require_ok(_req_int_field(ioc, "Oh_burnside_fix_sum", "p6.ioc") == 3696, "AUDIT_P6_BURN_OH", "Oh Burnside != 3696")
    wd = _require_dict_key(p6, "wall_drawing_compression", "p6")
    oracle.require_ok(_req_int_field(wd, "wd118_n50_segments", "p6.wd") == 1225, "AUDIT_P6_WD118", "WD118 n=50 != 1225")

    summ = _require_dict_key(payload, "summary", "payload")
    oracle.require_ok(_req_bool_field(summ, "all_six_pillars_verified", "summary"), "AUDIT_SUMMARY_ALL", "summary flag false")
    oracle.require_ok(_req_int_field(summ, "pillar_count", "summary") == 6, "AUDIT_SUMMARY_CNT", "pillar_count != 6")
    oracle.require_ok(_req_int_field(summ, "float_count_on_trust_path", "summary") == 0, "AUDIT_SUMMARY_FLT", "float_count != 0")
    oracle.require_ok(_req_int_field(summ, "bare_assert_count", "summary") == 0, "AUDIT_SUMMARY_ASS", "bare_assert_count != 0")
    oracle.require_ok(_req_int_field(summ, "rng_calls", "summary") == 0, "AUDIT_SUMMARY_RNG", "rng_calls != 0")

    _verify_exact_payload_tree(payload, _EXPECTED_PAYLOAD, "payload")

    return {
        "secondary_audit_passed": True,
        "pillars_audited": 6,
    }


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
    oracle.require_bool(full_replay, "full_replay")
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
        raise oracle.GeometricLineageError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
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


# ---------------------------------------------------------------------------
# Strict Fail-Closed CLI (Space & Equals Flag-Like Rejection)
# ---------------------------------------------------------------------------

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
            raise oracle.GeometricLineageError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

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
    except oracle.GeometricLineageError as exc:
        err = {"valid": False, "error_code": exc.code, "error_message": exc.message}
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

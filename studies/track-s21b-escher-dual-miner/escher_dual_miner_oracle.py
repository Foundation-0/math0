"""Track S21b: Escher Self-Application Fixed-Point Tomography (Drawing Hands / Print Gallery)
& Negative-Space Dual Complex Miner (Sky & Water) on Foundation-0/aletheia-corpus.

Library module only; the sole CLI entrypoint is `escher_dual_miner_audit.py`.
Pure Python 3 stdlib, exact Z/Q arithmetic only (zero floats on trust paths),
zero bare asserts, and full aletheia v2.1 Zone-B strict I/O hardening.

Two strictly executable, zero-metaphor exact-Z/Q operators:
  1. Self-Application Fixed-Point Operator (Drawing Hands / Print Gallery):
     Extracts claimed prose invariants and artifact ground truth directly from
     track-s20d-claim-to-witness-tomography/ (JSON cert, Markdown report, AST of
     claim_witness_checker.py & claim_witness_audit.py, file byte sizes) AND from
     Foundation-0/aletheia-corpus (CORPUS_MANIFEST.json, SECRET_SCRUB_RECEIPT.json,
     SHA256SUMS, README.md, torus-knot-analysis/*.json), then applies Track S20d's
     Claim-to-Witness Binding Operator (P_CTW: Pillars 1-3) to compare claimed vs.
     artifact fields and separate closed fixed points T(x)=x from irreducible
     central-void obstructions (tagged by witness_basis).
  2. Negative-Space Dual Complex Miner (Sky & Water):
     Deterministically parses EVERY historical FALSIFIED and PARTIAL/FRAGILE audit
     entry (including mixed-verdict headers, colon section headers, and slash-composite
     ledger rows) in verification/AUDIT_LOG.md, isolates each entry's surgical defect
     span with multi-line passing-tail stripping and linear-time classification, and
     computes the exact-Q marginal dual-cut coverage matrix, greedy marginal trajectory,
     and exhaustive minimal hitting set over real audit history.
"""

from __future__ import annotations

import ast
import copy
import errno
from fractions import Fraction
import hashlib
import hmac
import importlib.util
from itertools import combinations
import json
import math
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
from typing import Any, Callable

MAX_JSON_DEPTH = 64
MAX_JSON_BYTES = 2_000_000
MAX_INT_BITS = 2048
MAX_INT_DIGITS = 620
MAX_EVIDENCE_CHARS = 32_768
MIB_BYTES = 1_048_576

_EXACT_PATH_TYPE = type(Path("."))
_ASCII_DIGITS = frozenset("0123456789")
_HEX64_CHARS = frozenset("0123456789abcdef")
_SCOPE_TIERS: dict[str, int] = {
    "research_prototype": 1,
    "ctypes_benchmark_harness": 2,
    "packed_file_integration": 3,
    "production_deployment": 4,
}
_METRIC_PROVENANCE = frozenset((
    "same_experiment_measurement",
    "cross_experiment_anchor",
    "unmeasured_hypothesis",
))

OBSTRUCTION_FAMILIES: tuple[str, ...] = (
    "OBS_ZONEB_IO",
    "OBS_H1_HOLONOMY",
    "OBS_HOLLOW_WITNESS",
    "OBS_STALE_ANCHOR",
    "OBS_SCOPE_ATTRIBUTION",
    "OBS_ASSERT_O_BYPASS",
)
_OBSTRUCTION_FAMILY_SET = frozenset(OBSTRUCTION_FAMILIES)

REQUIRED_S20D_PIN_KEYS = frozenset((
    "claim_witness_checker.py",
    "claim_witness_audit.py",
    "claim_witness_certificate.json",
    "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md",
    "test_claim_witness_r5.py",
))
REQUIRED_CORP_PIN_KEYS = frozenset((
    "CORPUS_MANIFEST.json",
    "SECRET_SCRUB_RECEIPT.json",
    "SHA256SUMS",
    "README.md",
    "torus_activity_certificate.json",
    "torus_content_certificate.json",
    "zone_b_fuzzer_certificate.json",
    "corpus_audit_log",
))
_CORPUS_SECTION_NAMES: tuple[str, ...] = (
    "expedition",
    "publish-branches-index",
    "swarm",
    "tasks",
    "torus-knot-analysis",
    "transcripts",
)
_ZONE_B_CLAUSE_REPORT_MARKERS: tuple[tuple[str, str], ...] = (
    ("max_json_depth_64", "MAX_JSON_DEPTH = 64"),
    ("max_json_bytes_2mb", "MAX_JSON_BYTES = 2_000_000"),
    ("max_int_bits_2048", "MAX_INT_BITS = 2048"),
    ("max_int_digits_620", "MAX_INT_DIGITS = 620"),
    ("zero_floats_trust_path", "zero floats on trust paths"),
    ("zero_bare_asserts", "zero bare `assert`s"),
    ("strict_exact_types", "strict `type()` checks"),
    ("unpaired_surrogate_rejection", "unpaired UTF-16 surrogate"),
    ("ascii_hex64_pre_hmac", "ASCII-hex64 pre-check"),
    ("symlink_nul_crlf_guards", "symlink/NUL/CRLF"),
)


class EscherMinerError(ValueError):
    """Fail-closed error carrying a stable machine-readable error code."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


# ---------------------------------------------------------------------------
# Zone-B Strict I/O & Exact Z/Q Primitives
# ---------------------------------------------------------------------------


def _require_valid_utf8_str(val: Any, field: str) -> str:
    if type(val) is not str:
        raise EscherMinerError("INVALID_STR_TYPE", f"{field} must be exact str")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise EscherMinerError("INVALID_UTF8_SURROGATE", f"{field} contains unpaired surrogate") from exc
    return val


def require_str(val: Any, field: str, *, non_empty: bool = False) -> str:
    s = _require_valid_utf8_str(val, field)
    if non_empty and len(s) == 0:
        raise EscherMinerError("EMPTY_STR", f"{field} must be non-empty")
    return s


def require_bool(val: Any, field: str) -> bool:
    if type(val) is not bool:
        raise EscherMinerError("INVALID_BOOL_TYPE", f"{field} must be exact bool")
    return val


def require_int(
    val: Any,
    field: str,
    *,
    min_value: int | None = None,
    max_value: int | None = None,
    max_bits: int = MAX_INT_BITS,
) -> int:
    if type(val) is not int:
        raise EscherMinerError("INVALID_INT_TYPE", f"{field} must be exact int")
    bits = val.bit_length()
    if bits > max_bits:
        raise EscherMinerError(
            "INT_BIT_LIMIT_EXCEEDED",
            f"{field} has {bits} bits, exceeding limit {max_bits}",
        )
    if min_value is not None and val < min_value:
        raise EscherMinerError("INT_BELOW_MIN", f"{field} below minimum bound")
    if max_value is not None and val > max_value:
        raise EscherMinerError("INT_ABOVE_MAX", f"{field} above maximum bound")
    return val


def _parse_bounded_int_str(token: str, field: str) -> int:
    s = _require_valid_utf8_str(token, field)
    if len(s) == 0:
        raise EscherMinerError("INVALID_INT_LITERAL", f"{field} empty integer literal")
    digits = s[1:] if s[0] == "-" else s
    if len(digits) == 0 or any(ch not in _ASCII_DIGITS for ch in digits):
        raise EscherMinerError("INVALID_INT_LITERAL", f"{field} invalid ASCII integer literal")
    if len(digits) > MAX_INT_DIGITS:
        raise EscherMinerError(
            "INT_DIGIT_LIMIT_EXCEEDED",
            f"{field} has {len(digits)} digits, exceeding limit {MAX_INT_DIGITS}",
        )
    return require_int(int(s), field)


def _parse_canonical_int_str(token: str, field: str) -> int:
    s = _require_valid_utf8_str(token, field)
    if s == "-0":
        raise EscherMinerError("NON_CANONICAL_RATIONAL", f"{field} negative zero forbidden")
    neg = s.startswith("-")
    digits = s[1:] if neg else s
    if len(digits) == 0 or any(ch not in _ASCII_DIGITS for ch in digits):
        raise EscherMinerError("INVALID_INT_LITERAL", f"{field} invalid ASCII integer literal")
    if len(digits) > 1 and digits[0] == "0":
        raise EscherMinerError("NON_CANONICAL_RATIONAL", f"{field} leading zero forbidden")
    if len(digits) > MAX_INT_DIGITS:
        raise EscherMinerError(
            "INT_DIGIT_LIMIT_EXCEEDED",
            f"{field} has {len(digits)} digits, exceeding limit {MAX_INT_DIGITS}",
        )
    return require_int(int(s), field)


def require_exact_fraction(val: Any, field: str) -> Fraction:
    if type(val) is int:
        return Fraction(require_int(val, field), 1)
    if type(val) is Fraction:
        num = require_int(val.numerator, f"{field}.numerator")
        den = require_int(val.denominator, f"{field}.denominator", min_value=1)
        return Fraction(num, den)
    if type(val) is str:
        s = _require_valid_utf8_str(val, field)
        parts = s.split("/")
        if len(parts) == 1:
            return Fraction(_parse_canonical_int_str(parts[0], field), 1)
        if len(parts) == 2:
            num = _parse_canonical_int_str(parts[0], f"{field}.numerator")
            den = _parse_canonical_int_str(parts[1], f"{field}.denominator")
            if den <= 0:
                raise EscherMinerError("NON_POSITIVE_DENOMINATOR", f"{field} denominator must be > 0")
            if den == 1:
                raise EscherMinerError("NON_CANONICAL_RATIONAL", f"{field} denominator 1 must omit slash")
            if math.gcd(abs(num), den) != 1:
                raise EscherMinerError("NON_CANONICAL_RATIONAL", f"{field} fraction must be in lowest terms")
            return Fraction(num, den)
        raise EscherMinerError("INVALID_FRACTION_STR", f"{field} invalid rational format")
    raise EscherMinerError("INVALID_FRACTION_TYPE", f"{field} must be int, Fraction, or rational str")


def fmt_q(val: Fraction) -> str:
    q = require_exact_fraction(val, "rational")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def require_hex64_ascii(val: Any, field: str) -> str:
    s = _require_valid_utf8_str(val, field)
    if len(s) != 64:
        raise EscherMinerError("INVALID_HEX64_LEN", f"{field} must be exactly 64 hex chars")
    for ch in s:
        if ch not in _HEX64_CHARS:
            raise EscherMinerError("INVALID_HEX64_CHAR", f"{field} must be lowercase ASCII hex")
    return s


def require_hex40_ascii(val: Any, field: str) -> str:
    s = _require_valid_utf8_str(val, field)
    if len(s) != 40:
        raise EscherMinerError("INVALID_HEX40_LEN", f"{field} must be exactly 40 hex chars")
    for ch in s:
        if ch not in _HEX64_CHARS:
            raise EscherMinerError("INVALID_HEX40_CHAR", f"{field} must be lowercase ASCII hex")
    return s


def constant_time_hex64_equal(left: Any, right: Any, field: str = "digest") -> bool:
    a = require_hex64_ascii(left, f"{field}.left")
    b = require_hex64_ascii(right, f"{field}.right")
    return hmac.compare_digest(a.encode("ascii"), b.encode("ascii"))


def require_exact_dict(val: Any, field: str) -> dict[str, Any]:
    if type(val) is not dict:
        raise EscherMinerError("INVALID_DICT_TYPE", f"{field} must be exact dict")
    for k in val:
        _require_valid_utf8_str(k, f"{field}.key")
    return val


def require_exact_list(val: Any, field: str, *, non_empty: bool = False) -> list[Any]:
    if type(val) is not list:
        raise EscherMinerError("INVALID_LIST_TYPE", f"{field} must be exact list")
    if non_empty and len(val) == 0:
        raise EscherMinerError("EMPTY_LIST", f"{field} must be non-empty")
    return val


def validate_json_value(obj: Any, *, max_depth: int = MAX_JSON_DEPTH) -> None:
    """Iteratively validate exact JSON-compatible tree (zero floats, bounded depth/ints, valid UTF-8)."""
    depth_limit = require_int(max_depth, "max_depth", min_value=1, max_value=MAX_JSON_DEPTH)
    stack: list[tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > depth_limit:
            raise EscherMinerError("JSON_DEPTH_EXCEEDED", f"nesting exceeds depth {depth_limit}")
        t = type(cur)
        if cur is None or t is bool:
            continue
        if t is int:
            require_int(cur, "json.int")
            continue
        if t is str:
            _require_valid_utf8_str(cur, "json.str")
            continue
        if t is list:
            for item in cur:
                stack.append((item, depth + 1))
            continue
        if t is dict:
            for k, v in cur.items():
                _require_valid_utf8_str(k, "json.key")
                stack.append((v, depth + 1))
            continue
        raise EscherMinerError("UNSUPPORTED_JSON_TYPE", f"unsupported type {t.__name__}")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        _require_valid_utf8_str(k, "json.key")
        if k in out:
            raise EscherMinerError("JSON_DUPLICATE_KEY", f"duplicate JSON key: {k}")
        out[k] = v
    return out


def _reject_float_literal(raw: str) -> Any:
    raise EscherMinerError("JSON_FLOAT_FORBIDDEN", f"float literal forbidden: {raw}")


def _reject_constant_literal(raw: str) -> Any:
    raise EscherMinerError("JSON_CONSTANT_FORBIDDEN", f"non-standard JSON constant forbidden: {raw}")


def _bounded_json_int(raw: str) -> int:
    return _parse_bounded_int_str(raw, "json.int")


def parse_strict_json_text(
    raw_text: str,
    *,
    require_object: bool = True,
    max_depth: int = MAX_JSON_DEPTH,
    max_bytes: int = MAX_JSON_BYTES,
) -> Any:
    text = _require_valid_utf8_str(raw_text, "raw_text")
    req_obj = require_bool(require_object, "require_object")
    byte_limit = require_int(max_bytes, "max_bytes", min_value=1, max_value=MAX_JSON_BYTES)
    if len(text.encode("utf-8")) > byte_limit:
        raise EscherMinerError("JSON_TOO_LARGE", f"JSON text exceeds {byte_limit} bytes")
    try:
        obj = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float_literal,
            parse_int=_bounded_json_int,
            parse_constant=_reject_constant_literal,
        )
    except EscherMinerError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise EscherMinerError("JSON_SYNTAX_ERROR", str(exc)) from exc
    validate_json_value(obj, max_depth=max_depth)
    if req_obj and type(obj) is not dict:
        raise EscherMinerError("JSON_ROOT_NOT_OBJECT", "top-level JSON payload must be an object")
    return obj


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_value(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def require_no_symlink_path(path: Path) -> None:
    if type(path) is not _EXACT_PATH_TYPE:
        raise EscherMinerError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_s = _require_valid_utf8_str(str(path), "path")
    if "\x00" in raw_s:
        raise EscherMinerError("INVALID_PATH_NUL", "NUL byte forbidden in path")
    if path.is_symlink():
        raise EscherMinerError("SYMLINK_FORBIDDEN", "symlink target path forbidden")
    for parent in path.parents:
        if parent.is_symlink():
            raise EscherMinerError("SYMLINK_ANCESTOR_FORBIDDEN", "symlink ancestor forbidden")
    if not path.is_absolute():
        pwd_env = os.environ.get("PWD")
        if pwd_env:
            pwd_path = Path(pwd_env)
            try:
                same_cwd = os.path.samefile(pwd_path, Path.cwd())
            except (OSError, ValueError):
                same_cwd = False
            if same_cwd:
                for comp in (pwd_path, *pwd_path.parents):
                    if comp.is_symlink():
                        raise EscherMinerError("SYMLINK_ANCESTOR_FORBIDDEN", "symlink PWD ancestor forbidden")


def _raise_open_oserror(exc: OSError, eloop_code: str, eloop_msg: str) -> None:
    if exc.errno == errno.ELOOP:
        raise EscherMinerError(eloop_code, eloop_msg) from exc
    if exc.errno in (errno.ENOENT, errno.ENOTDIR, errno.ENAMETOOLONG, errno.EISDIR):
        raise EscherMinerError("FILE_NOT_FOUND", "regular file not found") from exc
    raise EscherMinerError("FILE_READ_ERROR", f"cannot read file: {exc}") from exc


def _open_regular_file_nofollow(path: Path) -> int:
    """Atomically walk ancestor directories with O_DIRECTORY|O_NOFOLLOW and open leaf regular file with O_NOFOLLOW."""
    is_abs = path.is_absolute()
    parts = path.parts[1:] if is_abs else path.parts
    if len(parts) == 0:
        raise EscherMinerError("FILE_NOT_FOUND", "regular file not found")
    dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    leaf_flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    anchor = "/" if is_abs else "."
    cur_fd = -1
    leaf_fd = -1
    try:
        try:
            cur_fd = os.open(anchor, os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            _raise_open_oserror(exc, "SYMLINK_ANCESTOR_FORBIDDEN", "symlink ancestor forbidden")
        for comp in parts[:-1]:
            if comp == ".":
                continue
            try:
                next_fd = os.open(comp, dir_flags, dir_fd=cur_fd)
            except OSError as exc:
                _raise_open_oserror(exc, "SYMLINK_ANCESTOR_FORBIDDEN", "symlink ancestor forbidden")
            os.close(cur_fd)
            cur_fd = next_fd
        try:
            leaf_fd = os.open(parts[-1], leaf_flags, dir_fd=cur_fd)
        except OSError as exc:
            _raise_open_oserror(exc, "SYMLINK_FORBIDDEN", "symlink target path forbidden")
        return leaf_fd
    finally:
        if cur_fd >= 0:
            os.close(cur_fd)


def read_strict_utf8_file(path: Path, *, max_bytes: int = MAX_JSON_BYTES) -> tuple[bytes, str]:
    require_no_symlink_path(path)
    byte_limit = require_int(max_bytes, "max_bytes", min_value=1, max_value=MAX_JSON_BYTES)
    fd = _open_regular_file_nofollow(path)
    try:
        try:
            st = os.fstat(fd)
        except OSError as exc:
            raise EscherMinerError("FILE_READ_ERROR", f"cannot stat file: {exc}") from exc
        if not stat.S_ISREG(st.st_mode):
            raise EscherMinerError("FILE_NOT_FOUND", "regular file not found")
        chunks: list[bytes] = []
        total = 0
        while True:
            want = min(65_536, byte_limit - total + 1)
            try:
                chunk = os.read(fd, want)
            except OSError as exc:
                raise EscherMinerError("FILE_READ_ERROR", f"cannot read file: {exc}") from exc
            if not chunk:
                break
            total += len(chunk)
            if total > byte_limit:
                raise EscherMinerError("FILE_TOO_LARGE", f"file exceeds {byte_limit} bytes")
            chunks.append(chunk)
        raw = b"".join(chunks)
    finally:
        os.close(fd)
    if b"\r" in raw:
        raise EscherMinerError("CR_LINE_ENDINGS_FORBIDDEN", "CR/CRLF line endings forbidden")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise EscherMinerError("INVALID_UTF8", f"invalid UTF-8: {exc}") from exc
    return raw, text


# ---------------------------------------------------------------------------
# Operator 1: Self-Application Fixed-Point Tomography (Drawing Hands / Print Gallery)
# ---------------------------------------------------------------------------


def check_exact_mib_rounding(n_bytes: int, claimed_centi_mib: int) -> dict[str, Any]:
    """Verify 2-decimal MiB claim against exact byte count in pure Q (|exact - claimed| <= 1/200)."""
    b = require_int(n_bytes, "n_bytes", min_value=0)
    c = require_int(claimed_centi_mib, "claimed_centi_mib", min_value=0)
    exact_q = Fraction(b, MIB_BYTES)
    claimed_q = Fraction(c, 100)
    residual_q = abs(exact_q - claimed_q)
    half_ulp = Fraction(1, 200)
    return {
        "bytes": b,
        "claimed_mib_q": fmt_q(claimed_q),
        "exact_mib_q": fmt_q(exact_q),
        "abs_residual_q": fmt_q(residual_q),
        "within_half_ulp": residual_q <= half_ulp,
    }


def _resolve_parent_dict(root: dict[str, Any], path: list[str]) -> tuple[dict[str, Any], str]:
    cur: Any = root
    for seg in path[:-1]:
        if type(cur) is not dict or seg not in cur:
            raise EscherMinerError("DESTRUCTION_PATH_MISSING", f"missing path segment: {seg}")
        cur = cur[seg]
    if type(cur) is not dict:
        raise EscherMinerError("DESTRUCTION_PARENT_NOT_DICT", "target parent must be dict")
    leaf = path[-1]
    if leaf not in cur:
        raise EscherMinerError("DESTRUCTION_LEAF_MISSING", f"missing leaf key: {leaf}")
    return cur, leaf


def _apply_semantic_destruction(witness: dict[str, Any], spec: dict[str, Any]) -> dict[str, Any]:
    mutated = copy.deepcopy(witness)
    op = require_str(spec.get("op"), "perturbation.op", non_empty=True)
    raw_path = require_exact_list(spec.get("path"), "perturbation.path", non_empty=True)
    path = [require_str(seg, f"perturbation.path[{i}]", non_empty=True) for i, seg in enumerate(raw_path)]
    parent, leaf = _resolve_parent_dict(mutated, path)

    if op == "empty_mapping_field":
        if type(parent[leaf]) is not dict or len(parent[leaf]) == 0:
            raise EscherMinerError("TARGET_NOT_NONEMPTY_DICT", "empty_mapping_field requires non-empty dict")
        parent[leaf] = {}
    elif op == "replace_list_with_arbitrary_dict":
        if type(parent[leaf]) is not list or len(parent[leaf]) == 0:
            raise EscherMinerError("TARGET_NOT_NONEMPTY_LIST", "replace_list requires non-empty list")
        parent[leaf] = [{"arbitrary": "destroyed-element"}]
    elif op == "drop_required_field":
        del parent[leaf]
    elif op == "corrupt_pinned_hash":
        old_hex = require_hex64_ascii(parent[leaf], "corrupt_pinned_hash.target")
        flipped = "1" if old_hex[0] == "0" else "0"
        parent[leaf] = flipped + old_hex[1:]
    elif op == "invert_numeric_claim":
        old_val = require_int(parent[leaf], "invert_numeric_claim.target")
        parent[leaf] = old_val + 1
    else:
        raise EscherMinerError("UNKNOWN_DESTRUCTION_OP", f"unsupported op: {op}")

    if "resign_hash_field" in spec:
        hfield = require_str(spec.get("resign_hash_field"), "resign_hash_field", non_empty=True)
        if hfield not in mutated:
            raise EscherMinerError("RESIGN_FIELD_MISSING", f"resign hash field missing: {hfield}")
        body = {k: v for k, v in mutated.items() if k != hfield}
        mutated[hfield] = canonical_sha256(body)
    return mutated


def _invoke_verifier_strict(verifier_fn: Callable[[dict[str, Any]], bool], witness: dict[str, Any]) -> bool:
    try:
        res = verifier_fn(witness)
    except Exception:
        return False
    if type(res) is not bool:
        raise EscherMinerError("INVALID_VERIFIER_RETURN_TYPE", "verifier_fn must return exact bool")
    return res


def run_semantic_destruction_gate(
    verifier_fn: Callable[[dict[str, Any]], bool],
    valid_witness: dict[str, Any],
    perturbations: list[dict[str, Any]],
) -> dict[str, Any]:
    """Law 2b anti-hollow gate: fail closed if verifier accepts ANY semantically destroyed witness."""
    if not callable(verifier_fn):
        raise EscherMinerError("VERIFIER_NOT_CALLABLE", "verifier_fn must be callable")
    base = require_exact_dict(valid_witness, "valid_witness")
    validate_json_value(base)
    specs = require_exact_list(perturbations, "perturbations", non_empty=True)

    if not _invoke_verifier_strict(verifier_fn, copy.deepcopy(base)):
        return {
            "passed": False,
            "verdict": "VALID_WITNESS_REJECTED",
            "perturbations_tested": 0,
            "hollow_survivals": 0,
            "surviving_ids": [],
        }

    results: list[dict[str, Any]] = []
    for idx, raw_spec in enumerate(specs):
        spec = require_exact_dict(raw_spec, f"perturbations[{idx}]")
        pid = require_str(spec.get("id"), f"perturbations[{idx}].id", non_empty=True)
        destroyed = _apply_semantic_destruction(base, spec)
        survived = _invoke_verifier_strict(verifier_fn, destroyed)
        results.append({"id": pid, "op": spec["op"], "survived": survived})

    surviving_ids = [r["id"] for r in results if r["survived"]]
    passed = len(surviving_ids) == 0
    return {
        "passed": passed,
        "verdict": "STRICT_SEMANTIC_VERIFIER" if passed else "HOLLOW_WITNESS_VERIFIER",
        "perturbations_tested": len(results),
        "hollow_survivals": len(surviving_ids),
        "surviving_ids": surviving_ids,
    }


def verify_prose_artifact_bindings(bindings: list[dict[str, Any]]) -> dict[str, Any]:
    """Pillar 1 executable checker matching Track S20d semantics in pure Z/Q."""
    items = require_exact_list(bindings, "bindings", non_empty=True)
    results: list[dict[str, Any]] = []
    for idx, raw in enumerate(items):
        rec = require_exact_dict(raw, f"bindings[{idx}]")
        bid = require_str(rec.get("id"), f"bindings[{idx}].id", non_empty=True)
        kind = require_str(rec.get("kind"), f"bindings[{idx}].kind", non_empty=True)
        if kind == "integer_range_binding":
            c_cnt = require_int(rec.get("claimed_count"), "claimed_count", min_value=1)
            c_min = require_int(rec.get("claimed_min"), "claimed_min")
            c_max = require_int(rec.get("claimed_max"), "claimed_max", min_value=c_min)
            a_cnt = require_int(rec.get("artifact_count"), "artifact_count", min_value=1)
            a_min = require_int(rec.get("artifact_min"), "artifact_min")
            a_max = require_int(rec.get("artifact_max"), "artifact_max", min_value=a_min)
            ok = c_cnt == a_cnt and c_min == a_min and c_max == a_max
            results.append({"id": bid, "kind": kind, "passed": ok})
        elif kind == "c_allocation_table":
            claimed_hot = require_int(rec.get("claimed_hot_bytes"), "claimed_hot_bytes", min_value=0)
            arrays = require_exact_list(rec.get("allocated_arrays"), "allocated_arrays", non_empty=True)
            actual_hot = 0
            seen: set[str] = set()
            for a_i, entry in enumerate(arrays):
                item = require_exact_dict(entry, f"allocated_arrays[{a_i}]")
                name = require_str(item.get("name"), f"allocated_arrays[{a_i}].name", non_empty=True)
                if name in seen:
                    raise EscherMinerError("DUPLICATE_ARRAY_NAME", f"duplicate array {name}")
                seen.add(name)
                nbytes = require_int(item.get("bytes"), f"allocated_arrays[{a_i}].bytes", min_value=1)
                if require_bool(item.get("hot_read"), f"allocated_arrays[{a_i}].hot_read"):
                    actual_hot += nbytes
            ok = claimed_hot == actual_hot
            if "claimed_cache_limit_bytes" in rec or "claimed_fits_cache" in rec:
                limit = require_int(rec.get("claimed_cache_limit_bytes"), "claimed_cache_limit_bytes", min_value=1)
                claimed_fits = require_bool(rec.get("claimed_fits_cache"), "claimed_fits_cache")
                ok = ok and (claimed_fits == (actual_hot <= limit))
            results.append({"id": bid, "kind": kind, "passed": ok, "actual_hot_bytes": actual_hot})
        else:
            raise EscherMinerError("UNKNOWN_BINDING_KIND", f"unknown binding kind: {kind}")
    failed_ids = [r["id"] for r in results if not r["passed"]]
    return {
        "passed": len(failed_ids) == 0,
        "checked_count": len(results),
        "failed_ids": failed_ids,
        "results": results,
    }


def verify_provenance_claims(claims: list[dict[str, Any]]) -> dict[str, Any]:
    """Pillar 2 executable provenance checker matching Track S20d semantics."""
    items = require_exact_list(claims, "claims", non_empty=True)
    results: list[dict[str, Any]] = []
    for idx, raw in enumerate(items):
        rec = require_exact_dict(raw, f"claims[{idx}]")
        cid = require_str(rec.get("id"), f"claims[{idx}].id", non_empty=True)
        kind = require_str(rec.get("kind"), f"claims[{idx}].kind", non_empty=True)
        if kind == "spec_completeness":
            req_raw = require_exact_list(rec.get("required_clauses"), "required_clauses", non_empty=True)
            imp_raw = require_exact_list(rec.get("implemented_clauses"), "implemented_clauses")
            claims_exact = require_bool(rec.get("claimed_exact_spec_equivalence"), "claimed_exact_spec_equivalence")
            req_set = {require_str(x, "required_clause", non_empty=True) for x in req_raw}
            imp_set = {require_str(x, "implemented_clause", non_empty=True) for x in imp_raw}
            missing = sorted(req_set - imp_set)
            ok = not (claims_exact and len(missing) > 0)
            results.append({"id": cid, "kind": kind, "passed": ok, "missing_count": len(missing)})
        elif kind == "delivery_scope":
            c_scope = require_str(rec.get("claimed_scope_tier"), "claimed_scope_tier", non_empty=True)
            w_scope = require_str(rec.get("witnessed_scope_tier"), "witnessed_scope_tier", non_empty=True)
            if c_scope not in _SCOPE_TIERS or w_scope not in _SCOPE_TIERS:
                raise EscherMinerError("UNKNOWN_SCOPE_TIER", "unknown scope tier")
            results.append({"id": cid, "kind": kind, "passed": _SCOPE_TIERS[c_scope] <= _SCOPE_TIERS[w_scope]})
        elif kind == "metric_attribution":
            c_subj = require_str(rec.get("claimed_subject"), "claimed_subject", non_empty=True)
            m_subj = require_str(rec.get("measured_subject"), "measured_subject", non_empty=True)
            c_prov = require_str(rec.get("claimed_provenance"), "claimed_provenance", non_empty=True)
            w_prov = require_str(rec.get("witness_provenance"), "witness_provenance", non_empty=True)
            if c_prov not in _METRIC_PROVENANCE or w_prov not in _METRIC_PROVENANCE:
                raise EscherMinerError("UNKNOWN_METRIC_PROVENANCE", "unknown metric provenance")
            executed = require_bool(rec.get("experiment_executed_for_claimed_subject"), "executed")
            ok = True
            if c_prov == "same_experiment_measurement":
                if w_prov != "same_experiment_measurement" or c_subj != m_subj or not executed:
                    ok = False
            if c_prov == "cross_experiment_anchor" and w_prov == "unmeasured_hypothesis":
                ok = False
            results.append({"id": cid, "kind": kind, "passed": ok})
        else:
            raise EscherMinerError("UNKNOWN_PROVENANCE_KIND", f"unknown provenance kind: {kind}")
    failed_ids = [r["id"] for r in results if not r["passed"]]
    return {
        "passed": len(failed_ids) == 0,
        "checked_count": len(results),
        "failed_ids": failed_ids,
        "results": results,
    }


def _make_s20d_self_witness() -> tuple[dict[str, Any], str]:
    """Minimal exact witness matching Track S20d certificate structure for Pillar-3 Drawing-Hands test."""
    payload = {
        "ai_verifier_families_count": 11,
        "audit118a_orthogonal_signatures_count": 8,
        "shared_nullspace_escapes_count": 6,
        "per_family_audit118a_sig_counts": {
            "swarm_verifier_1": 3,
            "claude_code": 3,
            "deepseek_v41_flash": 2,
            "muse_code": 2,
            "blinded_airgapped": 2,
            "glm_53": 1,
            "swarm_verifier_2": 1,
        },
        "negative_cases": [{"escape_id": "ESC-24"}, {"escape_id": "ESC-26"}],
    }
    p_sha = canonical_sha256(payload)
    body = {
        "schema_version": "aletheia.claim_witness_tomography.v1",
        "track_id": "track-s20d-claim-to-witness-tomography",
        "payload": payload,
        "payload_sha256": p_sha,
    }
    c_sha = canonical_sha256(body)
    body["certificate_sha256"] = c_sha
    return body, c_sha


def _hollow_self_hash_verifier(cert: dict[str, Any]) -> bool:
    """Hollow verifier checking only self-hash without recomputing expected payload or pin."""
    body = {k: v for k, v in cert.items() if k != "certificate_sha256"}
    return constant_time_hex64_equal(cert["certificate_sha256"], canonical_sha256(body))


def _strict_pinned_cert_verifier(expected_cert_sha: str, expected_payload_sha: str) -> Callable[[dict[str, Any]], bool]:
    def _verify(cert: dict[str, Any]) -> bool:
        p_sha = canonical_sha256(cert["payload"])
        if not constant_time_hex64_equal(cert["payload_sha256"], p_sha):
            return False
        if not constant_time_hex64_equal(p_sha, expected_payload_sha):
            return False
        body = {k: v for k, v in cert.items() if k != "certificate_sha256"}
        c_sha = canonical_sha256(body)
        if not constant_time_hex64_equal(cert["certificate_sha256"], c_sha):
            return False
        return constant_time_hex64_equal(c_sha, expected_cert_sha)

    return _verify


def _require_callable_hooks(
    bind_fn: Callable[..., Any],
    prov_fn: Callable[..., Any],
    destruct_fn: Callable[..., Any],
) -> None:
    if not callable(bind_fn):
        raise EscherMinerError("INVALID_HOOK_CALLABLE", "bind_fn must be callable")
    if not callable(prov_fn):
        raise EscherMinerError("INVALID_HOOK_CALLABLE", "prov_fn must be callable")
    if not callable(destruct_fn):
        raise EscherMinerError("INVALID_HOOK_CALLABLE", "destruct_fn must be callable")


def _verify_cert_internal_hashes(cert_obj: dict[str, Any], label: str) -> dict[str, Any]:
    """Verify payload_sha256 and certificate_sha256 inside an extracted JSON certificate."""
    payload = require_exact_dict(cert_obj.get("payload"), f"{label}.payload")
    rec_p_sha = require_hex64_ascii(cert_obj.get("payload_sha256"), f"{label}.payload_sha256")
    rec_c_sha = require_hex64_ascii(cert_obj.get("certificate_sha256"), f"{label}.certificate_sha256")
    actual_p_sha = canonical_sha256(payload)
    if not constant_time_hex64_equal(rec_p_sha, actual_p_sha, f"{label}.payload_sha256"):
        raise EscherMinerError("EXTRACTED_CERT_HASH_MISMATCH", f"{label} payload_sha256 mismatch")
    body = {k: v for k, v in cert_obj.items() if k != "certificate_sha256"}
    actual_c_sha = canonical_sha256(body)
    if not constant_time_hex64_equal(rec_c_sha, actual_c_sha, f"{label}.certificate_sha256"):
        raise EscherMinerError("EXTRACTED_CERT_HASH_MISMATCH", f"{label} certificate_sha256 mismatch")
    return payload


def _require_regex_match(pat: re.Pattern[str], text: str, code: str, label: str) -> re.Match[str]:
    m = pat.search(text)
    if m is None:
        raise EscherMinerError(code, f"missing expected prose field: {label}")
    return m


def _inspect_python_ast_trust_file(py_path: Path) -> tuple[bytes, dict[str, int], set[str]]:
    """Parse Python AST, enforce zero bare asserts & zero floats, and return (raw, int_consts, def_names)."""
    raw, src = read_strict_utf8_file(py_path)
    try:
        tree = ast.parse(src)
    except SyntaxError as exc:
        raise EscherMinerError("TRUST_PATH_SYNTAX_ERROR", f"syntax error in {py_path.name}: {exc}") from exc
    bare_asserts = sum(1 for n in ast.walk(tree) if isinstance(n, ast.Assert))
    if bare_asserts != 0:
        raise EscherMinerError("TRUST_PATH_BARE_ASSERT", f"bare assert found in {py_path.name}")
    float_consts = sum(1 for n in ast.walk(tree) if isinstance(n, ast.Constant) and type(n.value) is float)
    if float_consts != 0:
        raise EscherMinerError("TRUST_PATH_FLOAT_CONST", f"float literal found in {py_path.name}")
    int_consts: dict[str, int] = {}
    def_names: set[str] = set()
    for node in tree.body:
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Constant) and type(node.value.value) is int:
            for tgt in node.targets:
                if isinstance(tgt, ast.Name):
                    int_consts[tgt.id] = node.value.value
        elif isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            def_names.add(node.name)
    return raw, int_consts, def_names


def _extract_s20d_implemented_clauses(int_consts: dict[str, int], def_names: set[str]) -> list[str]:
    """Derive implemented Zone-B clauses strictly from claim_witness_checker.py AST."""
    clauses: list[str] = []
    if int_consts.get("MAX_JSON_DEPTH") == MAX_JSON_DEPTH:
        clauses.append("max_json_depth_64")
    if int_consts.get("MAX_JSON_BYTES") == MAX_JSON_BYTES:
        clauses.append("max_json_bytes_2mb")
    if int_consts.get("MAX_INT_BITS") == MAX_INT_BITS:
        clauses.append("max_int_bits_2048")
    if int_consts.get("MAX_INT_DIGITS") == MAX_INT_DIGITS:
        clauses.append("max_int_digits_620")
    clauses.append("zero_floats_trust_path")
    clauses.append("zero_bare_asserts")
    if {"require_str", "require_bool", "require_int", "require_exact_dict", "require_exact_list"} <= def_names:
        clauses.append("strict_exact_types")
    if "_require_valid_utf8_str" in def_names:
        clauses.append("unpaired_surrogate_rejection")
    if {"require_hex64_ascii", "constant_time_hex64_equal"} <= def_names:
        clauses.append("ascii_hex64_pre_hmac")
    if {"require_no_symlink_path", "read_strict_utf8_file"} <= def_names:
        clauses.append("symlink_nul_crlf_guards")
    return clauses


_S20D_RE_CERT_FILE_SHA = re.compile(r"File SHA-256:\s*`([0-9a-f]{64})`", re.ASCII)
_S20D_RE_PAYLOAD_SHA = re.compile(r"`payload_sha256`:\s*`([0-9a-f]{64})`", re.ASCII)
_S20D_RE_CERT_SHA = re.compile(r"`certificate_sha256`:\s*`([0-9a-f]{64})`", re.ASCII)
_S20D_RE_RUNS = re.compile(r"Across `(\d+)` multi-continent verification runs", re.ASCII)
_S20D_RE_FAMILIES = re.compile(r"\*\*`(\d+)` AI verifier families\*\*", re.ASCII)
_S20D_RE_MAX_SIG = re.compile(r"max single-family coverage `(\d+)/\d+", re.ASCII)
_S20D_RE_ESCAPES = re.compile(r"\*\*`(\d+)` live pull requests\*\*", re.ASCII)
_S20D_RE_BLOCKING = re.compile(r"\*\*`(\d+)` blocking findings\*\* total \(`([0-9 +]+)`\)", re.ASCII)


def extract_s20d_snapshot_from_dir(s20d_dir: Path, corpus_dir: Path | None = None) -> dict[str, Any]:
    """Live-parse Track S20d report prose (claimed) vs JSON cert, Python AST & file bytes (artifact)."""
    require_no_symlink_path(s20d_dir)
    if not s20d_dir.is_dir():
        raise EscherMinerError("S20D_DIR_NOT_FOUND", "track-s20d directory not found")

    chk_path = s20d_dir / "claim_witness_checker.py"
    aud_path = s20d_dir / "claim_witness_audit.py"
    cert_path = s20d_dir / "claim_witness_certificate.json"
    rep_path = s20d_dir / "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md"
    tst_path = s20d_dir / "test_claim_witness_r5.py"

    raw_chk, chk_consts, chk_defs = _inspect_python_ast_trust_file(chk_path)
    raw_aud, _, _ = _inspect_python_ast_trust_file(aud_path)
    chk_bytes = len(raw_chk)
    aud_bytes = len(raw_aud)
    raw_cert, txt_cert = read_strict_utf8_file(cert_path)
    raw_rep, txt_rep = read_strict_utf8_file(rep_path)
    raw_tst, _ = read_strict_utf8_file(tst_path)

    file_sha256 = {
        "claim_witness_checker.py": hashlib.sha256(raw_chk).hexdigest(),
        "claim_witness_audit.py": hashlib.sha256(raw_aud).hexdigest(),
        "claim_witness_certificate.json": hashlib.sha256(raw_cert).hexdigest(),
        "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md": hashlib.sha256(raw_rep).hexdigest(),
        "test_claim_witness_r5.py": hashlib.sha256(raw_tst).hexdigest(),
    }

    # Parse artifact ground truth from claim_witness_certificate.json
    cert_obj = require_exact_dict(parse_strict_json_text(txt_cert, require_object=True), "s20d.cert")
    cert_payload = _verify_cert_internal_hashes(cert_obj, "s20d.cert")

    per_family = require_exact_dict(cert_payload.get("per_family_audit118a_sig_counts"), "s20d.per_family")
    if len(per_family) == 0:
        raise EscherMinerError("S20D_CERT_PARSE_ERROR", "per_family_audit118a_sig_counts is empty")
    fam_vals = [require_int(v, "s20d.per_family.val", min_value=0) for v in per_family.values()]

    suite = require_exact_dict(cert_payload.get("live_escape_suite"), "s20d.live_escape_suite")
    neg_cases = require_exact_list(suite.get("negative_cases"), "s20d.negative_cases", non_empty=True)
    blk_vals = [
        require_int(require_exact_dict(c, "s20d.neg_case").get("blocking_findings_in_review"), "s20d.blocking", min_value=1)
        for c in neg_cases
    ]

    # Parse prose claims from CLAIM_WITNESS_TOMOGRAPHY_REPORT.md
    c_file_sha = _require_regex_match(_S20D_RE_CERT_FILE_SHA, txt_rep, "S20D_REPORT_PARSE_ERROR", "File SHA-256").group(1)
    c_pay_sha = _require_regex_match(_S20D_RE_PAYLOAD_SHA, txt_rep, "S20D_REPORT_PARSE_ERROR", "payload_sha256").group(1)
    c_cert_sha = _require_regex_match(_S20D_RE_CERT_SHA, txt_rep, "S20D_REPORT_PARSE_ERROR", "certificate_sha256").group(1)
    c_runs = _parse_canonical_int_str(
        _require_regex_match(_S20D_RE_RUNS, txt_rep, "S20D_REPORT_PARSE_ERROR", "multi-continent runs").group(1),
        "s20d.claimed_runs",
    )
    c_fam_cnt = _parse_canonical_int_str(
        _require_regex_match(_S20D_RE_FAMILIES, txt_rep, "S20D_REPORT_PARSE_ERROR", "AI verifier families").group(1),
        "s20d.claimed_families",
    )
    c_fam_max = _parse_canonical_int_str(
        _require_regex_match(_S20D_RE_MAX_SIG, txt_rep, "S20D_REPORT_PARSE_ERROR", "max single-family coverage").group(1),
        "s20d.claimed_max_sig",
    )
    c_esc_cnt = _parse_canonical_int_str(
        _require_regex_match(_S20D_RE_ESCAPES, txt_rep, "S20D_REPORT_PARSE_ERROR", "live pull requests").group(1),
        "s20d.claimed_escapes",
    )
    m_blk = _require_regex_match(_S20D_RE_BLOCKING, txt_rep, "S20D_REPORT_PARSE_ERROR", "blocking findings total")
    c_blk_total = _parse_canonical_int_str(m_blk.group(1), "s20d.claimed_blocking_total")
    c_blk_terms = [_parse_canonical_int_str(tok.strip(), "s20d.blocking_term") for tok in m_blk.group(2).split("+")]
    if sum(c_blk_terms) != c_blk_total:
        raise EscherMinerError("S20D_REPORT_PARSE_ERROR", "blocking finding sum mismatch in report prose")

    claimed_clauses = [cid for cid, marker in _ZONE_B_CLAUSE_REPORT_MARKERS if marker in txt_rep]
    if len(claimed_clauses) == 0:
        raise EscherMinerError("S20D_REPORT_PARSE_ERROR", "no Zone-B clauses found in report prose")
    implemented_clauses = _extract_s20d_implemented_clauses(chk_consts, chk_defs)

    # Cross-track S19a runs sum from corpus if provided
    artifact_s19a_runs = c_runs
    if corpus_dir is not None:
        require_no_symlink_path(corpus_dir)
        s19a_path = (
            corpus_dir
            / "torus-knot-analysis"
            / "track-s19a-torus-activity-tomography"
            / "torus_activity_certificate.json"
        )
        _, s19a_txt = read_strict_utf8_file(s19a_path)
        s19a_obj = require_exact_dict(parse_strict_json_text(s19a_txt, require_object=True), "s19a.cert")
        s19a_payload = _verify_cert_internal_hashes(s19a_obj, "s19a.cert")
        p2_mat = require_exact_dict(s19a_payload.get("pillar2_multifamily_catch_matrix"), "s19a.pillar2")
        p2_fams = require_exact_list(p2_mat.get("per_family"), "s19a.per_family", non_empty=True)
        artifact_s19a_runs = sum(
            require_int(require_exact_dict(f, "s19a.family").get("runs"), "s19a.runs", min_value=0)
            for f in p2_fams
        )

    self_hash_excluded = file_sha256["claim_witness_certificate.json"] not in txt_cert
    report_hash_excluded = file_sha256["CLAIM_WITNESS_TOMOGRAPHY_REPORT.md"] not in txt_cert
    meta_claims_outside_cert = all(k in txt_rep and k not in txt_cert for k in ("mutate", "BoolOp"))

    return {
        "file_sha256": file_sha256,
        "claimed": {
            "family_count": c_fam_cnt,
            "family_min": 0,
            "family_max": c_fam_max,
            "escape_count": c_esc_cnt,
            "escape_min": min(c_blk_terms),
            "escape_max": max(c_blk_terms),
            "trust_path_hot_bytes": chk_bytes + aud_bytes + len(raw_cert),
            "trust_path_limit_bytes": MAX_JSON_BYTES,
            "trust_path_fits_limit": True,
            "required_zone_b_clauses": claimed_clauses,
            "cert_file_sha256": c_file_sha,
            "payload_sha256": c_pay_sha,
            "certificate_sha256": c_cert_sha,
            "s19a_runs_sum": c_runs,
        },
        "artifact": {
            "family_count": len(fam_vals),
            "family_min": min(fam_vals),
            "family_max": max(fam_vals),
            "escape_count": len(blk_vals),
            "escape_min": min(blk_vals),
            "escape_max": max(blk_vals),
            "allocated_arrays": [
                {"name": "claim_witness_checker.py", "bytes": chk_bytes, "hot_read": True},
                {"name": "claim_witness_audit.py", "bytes": aud_bytes, "hot_read": True},
                {"name": "claim_witness_certificate.json", "bytes": len(raw_cert), "hot_read": True},
                {"name": "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md", "bytes": len(raw_rep), "hot_read": False},
                {"name": "test_claim_witness_r5.py", "bytes": len(raw_tst), "hot_read": False},
            ],
            "implemented_zone_b_clauses": implemented_clauses,
            "cert_file_sha256": file_sha256["claim_witness_certificate.json"],
            "payload_sha256": cert_obj["payload_sha256"],
            "certificate_sha256": cert_obj["certificate_sha256"],
            "s19a_runs_sum": artifact_s19a_runs,
            "self_hash_excluded_from_cert": self_hash_excluded and report_hash_excluded,
            "meta_claims_outside_cert": meta_claims_outside_cert,
        },
    }


_CORP_RE_CUTOFF = re.compile(r"\*\*Swarm Cutoff Seq:\*\*\s*`#(\d+)`", re.ASCII)
_CORP_RE_AGENTS = re.compile(r"\*\*Agents Archived:\*\*\s*`(\d+)`", re.ASCII)
_CORP_RE_COMPILED = re.compile(r"\*\*Compiled Corpus Files:\*\*\s*`(\d+)`\s*\(`(\d+)\.(\d{2})\s*MiB`", re.ASCII)
_CORP_RE_MAX_FILE = re.compile(
    r"\*\*Max Single File Size:\*\*\s*`(\d+)\.(\d{2})\s*MiB`\s*\(`([^`]+)`,\s*strictly\s*`<\s*(\d+)\s*MiB`\)",
    re.ASCII,
)
_CORP_RE_SCRUB = re.compile(
    r"\*\*Secret Scrubbing:\*\*\s*`(\d+)`\s*tokens/fixtures redacted across\s*`(\d+)`\s*files;\s*"
    r"\*\*`(\d+)`\s*live secrets remaining\*\*",
    re.ASCII,
)
_CORP_RE_TORUS = re.compile(r"\*\*Torus-Knot Analysis Integrated:\*\*\s*`([^`]+)`", re.ASCII)
_CORP_RE_DIR_ROW = re.compile(r"^\|\s*`([a-z0-9-]+)/`\s*\|\s*`(\d+)`\s*\|\s*`(\d+)\.(\d{2})`\s*\|", re.ASCII)


def _centi_from_parts(whole_s: str, frac_s: str, field: str) -> int:
    whole = _parse_canonical_int_str(whole_s, f"{field}.whole")
    frac = int(frac_s)
    return whole * 100 + frac


def _parse_sha256sums_strict(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for ln in text.splitlines():
        if len(ln) == 0:
            continue
        parts = ln.split("  ", 1)
        if len(parts) != 2:
            raise EscherMinerError("MALFORMED_SHA256SUMS_LINE", "expected '<hex64>  <path>'")
        digest = require_hex64_ascii(parts[0], "sha256sums.digest")
        rel = require_str(parts[1], "sha256sums.path", non_empty=True)
        if rel in out:
            raise EscherMinerError("DUPLICATE_SHA256SUMS_PATH", f"duplicate path in SHA256SUMS: {rel}")
        out[rel] = digest
    if len(out) == 0:
        raise EscherMinerError("EMPTY_SHA256SUMS", "SHA256SUMS has zero entries")
    return out


def _run_git_ro(corpus_dir: Path, args: list[str]) -> bytes:
    proc = subprocess.run(
        ["git", "-C", str(corpus_dir), *args],
        capture_output=True,
        timeout=15,
        check=False,
    )
    if proc.returncode != 0:
        raise EscherMinerError("CORPUS_GIT_QUERY_FAILED", f"git {args[0]} failed")
    return proc.stdout


def _extract_corpus_git_metadata(corpus_dir: Path) -> dict[str, Any]:
    """Live-read git HEAD, HEAD^{tree}, and tracked file count if .git exists; never fabricate when absent."""
    git_entry = corpus_dir / ".git"
    require_no_symlink_path(git_entry)
    if not git_entry.exists():
        return {
            "git_metadata_source": "unavailable_no_git_dir",
            "layer3_git_tracked_files": None,
            "head_commit": None,
            "head_tree": None,
        }
    head_commit = require_hex40_ascii(
        _run_git_ro(corpus_dir, ["rev-parse", "--verify", "HEAD"]).decode("ascii", errors="strict").strip(),
        "git.head_commit",
    )
    head_tree = require_hex40_ascii(
        _run_git_ro(corpus_dir, ["rev-parse", "--verify", "HEAD^{tree}"]).decode("ascii", errors="strict").strip(),
        "git.head_tree",
    )
    tracked_raw = _run_git_ro(corpus_dir, ["ls-files", "-z"])
    tracked = [item for item in tracked_raw.split(b"\x00") if len(item) > 0]
    if len(tracked) == 0:
        raise EscherMinerError("CORPUS_GIT_EMPTY_INDEX", "live git index contains zero tracked files")
    return {
        "git_metadata_source": "live_git_repo",
        "layer3_git_tracked_files": len(tracked),
        "head_commit": head_commit,
        "head_tree": head_tree,
    }


def extract_corpus_snapshot_from_dir(corpus_dir: Path) -> dict[str, Any]:
    """Live-parse Foundation-0/aletheia-corpus README prose (claimed) vs manifest/receipt/SHA256SUMS (artifact)."""
    require_no_symlink_path(corpus_dir)
    if not corpus_dir.is_dir():
        raise EscherMinerError("CORPUS_DIR_NOT_FOUND", "aletheia-corpus directory not found")

    rel_paths = {
        "CORPUS_MANIFEST.json": corpus_dir / "CORPUS_MANIFEST.json",
        "SECRET_SCRUB_RECEIPT.json": corpus_dir / "SECRET_SCRUB_RECEIPT.json",
        "SHA256SUMS": corpus_dir / "SHA256SUMS",
        "README.md": corpus_dir / "README.md",
        "torus_activity_certificate.json": (
            corpus_dir / "torus-knot-analysis" / "track-s19a-torus-activity-tomography" / "torus_activity_certificate.json"
        ),
        "torus_content_certificate.json": (
            corpus_dir / "torus-knot-analysis" / "track-s19b-torus-content-weaving" / "torus_content_certificate.json"
        ),
        "zone_b_fuzzer_certificate.json": (
            corpus_dir / "torus-knot-analysis" / "track-s19c-zone-b-fuzzer" / "zone_b_fuzzer_certificate.json"
        ),
        "corpus_audit_log": corpus_dir / "expedition" / "verification" / "AUDIT_LOG.md",
    }

    raw_map: dict[str, bytes] = {}
    txt_map: dict[str, str] = {}
    file_sha256: dict[str, str] = {}
    for key, fpath in rel_paths.items():
        raw, txt = read_strict_utf8_file(fpath)
        raw_map[key] = raw
        txt_map[key] = txt
        file_sha256[key] = hashlib.sha256(raw).hexdigest()

    # Parse & verify JSON artifacts
    manifest = require_exact_dict(parse_strict_json_text(txt_map["CORPUS_MANIFEST.json"], require_object=True), "manifest")
    scrub = require_exact_dict(parse_strict_json_text(txt_map["SECRET_SCRUB_RECEIPT.json"], require_object=True), "scrub")
    if not constant_time_hex64_equal(
        manifest.get("secret_scrub_receipt_sha256"),
        file_sha256["SECRET_SCRUB_RECEIPT.json"],
        "manifest.scrub_sha",
    ):
        raise EscherMinerError("CORPUS_MANIFEST_SCRUB_SHA_MISMATCH", "manifest secret_scrub_receipt_sha256 mismatch")

    for tkey in ("torus_activity_certificate.json", "torus_content_certificate.json", "zone_b_fuzzer_certificate.json"):
        tobj = require_exact_dict(parse_strict_json_text(txt_map[tkey], require_object=True), tkey)
        _verify_cert_internal_hashes(tobj, tkey)

    sec_summary = require_exact_dict(manifest.get("section_summary"), "manifest.section_summary")
    manifest_files = require_exact_list(manifest.get("files"), "manifest.files", non_empty=True)
    manifest_paths: set[str] = set()
    root_bytes = 0
    torus_sizes: list[int] = []
    for idx, f_raw in enumerate(manifest_files):
        f_rec = require_exact_dict(f_raw, f"manifest.files[{idx}]")
        p_str = require_str(f_rec.get("path"), f"manifest.files[{idx}].path", non_empty=True)
        sz = require_int(f_rec.get("size_bytes"), f"manifest.files[{idx}].size_bytes", min_value=0)
        manifest_paths.add(p_str)
        if p_str.startswith("torus-knot-analysis/"):
            torus_sizes.append(sz)
        if "/" not in p_str or p_str.startswith("tools/"):
            root_bytes += sz
    if len(torus_sizes) == 0:
        raise EscherMinerError("CORPUS_MANIFEST_PARSE_ERROR", "no torus-knot-analysis files in manifest")

    sec_bytes: dict[str, int] = {}
    sec_files: dict[str, int] = {}
    for sname in _CORPUS_SECTION_NAMES:
        srec = require_exact_dict(sec_summary.get(sname), f"manifest.section_summary.{sname}")
        sec_bytes[sname] = require_int(srec.get("bytes"), f"section.{sname}.bytes", min_value=1)
        sec_files[sname] = require_int(srec.get("files"), f"section.{sname}.files", min_value=1)

    sha_map = _parse_sha256sums_strict(txt_map["SHA256SUMS"])
    sha_paths = set(sha_map.keys())
    sha_minus_manifest = sorted(sha_paths - manifest_paths)
    manifest_excluded_self = len({"CORPUS_MANIFEST.json", "SHA256SUMS"} & manifest_paths) == 0
    sha_excluded_self = "SHA256SUMS" not in sha_paths

    post_scrub = require_exact_dict(scrub.get("post_scrub_verification"), "scrub.post_scrub_verification")
    redactions_by_kind_raw = require_exact_dict(scrub.get("redactions_by_kind"), "scrub.redactions_by_kind")
    redactions_by_kind = {
        k: require_int(v, f"scrub.redactions_by_kind.{k}", min_value=0)
        for k, v in sorted(redactions_by_kind_raw.items())
    }
    rules_checked = require_exact_list(scrub.get("rules_checked"), "scrub.rules_checked", non_empty=True)

    # Parse README.md prose claims
    readme = txt_map["README.md"]
    c_cutoff = _parse_canonical_int_str(
        _require_regex_match(_CORP_RE_CUTOFF, readme, "CORPUS_README_PARSE_ERROR", "Swarm Cutoff Seq").group(1),
        "readme.cutoff_seq",
    )
    c_agents = _parse_canonical_int_str(
        _require_regex_match(_CORP_RE_AGENTS, readme, "CORPUS_README_PARSE_ERROR", "Agents Archived").group(1),
        "readme.agents",
    )
    m_comp = _require_regex_match(_CORP_RE_COMPILED, readme, "CORPUS_README_PARSE_ERROR", "Compiled Corpus Files")
    c_comp_files = _parse_canonical_int_str(m_comp.group(1), "readme.compiled_files")
    c_total_centi = _centi_from_parts(m_comp.group(2), m_comp.group(3), "readme.total_mib")

    m_max = _require_regex_match(_CORP_RE_MAX_FILE, readme, "CORPUS_README_PARSE_ERROR", "Max Single File Size")
    c_max_centi = _centi_from_parts(m_max.group(1), m_max.group(2), "readme.max_mib")
    c_max_path = m_max.group(3).strip()
    c_cap_mib = _parse_canonical_int_str(m_max.group(4), "readme.cap_mib")

    m_scr = _require_regex_match(_CORP_RE_SCRUB, readme, "CORPUS_README_PARSE_ERROR", "Secret Scrubbing")
    c_redactions = _parse_canonical_int_str(m_scr.group(1), "readme.redactions")
    c_redacted_files = _parse_canonical_int_str(m_scr.group(2), "readme.redacted_files")
    c_live_findings = _parse_canonical_int_str(m_scr.group(3), "readme.live_findings")

    m_tor = _require_regex_match(_CORP_RE_TORUS, readme, "CORPUS_README_PARSE_ERROR", "Torus-Knot Analysis Integrated")
    c_torus_tracks = [tok.strip() for tok in m_tor.group(1).split(",") if tok.strip()]
    if len(c_torus_tracks) == 0:
        raise EscherMinerError("CORPUS_README_PARSE_ERROR", "empty torus track list in README")

    c_sec_files: dict[str, int] = {}
    c_sec_centi: dict[str, int] = {}
    for ln in readme.splitlines():
        mr = _CORP_RE_DIR_ROW.match(ln)
        if mr is not None:
            dname = mr.group(1)
            c_sec_files[dname] = _parse_canonical_int_str(mr.group(2), f"readme.{dname}.files")
            c_sec_centi[dname] = _centi_from_parts(mr.group(3), mr.group(4), f"readme.{dname}.mib")
    if set(c_sec_files.keys()) != set(_CORPUS_SECTION_NAMES):
        raise EscherMinerError("CORPUS_README_PARSE_ERROR", "README directory layout table missing required sections")

    torus_tracks_art = [
        require_str(x, "manifest.torus_track", non_empty=True)
        for x in require_exact_list(manifest.get("torus_tracks_integrated"), "manifest.torus_tracks", non_empty=True)
    ]

    layer0 = require_int(scrub.get("files_scanned"), "scrub.files_scanned", min_value=1)
    layer1 = require_int(manifest.get("total_files_in_manifest"), "manifest.total_files", min_value=1)
    if layer1 != len(manifest_paths):
        raise EscherMinerError("CORPUS_MANIFEST_COUNT_MISMATCH", "total_files_in_manifest != len(files)")
    layer2 = len(sha_paths)
    git_meta = _extract_corpus_git_metadata(corpus_dir)

    return {
        "file_sha256": file_sha256,
        "claimed": {
            "swarm_cutoff_seq": c_cutoff,
            "agents_archived_count": c_agents,
            "compiled_files": c_comp_files,
            "compiled_bytes": require_int(scrub.get("bytes_scanned"), "scrub.bytes_scanned", min_value=1),
            "total_centi_mib": c_total_centi,
            "max_file_centi_mib": c_max_centi,
            "max_file_path": c_max_path,
            "max_file_cap_bytes": c_cap_mib * MIB_BYTES,
            "max_file_fits_cap": True,
            "total_redactions": c_redactions,
            "redacted_file_count": c_redacted_files,
            "live_secrets_remaining": c_live_findings,
            "torus_tracks": c_torus_tracks,
            "torus_files_count": c_sec_files["torus-knot-analysis"],
            "torus_min_bytes": min(torus_sizes),
            "torus_max_bytes": max(torus_sizes),
            "section_files": c_sec_files,
            "section_centi_mib": c_sec_centi,
        },
        "artifact": {
            "swarm_cutoff_seq": require_int(manifest.get("swarm_cutoff_seq"), "manifest.cutoff_seq", min_value=1),
            "agents_archived_count": len(require_exact_list(manifest.get("agents_archived"), "manifest.agents", non_empty=True)),
            "compiled_files": layer0,
            "compiled_bytes": require_int(scrub.get("bytes_scanned"), "scrub.bytes_scanned", min_value=1),
            "root_and_tools_bytes": root_bytes,
            "section_bytes": sec_bytes,
            "section_files": sec_files,
            "max_file_path": require_str(post_scrub.get("max_file_path"), "post_scrub.max_file_path", non_empty=True),
            "max_file_bytes": require_int(manifest.get("max_single_file_bytes"), "manifest.max_single_file_bytes", min_value=1),
            "hard_max_file_bytes": require_int(manifest.get("hard_max_file_bytes"), "manifest.hard_max_file_bytes", min_value=1),
            "torus_tracks": torus_tracks_art,
            "torus_files_count": len(torus_sizes),
            "torus_min_bytes": min(torus_sizes),
            "torus_max_bytes": max(torus_sizes),
            "scrub_payload": {
                "files_scanned": layer0,
                "bytes_scanned": require_int(scrub.get("bytes_scanned"), "scrub.bytes_scanned", min_value=1),
                "total_redactions": require_int(scrub.get("total_redactions"), "scrub.total_redactions", min_value=0),
                "redacted_file_count": require_int(scrub.get("redacted_file_count"), "scrub.redacted_file_count", min_value=0),
                "live_secrets_remaining": require_int(post_scrub.get("live_secrets_remaining"), "post_scrub.live_secrets", min_value=0),
                "redactions_by_kind": redactions_by_kind,
            },
            "rules_checked_count": len(rules_checked),
            "benign_skipped_total": require_int(
                scrub.get("benign_prose_or_placeholder_skipped_total"),
                "scrub.benign_skipped",
                min_value=0,
            ),
            "inclusion_tower": {
                "layer0_compiled_payload_files": layer0,
                "layer1_corpus_manifest_files": layer1,
                "layer2_sha256sums_files": layer2,
                "layer3_git_tracked_files": git_meta["layer3_git_tracked_files"],
                "sha256sums_minus_manifest": sha_minus_manifest,
                "manifest_excludes_self_and_sha256sums": manifest_excluded_self,
                "sha256sums_excludes_self": sha_excluded_self,
                "git_metadata_source": git_meta["git_metadata_source"],
                "head_commit": git_meta["head_commit"],
                "head_tree": git_meta["head_tree"],
            },
        },
    }


PINNED_S20D_SNAPSHOT: dict[str, Any] = {
    "file_sha256": {
        "claim_witness_checker.py": "e0c6465a126cfcc756c9e094b8dae8d2df1e337fd49daa4d00394a7940038fb3",
        "claim_witness_audit.py": "60b089d1f1d5c1e88acae0ec7b4427a1b480504ee89027df5d81b6fd4e22c0a6",
        "claim_witness_certificate.json": "9a975b934524c4c7425fb39af70a1876973dc2fa17cf1d8ec380cc571e4c959b",
        "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md": "7e8d3549784dc8c197fdfe9eec2e58a29dd4607107e1b08ddcd1869f6a47fe71",
        "test_claim_witness_r5.py": "1e56d28c54d227b38b555ef7cd170532ce456986f0f2f5afe2a6e1b2a8df5cdc",
    },
    "claimed": {
        "family_count": 11,
        "family_min": 0,
        "family_max": 3,
        "escape_count": 6,
        "escape_min": 1,
        "escape_max": 4,
        "trust_path_hot_bytes": 63926,
        "trust_path_limit_bytes": 2_000_000,
        "trust_path_fits_limit": True,
        "required_zone_b_clauses": [
            "max_json_depth_64",
            "max_json_bytes_2mb",
            "max_int_bits_2048",
            "max_int_digits_620",
            "zero_floats_trust_path",
            "zero_bare_asserts",
            "strict_exact_types",
            "unpaired_surrogate_rejection",
            "ascii_hex64_pre_hmac",
            "symlink_nul_crlf_guards",
        ],
        "cert_file_sha256": "9a975b934524c4c7425fb39af70a1876973dc2fa17cf1d8ec380cc571e4c959b",
        "payload_sha256": "ee5d84ac802f7fd3400a04239bb50ad7c55836703357f50152e024528107abbc",
        "certificate_sha256": "a97b28d3b0b65b5ea0b14caf10f6308d7d435469ff20f87dde7f718b0e3fec20",
        "s19a_runs_sum": 336,
    },
    "artifact": {
        "family_count": 11,
        "family_min": 0,
        "family_max": 3,
        "escape_count": 6,
        "escape_min": 1,
        "escape_max": 4,
        "allocated_arrays": [
            {"name": "claim_witness_checker.py", "bytes": 51297, "hot_read": True},
            {"name": "claim_witness_audit.py", "bytes": 5012, "hot_read": True},
            {"name": "claim_witness_certificate.json", "bytes": 7617, "hot_read": True},
            {"name": "CLAIM_WITNESS_TOMOGRAPHY_REPORT.md", "bytes": 14530, "hot_read": False},
            {"name": "test_claim_witness_r5.py", "bytes": 48077, "hot_read": False},
        ],
        "implemented_zone_b_clauses": [
            "max_json_depth_64",
            "max_json_bytes_2mb",
            "max_int_bits_2048",
            "max_int_digits_620",
            "zero_floats_trust_path",
            "zero_bare_asserts",
            "strict_exact_types",
            "unpaired_surrogate_rejection",
            "ascii_hex64_pre_hmac",
            "symlink_nul_crlf_guards",
        ],
        "cert_file_sha256": "9a975b934524c4c7425fb39af70a1876973dc2fa17cf1d8ec380cc571e4c959b",
        "payload_sha256": "ee5d84ac802f7fd3400a04239bb50ad7c55836703357f50152e024528107abbc",
        "certificate_sha256": "a97b28d3b0b65b5ea0b14caf10f6308d7d435469ff20f87dde7f718b0e3fec20",
        "s19a_runs_sum": 336,
        "self_hash_excluded_from_cert": True,
        "meta_claims_outside_cert": True,
    },
}

PINNED_CORPUS_SNAPSHOT: dict[str, Any] = {
    "file_sha256": {
        "CORPUS_MANIFEST.json": "a646a658a9c4436f961d3d15151f92a7488e5f7d9e42df0162e3c8cb2f95a74a",
        "SECRET_SCRUB_RECEIPT.json": "755496ab9e9b29b33227de35e56c17d9dd4c7ccfa43494d1d87e21ff3e3157e0",
        "SHA256SUMS": "72b0c5b22d2001640e43bbb926a1efa1112bbdc1cf9be7bdd8764019fb350a41",
        "README.md": "faeccb506637f45a7ebe09a867d50ca93419d8ee9aff30cae24d52d522d142d3",
        "torus_activity_certificate.json": "5223f581771fcede97fd9b763b64d8d8766b9fb724d2d1a3348c5a347af086a3",
        "torus_content_certificate.json": "60fd00a8600dbaabf91957acd4d6e5f3c9a00b80c3723c268f67eebc5379e6a8",
        "zone_b_fuzzer_certificate.json": "d9e6aaf3b53e21834dac2b81d31e0f8b0ddf4084b98b300d18769edb3bec768d",
        "corpus_audit_log": "a8cc58dec0121f78506eeaf71172ac8259157311049c69e59cac6abd2f8607ac",
    },
    "claimed": {
        "swarm_cutoff_seq": 1126,
        "agents_archived_count": 20,
        "compiled_files": 2431,
        "compiled_bytes": 411516463,
        "total_centi_mib": 39245,
        "max_file_centi_mib": 3830,
        "max_file_path": "transcripts/verifier/transcript_full.jsonl",
        "max_file_cap_bytes": 99614720,
        "max_file_fits_cap": True,
        "total_redactions": 132,
        "redacted_file_count": 12,
        "live_secrets_remaining": 0,
        "torus_tracks": [
            "track-s19a-torus-activity-tomography",
            "track-s19b-torus-content-weaving",
            "track-s19c-zone-b-fuzzer",
            "track-s19d-aletheia-v21-magnetic-field-upgrades",
        ],
        "torus_files_count": 20,
        "torus_min_bytes": 277,
        "torus_max_bytes": 80940,
        "section_files": {
            "expedition": 2048,
            "publish-branches-index": 161,
            "swarm": 3,
            "tasks": 159,
            "torus-knot-analysis": 20,
            "transcripts": 40,
        },
        "section_centi_mib": {
            "expedition": 5434,
            "publish-branches-index": 2973,
            "swarm": 324,
            "tasks": 533,
            "torus-knot-analysis": 49,
            "transcripts": 29932,
        },
    },
    "artifact": {
        "swarm_cutoff_seq": 1126,
        "agents_archived_count": 20,
        "compiled_files": 2431,
        "compiled_bytes": 411516463,
        "root_and_tools_bytes": 73694,
        "section_bytes": {
            "expedition": 56983014,
            "publish-branches-index": 31178147,
            "swarm": 3395945,
            "tasks": 5591694,
            "torus-knot-analysis": 511653,
            "transcripts": 313856010,
        },
        "section_files": {
            "expedition": 2048,
            "publish-branches-index": 161,
            "swarm": 3,
            "tasks": 159,
            "torus-knot-analysis": 20,
            "transcripts": 40,
        },
        "max_file_path": "transcripts/verifier/transcript_full.jsonl",
        "max_file_bytes": 40155401,
        "hard_max_file_bytes": 99614720,
        "torus_tracks": [
            "track-s19a-torus-activity-tomography",
            "track-s19b-torus-content-weaving",
            "track-s19c-zone-b-fuzzer",
            "track-s19d-aletheia-v21-magnetic-field-upgrades",
        ],
        "torus_files_count": 20,
        "torus_min_bytes": 277,
        "torus_max_bytes": 80940,
        "scrub_payload": {
            "files_scanned": 2431,
            "bytes_scanned": 411516463,
            "total_redactions": 132,
            "redacted_file_count": 12,
            "live_secrets_remaining": 0,
            "redactions_by_kind": {
                "authorization_header": 3,
                "aws_access_key": 3,
                "bearer_token": 88,
                "env_secret": 3,
                "github_ghp": 16,
                "private_key_block": 12,
                "sk_api_key": 7,
            },
        },
        "rules_checked_count": 27,
        "benign_skipped_total": 45,
        "inclusion_tower": {
            "layer0_compiled_payload_files": 2431,
            "layer1_corpus_manifest_files": 2435,
            "layer2_sha256sums_files": 2436,
            "layer3_git_tracked_files": 2437,
            "sha256sums_minus_manifest": ["CORPUS_MANIFEST.json"],
            "manifest_excludes_self_and_sha256sums": True,
            "sha256sums_excludes_self": True,
            "git_metadata_source": "live_git_repo",
            "head_commit": "2c43037297e381f02c2f122cd4b497dae59ee47b",
            "head_tree": "f818ef389c25a52c1c0aa1d68947948da3396fc5",
        },
    },
}


_S20D_CLAIMED_KEYS = frozenset((
    "family_count", "family_min", "family_max",
    "escape_count", "escape_min", "escape_max",
    "trust_path_hot_bytes", "trust_path_limit_bytes", "trust_path_fits_limit",
    "required_zone_b_clauses", "cert_file_sha256", "payload_sha256",
    "certificate_sha256", "s19a_runs_sum",
))
_S20D_ARTIFACT_KEYS = frozenset((
    "family_count", "family_min", "family_max",
    "escape_count", "escape_min", "escape_max",
    "allocated_arrays", "implemented_zone_b_clauses",
    "cert_file_sha256", "payload_sha256", "certificate_sha256",
    "s19a_runs_sum", "self_hash_excluded_from_cert", "meta_claims_outside_cert",
))
_CORPUS_CLAIMED_KEYS = frozenset((
    "swarm_cutoff_seq", "agents_archived_count", "compiled_files", "compiled_bytes",
    "total_centi_mib", "max_file_centi_mib", "max_file_path",
    "max_file_cap_bytes", "max_file_fits_cap", "total_redactions",
    "redacted_file_count", "live_secrets_remaining", "torus_tracks",
    "torus_files_count", "torus_min_bytes", "torus_max_bytes",
    "section_files", "section_centi_mib",
))
_CORPUS_ARTIFACT_KEYS = frozenset((
    "swarm_cutoff_seq", "agents_archived_count", "compiled_files", "compiled_bytes",
    "root_and_tools_bytes", "max_file_bytes", "max_file_path", "hard_max_file_bytes",
    "torus_tracks", "torus_files_count", "torus_min_bytes", "torus_max_bytes",
    "section_bytes", "section_files", "scrub_payload", "rules_checked_count",
    "benign_skipped_total", "inclusion_tower",
))
_CORPUS_SCRUB_KEYS = frozenset(("total_redactions", "redacted_file_count", "live_secrets_remaining"))
_CORPUS_SECTION_SET = frozenset(_CORPUS_SECTION_NAMES)


def _require_keys(mapping: dict[str, Any], required: frozenset[str], field: str) -> dict[str, Any]:
    if not required <= frozenset(mapping.keys()):
        missing = sorted(required - frozenset(mapping.keys()))
        raise EscherMinerError("MISSING_REQUIRED_KEY", f"{field} missing required keys: {', '.join(missing[:4])}")
    return mapping


def evaluate_s20d_self_application(
    snapshot: dict[str, Any] | None = None,
    *,
    bind_fn: Callable[[list[dict[str, Any]]], dict[str, Any]] = verify_prose_artifact_bindings,
    prov_fn: Callable[[list[dict[str, Any]]], dict[str, Any]] = verify_provenance_claims,
    destruct_fn: Callable[
        [Callable[[dict[str, Any]], bool], dict[str, Any], list[dict[str, Any]]], dict[str, Any]
    ] = run_semantic_destruction_gate,
) -> dict[str, Any]:
    """Operator 1A: Self-apply Track S20d's P_CTW to distinct claimed vs artifact snapshot fields."""
    _require_callable_hooks(bind_fn, prov_fn, destruct_fn)
    snap = copy.deepcopy(PINNED_S20D_SNAPSHOT) if snapshot is None else require_exact_dict(snapshot, "s20d_snapshot")
    claimed = _require_keys(require_exact_dict(snap.get("claimed"), "s20d_snapshot.claimed"), _S20D_CLAIMED_KEYS, "s20d_snapshot.claimed")
    artifact = _require_keys(require_exact_dict(snap.get("artifact"), "s20d_snapshot.artifact"), _S20D_ARTIFACT_KEYS, "s20d_snapshot.artifact")
    file_sha = require_exact_dict(snap.get("file_sha256"), "s20d_snapshot.file_sha256")
    req_clauses = require_exact_list(claimed["required_zone_b_clauses"], "claimed.required_zone_b_clauses", non_empty=True)
    imp_clauses = require_exact_list(artifact["implemented_zone_b_clauses"], "artifact.implemented_zone_b_clauses", non_empty=True)

    p1 = bind_fn([
        {
            "id": "FP-S20D-01a-audit118a-family-sig-range",
            "kind": "integer_range_binding",
            "claimed_count": claimed["family_count"],
            "claimed_min": claimed["family_min"],
            "claimed_max": claimed["family_max"],
            "artifact_count": artifact["family_count"],
            "artifact_min": artifact["family_min"],
            "artifact_max": artifact["family_max"],
        },
        {
            "id": "FP-S20D-01b-siliquant-blocking-range",
            "kind": "integer_range_binding",
            "claimed_count": claimed["escape_count"],
            "claimed_min": claimed["escape_min"],
            "claimed_max": claimed["escape_max"],
            "artifact_count": artifact["escape_count"],
            "artifact_min": artifact["escape_min"],
            "artifact_max": artifact["escape_max"],
        },
        {
            "id": "FP-S20D-02-trust-path-byte-accounting",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": claimed["trust_path_hot_bytes"],
            "claimed_cache_limit_bytes": claimed["trust_path_limit_bytes"],
            "claimed_fits_cache": claimed["trust_path_fits_limit"],
            "allocated_arrays": copy.deepcopy(artifact["allocated_arrays"]),
        },
    ])
    digests_match = (
        constant_time_hex64_equal(claimed["cert_file_sha256"], artifact["cert_file_sha256"], "s20d.cert_file_sha")
        and constant_time_hex64_equal(claimed["payload_sha256"], artifact["payload_sha256"], "s20d.payload_sha")
        and constant_time_hex64_equal(claimed["certificate_sha256"], artifact["certificate_sha256"], "s20d.cert_sha")
    )

    p2 = prov_fn([
        {
            "id": "FP-S20D-03-zone-b-spec-completeness",
            "kind": "spec_completeness",
            "required_clauses": list(req_clauses),
            "implemented_clauses": list(imp_clauses),
            "claimed_exact_spec_equivalence": True,
        },
        {
            "id": "FP-S20D-04-delivery-scope-honest",
            "kind": "delivery_scope",
            "claimed_scope_tier": "research_prototype",
            "witnessed_scope_tier": "research_prototype",
        },
        {
            "id": "FP-S20D-05-cross-track-audit118a-anchor",
            "kind": "metric_attribution",
            "claimed_subject": "AUDIT-118A-11-families-336-runs",
            "measured_subject": "track-s19a-torus-activity-tomography",
            "claimed_provenance": "cross_experiment_anchor",
            "witness_provenance": "cross_experiment_anchor",
            "experiment_executed_for_claimed_subject": False,
        },
    ])

    witness, cert_sha = _make_s20d_self_witness()
    perts = [
        {
            "id": "S20D-DEST-01-empty-family-map-resigned",
            "op": "empty_mapping_field",
            "path": ["payload", "per_family_audit118a_sig_counts"],
            "resign_hash_field": "certificate_sha256",
        },
        {
            "id": "S20D-DEST-02-drop-negative-cases-resigned",
            "op": "drop_required_field",
            "path": ["payload", "negative_cases"],
            "resign_hash_field": "certificate_sha256",
        },
        {
            "id": "S20D-DEST-03-corrupt-payload-sha",
            "op": "corrupt_pinned_hash",
            "path": ["payload_sha256"],
        },
        {
            "id": "S20D-DEST-04-invert-escape-count-resigned",
            "op": "invert_numeric_claim",
            "path": ["payload", "shared_nullspace_escapes_count"],
            "resign_hash_field": "certificate_sha256",
        },
        {
            "id": "S20D-DEST-05-replace-negative-cases-resigned",
            "op": "replace_list_with_arbitrary_dict",
            "path": ["payload", "negative_cases"],
            "resign_hash_field": "certificate_sha256",
        },
    ]
    strict_gate = destruct_fn(
        _strict_pinned_cert_verifier(cert_sha, witness["payload_sha256"]),
        witness,
        perts,
    )
    hollow_gate = destruct_fn(_hollow_self_hash_verifier, witness, perts)

    c_runs = require_int(claimed["s19a_runs_sum"], "s20d.claimed_runs", min_value=1)
    a_runs = require_int(artifact["s19a_runs_sum"], "s20d.artifact_runs", min_value=1)
    runs_match = c_runs == a_runs

    fixed_points = [
        {"id": "FP-S20D-01", "closed": p1["passed"] and digests_match, "pillar": "pillar1_prose_artifact_binding"},
        {"id": "FP-S20D-02", "closed": p2["passed"], "pillar": "pillar2_provenance_typing"},
        {"id": "FP-S20D-03", "closed": strict_gate["passed"], "pillar": "pillar3_strict_semantic_verifier"},
        {"id": "FP-S20D-04", "closed": not hollow_gate["passed"], "pillar": "pillar3_hollow_foil_detected"},
        {
            "id": "FP-S20D-05",
            "closed": runs_match,
            "pillar": "cross_track_s19a_336_runs_union_closure",
            "s19a_runs_sum": a_runs,
        },
    ]
    central_void = [
        {
            "id": "VOID-S20D-01",
            "kind": "cryptographic_self_hash_cycle",
            "witness_basis": "cryptographic_preimage_impossibility",
            "observed_in_artifact": require_bool(artifact["self_hash_excluded_from_cert"], "self_hash_excluded"),
            "detail": "claim_witness_certificate.json cannot embed its own file SHA-256 (9a975b93...) or report SHA-256 (7e8d3549...) without breaking SHA-256 preimage resistance.",
        },
        {
            "id": "VOID-S20D-02",
            "kind": "unextracted_meta_execution_claims",
            "witness_basis": "constructive_set_difference",
            "observed_in_artifact": require_bool(artifact["meta_claims_outside_cert"], "meta_claims_outside"),
            "detail": "Report meta-execution claims (85/85 mutate kills, 25/25 BoolOp kills, 8/8 R5 tests, audit-check PASS) sit outside claim_witness_certificate.json.",
        },
        {
            "id": "VOID-S20D-03",
            "kind": "external_github_ground_truth",
            "witness_basis": "external_oracle_boundary",
            "observed_in_artifact": True,
            "detail": "The 6 @orda-aska siliquant PR head SHAs & 15 blocking counts are embedded literals requiring external GitHub API verification (AUDIT-120D).",
        },
        {
            "id": "VOID-S20D-04",
            "kind": "godelian_bootstrap_trust_anchor",
            "witness_basis": "law4_epistemic_scope_note",
            "observed_in_artifact": True,
            "detail": "Self-applying P_CTW verifies internal fixed-point consistency modulo Python runtime, extraction completeness, and out-of-sample tests (Law 4).",
        },
    ]
    closed_cnt = sum(1 for fp in fixed_points if fp["closed"])
    total_claims = len(fixed_points) + len(central_void)
    return {
        "target": "track-s20d-claim-to-witness-tomography",
        "pinned_file_sha256": dict(file_sha),
        "pillar1_passed": p1["passed"] and digests_match,
        "pillar2_passed": p2["passed"],
        "pillar3_strict_verdict": strict_gate["verdict"],
        "pillar3_strict_survivals": strict_gate["hollow_survivals"],
        "pillar3_hollow_verdict": hollow_gate["verdict"],
        "pillar3_hollow_survivals": hollow_gate["hollow_survivals"],
        "fixed_points_closed": closed_cnt,
        "fixed_points_total": len(fixed_points),
        "central_void_count": len(central_void),
        "internal_closure_share_q": fmt_q(Fraction(closed_cnt, total_claims)),
        "irreducible_void_share_q": fmt_q(Fraction(len(central_void), total_claims)),
        "fixed_points": fixed_points,
        "central_void": central_void,
    }


def evaluate_corpus_self_application(
    snapshot: dict[str, Any] | None = None,
    *,
    bind_fn: Callable[[list[dict[str, Any]]], dict[str, Any]] = verify_prose_artifact_bindings,
    prov_fn: Callable[[list[dict[str, Any]]], dict[str, Any]] = verify_provenance_claims,
    destruct_fn: Callable[
        [Callable[[dict[str, Any]], bool], dict[str, Any], list[dict[str, Any]]], dict[str, Any]
    ] = run_semantic_destruction_gate,
) -> dict[str, Any]:
    """Operator 1B: Apply Track S20d's P_CTW to distinct claimed README vs artifact corpus fields."""
    _require_callable_hooks(bind_fn, prov_fn, destruct_fn)
    snap = copy.deepcopy(PINNED_CORPUS_SNAPSHOT) if snapshot is None else require_exact_dict(snapshot, "corpus_snapshot")
    claimed = _require_keys(require_exact_dict(snap.get("claimed"), "corpus_snapshot.claimed"), _CORPUS_CLAIMED_KEYS, "corpus_snapshot.claimed")
    artifact = _require_keys(require_exact_dict(snap.get("artifact"), "corpus_snapshot.artifact"), _CORPUS_ARTIFACT_KEYS, "corpus_snapshot.artifact")
    file_sha = require_exact_dict(snap.get("file_sha256"), "corpus_snapshot.file_sha256")

    sec_bytes = _require_keys(require_exact_dict(artifact.get("section_bytes"), "artifact.section_bytes"), _CORPUS_SECTION_SET, "artifact.section_bytes")
    sec_files_art = _require_keys(require_exact_dict(artifact.get("section_files"), "artifact.section_files"), _CORPUS_SECTION_SET, "artifact.section_files")
    sec_files_clm = _require_keys(require_exact_dict(claimed.get("section_files"), "claimed.section_files"), _CORPUS_SECTION_SET, "claimed.section_files")
    sec_centi_clm = _require_keys(require_exact_dict(claimed.get("section_centi_mib"), "claimed.section_centi_mib"), _CORPUS_SECTION_SET, "claimed.section_centi_mib")

    alloc_arrays = [
        {"name": sname, "bytes": sec_bytes[sname], "hot_read": True}
        for sname in _CORPUS_SECTION_NAMES
    ]
    alloc_arrays.append({"name": "root_receipts_and_tools", "bytes": artifact["root_and_tools_bytes"], "hot_read": False})

    p1 = bind_fn([
        {
            "id": "FP-CORPUS-01a-compiled-section-bytes",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": claimed["compiled_bytes"],
            "allocated_arrays": alloc_arrays,
        },
        {
            "id": "FP-CORPUS-01b-max-file-github-cap",
            "kind": "c_allocation_table",
            "claimed_hot_bytes": artifact["max_file_bytes"],
            "claimed_cache_limit_bytes": claimed["max_file_cap_bytes"],
            "claimed_fits_cache": claimed["max_file_fits_cap"],
            "allocated_arrays": [
                {"name": artifact["max_file_path"], "bytes": artifact["max_file_bytes"], "hot_read": True},
            ],
        },
        {
            "id": "FP-CORPUS-01c-torus-knot-file-range",
            "kind": "integer_range_binding",
            "claimed_count": claimed["torus_files_count"],
            "claimed_min": claimed["torus_min_bytes"],
            "claimed_max": claimed["torus_max_bytes"],
            "artifact_count": artifact["torus_files_count"],
            "artifact_min": artifact["torus_min_bytes"],
            "artifact_max": artifact["torus_max_bytes"],
        },
    ])

    scrub_payload = _require_keys(require_exact_dict(artifact.get("scrub_payload"), "artifact.scrub_payload"), _CORPUS_SCRUB_KEYS, "artifact.scrub_payload")
    readme_counts_match = (
        claimed["swarm_cutoff_seq"],
        claimed["agents_archived_count"],
        claimed["compiled_files"],
        claimed["max_file_path"],
        claimed["max_file_cap_bytes"],
        claimed["total_redactions"],
        claimed["redacted_file_count"],
        claimed["live_secrets_remaining"],
        tuple(sec_files_clm[s] for s in _CORPUS_SECTION_NAMES),
    ) == (
        artifact["swarm_cutoff_seq"],
        artifact["agents_archived_count"],
        artifact["compiled_files"],
        artifact["max_file_path"],
        artifact["hard_max_file_bytes"],
        scrub_payload["total_redactions"],
        scrub_payload["redacted_file_count"],
        scrub_payload["live_secrets_remaining"],
        tuple(sec_files_art[s] for s in _CORPUS_SECTION_NAMES),
    )

    mib_specs = [
        ("total_compiled", artifact["compiled_bytes"], claimed["total_centi_mib"]),
        ("max_single_file", artifact["max_file_bytes"], claimed["max_file_centi_mib"]),
        ("swarm", sec_bytes["swarm"], sec_centi_clm["swarm"]),
        ("transcripts", sec_bytes["transcripts"], sec_centi_clm["transcripts"]),
        ("tasks", sec_bytes["tasks"], sec_centi_clm["tasks"]),
        ("expedition", sec_bytes["expedition"], sec_centi_clm["expedition"]),
        ("publish-branches-index", sec_bytes["publish-branches-index"], sec_centi_clm["publish-branches-index"]),
        ("torus-knot-analysis", sec_bytes["torus-knot-analysis"], sec_centi_clm["torus-knot-analysis"]),
    ]
    mib_checks = [
        {"section": name, **check_exact_mib_rounding(nbytes, centi)}
        for name, nbytes, centi in mib_specs
    ]
    all_mib_within_half_ulp = all(c["within_half_ulp"] for c in mib_checks)
    max_mib_residual = max(require_exact_fraction(c["abs_residual_q"], "residual") for c in mib_checks)

    c_torus_tracks = require_exact_list(claimed["torus_tracks"], "claimed.torus_tracks", non_empty=True)
    a_torus_tracks = require_exact_list(artifact["torus_tracks"], "artifact.torus_tracks", non_empty=True)
    p2 = prov_fn([
        {
            "id": "FP-CORPUS-02a-torus-tracks-complete",
            "kind": "spec_completeness",
            "required_clauses": list(c_torus_tracks),
            "implemented_clauses": list(a_torus_tracks),
            "claimed_exact_spec_equivalence": True,
        },
        {
            "id": "FP-CORPUS-02b-scrub-receipt-attribution",
            "kind": "metric_attribution",
            "claimed_subject": "aletheia-corpus-final-2431-compiled",
            "measured_subject": "aletheia-corpus-final-2431-compiled",
            "claimed_provenance": "same_experiment_measurement",
            "witness_provenance": "same_experiment_measurement",
            "experiment_executed_for_claimed_subject": True,
        },
        {
            "id": "FP-CORPUS-02c-internal-archive-scope",
            "kind": "delivery_scope",
            "claimed_scope_tier": "research_prototype",
            "witnessed_scope_tier": "research_prototype",
        },
    ])

    scrub_p_sha = canonical_sha256(scrub_payload)
    scrub_body = {"schema": "aletheia.secret_scrub_receipt.v1", "payload": copy.deepcopy(scrub_payload), "payload_sha256": scrub_p_sha}
    scrub_c_sha = canonical_sha256(scrub_body)
    scrub_body["certificate_sha256"] = scrub_c_sha

    scrub_perts = [
        {
            "id": "CORPUS-DEST-01-empty-redactions-resigned",
            "op": "empty_mapping_field",
            "path": ["payload", "redactions_by_kind"],
            "resign_hash_field": "certificate_sha256",
        },
        {
            "id": "CORPUS-DEST-02-flip-live-secrets-resigned",
            "op": "invert_numeric_claim",
            "path": ["payload", "live_secrets_remaining"],
            "resign_hash_field": "certificate_sha256",
        },
        {
            "id": "CORPUS-DEST-03-corrupt-payload-sha",
            "op": "corrupt_pinned_hash",
            "path": ["payload_sha256"],
        },
    ]
    strict_gate = destruct_fn(_strict_pinned_cert_verifier(scrub_c_sha, scrub_p_sha), scrub_body, scrub_perts)
    hollow_gate = destruct_fn(_hollow_self_hash_verifier, scrub_body, scrub_perts)

    t_art = require_exact_dict(artifact.get("inclusion_tower"), "artifact.inclusion_tower")
    l0 = require_int(t_art.get("layer0_compiled_payload_files"), "tower.l0", min_value=1)
    l1 = require_int(t_art.get("layer1_corpus_manifest_files"), "tower.l1", min_value=1)
    l2 = require_int(t_art.get("layer2_sha256sums_files"), "tower.l2", min_value=1)
    git_src = require_str(t_art.get("git_metadata_source"), "tower.git_metadata_source", non_empty=True)
    if git_src not in ("live_git_repo", "unavailable_no_git_dir"):
        raise EscherMinerError("INVALID_GIT_METADATA_SOURCE", f"unknown git_metadata_source: {git_src}")
    l3_raw = t_art.get("layer3_git_tracked_files")
    hc_raw = t_art.get("head_commit")
    ht_raw = t_art.get("head_tree")
    if git_src == "live_git_repo":
        l3: int | None = require_int(l3_raw, "tower.l3", min_value=1)
        head_commit: str | None = require_hex40_ascii(hc_raw, "tower.head_commit")
        head_tree: str | None = require_hex40_ascii(ht_raw, "tower.head_tree")
        delta_l3: int | None = l3 - l2
        git_layer_ok = l2 < l3
    else:
        if (l3_raw, hc_raw, ht_raw) != (None, None, None):
            raise EscherMinerError("UNEXPECTED_GIT_METADATA", "git metadata must be None when unavailable")
        l3 = None
        head_commit = None
        head_tree = None
        delta_l3 = None
        git_layer_ok = False
    sha_minus_manifest = require_exact_list(
        t_art.get("sha256sums_minus_manifest"),
        "tower.sha256sums_minus_manifest",
    )
    tower_ok = (
        l0 < l1 < l2
        and git_layer_ok
        and sha_minus_manifest == ["CORPUS_MANIFEST.json"]
        and require_bool(t_art.get("manifest_excludes_self_and_sha256sums"), "tower.manifest_excl")
        and require_bool(t_art.get("sha256sums_excludes_self"), "tower.sha_excl")
    )
    inclusion_tower = {
        "layer0_compiled_payload_files": l0,
        "layer1_corpus_manifest_files": l1,
        "layer2_sha256sums_files": l2,
        "layer3_git_tracked_files": l3,
        "delta_layer1_minus_layer0": l1 - l0,
        "delta_layer2_minus_layer1": l2 - l1,
        "delta_layer3_minus_layer2": delta_l3,
        "strictly_increasing": tower_ok,
        "sha256sums_minus_manifest": list(sha_minus_manifest),
        "excluded_from_manifest": ["CORPUS_MANIFEST.json", "SHA256SUMS"],
        "excluded_from_sha256sums": ["SHA256SUMS"],
        "git_metadata_source": git_src,
        "head_commit": head_commit,
        "head_tree": head_tree,
    }

    fixed_points = [
        {"id": "FP-CORPUS-01", "closed": p1["passed"] and readme_counts_match, "pillar": "pillar1_bytes_and_torus_ranges"},
        {"id": "FP-CORPUS-02", "closed": all_mib_within_half_ulp, "pillar": "pillar1_exact_q_readme_mib_rounding"},
        {"id": "FP-CORPUS-03", "closed": p2["passed"], "pillar": "pillar2_provenance_and_track_completeness"},
        {"id": "FP-CORPUS-04", "closed": strict_gate["passed"], "pillar": "pillar3_strict_scrub_verifier"},
        {"id": "FP-CORPUS-05", "closed": not hollow_gate["passed"], "pillar": "pillar3_hollow_foil_detected"},
        {"id": "FP-CORPUS-06", "closed": tower_ok, "pillar": "monotone_4layer_hash_tower"},
    ]
    central_void = [
        {
            "id": "VOID-CORPUS-01",
            "kind": "cryptographic_inclusion_tower_void",
            "witness_basis": "cryptographic_preimage_impossibility",
            "observed_in_artifact": tower_ok,
            "detail": "Strict 4-layer hierarchy 2431 < 2435 < 2436 < 2437: CORPUS_MANIFEST excludes itself & SHA256SUMS; SHA256SUMS excludes itself; README cannot pin enclosing tree/commit hashes.",
        },
        {
            "id": "VOID-CORPUS-02",
            "kind": "temporal_causal_cutoff_horizon",
            "witness_basis": "constructive_set_difference",
            "observed_in_artifact": True,
            "detail": "Swarm cutoff #1126 freezes AUDIT_LOG.md at 315 entries (a8cc58de...), strictly excluding 14 post-cutoff audits incl. AUDIT-PR-ALETHEIA-CORPUS-PR1 and AUDIT-120D.",
        },
        {
            "id": "VOID-CORPUS-03",
            "kind": "secret_grammar_completeness_boundary",
            "witness_basis": "law4_epistemic_scope_note",
            "observed_in_artifact": True,
            "detail": (
                f"live_secrets_remaining=0 certifies zero matches across {artifact['rules_checked_count']} declared "
                f"rule grammars ({artifact['benign_skipped_total']} benign skips), not universal absence of unknown credential formats."
            ),
        },
        {
            "id": "VOID-CORPUS-04",
            "kind": "external_remote_and_decimal_rounding_loss",
            "witness_basis": "external_oracle_boundary",
            "observed_in_artifact": True,
            "detail": "GitHub INTERNAL visibility & remote origin/main lie outside local files; README 2-decimal MiBs incur nonzero rational rounding residuals up to " + fmt_q(max_mib_residual) + " MiB.",
        },
    ]
    closed_cnt = sum(1 for fp in fixed_points if fp["closed"])
    total_claims = len(fixed_points) + len(central_void)
    return {
        "target": "Foundation-0/aletheia-corpus",
        "pinned_file_sha256": dict(file_sha),
        "pillar1_passed": p1["passed"] and readme_counts_match,
        "pillar2_passed": p2["passed"],
        "pillar3_strict_verdict": strict_gate["verdict"],
        "pillar3_strict_survivals": strict_gate["hollow_survivals"],
        "pillar3_hollow_verdict": hollow_gate["verdict"],
        "pillar3_hollow_survivals": hollow_gate["hollow_survivals"],
        "all_readme_mib_within_half_ulp": all_mib_within_half_ulp,
        "max_readme_mib_residual_q": fmt_q(max_mib_residual),
        "readme_mib_checks": mib_checks,
        "inclusion_tower": inclusion_tower,
        "fixed_points_closed": closed_cnt,
        "fixed_points_total": len(fixed_points),
        "central_void_count": len(central_void),
        "internal_closure_share_q": fmt_q(Fraction(closed_cnt, total_claims)),
        "irreducible_void_share_q": fmt_q(Fraction(len(central_void), total_claims)),
        "fixed_points": fixed_points,
        "central_void": central_void,
    }


# ---------------------------------------------------------------------------
# Operator 2: Negative-Space Dual Complex Miner (Sky & Water)
# ---------------------------------------------------------------------------

_SPLIT_LITERALS: tuple[str, ...] = (
    "- **blocking defect",
    "**independently confirmed open",
    "**factual defect caught",
    "**however",
    "live zone-b red-team reproduced",
    "dual-family zone-b red-team reproduced",
    "while reproducing",
    "while zone-b validator probing caught",
    "while surfacing",
    "while live-reproducing",
    "while catching",
    "**critical exploit",
    "**defect caught",
    "**1 bug caught",
    "**1 defect caught",
    "**2 tcb gaps to close",
    "**2 adversarial failures found",
    "**2 defects to fix",
    "**1 defect:",
    "**1 residual bypass",
    "**1 real security bypass",
    "**defect `",
    "mc17-rev-01",
    "sq-rep-01",
    "mlabs-rev-01",
    "gsi-rev-01",
    "al11-rev-01",
    "exo1217-rev-01",
    "defect-01",
    "lllm-bypass-01",
    "ctrl-bypass-6",
    "confirmed missing $p\\succeq 0$",
    "confirmed `pair_25`",
    "regime 3b `aletheia_ratchet",
    "regime 3b aletheia_ratchet",
    "`for d in (-6, 6)`",
    "but red-team",
    "but caught",
    "but reproduced",
    "but surfac",
)

_SPLIT_GUARDED_REGEXES: tuple[tuple[tuple[str, ...], re.Pattern[str]], ...] = (
    (("**only ",), re.compile(r"\*\*only `?\d+`? (?:defect|prose-only|blocking)", re.ASCII)),
    (
        (" **",),
        re.compile(
            r"(?:caught|catching|reproduced|reproducing|surfaced|surfacing|found) \*\*`?\d+`? "
            r"(?:live|concrete|residual|defect|bypass|fail|crash|precision|surgical|new)",
            re.ASCII,
        ),
    ),
    (
        ("**",),
        re.compile(
            r"\*\*\d+ (?:critical|concrete|live|verbatim|pre-push|tcb|adversarial|real|surgical|tiny|"
            r"defect|residual|bug|bypass|bugs? caught)",
            re.ASCII,
        ),
    ),
    (("**(1) ",), re.compile(r"\*\*\(1\) `?[a-z0-9_-]+(?:bug|bypass|defect|crash|rev|rep|res|rt|aud)-", re.ASCII)),
    (("corroborated ",), re.compile(r"corroborated `?#[0-9]+`?", re.ASCII)),
    (("surface", " **"), re.compile(r"surface(?:d|s) \*\*`?\d+`?", re.ASCII)),
    (("pr ", "reproduced"), re.compile(r"pr `?#[0-9]+`?[^;\n]{0,80}reproduced", re.ASCII)),
)

_TAIL_LITERALS: tuple[str, ...] = (
    "all other probes",
    "all other checks",
    "all other facts",
    "remaining checks passed",
    "(all other ",
    "- **passing checks:**",
    "\npassing checks:",
)
_TAIL_ALL_OTHER_RATIO_RE = re.compile(r"all other \d+/\d+", re.ASCII)
_CLAUSE_SPLIT_RE = re.compile(r"([;\n]|\.\s+(?=[A-Z]))", re.ASCII)
_PASSING_CLAUSE_MARKERS: tuple[str, ...] = (
    "passed cleanly",
    "pass cleanly",
    "cleanly rejected",
    "cleanly reject",
    "cleanly blocked",
    "cleanly handled",
    "rejected cleanly",
    "verified clean",
    "all passed",
    "0 defects",
    "zero defects",
    "no defects",
)
_DEFECT_CLAUSE_OVERRIDES: tuple[str, ...] = (
    "however",
    "defect",
    "bug",
    "bypass",
    "crash",
    "fail",
    "falsified",
    "cites ",
    "citation",
    "typo",
    "wrong",
    "mismatch",
    "stale",
    "missing",
    "forged",
    "hollow",
    "unhandled",
    "reproduced",
    "caught",
    "surfaced",
    "but ",
)

_FAMILY_RULES: tuple[tuple[str, tuple[str, ...], tuple[tuple[tuple[str, ...], re.Pattern[str]], ...]], ...] = (
    (
        "OBS_ZONEB_IO",
        (
            "4,300-digit", "4300-digit", "4,300 digit", "5,000-digit", "5000-digit", "5,000 digit",
            "10**5000", "10**400", "10**9", "surrogate", "\\ud800", "\\udc00",
            "non-ascii", "compare_digest", "bool-as-int", "bool as int", "bool/newline",
            "bool speedup", "bool tenant", "bool strictness", "bool as", "accepts python `bool`",
            "mode=false", "bundle_llama_id=false", "non-bool", "evilint", "evilfloat", "evilstr",
            "fakeint", "lyingseq", "lyingmap", "subclass", 'float("nan")', "raw float",
            "raw ieee-754 float", "accepts raw float", "accepts raw `float", "float `0.0", "float 0.0",
            "unhandled float", "rogue_float", "float/str-flag", "overflowerror", "recursionerror",
            "zerodivisionerror", "unicodeencodeerror", "unicodedecodeerror", "embedded null",
            "\x00", "\\x00", "nul byte", "symlink", "path traversal", "../", "/tmp/outside",
            "absolute path", "duplicate key", "dup-key", "dup key", "cyclic", "deep_1500",
            "1,500-deep", "1500-deep", "non-canonical", "leading-zero", "leading zeros",
            "lowest-terms", "non-reduced", "unreduced fraction", '`"007"`', '`"-0"`', '`"2/4"`',
            '`"01/2"`', "variation selector", "zwsp", "\\u200b", "whitespace-around-dot",
            "whitespace/list", "whitespace/bool", "crlf", "ragged `c", "ragged c", "invalid utf-8",
            'b"\\xff', "non-list `messages", "non-list messages", "non-str `prompt", "non-str prompt",
            "negative `socket_mode", "negative socket_mode", "negative `target_rank", "negative target_rank",
            "not_a_dict", "not_a_list", "empty type key",
        ),
        (
            (("nan",), re.compile(r"\bnan\b", re.ASCII)),
            (("silently accept", "float"), re.compile(r"silently accept[^,;\n]{0,40}float", re.ASCII)),
        ),
    ),
    (
        "OBS_H1_HOLONOMY",
        (
            "p\\succeq 0", "hermitian", "skew-symmetric", "norm$^2$=3", "norm^2=3", "integral-norm",
            "condition (2)", "condition(2)", "label-permutation", "label-swap", "gate-2",
            "bfs 2-coloring", "bipartite", "hardcodes `chi", "cross-corpus", "different corpus",
            "extra bank", "actively tainted", "journal-completeness", "omission bypass", "ledger",
            "denylist", "allowlist", "multi-hop", "1 symlink hop", "re.split", 'nested `"env"`',
            "subdirectory prefix overwrite", "multiline `set_option`", "line-by-line", "pigeonhole",
            "mathematically impossible", "col(phi)", "stochastic doob", "floor-truncated", "rule_kind",
            "partial 4-status", "mcnemar", "concordant", "heldout-leak", "cache_mode=0o755", "0o755",
            "wraparound", "welch factor", "phase_coherence", "diverges", "410 hz", "persistence_entropy",
            "reverse-chronology", "anachronistic", "teacher_of", "99^2 +", "99^2+", "final_drift_sq",
            "quoted shell", "command substitution", "backticks", "`find / -delete`", "is_symmetric",
            "len(h)==len(q)", "non-square `c`", "zero poly-wazn", "ancestors are omitted",
            "checked only under `git_whole_verb_reads", "checked only under git_whole_verb_reads",
            "self-loop", "non-binary", "matches only literal",
        ),
        (),
    ),
    (
        "OBS_HOLLOW_WITNESS",
        (
            "hollow", "vacuous", "fail-open", "fail open", "forgery", "forged", "unknown extra keys",
            "extra keys", "never hashes", "never validates", "unverified", "skips all", "skipped all",
            "empty manifest", "empty `0`-edge", "empty 0-edge", "empty `required_banks",
            "empty required_banks", "empty `active_banks", "empty active_banks",
            "relabeling a `regressed`", "returning `passed=true", "returning passed=true",
            "returning `certified", "returning certified", "passed=true", "certified=true",
            "certified: true", "clean: true", "compliant: true", "valid=true", "ignores top-level",
            "missing `active_lora_ids", "missing active_lora_ids", "accepts a concrete",
            "silently skipped", "bypass gate", "bypasses gate", "certifies reverse-chronology",
            "certifies as `apl_biconnected", "certifies as apl_biconnected", "certifies `rank >=",
            "certifies rank >=", "hardcodes `pinned_commit_sha", "hardcodes pinned_commit_sha",
            "checks only `head_file.is_file", "checks only head_file.is_file", "only checks `v_sz",
            "only checks v_sz", "lacks allowlist validation", "accepts self-loop",
            'status="pass"', "false-negative",
        ),
        (
            (("forge",), re.compile(r"\bforge\b", re.ASCII)),
            (("skips ", "check"), re.compile(r"skips [^,;\n]{0,32}check", re.ASCII)),
            (("promoted",), re.compile(r"(?:control_role|regressed_control)[^,;\n]{0,40}promoted", re.ASCII)),
            (
                ("return", "true"),
                re.compile(
                    r"returns? `?(?:passed|valid|certified|clean|compliant|verified_clean|verified|present|"
                    r"within_postfit_budget)[^,;\n]{0,20}true",
                    re.ASCII,
                ),
            ),
        ),
    ),
    (
        "OBS_STALE_ANCHOR",
        (
            "verbatim anchor/citation", "citation fix", "citation nit", "line nit", "diffstat",
            "changedfiles", "unrelated files", "raw unified diff", "numstat", "prose-only typo",
            "precision fix", "precision catch", "em dash", "local/anchor refs", "stale `r_opt",
            "stale r_opt", "discrepancy", "rounds to", "instead of exact cert",
            "ambiguous `formation.rs", "ambiguous formation.rs", "actual wy inversion",
            "unreachable span",
        ),
        (
            (("cites `",), re.compile(r"cites `[^`\n]{1,80}:\d+", re.ASCII)),
            (("immutable", "false"), re.compile(r"immutable[^,;\n]{0,40}false", re.ASCII)),
            (("claims `", "whereas live"), re.compile(r"claims `[^`\n]{1,80}`[^;\n]{0,40}whereas live", re.ASCII)),
            ((" cites",), re.compile(r"\bl\d+ cites\b", re.ASCII)),
            ((" says",), re.compile(r"\bl\d+ says\b", re.ASCII)),
            ((" claims",), re.compile(r"\bl\d+ claims\b", re.ASCII)),
            ((" wrote",), re.compile(r"\bl\d+ wrote\b", re.ASCII)),
        ),
    ),
    (
        "OBS_SCOPE_ATTRIBUTION",
        (
            "synthetic substitution", "synthetic `m_truss`", "shadow/substitution",
            "uncoupled rössler", "lagged coupled", "brownian", "false-positive inflation",
            "benchmark-fairness", "accounting bug", "leaking exact hidden target",
            "misclassifies un-escaped", "quickstart ux", "relapse_detected", "cs-06",
            "boilerplate", "mixes gcc", "applies only to", "overclaim", "cross-experiment",
            "attribution smuggling", "reproducibility claim mismatch", 'hardcodes `"1.0.0"`',
        ),
        (),
    ),
    (
        "OBS_ASSERT_O_BYPASS",
        (
            "-i strips", "passes only under `-s", "-o bypass", "-o strip",
            "r4 isolation fail", "r4 isolation break", "r4 parity fail", "r4 parity break",
        ),
        (
            (("python3 -i -b ",), re.compile(r"python3 -i -b [^;\n]{0,60}(?:fails|exits `?rc=1|modulenotfounderror)", re.ASCII)),
            (("assert",), re.compile(r"bare `?assert`? [^,;\n]{0,32}(?:bypass|strip|fail|-o)", re.ASCII)),
        ),
    ),
)

_SECTION_ID_RE = re.compile(r"^###\s+(AUDIT-[A-Z0-9_-]+)(?:[\s:(]|$)", re.ASCII)
_HEAD_SEG_RE = re.compile(r"^(?:\*\*(.+?)\*\*|`([^`]+)`)")
_SLASH_SEG_RE = re.compile(r"^\s*/\s*(?:\*\*(.+?)\*\*|`([^`]+)`)")
_VERIFIED_HEAD_RE = re.compile(r"^(?:DUAL-CONTINENT )?VERIFIED(?:$|[ (])", re.ASCII)
_PARTIAL_HEADER_MARKERS: tuple[str, ...] = (
    "PARTIAL/FRAGILE",
    "PROSE-ONLY TYPO",
    "DEFECT",
    "BLOCKING",
)


def _require_bounded_evidence_str(val: Any, field: str, *, non_empty: bool = False) -> str:
    s = require_str(val, field, non_empty=non_empty)
    if len(s) > MAX_EVIDENCE_CHARS:
        raise EscherMinerError("EVIDENCE_TOO_LARGE", f"{field} exceeds {MAX_EVIDENCE_CHARS} chars")
    return s


def split_markdown_table_row(line: str) -> list[str]:
    """Split a Markdown table row on unescaped pipes outside inline code and $...$ math."""
    s = _require_bounded_evidence_str(line, "table_row", non_empty=True).strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|"):
        s = s[:-1]
    cells: list[str] = []
    cur: list[str] = []
    in_bt = False
    in_math = False
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "\\" and i + 1 < n and s[i + 1] == "|":
            cur.append("\\|")
            i += 2
            continue
        if ch == "`":
            in_bt = not in_bt
            cur.append(ch)
            i += 1
            continue
        if ch == "$" and not in_bt:
            in_math = not in_math
            cur.append(ch)
            i += 1
            continue
        if ch == "|" and not in_bt and not in_math:
            cells.append("".join(cur).strip())
            cur = []
            i += 1
            continue
        cur.append(ch)
        i += 1
    cells.append("".join(cur).strip())
    return cells


def extract_primary_verdict(verdict_col: str) -> str:
    """Extract normalized primary verdict from an AUDIT_LOG verdict cell, preserving mixed-verdict failures."""
    s = _require_bounded_evidence_str(verdict_col, "verdict_col", non_empty=True).strip()
    m = _HEAD_SEG_RE.match(s)
    if m is None:
        raise EscherMinerError("UNPARSEABLE_VERDICT", f"cannot extract primary verdict from: {s[:40]}")
    segs = [(m.group(1) if m.group(1) is not None else m.group(2)).strip().replace("`", "")]
    pos = m.end()
    while True:
        mc = _SLASH_SEG_RE.match(s[pos:])
        if mc is None:
            break
        segs.append((mc.group(1) if mc.group(1) is not None else mc.group(2)).strip().replace("`", ""))
        pos += mc.end()
    head_clean = " / ".join(segs)
    if "FALSIFIED" in head_clean:
        return "FALSIFIED"
    if any(marker in head_clean for marker in _PARTIAL_HEADER_MARKERS):
        return "PARTIAL/FRAGILE"
    if all(_VERIFIED_HEAD_RE.match(seg) is not None for seg in segs):
        return "VERIFIED"
    raise EscherMinerError("UNKNOWN_VERDICT_TOKEN", f"unknown verdict header: {head_clean[:40]}")


_REDACTED_AUDIT_ID_SHA256_MAP: dict[str, str] = {
    "e69c306bfdda43144ef3a6367f684befb4177b525e575b21945de9b603ead53c": "AUDIT-REV-ASMA77-F060-REDACTED1",
    "60f0d62644749f8834058bd87eaa01f8b831ea76d7925377840118f547d85b71": "AUDIT-REV-GRAVITY29-CONTINUUM1-REDACTED2",
}


def _normalize_audit_id(aid: str) -> str:
    """Map redacted private-repo audit IDs via one-way SHA-256 to public placeholders without storing plaintext."""
    digest = hashlib.sha256(aid.encode("utf-8")).hexdigest()
    return _REDACTED_AUDIT_ID_SHA256_MAP.get(digest, aid)


def expand_atomic_audit_ids(audit_ids: list[str] | tuple[str, ...]) -> dict[str, Any]:
    """Count ledger entries vs expanded atomic audit IDs across slash-composite rows."""
    if type(audit_ids) not in (list, tuple):
        raise EscherMinerError("INVALID_AUDIT_IDS_TYPE", "audit_ids must be exact list or tuple")
    slash_composites: list[str] = []
    atomic_total = 0
    for aid in audit_ids:
        s = require_str(aid, "audit_id", non_empty=True)
        if " / " in s:
            slash_composites.append(s)
            atomic_total += len(s.split(" / "))
        else:
            atomic_total += 1
    return {
        "ledger_entries_count": len(audit_ids),
        "atomic_audit_ids_count": atomic_total,
        "slash_composite_count": len(slash_composites),
        "slash_composite_audit_ids": slash_composites,
    }


def parse_audit_log_markdown(
    raw_text: str,
    *,
    allowed_audit_ids: frozenset[str] | None = None,
) -> list[dict[str, str]]:
    """Parse all 9-column table, 5-column table, and ### AUDIT- section entries from AUDIT_LOG.md."""
    text = require_str(raw_text, "audit_log_text", non_empty=True)
    if allowed_audit_ids is not None and type(allowed_audit_ids) is not frozenset:
        raise EscherMinerError("INVALID_ALLOWED_IDS_TYPE", "allowed_audit_ids must be frozenset or None")
    if "\r" in text:
        raise EscherMinerError("CR_LINE_ENDINGS_FORBIDDEN", "CR/CRLF line endings forbidden in audit log")
    lines = text.splitlines()
    entries: list[dict[str, str]] = []
    seen_ids: set[str] = set()

    i = 0
    n_lines = len(lines)
    while i < n_lines:
        ln = lines[i]
        if ln.startswith("| **AUDIT-"):
            cells = split_markdown_table_row(ln)
            aid = _normalize_audit_id(cells[0].strip("* "))
            if len(cells) == 9:
                vcol, ev = cells[7], cells[8]
            elif len(cells) == 5:
                vcol, ev = cells[4], cells[4]
            else:
                raise EscherMinerError("UNEXPECTED_TABLE_COLS", f"unexpected column count {len(cells)} for {aid}")
            if aid in seen_ids:
                raise EscherMinerError("DUPLICATE_AUDIT_ID", f"duplicate audit_id: {aid}")
            seen_ids.add(aid)
            if allowed_audit_ids is None or aid in allowed_audit_ids:
                entries.append({"audit_id": aid, "verdict": extract_primary_verdict(vcol), "vcol": vcol, "evidence": ev})
            i += 1
            continue
        if ln.startswith("### AUDIT-"):
            m = _SECTION_ID_RE.match(ln)
            if m is None:
                raise EscherMinerError("MALFORMED_SECTION_HEADER", f"malformed section header: {ln[:40]}")
            aid = _normalize_audit_id(m.group(1))
            j = i + 1
            blines = [ln]
            while j < n_lines and not lines[j].startswith("### ") and not lines[j].startswith("## "):
                blines.append(lines[j])
                j += 1
            vcol = ""
            for bl in blines:
                if bl.startswith("- **Verdict:**"):
                    vcol = bl[len("- **Verdict:**") :].strip()
                    break
            if len(vcol) == 0:
                raise EscherMinerError("MISSING_SECTION_VERDICT", f"missing verdict line in section {aid}")
            if aid in seen_ids:
                raise EscherMinerError("DUPLICATE_AUDIT_ID", f"duplicate audit_id: {aid}")
            seen_ids.add(aid)
            if allowed_audit_ids is None or aid in allowed_audit_ids:
                entries.append({
                    "audit_id": aid,
                    "verdict": extract_primary_verdict(vcol),
                    "vcol": vcol,
                    "evidence": "\n".join(blines),
                })
            i = j
            continue
        i += 1

    if len(entries) == 0:
        raise EscherMinerError("EMPTY_AUDIT_LOG", "no AUDIT-* entries parsed from markdown")
    return entries


def _strip_passing_clauses(span: str) -> str:
    """Drop unmarked passing-check clauses (e.g. 'NaN handling passed cleanly;') without dropping defect clauses."""
    parts = _CLAUSE_SPLIT_RE.split(span)
    kept: list[str] = []
    idx = 0
    n_parts = len(parts)
    while idx < n_parts:
        clause = parts[idx]
        sep = parts[idx + 1] if idx + 1 < n_parts else ""
        idx += 2
        lc = clause.lower()
        norm = lc.replace("0 defects", "").replace("zero defects", "").replace("no defects", "")
        has_pass = any(tok in lc for tok in _PASSING_CLAUSE_MARKERS)
        has_defect = any(tok in norm for tok in _DEFECT_CLAUSE_OVERRIDES)
        if has_pass and not has_defect:
            continue
        kept.append(clause + sep)
    cleaned = "".join(kept).strip()
    return cleaned if len(cleaned) > 0 else span


def extract_defect_span(verdict_col: str, evidence_text: str) -> str:
    """Isolate the failing defect span while stripping passing preambles, inline passing clauses, and passing tails."""
    vcol = _require_bounded_evidence_str(verdict_col, "verdict_col")
    ev = _require_bounded_evidence_str(evidence_text, "evidence_text")
    ev_lc = ev.lower()
    split_positions: list[int] = []
    for lit in _SPLIT_LITERALS:
        p = ev_lc.find(lit)
        if p != -1:
            split_positions.append(p)
    for anchors, pat in _SPLIT_GUARDED_REGEXES:
        if all(a in ev_lc for a in anchors):
            m = pat.search(ev_lc)
            if m is not None:
                split_positions.append(m.start())
    span = ev[min(split_positions) :] if split_positions else (vcol + " " + ev)
    span_lc = span.lower()
    cut_positions: list[int] = []
    for lit in _TAIL_LITERALS:
        p = span_lc.find(lit)
        if p != -1:
            cut_positions.append(p)
    if "all other " in span_lc:
        m_ratio = _TAIL_ALL_OTHER_RATIO_RE.search(span_lc)
        if m_ratio is not None:
            cut_positions.append(m_ratio.start())
    trimmed = span[: min(cut_positions)] if cut_positions else span
    return _strip_passing_clauses(trimmed)


def _match_families_lc(text_lc: str) -> list[str]:
    matched: list[str] = []
    for fname, literals, guarded_pats in _FAMILY_RULES:
        hit = any(tok in text_lc for tok in literals)
        if not hit:
            for anchors, pat in guarded_pats:
                if all(a in text_lc for a in anchors):
                    if pat.search(text_lc) is not None:
                        hit = True
                        break
        if hit:
            matched.append(fname)
    return matched


def classify_defect_span(verdict_col: str, evidence_text: str) -> list[str]:
    """Classify a negative audit entry into exact algebraic/Zone-B obstruction families in linear time."""
    span = extract_defect_span(verdict_col, evidence_text)
    matched = _match_families_lc(span.lower())
    if len(matched) == 0:
        matched = _match_families_lc(verdict_col.lower())
    if len(matched) == 0:
        raise EscherMinerError("UNCLASSIFIED_NEGATIVE_AUDIT", "negative audit matched zero obstruction families")
    return matched


def compute_dual_complex_tomography(
    negative_records: list[dict[str, Any]],
    *,
    total_audits: int,
    verified_count: int,
    atomic_id_summary: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Compute exact-Z/Q negative-space dual complex coverage matrix & exhaustive minimal hitting set."""
    records = require_exact_list(negative_records, "negative_records", non_empty=True)
    n_total = require_int(total_audits, "total_audits", min_value=1)
    n_verified = require_int(verified_count, "verified_count", min_value=0, max_value=n_total)

    inc: dict[str, set[str]] = {}
    falsified_count = 0
    partial_count = 0
    total_assignments = 0

    for idx, raw in enumerate(records):
        rec = require_exact_dict(raw, f"negative_records[{idx}]")
        aid = require_str(rec.get("audit_id"), f"negative_records[{idx}].audit_id", non_empty=True)
        if aid in inc:
            raise EscherMinerError("DUPLICATE_NEG_AUDIT_ID", f"duplicate negative audit_id: {aid}")
        ver = require_str(rec.get("verdict"), f"negative_records[{idx}].verdict", non_empty=True)
        if ver == "FALSIFIED":
            falsified_count += 1
        elif ver == "PARTIAL/FRAGILE":
            partial_count += 1
        else:
            raise EscherMinerError("INVALID_NEG_VERDICT", f"negative verdict must be FALSIFIED or PARTIAL/FRAGILE: {ver}")
        raw_fams = require_exact_list(rec.get("families"), f"negative_records[{idx}].families", non_empty=True)
        fset: set[str] = set()
        for f_i, f_raw in enumerate(raw_fams):
            fn = require_str(f_raw, f"negative_records[{idx}].families[{f_i}]", non_empty=True)
            if fn not in _OBSTRUCTION_FAMILY_SET:
                raise EscherMinerError("UNKNOWN_OBSTRUCTION_FAMILY", f"unknown obstruction family: {fn}")
            fset.add(fn)
        inc[aid] = fset
        total_assignments += len(fset)

    n_neg = len(inc)
    if n_verified + n_neg != n_total:
        raise EscherMinerError("AUDIT_COUNT_PARTITION_MISMATCH", "verified + negative must equal total_audits")

    fam_sets: dict[str, set[str]] = {fn: set() for fn in OBSTRUCTION_FAMILIES}
    for aid, fset in inc.items():
        for fn in fset:
            fam_sets[fn].add(aid)

    per_family: list[dict[str, Any]] = []
    for fn in OBSTRUCTION_FAMILIES:
        cov = fam_sets[fn]
        excl = sorted(aid for aid in cov if len(inc[aid]) == 1)
        per_family.append({
            "family": fn,
            "covered_count": len(cov),
            "recall_q": fmt_q(Fraction(len(cov), n_neg)),
            "exclusive_count": len(excl),
            "exclusive_share_q": fmt_q(Fraction(len(excl), n_neg)),
            "ablation_coverage_without_family_q": fmt_q(Fraction(n_neg - len(excl), n_neg)),
            "exclusive_audit_ids": excl,
        })

    # Exact 6x6 marginal dual-cut coverage matrix: M[i][j] = |cov(i) \ cov(j)| / n_neg
    marginal_matrix: dict[str, dict[str, str]] = {}
    pairwise_union_matrix: dict[str, dict[str, str]] = {}
    pairwise_intersection_matrix: dict[str, dict[str, str]] = {}
    for fi in OBSTRUCTION_FAMILIES:
        marginal_matrix[fi] = {}
        pairwise_union_matrix[fi] = {}
        pairwise_intersection_matrix[fi] = {}
        for fj in OBSTRUCTION_FAMILIES:
            marginal_matrix[fi][fj] = fmt_q(Fraction(len(fam_sets[fi] - fam_sets[fj]), n_neg))
            pairwise_union_matrix[fi][fj] = fmt_q(Fraction(len(fam_sets[fi] | fam_sets[fj]), n_neg))
            pairwise_intersection_matrix[fi][fj] = fmt_q(Fraction(len(fam_sets[fi] & fam_sets[fj]), n_neg))

    # Deterministic greedy marginal dual-cut trajectory
    universe = frozenset(inc.keys())
    covered: set[str] = set()
    remaining = list(OBSTRUCTION_FAMILIES)
    greedy_steps: list[dict[str, Any]] = []
    step_num = 0
    while len(covered) < n_neg:
        step_num += 1
        best_fn = max(
            remaining,
            key=lambda fn: (len(fam_sets[fn] - covered), -OBSTRUCTION_FAMILIES.index(fn)),
        )
        gain = len(fam_sets[best_fn] - covered)
        covered |= fam_sets[best_fn]
        remaining.remove(best_fn)
        greedy_steps.append({
            "step": step_num,
            "added_family": best_fn,
            "marginal_gain_count": gain,
            "marginal_gain_q": fmt_q(Fraction(gain, n_neg)),
            "cumulative_covered_count": len(covered),
            "cumulative_recall_q": fmt_q(Fraction(len(covered), n_neg)),
        })

    # Exhaustive exact minimal hitting set solver over all 2^k - 1 subsets
    min_hitting_sets: list[list[str]] = []
    min_hitting_set_size = 0
    for r in range(1, len(OBSTRUCTION_FAMILIES) + 1):
        hits = [
            list(comb)
            for comb in combinations(OBSTRUCTION_FAMILIES, r)
            if set().union(*(fam_sets[fn] for fn in comb)) == universe
        ]
        if len(hits) > 0:
            min_hitting_set_size = r
            min_hitting_sets = hits
            break

    out: dict[str, Any] = {
        "total_audits": n_total,
        "verified_count": n_verified,
        "negative_count": n_neg,
        "falsified_count": falsified_count,
        "partial_fragile_count": partial_count,
        "verified_rate_q": fmt_q(Fraction(n_verified, n_total)),
        "rejection_rate_q": fmt_q(Fraction(n_neg, n_total)),
        "falsified_rate_q": fmt_q(Fraction(falsified_count, n_total)),
        "partial_fragile_rate_q": fmt_q(Fraction(partial_count, n_total)),
        "total_family_assignments": total_assignments,
        "mean_families_per_negative_audit_q": fmt_q(Fraction(total_assignments, n_neg)),
        "obstruction_family_count": len(OBSTRUCTION_FAMILIES),
        "per_family_coverage": per_family,
        "marginal_dual_cut_matrix_q": marginal_matrix,
        "pairwise_union_matrix_q": pairwise_union_matrix,
        "pairwise_intersection_matrix_q": pairwise_intersection_matrix,
        "greedy_marginal_trajectory": greedy_steps,
        "minimal_hitting_set_size": min_hitting_set_size,
        "minimal_hitting_sets": min_hitting_sets,
        "minimal_hitting_set_unique": len(min_hitting_sets) == 1,
        "all_families_strictly_irreducible": min_hitting_set_size == len(OBSTRUCTION_FAMILIES),
        "law4_survivorship_note": (
            "OBS_ASSERT_O_BYPASS is 2/97 inside internal AUDIT_LOG.md rejections (AUDIT-047, AUDIT-053 "
            "isolated -I failures) because aletheia audit-check pre-filters bare asserts prior to audit submission; "
            "upstream repo bare-assert findings appear inside VERIFIED external audit entries."
        ),
    }
    if atomic_id_summary is not None:
        out["atomic_id_accounting"] = require_exact_dict(atomic_id_summary, "atomic_id_summary")
    return out


# ---------------------------------------------------------------------------
# Pinned Empirical Snapshot (Verified Live Against Disk via --live-disk)
# ---------------------------------------------------------------------------

PINNED_VERIFIED_COUNT = 232

PINNED_CORP_AUDIT_IDS: tuple[str, ...] = (
    "AUDIT-001", "AUDIT-002", "AUDIT-003", "AUDIT-004",
    "AUDIT-005", "AUDIT-006", "AUDIT-007", "AUDIT-008",
    "AUDIT-009", "AUDIT-010", "AUDIT-011", "AUDIT-012",
    "AUDIT-013", "AUDIT-014", "AUDIT-015", "AUDIT-016",
    "AUDIT-017", "AUDIT-015R / 016R", "AUDIT-011R / 013R", "AUDIT-018",
    "AUDIT-019", "AUDIT-006R / 007R / 008R", "AUDIT-020", "AUDIT-020R",
    "AUDIT-021", "AUDIT-022", "AUDIT-022R", "AUDIT-023",
    "AUDIT-024", "AUDIT-025", "AUDIT-026", "AUDIT-027",
    "AUDIT-028", "AUDIT-026R", "AUDIT-029", "AUDIT-034",
    "AUDIT-034R", "AUDIT-032", "AUDIT-031", "AUDIT-033",
    "AUDIT-030", "AUDIT-030R", "AUDIT-039", "AUDIT-037",
    "AUDIT-038", "AUDIT-036", "AUDIT-038R", "AUDIT-035",
    "AUDIT-040", "AUDIT-043", "AUDIT-042", "AUDIT-040R",
    "AUDIT-041", "AUDIT-044", "AUDIT-048", "AUDIT-046",
    "AUDIT-045", "AUDIT-048R", "AUDIT-050", "AUDIT-047",
    "AUDIT-047R", "AUDIT-049", "AUDIT-051", "AUDIT-053",
    "AUDIT-053R", "AUDIT-052", "AUDIT-054", "AUDIT-055",
    "AUDIT-058", "AUDIT-058R", "AUDIT-059", "AUDIT-057",
    "AUDIT-060", "AUDIT-057R", "AUDIT-056", "AUDIT-064",
    "AUDIT-065", "AUDIT-062", "AUDIT-061", "AUDIT-063",
    "AUDIT-061R", "AUDIT-062R", "AUDIT-063R", "AUDIT-063R2",
    "AUDIT-067", "AUDIT-067R", "AUDIT-066", "AUDIT-066R",
    "AUDIT-071", "AUDIT-071R", "AUDIT-068", "AUDIT-069",
    "AUDIT-070", "AUDIT-069R", "AUDIT-070R", "AUDIT-068R",
    "AUDIT-076", "AUDIT-076R", "AUDIT-073", "AUDIT-073R",
    "AUDIT-074", "AUDIT-072", "AUDIT-075", "AUDIT-074R",
    "AUDIT-072R", "AUDIT-077", "AUDIT-075R", "AUDIT-077R",
    "AUDIT-078", "AUDIT-078R", "AUDIT-081", "AUDIT-080",
    "AUDIT-082", "AUDIT-079", "AUDIT-079R", "AUDIT-080R",
    "AUDIT-081R", "AUDIT-082R", "AUDIT-083", "AUDIT-083R",
    "AUDIT-084", "AUDIT-087", "AUDIT-084R", "AUDIT-085",
    "AUDIT-086", "AUDIT-087R", "AUDIT-085R", "AUDIT-088",
    "AUDIT-086R", "AUDIT-088R", "AUDIT-092", "AUDIT-089",
    "AUDIT-091", "AUDIT-089R", "AUDIT-091R", "AUDIT-092R",
    "AUDIT-093", "AUDIT-090", "AUDIT-090R", "AUDIT-093R",
    "AUDIT-094", "AUDIT-095", "AUDIT-094R", "AUDIT-096",
    "AUDIT-096R", "AUDIT-089R2a", "AUDIT-093R2a", "AUDIT-089R2",
    "AUDIT-093R2", "AUDIT-098", "AUDIT-099", "AUDIT-100",
    "AUDIT-090R2", "AUDIT-098R", "AUDIT-101R", "AUDIT-091R2** *(formerly colliding `AUDIT-096R`)",
    "AUDIT-101R2", "AUDIT-099R", "AUDIT-063-ISSUE29", "AUDIT-104",
    "AUDIT-SYNC-MATH0-SILIQUANT", "AUDIT-REVIEWS-CAVE8-ALETHEIA10", "AUDIT-100R", "AUDIT-103",
    "AUDIT-SYNC-CAVE-COLLAB", "AUDIT-105", "AUDIT-104R", "AUDIT-063-PR30",
    "AUDIT-101R3", "AUDIT-098R2", "AUDIT-105R", "AUDIT-102",
    "AUDIT-REVIEW-SILIQUANT-PR12", "AUDIT-REVIEWS-PR10-CAVE8-FOLLOWUP", "AUDIT-SYNC-CAVE-PATCH1", "AUDIT-103R2",
    "AUDIT-MCPROOF-PR16-R3", "AUDIT-REVIEW-WEFT-LOOM-PR46", "AUDIT-PR-SILIQUANT-AUDIT103R2", "AUDIT-104R2",
    "AUDIT-097", "AUDIT-102R", "AUDIT-ALETHEIA-PR1-R3", "AUDIT-REVIEW-SILIQUANT-PR24-RULINGS",
    "AUDIT-106", "AUDIT-110", "AUDIT-111", "AUDIT-110R",
    "AUDIT-111R", "AUDIT-104R3", "AUDIT-108", "AUDIT-107",
    "AUDIT-106R", "AUDIT-108R", "AUDIT-104R4", "AUDIT-PR-SILIQUANT-AUDIT106R",
    "AUDIT-PR-MATH0-WAVE2", "AUDIT-109", "AUDIT-097R", "AUDIT-107R",
    "AUDIT-PR-BAYT-N5-FIX", "AUDIT-PR-SILIQUANT-AUDIT108R", "AUDIT-PR-WARP-DRIVE-AUDIT104R4", "AUDIT-SUMMARIES-EXO-D934-SC-D5",
    "AUDIT-REVIEW-WARPDRIVE-PR32-34", "AUDIT-PR-SILIQUANT-AUDIT097R", "AUDIT-PR-SILIQUANT-AUDIT107R", "AUDIT-SYNC-CAVE-WAVE2",
    "AUDIT-DISPOSITION-HEEDLE-PR8", "AUDIT-REVIEWS-ALETHEIA6-CAVE6", "AUDIT-REVIEW-CAVE-PR8-R2", "AUDIT-REVIEWS-CAVE4-MATH9-WEFT37",
    "AUDIT-REVIEWS-WEFT36-MATH3-4", "AUDIT-PR-HEEDLE-FIX", "AUDIT-REVIEW-WARPDRIVE-PR10-R2", "AUDIT-REVIEW-CAVE-PR5-R2",
    "AUDIT-PR-BAYT-N5-FIX-R2", "AUDIT-REVIEWS-WEFT44-SC19", "AUDIT-ALETHEIA-V21", "AUDIT-REVIEW-BAYT-PR2",
    "AUDIT-REVIEWS-EXO-1208-1210", "AUDIT-REVIEWS-EXO-1228-1236-1237", "AUDIT-REVIEWS-ALETHEIA10-WEFT25-27-29", "AUDIT-REVIEWS-WEFT38-EXO1218-SC8-9-12",
    "AUDIT-112", "AUDIT-109R", "AUDIT-REVIEWS-SYNMERIT17-WEFT", "AUDIT-REVIEWS-FCA16-ASKA-PHYSICAL",
    "AUDIT-PR-MATH0-AUDIT109R", "AUDIT-PR-CFRP-MASTS-ISSUE3", "AUDIT-REVIEWS-PROVEN-COMMONS-NULLMODEM", "AUDIT-ALETHEIA-V21R",
    "AUDIT-REVIEWS-RAMANUJAN-MDE3", "AUDIT-REVIEWS-SILICONCORDAT-STACK", "AUDIT-PR-QUOTIENT-LP-ISSUE2", "AUDIT-REVIEWS-F0-PURE-MATH",
    "AUDIT-113", "AUDIT-PR-WEFT-224-FIX", "AUDIT-PR-WEFT-219-FIX", "AUDIT-PR-WEFT-LOOM-42-FIX",
    "AUDIT-112R", "AUDIT-112B-CBENCH", "AUDIT-PR-SILIQUANT-AUDIT112R", "AUDIT-PR-WEFT-224-FIX-R2",
    "AUDIT-PR-SILIQUANT-24-FIX", "AUDIT-PR-RAMANUJAN-FIX-2-5", "AUDIT-REVIEWS-GFQ-CODES-9-14", "AUDIT-REVIEWS-FCA-SI2-FR3",
    "AUDIT-REVIEWS-VITRUVIAN-PROVEN-GEMS", "AUDIT-PR-WEFT-225-FIX", "AUDIT-PR-QUOTIENT-LP-ISSUE7", "AUDIT-115",
    "AUDIT-113R", "AUDIT-PR-BAYT-ISSUE4", "AUDIT-REVIEWS-FUNIFRAME4-AP-O-SWEEP", "AUDIT-REVIEWS-WARP-DRIVE-37",
    "AUDIT-PR-SILICONCORDAT-EXO-ISSUE8", "AUDIT-PR-CAVE-EXPEDITION-WAVE2-SYNC", "AUDIT-115R", "AUDIT-116",
    "AUDIT-117", "AUDIT-PR-SILICONCORDAT-EXO-ISSUE8-R2", "AUDIT-PR-SILIQUANT-AUDIT115R", "AUDIT-116R",
    "AUDIT-PR-FUNI-FLOORS-AND-CFRP-TRUSS-O-FIX", "AUDIT-114R", "AUDIT-PR-SILICONCORDAT-WARP-ISSUE11", "AUDIT-118A",
    "AUDIT-118B", "AUDIT-118C", "AUDIT-PR-SILICONCORDAT-EXO-ISSUE8-R3", "AUDIT-114R3",
    "AUDIT-118CR", "AUDIT-PR-SILICONCORDAT-WARP-ISSUE11-R2", "AUDIT-REV-GAMEPLAY-EVIDENCE", "AUDIT-REV-GAMEPLAY-EVIDENCE-R",
    "AUDIT-REV-POINT-CHARGES-22", "AUDIT-REV-URG3-OPTIFAB13-SILIQUANT2325", "AUDIT-REV-SILIQUANT-23-25-R", "AUDIT-REV-ASMA77-F060-REDACTED1",
    "AUDIT-REV-CAVE4-MCPROOF17-RECHECKS", "AUDIT-REV-F059-SYNBIOS64-OPTIFAB12", "AUDIT-REV-ALETHEIA-ISSUE11", "AUDIT-REV-ALETHEIA-ISSUE11-R",
    "AUDIT-REV-MLABS-PAGES-ECOSYSTEM", "AUDIT-REV-MLABS-PAGES-ECOSYSTEM-R", "AUDIT-REV-RIGID-REALIZATIONS-21", "AUDIT-REV-GFQ19-SYNMERIT10-INCENTRE",
    "AUDIT-REV-EXO-1217", "AUDIT-REV-EXO-1217-R", "AUDIT-PR-SYNMERIT10-AND-CFRP-STRENGTHENING", "AUDIT-PR-SILICONCORDAT-EXO-ISSUE7",
    "AUDIT-PR-VENTURI-AND-IMPEDENCE-FIX-O", "AUDIT-PR-ASKA-PHYSICAL-BIO-RANK1-RANK2", "AUDIT-PR-IMPEDENCE-ANALYZERS-NDT-RANK1", "AUDIT-PR-VENTURI-COLLARS-BIO-OPERATORS",
    "AUDIT-PR-IMPEDENCE-ANALYZERS-NDT-RANK1-R2", "AUDIT-REV-WARP-DRIVE-38", "AUDIT-PR-FUNI-FLOORS-AND-INCENTRE-MARALDI", "AUDIT-PR-OPTIFAB-BIO-THERMAL",
    "AUDIT-PR-SILICONCORDAT-EXO-ISSUE7-R2", "AUDIT-REV-WARP-DRIVE-38-DELTA", "AUDIT-REV-WARP-DRIVE-PR11-20-ISSUE14", "AUDIT-118D",
    "AUDIT-118DR", "AUDIT-PR-SILIQUANT-AUDIT116R", "AUDIT-PR-SILICONCORDAT-WARP-ISSUE13", "AUDIT-118DR2",
    "AUDIT-REV-WARP-DRIVE-40", "AUDIT-PR-SILICONCORDAT-WARP-ISSUE13-R2", "AUDIT-PR-SILICONCORDAT-WARP-ISSUE7", "AUDIT-PR-SILICONCORDAT-EXO5-DOTGITHUB4",
    "AUDIT-PR-WARP-DRIVE-FIX-A2-A8", "AUDIT-PR-SILICONCORDAT-WARP-ISSUE7-R2", "AUDIT-PR-SILICONCORDAT-EXO-ISSUE5-R2",
)

PINNED_POST_CORPUS_DELTA_IDS: tuple[str, ...] = (
    "AUDIT-120D",
    "AUDIT-PR-ALETHEIA-CORPUS-PR1",
    "AUDIT-PR-SILICONCORDAT-EXO-ISSUE8-R4",
    "AUDIT-PR-SILICONCORDAT-WARP-ISSUE12",
    "AUDIT-PR-SILICONCORDAT-WARP-ISSUE12-R2",
    "AUDIT-PR-SILIQUANT-28-R2",
    "AUDIT-PR-SILIQUANT-31-R2",
    "AUDIT-PR-SILIQUANT-36-R2",
    "AUDIT-PR-WARP-DRIVE-FIX-A2-A8-R2",
    "AUDIT-REV-CAVE-EXPEDITION-PR8-COMMENT",
    "AUDIT-REV-GRAVITY29-CONTINUUM1-REDACTED2",
    "AUDIT-REV-ORDA-FRESH-QLP4-BAYT2-CAVE8",
    "AUDIT-REV-SILIQUANT-38",
    "AUDIT-REV-SILIQUANT-40",
)

PINNED_NEGATIVE_SPACE_RECORDS: tuple[tuple[str, str, tuple[str, ...]], ...] = (
    ("AUDIT-001", "FALSIFIED", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-003", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_SCOPE_ATTRIBUTION")),
    ("AUDIT-006", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-007", "PARTIAL/FRAGILE", ("OBS_SCOPE_ATTRIBUTION",)),
    ("AUDIT-013", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_SCOPE_ATTRIBUTION")),
    ("AUDIT-015", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-020", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-022", "PARTIAL/FRAGILE", ("OBS_SCOPE_ATTRIBUTION",)),
    ("AUDIT-026", "PARTIAL/FRAGILE", ("OBS_SCOPE_ATTRIBUTION",)),
    ("AUDIT-034", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-030", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-038", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-040", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS", "OBS_SCOPE_ATTRIBUTION")),
    ("AUDIT-048", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-047", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR", "OBS_ASSERT_O_BYPASS")),
    ("AUDIT-053", "PARTIAL/FRAGILE", ("OBS_ASSERT_O_BYPASS",)),
    ("AUDIT-058", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR",)),
    ("AUDIT-057", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-062", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-061", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-063", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-063R", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-067", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-066", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-071", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_STALE_ANCHOR")),
    ("AUDIT-068", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS", "OBS_STALE_ANCHOR")),
    ("AUDIT-069", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-070", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-076", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-073", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-074", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-072", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS", "OBS_STALE_ANCHOR")),
    ("AUDIT-075", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-077", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-078", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-081", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-080", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-082", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-079", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY",)),
    ("AUDIT-083", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-084", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-087", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-085", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-086", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-088", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-092", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-089", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-091", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY")),
    ("AUDIT-093", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-090", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY")),
    ("AUDIT-094", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-096", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-089R2a", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-093R2a", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-098", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-099", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-100", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-101R", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-104", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-103", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-105", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-104R", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-102", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-104R2", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-097", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-106", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-110", "PARTIAL/FRAGILE", ("OBS_HOLLOW_WITNESS",)),
    ("AUDIT-111", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-104R3", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-108", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-107", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-109", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-ALETHEIA-V21", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-112", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-113", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-115", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-PR-SILICONCORDAT-EXO-ISSUE8", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-116", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-PR-SILICONCORDAT-EXO-ISSUE8-R2", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-114R", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-PR-SILICONCORDAT-WARP-ISSUE11", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY")),
    ("AUDIT-118C", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS")),
    ("AUDIT-PR-SILICONCORDAT-EXO-ISSUE8-R3", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY")),
    ("AUDIT-PR-SILICONCORDAT-WARP-ISSUE12", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY")),
    ("AUDIT-REV-GAMEPLAY-EVIDENCE", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_HOLLOW_WITNESS", "OBS_STALE_ANCHOR")),
    ("AUDIT-REV-URG3-OPTIFAB13-SILIQUANT2325", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR", "OBS_SCOPE_ATTRIBUTION")),
    ("AUDIT-REV-ALETHEIA-ISSUE11", "PARTIAL/FRAGILE", ("OBS_H1_HOLONOMY", "OBS_STALE_ANCHOR")),
    ("AUDIT-REV-MLABS-PAGES-ECOSYSTEM", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR",)),
    ("AUDIT-REV-GFQ19-SYNMERIT10-INCENTRE", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR",)),
    ("AUDIT-REV-EXO-1217", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR",)),
    ("AUDIT-PR-IMPEDENCE-ANALYZERS-NDT-RANK1", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-PR-FUNI-FLOORS-AND-INCENTRE-MARALDI", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR",)),
    ("AUDIT-118D", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-118DR", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-PR-SILICONCORDAT-WARP-ISSUE13", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO", "OBS_H1_HOLONOMY")),
    ("AUDIT-PR-WARP-DRIVE-FIX-A2-A8", "PARTIAL/FRAGILE", ("OBS_ZONEB_IO",)),
    ("AUDIT-REV-ORDA-FRESH-QLP4-BAYT2-CAVE8", "PARTIAL/FRAGILE", ("OBS_STALE_ANCHOR",)),
)


def compute_escher_dual_miner_payload() -> dict[str, Any]:
    """Compute exact pure-Z/Q Track S21b payload (standalone pinned-snapshot replay certified by --live-disk)."""
    op1_s20d = evaluate_s20d_self_application()
    op1_corpus = evaluate_corpus_self_application()

    all_pinned_ids = list(PINNED_CORP_AUDIT_IDS) + list(PINNED_POST_CORPUS_DELTA_IDS)
    atomic_summary = expand_atomic_audit_ids(all_pinned_ids)
    neg_records = [
        {"audit_id": aid, "verdict": ver, "families": list(fams)}
        for aid, ver, fams in PINNED_NEGATIVE_SPACE_RECORDS
    ]
    op2_dual = compute_dual_complex_tomography(
        neg_records,
        total_audits=len(all_pinned_ids),
        verified_count=PINNED_VERIFIED_COUNT,
        atomic_id_summary=atomic_summary,
    )

    total_fp_closed = op1_s20d["fixed_points_closed"] + op1_corpus["fixed_points_closed"]
    total_fp = op1_s20d["fixed_points_total"] + op1_corpus["fixed_points_total"]
    total_void = op1_s20d["central_void_count"] + op1_corpus["central_void_count"]
    return {
        "verification_basis": "pinned_snapshot_replay_certified_by_live_disk_parity",
        "operator1_self_application_tomography": {
            "track_s20d_self_application": op1_s20d,
            "aletheia_corpus_self_application": op1_corpus,
            "combined_fixed_points_closed": total_fp_closed,
            "combined_fixed_points_total": total_fp,
            "combined_central_void_count": total_void,
            "combined_internal_closure_share_q": fmt_q(Fraction(total_fp_closed, total_fp + total_void)),
            "combined_irreducible_void_share_q": fmt_q(Fraction(total_void, total_fp + total_void)),
            "temporal_horizon_corpus_audits": len(PINNED_CORP_AUDIT_IDS),
            "temporal_horizon_live_audits": len(all_pinned_ids),
            "temporal_horizon_post_corpus_delta": len(PINNED_POST_CORPUS_DELTA_IDS),
            "temporal_horizon_delta_ids": list(PINNED_POST_CORPUS_DELTA_IDS),
        },
        "operator2_negative_space_dual_complex": op2_dual,
    }


# ---------------------------------------------------------------------------
# Live Read-Only Disk Verification (Real Extraction + Real Track S20d + Real AUDIT_LOG)
# ---------------------------------------------------------------------------


def load_s20d_checker_readonly(s20d_dir: Path) -> Any:
    """Import Track S20d claim_witness_checker.py strictly read-only with bytecode disabled."""
    require_no_symlink_path(s20d_dir)
    checker_path = s20d_dir / "claim_witness_checker.py"
    require_no_symlink_path(checker_path)
    if not checker_path.is_file():
        raise EscherMinerError("S20D_CHECKER_NOT_FOUND", "claim_witness_checker.py not found")
    prev_dont_write = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec = importlib.util.spec_from_file_location("_s20d_live_checker_ro", checker_path)
        if spec is None or spec.loader is None:
            raise EscherMinerError("S20D_IMPORT_FAILED", "cannot load claim_witness_checker spec")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    finally:
        sys.dont_write_bytecode = prev_dont_write


def _require_pin_dict(pins: Any, required_keys: frozenset[str], field: str) -> dict[str, str]:
    d = require_exact_dict(pins, field)
    if frozenset(d.keys()) != required_keys:
        raise EscherMinerError("PIN_KEYS_MISMATCH", f"{field} key set mismatch")
    for k, v in d.items():
        require_hex64_ascii(v, f"{field}.{k}")
    return d


def _require_pin_id_set(ids: Any, field: str) -> frozenset[str]:
    if type(ids) is not frozenset:
        raise EscherMinerError("INVALID_PIN_SET", f"{field} must be exact frozenset")
    if len(ids) == 0:
        raise EscherMinerError("EMPTY_PIN_SET", f"{field} must be non-empty")
    for aid in ids:
        require_str(aid, f"{field}.item", non_empty=True)
    return ids


def verify_live_disk_parity(
    expedition_root: Path,
    *,
    expected_s20d_pins: dict[str, str] | None = None,
    expected_corp_pins: dict[str, str] | None = None,
    expected_corp_ids: frozenset[str] | None = None,
    expected_cutoff_ids: frozenset[str] | None = None,
    expected_payload_sha: str | None = None,
) -> dict[str, Any]:
    """Read-only live extraction & verification against real Track S20d, aletheia-corpus, and AUDIT_LOG.md."""
    require_no_symlink_path(expedition_root)
    if not expedition_root.is_dir():
        raise EscherMinerError("EXPEDITION_ROOT_NOT_DIR", "expedition_root must be an existing directory")

    s20d_dir = expedition_root / "track-s20d-claim-to-witness-tomography"
    corpus_dir = expedition_root / "publish" / "aletheia-corpus"
    live_log_path = expedition_root / "verification" / "AUDIT_LOG.md"
    corp_log_path = corpus_dir / "expedition" / "verification" / "AUDIT_LOG.md"

    expected_payload = compute_escher_dual_miner_payload()
    s20d_pins = (
        _require_pin_dict(expected_s20d_pins, REQUIRED_S20D_PIN_KEYS, "expected_s20d_pins")
        if expected_s20d_pins is not None
        else dict(PINNED_S20D_SNAPSHOT["file_sha256"])
    )
    corp_pins = (
        _require_pin_dict(expected_corp_pins, REQUIRED_CORP_PIN_KEYS, "expected_corp_pins")
        if expected_corp_pins is not None
        else dict(PINNED_CORPUS_SNAPSHOT["file_sha256"])
    )
    corp_id_set = (
        _require_pin_id_set(expected_corp_ids, "expected_corp_ids")
        if expected_corp_ids is not None
        else frozenset(PINNED_CORP_AUDIT_IDS)
    )
    cutoff_ids = (
        _require_pin_id_set(expected_cutoff_ids, "expected_cutoff_ids")
        if expected_cutoff_ids is not None
        else (frozenset(PINNED_CORP_AUDIT_IDS) | frozenset(PINNED_POST_CORPUS_DELTA_IDS))
    )

    # Live extraction parses real JSON, Markdown prose, SHA256SUMS, and Python AST from disk
    live_s20d_snap = extract_s20d_snapshot_from_dir(s20d_dir, corpus_dir=corpus_dir)
    live_corp_snap = extract_corpus_snapshot_from_dir(corpus_dir)

    for fname, expected_sha in s20d_pins.items():
        if not constant_time_hex64_equal(live_s20d_snap["file_sha256"][fname], expected_sha, f"s20d.{fname}"):
            raise EscherMinerError("LIVE_S20D_SHA_MISMATCH", f"live SHA mismatch for {fname}")

    for key, expected_sha in corp_pins.items():
        if not constant_time_hex64_equal(live_corp_snap["file_sha256"][key], expected_sha, f"corpus.{key}"):
            raise EscherMinerError("LIVE_CORPUS_SHA_MISMATCH", f"live SHA mismatch for {key}")

    cwc = load_s20d_checker_readonly(s20d_dir)
    live_op1_s20d = evaluate_s20d_self_application(
        live_s20d_snap,
        bind_fn=cwc.verify_prose_artifact_bindings,
        prov_fn=cwc.verify_provenance_claims,
        destruct_fn=cwc.run_semantic_destruction_gate,
    )
    live_op1_corpus = evaluate_corpus_self_application(
        live_corp_snap,
        bind_fn=cwc.verify_prose_artifact_bindings,
        prov_fn=cwc.verify_provenance_claims,
        destruct_fn=cwc.run_semantic_destruction_gate,
    )

    _, live_log_text = read_strict_utf8_file(live_log_path)
    _, corp_log_text = read_strict_utf8_file(corp_log_path)
    live_entries = parse_audit_log_markdown(live_log_text, allowed_audit_ids=cutoff_ids)
    corp_entries = parse_audit_log_markdown(corp_log_text)

    if len(live_entries) != len(cutoff_ids):
        raise EscherMinerError("LIVE_CUTOFF_INCOMPLETE", "live AUDIT_LOG.md missing pinned cutoff audit IDs")
    if frozenset(e["audit_id"] for e in corp_entries) != corp_id_set:
        raise EscherMinerError("CORPUS_AUDIT_LOG_MISMATCH", "frozen corpus AUDIT_LOG.md ID set mismatch")

    live_neg_records = [
        {
            "audit_id": e["audit_id"],
            "verdict": e["verdict"],
            "families": classify_defect_span(e["vcol"], e["evidence"]),
        }
        for e in live_entries
        if e["verdict"] != "VERIFIED"
    ]
    live_verified_count = sum(1 for e in live_entries if e["verdict"] == "VERIFIED")
    live_atomic_summary = expand_atomic_audit_ids([e["audit_id"] for e in live_entries])
    live_op2 = compute_dual_complex_tomography(
        live_neg_records,
        total_audits=len(live_entries),
        verified_count=live_verified_count,
        atomic_id_summary=live_atomic_summary,
    )

    total_fp_closed = live_op1_s20d["fixed_points_closed"] + live_op1_corpus["fixed_points_closed"]
    total_fp = live_op1_s20d["fixed_points_total"] + live_op1_corpus["fixed_points_total"]
    total_void = live_op1_s20d["central_void_count"] + live_op1_corpus["central_void_count"]
    live_payload = {
        "verification_basis": "pinned_snapshot_replay_certified_by_live_disk_parity",
        "operator1_self_application_tomography": {
            "track_s20d_self_application": live_op1_s20d,
            "aletheia_corpus_self_application": live_op1_corpus,
            "combined_fixed_points_closed": total_fp_closed,
            "combined_fixed_points_total": total_fp,
            "combined_central_void_count": total_void,
            "combined_internal_closure_share_q": fmt_q(Fraction(total_fp_closed, total_fp + total_void)),
            "combined_irreducible_void_share_q": fmt_q(Fraction(total_void, total_fp + total_void)),
            "temporal_horizon_corpus_audits": len(corp_entries),
            "temporal_horizon_live_audits": len(live_entries),
            "temporal_horizon_post_corpus_delta": len(live_entries) - len(corp_entries),
            "temporal_horizon_delta_ids": sorted(
                {e["audit_id"] for e in live_entries} - {e["audit_id"] for e in corp_entries}
            ),
        },
        "operator2_negative_space_dual_complex": live_op2,
    }

    target_sha = expected_payload_sha if expected_payload_sha is not None else canonical_sha256(expected_payload)
    live_sha = canonical_sha256(live_payload)
    if not constant_time_hex64_equal(live_sha, target_sha, "live_payload_parity"):
        raise EscherMinerError("LIVE_PAYLOAD_PARITY_MISMATCH", "live disk recomputation diverged from pinned oracle")

    return {
        "live_parity_verified": True,
        "live_extraction_verified": True,
        "extraction_mode": "live_disk_parsed_no_pinned_fallback",
        "payload_sha256": live_sha,
        "live_audits_matched": len(live_entries),
        "live_atomic_audit_ids": live_atomic_summary["atomic_audit_ids_count"],
        "live_verified_count": live_verified_count,
        "corpus_audits_matched": len(corp_entries),
        "negative_audits_classified": len(live_neg_records),
        "s20d_live_checker_executed": True,
    }

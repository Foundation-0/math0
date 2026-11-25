#!/usr/bin/env python3
"""
Track S89: Zone-B Hardened & R10+ Lean 4.36.0 Certificate Verifier.

Pure Python 3 standard library. Zero floats, zero bare asserts, zero hardcoded host paths.
Provides all 4 independent verification surfaces for Zone-B fuzzing (`82/82`):
  1. CLI (`--check <cert.json> [--json]`)
  2. `verify_certificate_dict(cert, full_replay=True)`  (FR1)
  3. `verify_certificate_dict(cert, full_replay=False)` (FR0)
  4. `secondary_audit_payload(cert_or_payload)`          (SEC — independent audit, no oracle replay)
Plus `--standalone --json`, `--write <cert.json>`, `--verify-lean <file.lean>`, and
optional read-only `--verify-corpus <text_dir> --inventory <file_inventory.json>`.
"""
from __future__ import annotations

import argparse
from collections.abc import Sequence
import errno
from fractions import Fraction
import hashlib
import hmac
import json
import math
import os
from pathlib import Path
import re
import secrets
import shutil
import stat
import subprocess
import sys
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

import s89_heritage_atlas_oracle as s89  # noqa: E402
from s89_heritage_atlas_oracle import (  # noqa: E402
    LEAN_FILE_SHA256,
    LEAN_THEOREMS,
    SCHEMA_VERSION,
    S89Error,
    TRACK_ID,
    build_certificate,
    build_payload,
    canonical_json_bytes,
    require_ok,
)

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_INT_DIGITS = 1000
_MAX_INT_BITS = (10 ** MAX_INT_DIGITS - 1).bit_length()
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PAYLOAD_KEYS = frozenset(
    {
        "schema_version",
        "track_id",
        "oracle_class",
        "pillar1_corpus_audit",
        "pillar2_anchor_nodes",
        "pillar3_k10_mesh_and_s83_bridge",
        "pillar4_lean4_and_novelty",
    }
)
_ALLOWED_LEAN_AXIOMS = frozenset({"propext", "Quot.sound"})
_K10_NODE_IDX: dict[str, int] = {f"h{i:02d}": i for i in range(10)}
_S83_NODE_IDS = frozenset(f"v{i}" for i in range(8))
_K10_EDGE_WEIGHTS: dict[str, int] = {
    "EXACT_COMMUTE": 4,
    "CONDITIONAL_BRIDGE": 2,
    "EXACT_OBSTRUCTION": 1,
}
_CROSS_CLASSES = frozenset(
    {
        "EXACT_OPERATOR_ISOMORPHISM",
        "CONDITIONAL_TRANSPOSITION",
        "EXACT_LAW5_OBSTRUCTION",
    }
)


# ---------------------------------------------------------------------------
# Strict Zone-B Type, Container, Rational & Digest Guards
# ---------------------------------------------------------------------------

def _is_strict_int(val: Any) -> bool:
    return type(val) is int


def _is_strict_str(val: Any) -> bool:
    return type(val) is str


def _is_lower_hex64(val: Any) -> bool:
    return type(val) is str and len(val) == 64 and all(ch in _HEX_LOWER for ch in val)


def _has_surrogate(text: str) -> bool:
    return any(0xD800 <= ord(ch) <= 0xDFFF for ch in text)


def _check_int_digits(val: int) -> None:
    if abs(val).bit_length() > _MAX_INT_BITS:
        raise S89Error("INT_TOO_LARGE", "integer exceeds digit bound")
    if len(str(abs(val))) > MAX_INT_DIGITS:
        raise S89Error("INT_TOO_LARGE", "integer exceeds digit bound")


def _check_container_safety(root: Any) -> None:
    """Iterative depth-bounded strict type & value audit (zero RecursionError)."""
    stack: list[tuple[Any, int]] = [(root, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > MAX_JSON_DEPTH:
            raise S89Error("MAX_DEPTH_EXCEEDED", "container depth exceeds MAX_JSON_DEPTH")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                if type(k) is not str or _has_surrogate(k):
                    raise S89Error("INVALID_DICT_KEY", "dict key must be valid strict str")
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:
                stack.append((item, depth + 1))
        elif t is str:
            if _has_surrogate(cur):
                raise S89Error("LONE_SURROGATE", "lone UTF-16 surrogate forbidden")
        elif t is int:
            _check_int_digits(cur)
        elif t is bool or cur is None:
            continue
        else:
            raise S89Error("FORBIDDEN_VALUE_TYPE", f"forbidden type: {t.__name__}")


def parse_canonical_rational(val: Any, label: str = "rational") -> Fraction:
    """Parse canonical reduced rational string ('n' or 'n/d', d > 1, gcd(|n|,d)==1)."""
    if type(val) is not str:
        raise S89Error("INVALID_RATIONAL", f"{label}: must be strict str")
    parts = val.split("/")
    if len(parts) > 2:
        raise S89Error("INVALID_RATIONAL", f"{label}: multiple slashes")
    num_s = parts[0]
    neg = num_s.startswith("-")
    ndig = num_s[1:] if neg else num_s
    if not ndig or len(ndig) > MAX_INT_DIGITS or any(ch not in _ASCII_DIGITS for ch in ndig):
        raise S89Error("INVALID_RATIONAL", f"{label}: invalid numerator")
    if len(ndig) > 1 and ndig[0] == "0":
        raise S89Error("INVALID_RATIONAL", f"{label}: leading zero in numerator")
    if neg and ndig == "0":
        raise S89Error("INVALID_RATIONAL", f"{label}: negative zero forbidden")
    num = -int(ndig) if neg else int(ndig)
    if len(parts) == 1:
        return Fraction(num, 1)
    den_s = parts[1]
    if not den_s or len(den_s) > MAX_INT_DIGITS or any(ch not in _ASCII_DIGITS for ch in den_s):
        raise S89Error("INVALID_RATIONAL", f"{label}: invalid denominator")
    if den_s[0] == "0":
        raise S89Error("INVALID_RATIONAL", f"{label}: leading zero in denominator")
    den = int(den_s)
    if den <= 1:
        raise S89Error("INVALID_RATIONAL", f"{label}: denominator must be > 1")
    if math.gcd(abs(num), den) != 1:
        raise S89Error("INVALID_RATIONAL", f"{label}: fraction not reduced")
    return Fraction(num, den)


# ---------------------------------------------------------------------------
# Strict Zone-B Atomic `dir_fd` I/O (Symlink, Hardlink, FIFO & TOCTOU Safe)
# ---------------------------------------------------------------------------

def _check_pwd_no_symlinks() -> None:
    pwd = os.environ.get("PWD", "")
    if not pwd.startswith("/"):
        return
    cur = Path("/")
    for part in Path(pwd).parts[1:]:
        cur = cur / part
        try:
            st = os.lstat(cur)
        except OSError:
            return
        if stat.S_ISLNK(st.st_mode):
            raise S89Error("SYMLINK_IN_PATH", f"logical PWD contains symlink: {part}")


def _require_single_link(nlink: int, code: str, label: str) -> None:
    if nlink != 1:
        raise S89Error(code, f"hardlinked file forbidden: {label}")


def _open_dir_chain(path: Path) -> tuple[int, str]:
    """Walk parent directory components via O_NOFOLLOW | O_DIRECTORY, returning (dir_fd, basename)."""
    _check_pwd_no_symlinks()
    if not path.is_absolute():
        try:
            cwd = Path(os.getcwd())
        except OSError as exc:
            raise S89Error("CWD_UNAVAILABLE", f"current directory unavailable: {exc}") from exc
        full = cwd / path
    else:
        full = path
    norm_parts: list[str] = []
    for part in full.parts[1:]:
        if part == "..":
            if norm_parts:
                norm_parts.pop()
        elif part != ".":
            norm_parts.append(part)
    if not norm_parts:
        raise S89Error("INVALID_TARGET_PATH", "path names root directory")
    dir_parts = norm_parts[:-1]
    base_name = norm_parts[-1]
    flags = os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_NOFOLLOW", 0)
    dfd = os.open("/", flags)
    for comp in dir_parts:
        try:
            nxt = os.open(comp, flags, dir_fd=dfd)
        except OSError as exc:
            os.close(dfd)
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                raise S89Error("SYMLINK_IN_PATH", f"symlink or non-dir component: {comp}") from exc
            raise S89Error("DIR_OPEN_FAILED", f"cannot traverse {comp}: {exc}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd, base_name


def read_regular_file_bytes(path: Path, *, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Read regular non-symlink, non-hardlinked, non-FIFO file bytes safely via dir_fd."""
    dfd, name = _open_dir_chain(path)
    oflags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    fd = -1
    try:
        try:
            fd = os.open(name, oflags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise S89Error("SYMLINK_FORBIDDEN", f"target is symlink: {name}") from exc
            raise S89Error("FILE_OPEN_FAILED", f"cannot open {name}: {exc}") from exc
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise S89Error("NOT_REGULAR_FILE", f"target is not a regular file: {name}")
        _require_single_link(st.st_nlink, "HARDLINK_FORBIDDEN", name)
        chunks: list[bytes] = []
        total = 0
        while True:
            blk = os.read(fd, 65536)
            if not blk:
                break
            total += len(blk)
            if total > max_bytes:
                raise S89Error("FILE_TOO_LARGE", f"file read exceeds {max_bytes} bytes")
            chunks.append(blk)
        return b"".join(chunks)
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dfd)


def write_atomic_0600_bytes(path: Path, data: bytes) -> None:
    """Atomically write 0o600 bytes via dir_fd with hardlink/symlink/FIFO target refusal."""
    dfd, name = _open_dir_chain(path)
    tmp_name = f".{name}.{secrets.token_hex(8)}.tmp"
    tflags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    tfd = -1
    created = False
    try:
        try:
            existing = os.lstat(name, dir_fd=dfd)
        except FileNotFoundError:
            existing = None
        if existing is not None:
            if stat.S_ISLNK(existing.st_mode):
                raise S89Error("SYMLINK_FORBIDDEN", f"refusing symlink target: {name}")
            if not stat.S_ISREG(existing.st_mode):
                raise S89Error("NOT_REGULAR_FILE", f"refusing non-regular target: {name}")
            _require_single_link(existing.st_nlink, "HARDLINK_FORBIDDEN", name)
        tfd = os.open(tmp_name, tflags, 0o600, dir_fd=dfd)
        created = True
        view = memoryview(data)
        written = 0
        while written < len(data):
            n = os.write(tfd, view[written:])
            written += n
        os.fchmod(tfd, 0o600)
        os.fsync(tfd)
        tst = os.fstat(tfd)
        _require_single_link(tst.st_nlink, "TMP_HARDLINK_DETECTED", tmp_name)
        os.close(tfd)
        tfd = -1
        os.replace(tmp_name, name, src_dir_fd=dfd, dst_dir_fd=dfd)
        created = False
        os.fsync(dfd)
    except S89Error:
        raise
    except OSError as exc:
        raise S89Error("ATOMIC_WRITE_FAILED", f"atomic write failed: {exc}") from exc
    finally:
        if tfd >= 0:
            os.close(tfd)
        if created:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Strict Zero-Float Canonical JSON Parser (Pre-Parse Digit Cap & Depth Guard)
# ---------------------------------------------------------------------------

def _parse_bounded_int(token: str) -> int:
    digits = token[1:] if token.startswith("-") else token
    if len(digits) > MAX_INT_DIGITS:
        raise S89Error("INT_TOO_LARGE", "JSON integer exceeds digit limit")
    return int(token)


def _reject_float(token: str) -> Any:
    raise S89Error("FLOAT_FORBIDDEN", f"JSON float forbidden: {token}")


def _reject_constant(token: str) -> Any:
    raise S89Error("NONFINITE_JSON", f"non-finite JSON constant forbidden: {token}")


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise S89Error("DUPLICATE_JSON_KEY", f"duplicate JSON key: {k}")
        out[k] = v
    return out


def _check_raw_json_nesting(text: str) -> None:
    """Iterative pre-parse bracket/brace depth check preventing json.loads RecursionError."""
    depth = 0
    in_str = False
    esc = False
    for ch in text:
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
        elif ch == '"':
            in_str = True
        elif ch in "{[":
            depth += 1
            if depth > MAX_JSON_DEPTH:
                raise S89Error("MAX_DEPTH_EXCEEDED", "JSON nesting depth exceeds limit")
        elif ch in "}]":
            if depth > 0:
                depth -= 1


def parse_strict_json_bytes(raw: bytes, *, require_canonical: bool = True) -> dict[str, Any]:
    if b"\r" in raw:
        raise S89Error("CRLF_FORBIDDEN", "CR/CRLF forbidden in canonical JSON")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise S89Error("INVALID_UTF8", f"invalid UTF-8 JSON: {exc}") from exc
    _check_raw_json_nesting(text)
    try:
        obj = json.loads(
            text,
            parse_int=_parse_bounded_int,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_no_dup_pairs,
        )
    except S89Error:
        raise
    except (ValueError, RecursionError) as exc:
        raise S89Error("INVALID_JSON", f"JSON parse error: {exc}") from exc
    if type(obj) is not dict:
        raise S89Error("NON_OBJECT_ROOT", "JSON root must be an object")
    _check_container_safety(obj)
    if require_canonical:
        expected_raw = canonical_json_bytes(obj) + b"\n"
        if raw != expected_raw:
            raise S89Error("NON_CANONICAL_JSON", "JSON bytes are not canonical LF-terminated")
    return obj


# ---------------------------------------------------------------------------
# Full R10+ 15-Class Lean 4.36.0 Static Scanner & Live Kernel Verifier
# ---------------------------------------------------------------------------

_LEAN4_IDENT_EXTRA = "_.'"
_LEAN4_CHAR_PREV_IDENT = "_'»!?"
_LEAN4_HEX = frozenset("0123456789abcdefABCDEF")
_LEAN4_GUIL_SIMPLE_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_']*\Z")
_LEAN4_GUIL_UNWRAP_RE = re.compile(r"«([A-Za-z_][A-Za-z0-9_']*)»")
_LEAN4_INTERP_BANG_WORDS = frozenset(
    ("s", "f", "m", "v", "println", "reportIssue", "reportDbgIssue", "reportEMatchIssue")
)
_LEAN4_INTERP_KW = frozenset(("dbg_trace", "throwError"))
_LEAN4_TRACE_BRACK_WORDS = frozenset(("trace", "trace_goal"))
_LEAN4_SYNTAX_QUOTE_KW = frozenset(("notation", "prefix", "infix", "infixl", "infixr", "postfix"))

_LEAN4_HARD_LINE_RULES: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\bsorry\b"), "LEAN4_SORRY"),
    (re.compile(r"\badmit\b"), "LEAN4_ADMIT"),
    (re.compile(r"(?<!\.)\baxiom\b"), "LEAN4_AXIOM"),
    (re.compile(r"(?<!\.)\bunsafe\b"), "LEAN4_UNSAFE"),
    (re.compile(r"\bnative_decide\b"), "LEAN4_NATIVE_DECIDE"),
    (re.compile(r"\bsorryAx\b"), "LEAN4_SORRY_AX"),
    (re.compile(r"\bLean\.Meta\.mkSorry\b|\bmkSorry\b"), "LEAN4_MK_SORRY"),
    (re.compile(r"\bLean\.ofReduceBool\b|\bofReduceBool\b"), "LEAN4_OF_REDUCE_BOOL"),
    (re.compile(r"\bLean\.ofReduceNat\b|\bofReduceNat\b"), "LEAN4_OF_REDUCE_NAT"),
    (re.compile(r"\bLean\.trustCompiler\b|\btrustCompiler\b"), "LEAN4_TRUST_COMPILER"),
    (
        re.compile(r"(?<!\.)\b(?:macro|macro_rules|elab|elab_rules|syntax)\b|\binterpolatedStr\b"),
        "LEAN4_META_SYNTAX_ESCAPE",
    ),
)
_LEAN4_IMPORT_RE = re.compile(
    r"(?:^|\n)[ \t]*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)",
    flags=re.DOTALL,
)
_LEAN4_PARTIAL_DECL_RE = re.compile(r"(?<!\.)\bpartial\s+(?:def|instance|abbrev)\b", flags=re.DOTALL)
_LEAN4_DEBUG_RE = re.compile(
    r"\bdebug\s*\.\s*(?:skipKernelTC|byAsSorry|proofAsSorry|terminalTacticsAsSorry)\b",
    flags=re.DOTALL,
)
_LEAN4_PRINT_KW_BLOCK = (
    "def|theorem|lemma|axiom|inductive|structure|class|instance|opaque|abbrev|example|"
    "namespace|section|end|open|variable|universe|import|set_option|attribute|"
    "local|scoped|private|protected|noncomputable|partial|unsafe|meta|where|by|in|let|have"
)
_LEAN4_SPOOF_RE = re.compile(
    r"#(?:eval!?(?![\w'!?])|reduce(?![\w'!?])|exit(?![\w'!?])|"
    r"print(?![\w'!?])(?!\s+axioms[ \t]+(?!(?:" + _LEAN4_PRINT_KW_BLOCK + r")(?![\w'!?]))[A-Za-z_]))"
    r"|(?<!\.)\b(?:run_cmd|run_meta|initialize|builtin_initialize)\b",
    flags=re.DOTALL,
)
_LEAN4_ATTR_OPEN_RE = re.compile(r"(?:@|(?<!\.)\battribute\s*)\[", flags=re.DOTALL)
_LEAN4_HARD_ATTR_RE = re.compile(r"\b(?:extern|implemented_by|csimp)\b")
_LEAN4_DECIDE_KW_RE = re.compile(r"\bdecide\b")
_LEAN4_FLAG_TOK_RE = re.compile(r"[+-][A-Za-z0-9_]+")
_LEAN4_OPT_PREFIX_RE = re.compile(r"\s*([A-Za-z0-9_]+)\s*:=")
_LEAN4_CONFIG_NATIVE_RE = re.compile(r"\bnative\b(?:\s*:=\s*([^},]*))?")
_LEAN4_CONFIG_WITH_RE = re.compile(r"\bwith\b")
_LEAN4_DECIDE_CFG_BIND_RE = re.compile(
    r"\b(?:DecideConfig|Decide\.Config)\b[ \t)]*:=\s*(?:\(\s*)*\{[^}{]*\bnative\s*:=\s*([^}{,]*)(?:,[^}{]*)?\}"
    r"|\{[^}{]*\bnative\s*:=\s*([^}{,]*)(?:,[^}{]*)?\}\s*:\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*(?:DecideConfig|Decide\.Config)\b",
    flags=re.DOTALL,
)
_LEAN4_AXIOM_OUT_RE = re.compile(
    r"^'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])$"
)


def _is_lean4_ident_prev(source: str, pos: int) -> bool:
    if pos < 0:
        return False
    ch = source[pos]
    if ch.isalnum() or ch in _LEAN4_IDENT_EXTRA:
        return True
    if ch in "!?":
        for k in range(pos - 1, -1, -1):
            if source[k] not in "!?":
                return source[k].isalnum() or source[k] in "_'"
        return False
    return False


def _match_lean4_char_end(source: str, i: int, n: int) -> int | None:
    if i + 2 < n and source[i + 1] != "\\" and source[i + 1] != "\n" and source[i + 2] == "'":
        return i + 3
    if i + 3 < n and source[i + 1] == "\\":
        if source[i + 3] == "'" and source[i + 2] != "\n":
            return i + 4
        esc = source[i + 2]
        if esc == "x" and i + 5 < n and source[i + 5] == "'" and all(c in _LEAN4_HEX for c in source[i + 3 : i + 5]):
            return i + 6
        if esc == "u" and i + 7 < n and source[i + 7] == "'" and all(c in _LEAN4_HEX for c in source[i + 3 : i + 7]):
            return i + 8
    return None


def _strip_lean4_r10(source: str) -> tuple[str, list[str]]:
    out: list[str] = []
    errors: list[str] = []
    i = 0
    n = len(source)
    depth = 0
    in_str = False
    in_interp = False
    pending_interp = False
    trace_brack = 0
    in_syntax_header = False
    syntax_quote_reported = False
    interp_stack: list[int] = []
    raw_hashes = -1
    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if raw_hashes >= 0:
            close_seq = '"' + ("#" * raw_hashes)
            if source.startswith(close_seq, i):
                out.append(" " * len(close_seq))
                i += len(close_seq)
                raw_hashes = -1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_str:
            if ch == "\\":
                if nxt == '"' and in_syntax_header and not syntax_quote_reported:
                    syntax_quote_reported = True
                    errors.append("LEAN4_SYNTAX_QUOTE_TOKEN")
                out.append(" \n" if nxt == "\n" else "  ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_interp:
            if ch == "\\":
                out.append(" \n" if nxt == "\n" else "  ")
                i += 2
            elif ch == "{":
                interp_stack.append(1)
                in_interp = False
                out.append(" ")
                i += 1
            elif ch == '"':
                in_interp = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch.isspace():
            out.append(ch)
            i += 1
            continue
        if ch != '"':
            pending_interp = False
        if ch != "[" and trace_brack == 1:
            trace_brack = 0
        if interp_stack:
            if ch == "{":
                interp_stack[-1] += 1
                out.append(ch)
                i += 1
                continue
            if ch == "}":
                interp_stack[-1] -= 1
                out.append(ch)
                i += 1
                if interp_stack[-1] == 0:
                    interp_stack.pop()
                    in_interp = True
                continue
        if ch == "[" and trace_brack >= 1:
            trace_brack += 1
            out.append(ch)
            i += 1
        elif ch == "]" and trace_brack >= 2:
            trace_brack -= 1
            if trace_brack == 1:
                trace_brack = 0
                pending_interp = True
            out.append(ch)
            i += 1
        elif ch == "=" and nxt == ">":
            in_syntax_header = False
            out.append("=>")
            i += 2
        elif ch == '"':
            if pending_interp:
                in_interp = True
                pending_interp = False
            else:
                if _is_lean4_ident_prev(source, i - 2) and source[i - 1] == "!":
                    is_panic = (
                        source[i - 6 : i] == "panic!"
                        and not _is_lean4_ident_prev(source, i - 7)
                    )
                    if not is_panic:
                        errors.append("LEAN4_UNKNOWN_BANG_STRING")
                in_str = True
                syntax_quote_reported = False
            out.append(" ")
            i += 1
        elif ch == "«":
            end_g = source.find("»", i + 1)
            if end_g == -1:
                errors.append("LEAN4_UNTERMINATED_IDENT")
                break
            inner = source[i + 1 : end_g]
            if _LEAN4_GUIL_SIMPLE_RE.match(inner) is not None and inner != "axioms":
                out.append(source[i : end_g + 1])
            else:
                out.append(" " + "".join("\n" if c == "\n" else " " for c in inner) + " ")
            i = end_g + 1
        elif ch == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in _LEAN4_CHAR_PREV_IDENT)):
            char_end = _match_lean4_char_end(source, i, n)
            if char_end is not None:
                out.append(" " * (char_end - i))
                i = char_end
            else:
                out.append(ch)
                i += 1
        else:
            if ch == "r" and not _is_lean4_ident_prev(source, i - 1):
                j = i + 1
                while j < n and source[j] == "#":
                    j += 1
                if j < n and source[j] == '"':
                    raw_hashes = j - (i + 1)
                    out.append(" " * (j - i + 1))
                    i = j + 1
                    continue
            if ch.isalpha() and not _is_lean4_ident_prev(source, i - 1):
                w_end = i + 1
                while w_end < n and (source[w_end].isalnum() or source[w_end] == "_"):
                    w_end += 1
                word = source[i:w_end]
                if word == "Macro" and source.startswith(".trace", w_end):
                    end_mt = w_end + 6
                    if trace_brack == 0:
                        trace_brack = 1
                    out.append(source[i:end_mt])
                    i = end_mt
                    continue
                next_ch = source[w_end] if w_end < n else ""
                if next_ch == "!" and word in _LEAN4_INTERP_BANG_WORDS:
                    pending_interp = True
                    out.append(source[i : w_end + 1])
                    i = w_end + 1
                    continue
                if next_ch not in ".'!?":
                    if word in _LEAN4_INTERP_KW:
                        pending_interp = True
                    elif word in _LEAN4_TRACE_BRACK_WORDS and trace_brack == 0:
                        trace_brack = 1
                    elif word in _LEAN4_SYNTAX_QUOTE_KW:
                        in_syntax_header = True
                out.append(word)
                i = w_end
                continue
            out.append(ch)
            i += 1
    if depth > 0:
        errors.append("LEAN4_UNTERMINATED_COMMENT")
    elif in_str or in_interp or raw_hashes >= 0 or interp_stack:
        errors.append("LEAN4_UNTERMINATED_STRING")
    return "".join(out), errors


def _strip_outer_parens(rhs: str) -> str:
    s = rhs.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        s = s[1:-1].strip()
    return s


def _is_native_false(rhs: str) -> bool:
    return _strip_outer_parens(rhs) in ("false", "Bool.false")


def _scan_decide_native(cleaned: str) -> bool:
    for mc in _LEAN4_DECIDE_CFG_BIND_RE.finditer(cleaned):
        for grp in mc.groups():
            if grp is not None and not _is_native_false(grp):
                return True
    n = len(cleaned)
    match_rp: dict[int, int] = {}
    pstack: list[int] = []
    for idx, ch in enumerate(cleaned):
        if ch == "(":
            pstack.append(idx)
        elif ch == ")" and pstack:
            match_rp[pstack.pop()] = idx
    for m in _LEAN4_DECIDE_KW_RE.finditer(cleaned):
        pos = m.end()
        while True:
            while pos < n and cleaned[pos].isspace():
                pos += 1
            if pos >= n:
                break
            ch = cleaned[pos]
            if ch in "+-":
                mf = _LEAN4_FLAG_TOK_RE.match(cleaned, pos)
                if mf is None:
                    break
                if mf.group(0) == "+native":
                    return True
                pos = mf.end()
                continue
            if ch == "(":
                close_i = match_rp.get(pos)
                if close_i is None:
                    break
                mp = _LEAN4_OPT_PREFIX_RE.match(cleaned, pos + 1, close_i)
                if mp is None:
                    break
                key = mp.group(1)
                rhs = cleaned[mp.end() : close_i].strip()
                if key == "native" and not _is_native_false(rhs):
                    return True
                if key == "config":
                    inner = _strip_outer_parens(rhs)
                    if not (inner.startswith("{") and inner.endswith("}")):
                        return True
                    body = inner[1:-1]
                    if "{" in body or "}" in body or _LEAN4_CONFIG_WITH_RE.search(body) is not None:
                        return True
                    for mn in _LEAN4_CONFIG_NATIVE_RE.finditer(body):
                        if mn.group(1) is None or not _is_native_false(mn.group(1)):
                            return True
                pos = close_i + 1
                continue
            break
    return False


def audit_lean4_source_r10(source: str) -> list[str]:
    """Return list of R10+ static Lean 4 finding codes (empty iff clean)."""
    if type(source) is not str:
        raise S89Error("INVALID_LEAN_SOURCE", "Lean source must be strict str")
    cleaned, findings = _strip_lean4_r10(source)
    cleaned = _LEAN4_GUIL_UNWRAP_RE.sub(r"\1", cleaned)
    for line in cleaned.splitlines():
        for pat, code in _LEAN4_HARD_LINE_RULES:
            if pat.search(line) is not None:
                findings.append(code)
    for m_imp in _LEAN4_IMPORT_RE.finditer(cleaned):
        root_pkg = m_imp.group(1).split(".")[0]
        if root_pkg not in ("Init", "Std"):
            findings.append("LEAN4_NON_INIT_IMPORT")
    if _LEAN4_PARTIAL_DECL_RE.search(cleaned) is not None:
        findings.append("LEAN4_PARTIAL")
    if _scan_decide_native(cleaned):
        findings.append("LEAN4_DECIDE_NATIVE")
    if _LEAN4_DEBUG_RE.search(cleaned) is not None:
        findings.append("LEAN4_SKIP_KERNEL_TC")
    if _LEAN4_SPOOF_RE.search(cleaned) is not None:
        findings.append("LEAN4_EVAL_SPOOF")
    match_rb: dict[int, int] = {}
    bstack: list[int] = []
    for idx, ch in enumerate(cleaned):
        if ch == "[":
            bstack.append(idx)
        elif ch == "]" and bstack:
            match_rb[bstack.pop()] = idx
    for m_open in _LEAN4_ATTR_OPEN_RE.finditer(cleaned):
        lb = m_open.end() - 1
        rb = match_rb.get(lb)
        if rb is not None and _LEAN4_HARD_ATTR_RE.search(cleaned, lb + 1, rb) is not None:
            findings.append("LEAN4_ATTR_TRUST_ESCAPE")
    return findings


def _find_lean_binary() -> str:
    found = shutil.which("lean")
    if found is not None:
        return found
    home_env = os.environ.get("HOME")
    if home_env:
        elan_lean = Path(home_env) / ".elan" / "bin" / "lean"
        if elan_lean.is_file():
            return str(elan_lean)
    raise S89Error("LEAN_BINARY_NOT_FOUND", "lean binary not found on PATH or $HOME/.elan/bin")


def _verify_lean_output(
    returncode: int,
    stderr: str,
    stdout: str,
    *,
    check_pinned_sha: bool = True,
) -> dict[str, list[str]]:
    require_ok(returncode == 0, "LEAN_COMPILE_FAILED", f"lean exited {returncode}: {stderr}")
    require_ok(stderr == "", "LEAN_STDERR_NONEMPTY", f"unexpected lean stderr: {stderr}")
    records: list[str] = []
    for raw_line in stdout.splitlines():
        s = raw_line.strip()
        if records and "[" in records[-1] and "]" not in records[-1]:
            records[-1] = records[-1] + " " + s
        else:
            records.append(s)
    seen: dict[str, list[str]] = {}
    for line in records:
        m = _LEAN4_AXIOM_OUT_RE.match(line)
        require_ok(m is not None, "LEAN_UNEXPECTED_OUTPUT", f"unexpected lean output: {line}")
        thm = m.group(1)
        require_ok(thm not in seen, "LEAN_DUPLICATE_THEOREM", f"duplicate theorem output: {thm}")
        ax_raw = m.group(2)
        ax_list = [] if ax_raw is None else [a.strip() for a in ax_raw.split(",") if a.strip()]
        for ax in ax_list:
            require_ok(ax in _ALLOWED_LEAN_AXIOMS, "LEAN_FORBIDDEN_AXIOM", f"{thm} uses forbidden axiom {ax}")
        seen[thm] = ax_list
    if check_pinned_sha:
        require_ok(tuple(seen.keys()) == LEAN_THEOREMS, "LEAN_THEOREM_SET_MISMATCH", "theorem set mismatch")
    return seen


def verify_lean_file(path: Path, *, check_pinned_sha: bool = True) -> dict[str, Any]:
    raw = read_regular_file_bytes(path, max_bytes=MAX_JSON_BYTES)
    if b"\r" in raw:
        raise S89Error("CRLF_FORBIDDEN", "CR/CRLF forbidden in Lean file")
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise S89Error("INVALID_UTF8", f"invalid UTF-8 in Lean file: {exc}") from exc
    sha = hashlib.sha256(raw).hexdigest()
    if check_pinned_sha and not hmac.compare_digest(sha, LEAN_FILE_SHA256):
        raise S89Error("LEAN_SHA_MISMATCH", "Lean file SHA-256 mismatch")
    findings = audit_lean4_source_r10(source)
    require_ok(len(findings) == 0, "LEAN_R10_STATIC_FINDING", f"R10 findings: {findings}")
    lean_bin = _find_lean_binary()
    proc = subprocess.run([lean_bin, str(path)], capture_output=True, text=True, timeout=120, check=False)
    seen = _verify_lean_output(proc.returncode, proc.stderr, proc.stdout, check_pinned_sha=check_pinned_sha)
    return {
        "lean_file": path.name,
        "sha256": sha,
        "r10_findings": 0,
        "theorems_verified": len(seen),
        "allowed_axioms": sorted(_ALLOWED_LEAN_AXIOMS),
    }


# ---------------------------------------------------------------------------
# Independent Secondary Payload Audit (Surface 4: SEC — ZERO Oracle Replay!)
# ---------------------------------------------------------------------------

def _require_dict_keys(obj: Any, expected: frozenset[str], code: str) -> dict[str, Any]:
    if type(obj) is not dict or set(obj.keys()) != expected:
        raise S89Error(code, f"exact keys mismatch for {code}")
    return obj


def _verify_envelope_digests(cert: dict[str, Any]) -> dict[str, Any]:
    _require_dict_keys(cert, _CERT_KEYS, "BAD_CERT_KEYS")
    require_ok(cert["schema_version"] == SCHEMA_VERSION, "BAD_SCHEMA_VERSION", "schema mismatch")
    require_ok(cert["track_id"] == TRACK_ID, "BAD_TRACK_ID", "track_id mismatch")
    psha = cert["payload_sha256"]
    csha = cert["certificate_sha256"]
    require_ok(_is_lower_hex64(psha), "BAD_PAYLOAD_SHA_SYNTAX", "payload_sha256 must be 64 lower hex")
    require_ok(_is_lower_hex64(csha), "BAD_CERT_SHA_SYNTAX", "certificate_sha256 must be 64 lower hex")
    payload = cert["payload"]
    if type(payload) is not dict:
        raise S89Error("BAD_PAYLOAD_TYPE", "payload must be strict dict")
    calc_p = hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
    require_ok(hmac.compare_digest(psha, calc_p), "PAYLOAD_SHA_MISMATCH", "payload digest mismatch")
    env = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": psha,
        "payload": payload,
    }
    calc_c = hashlib.sha256(canonical_json_bytes(env)).hexdigest()
    require_ok(hmac.compare_digest(csha, calc_c), "CERT_SHA_MISMATCH", "certificate digest mismatch")
    return payload


def secondary_audit_payload(cert_or_payload: Any) -> dict[str, Any]:
    """
    Independent structural & mathematical audit of Track S89 certificate or payload
    without replaying `build_payload()`. Raises `S89Error` (`ValueError`) on any defect.
    """
    if type(cert_or_payload) is not dict:
        raise S89Error("NON_DICT_INPUT", "input must be strict dict")
    _check_container_safety(cert_or_payload)
    if "certificate_sha256" in cert_or_payload:
        payload = _verify_envelope_digests(cert_or_payload)
    else:
        payload = cert_or_payload

    _require_dict_keys(payload, _PAYLOAD_KEYS, "BAD_PAYLOAD_KEYS")
    require_ok(payload["schema_version"] == SCHEMA_VERSION, "BAD_PAYLOAD_SCHEMA", "payload schema mismatch")
    require_ok(payload["track_id"] == TRACK_ID, "BAD_PAYLOAD_TRACK", "payload track mismatch")
    require_ok(payload["oracle_class"] == s89.ORACLE_CLASS, "BAD_ORACLE_CLASS", "oracle_class mismatch")

    # Pillar 1 independent audit
    p1 = payload["pillar1_corpus_audit"]
    require_ok(type(p1) is dict, "BAD_P1_TYPE", "pillar1 must be dict")
    require_ok(_is_lower_hex64(p1.get("inventory_sha256")), "BAD_INV_SHA", "invalid inventory sha256")
    totals = p1.get("totals")
    require_ok(type(totals) is dict, "BAD_P1_TOTALS", "totals must be dict")
    by_dir = p1.get("by_top_dir")
    by_ext = p1.get("by_extension")
    txt_ext = p1.get("text_layer_by_extension")
    tiers = p1.get("work_tier_distribution")
    diag = p1.get("quality_diagnostics_law4")
    require_ok(
        type(by_dir) is list and type(by_ext) is list and type(txt_ext) is list and type(tiers) is list and type(diag) is dict,
        "BAD_P1_SECTIONS",
        "pillar1 sub-sections invalid",
    )
    require_ok(len(by_dir) == 10 and len(by_ext) == 8 and len(txt_ext) == 4, "BAD_P1_LENGTHS", "pillar1 table length drift")
    for row in by_dir:
        require_ok(
            type(row) is dict and _is_strict_int(row.get("files")) and _is_strict_int(row.get("pdfs")) and _is_strict_int(row.get("bytes")),
            "BAD_P1_DIR_ROW",
            "invalid by_top_dir row",
        )
    for row in by_ext:
        require_ok(
            type(row) is dict and _is_strict_int(row.get("files")) and _is_strict_int(row.get("bytes")),
            "BAD_P1_EXT_ROW",
            "invalid by_extension row",
        )
    for row in txt_ext:
        require_ok(
            type(row) is dict and _is_strict_int(row.get("files")) and _is_strict_int(row.get("bytes")) and _is_strict_int(row.get("words")),
            "BAD_P1_TXT_ROW",
            "invalid text_layer_by_extension row",
        )
    require_ok(
        _is_strict_int(totals.get("inventory_files")) and sum(r["files"] for r in by_dir) == totals["inventory_files"] and sum(r["files"] for r in by_ext) == totals["inventory_files"],
        "P1_FILES_SUM_MISMATCH",
        "inventory_files sum mismatch",
    )
    require_ok(
        _is_strict_int(totals.get("inventory_bytes")) and sum(r["bytes"] for r in by_dir) == totals["inventory_bytes"] and sum(r["bytes"] for r in by_ext) == totals["inventory_bytes"],
        "P1_BYTES_SUM_MISMATCH",
        "inventory_bytes sum mismatch",
    )
    require_ok(
        _is_strict_int(totals.get("inventory_pdfs")) and sum(r["pdfs"] for r in by_dir) == totals["inventory_pdfs"],
        "P1_PDFS_SUM_MISMATCH",
        "inventory_pdfs sum mismatch",
    )
    gib_q = parse_canonical_rational(totals.get("inventory_gib_exact"), "inventory_gib_exact")
    require_ok(gib_q == Fraction(totals["inventory_bytes"], s89.GIB_BYTES), "P1_GIB_MISMATCH", "inventory_gib_exact mismatch")
    require_ok(
        _is_strict_int(totals.get("downloaded_text_files")) and sum(r["files"] for r in txt_ext) == totals["downloaded_text_files"],
        "P1_TXT_FILES_MISMATCH",
        "downloaded_text_files sum mismatch",
    )
    require_ok(
        _is_strict_int(totals.get("downloaded_text_bytes")) and sum(r["bytes"] for r in txt_ext) == totals["downloaded_text_bytes"],
        "P1_TXT_BYTES_MISMATCH",
        "downloaded_text_bytes sum mismatch",
    )
    require_ok(
        _is_strict_int(totals.get("downloaded_text_words")) and sum(r["words"] for r in txt_ext) == totals["downloaded_text_words"],
        "P1_TXT_WORDS_MISMATCH",
        "downloaded_text_words sum mismatch",
    )
    crlf_q = parse_canonical_rational(diag.get("crlf_text_fraction"), "crlf_text_fraction")
    require_ok(
        _is_strict_int(diag.get("crlf_text_files")) and crlf_q == Fraction(diag["crlf_text_files"], totals["downloaded_text_files"]),
        "P1_CRLF_FRAC_MISMATCH",
        "crlf_text_fraction mismatch",
    )
    bad_q = parse_canonical_rational(diag.get("malformed_jsonl_bad_fraction"), "malformed_jsonl_bad_fraction")
    require_ok(
        _is_strict_int(diag.get("malformed_jsonl_bad_lines"))
        and _is_strict_int(diag.get("malformed_jsonl_checked_lines"))
        and diag["malformed_jsonl_checked_lines"] > 0
        and bad_q == Fraction(diag["malformed_jsonl_bad_lines"], diag["malformed_jsonl_checked_lines"]),
        "P1_JSONL_FRAC_MISMATCH",
        "malformed_jsonl_bad_fraction mismatch",
    )

    # Pillar 2 independent audit (10 anchors, 20 lower-hex64 SHAs, rational witnesses)
    p2 = payload["pillar2_anchor_nodes"]
    require_ok(type(p2) is dict, "BAD_P2_TYPE", "pillar2 must be dict")
    anchors = p2.get("anchors")
    require_ok(type(anchors) is list and len(anchors) == 10, "BAD_P2_ANCHOR_COUNT", "must have 10 anchors")
    p2_bytes = 0
    p2_words = 0
    for idx, node in enumerate(anchors):
        require_ok(type(node) is dict and node.get("id") == f"h{idx:02d}", "BAD_P2_ANCHOR_ID", f"bad anchor at {idx}")
        for slot in ("primary_anchor", "secondary_anchor"):
            meta = node.get(slot)
            require_ok(
                type(meta) is dict
                and _is_strict_str(meta.get("rel_path"))
                and not meta["rel_path"].startswith("/")
                and _is_lower_hex64(meta.get("sha256"))
                and _is_strict_int(meta.get("bytes"))
                and _is_strict_int(meta.get("words")),
                "BAD_P2_ANCHOR_META",
                f"invalid {slot} on h{idx:02d}",
            )
            p2_bytes += meta["bytes"]
            p2_words += meta["words"]
    require_ok(
        _is_strict_int(p2.get("pinned_files_total_bytes")) and p2["pinned_files_total_bytes"] == p2_bytes,
        "P2_BYTES_MISMATCH",
        "pinned bytes total mismatch",
    )
    require_ok(
        _is_strict_int(p2.get("pinned_files_total_words")) and p2["pinned_files_total_words"] == p2_words,
        "P2_WORDS_MISMATCH",
        "pinned words total mismatch",
    )
    wit = p2.get("exact_rational_witnesses")
    require_ok(type(wit) is dict, "BAD_P2_WITNESSES", "witnesses must be dict")
    c1 = parse_canonical_rational(wit.get("h07_farisi_primary_cos2"), "farisi_c1")
    c2 = parse_canonical_rational(wit.get("h07_farisi_secondary_cos2"), "farisi_c2")
    gap = parse_canonical_rational(wit.get("h07_farisi_alexander_band_cos2_gap"), "farisi_gap")
    require_ok(c1 == Fraction(7, 27) and c2 == Fraction(7, 72) and gap == c1 - c2, "P2_FARISI_MISMATCH", "Farisi caustic mismatch")
    lip = parse_canonical_rational(wit.get("h06_kashi_lipschitz_bound"), "kashi_lip")
    require_ok(Fraction(0) < lip < Fraction(1), "P2_KASHI_LIP_MISMATCH", "Al-Kashi Lipschitz out of (0,1)")

    # Pillar 3 independent K_10 Laplacian (grounded at h00), inertia, Foster, compounding,
    # 120-triangle holonomy, 210-tetrahedron Z_2 Bianchi, 5|5 silo-cut & 10x8 cross-mapping audit
    p3 = payload["pillar3_k10_mesh_and_s83_bridge"]
    require_ok(type(p3) is dict, "BAD_P3_TYPE", "pillar3 must be dict")
    edges = p3.get("edges")
    require_ok(type(edges) is list and len(edges) == 45, "BAD_P3_EDGES", "must have 45 edges")
    edge_cls_map: dict[tuple[int, int], str] = {}
    edge_parsed: list[tuple[int, int, int, Fraction, Fraction, Fraction]] = []
    cls_counts = {"EXACT_COMMUTE": 0, "CONDITIONAL_BRIDGE": 0, "EXACT_OBSTRUCTION": 0}
    lap: list[list[Fraction]] = [[Fraction(0) for _ in range(10)] for _ in range(10)]
    for e in edges:
        require_ok(type(e) is dict, "BAD_P3_EDGE", "edge must be dict")
        u_id = e.get("u")
        v_id = e.get("v")
        ecls = e.get("edge_class")
        w = e.get("weight")
        require_ok(
            type(u_id) is str
            and type(v_id) is str
            and u_id in _K10_NODE_IDX
            and v_id in _K10_NODE_IDX,
            "BAD_P3_EDGE_NODES",
            "invalid K_10 edge endpoints",
        )
        ui = _K10_NODE_IDX[u_id]
        vj = _K10_NODE_IDX[v_id]
        require_ok(ui < vj and (ui, vj) not in edge_cls_map, "BAD_P3_EDGE_PAIR", "invalid or duplicate K_10 pair")
        require_ok(
            type(ecls) is str and ecls in _K10_EDGE_WEIGHTS and _is_strict_int(w) and w == _K10_EDGE_WEIGHTS[ecls],
            "BAD_P3_EDGE_CLASS_WEIGHT",
            "edge_class/weight mismatch",
        )
        reff = parse_canonical_rational(e.get("r_eff"), "r_eff")
        geff = parse_canonical_rational(e.get("g_eff"), "g_eff")
        ratio = parse_canonical_rational(e.get("compounding_ratio"), "compounding_ratio")
        edge_cls_map[(ui, vj)] = ecls
        cls_counts[ecls] += 1
        edge_parsed.append((ui, vj, w, reff, geff, ratio))
        wf = Fraction(w)
        lap[ui][ui] += wf
        lap[vj][vj] += wf
        lap[ui][vj] -= wf
        lap[vj][ui] -= wf

    require_ok(p3.get("edge_class_counts") == cls_counts, "P3_EDGE_CLASS_COUNTS_MISMATCH", "edge_class_counts mismatch")

    # Independent Sylvester LDL^T inertia over Q (zero shared code with oracle)
    lap_a = [[lap[r][c] for c in range(10)] for r in range(10)]
    pos_piv = 0
    zero_piv = 0
    for k in range(10):
        piv = lap_a[k][k]
        if piv > 0:
            pos_piv += 1
            for r in range(k + 1, 10):
                fac = lap_a[r][k] / piv
                for c in range(k + 1, 10):
                    lap_a[r][c] -= fac * lap_a[k][c]
        else:
            zero_piv += 1
    require_ok(p3.get("laplacian_inertia") == [pos_piv, 0, zero_piv], "P3_INERTIA_MISMATCH", "inertia != [9,0,1]")

    # Independent 9x9 SPD inversion grounded at h00 (nodes 1..9) -> exact resistances
    aug = [
        [lap[r + 1][c + 1] for c in range(9)] + [Fraction(1 if r == c else 0) for c in range(9)]
        for r in range(9)
    ]
    for col in range(9):
        piv = aug[col][col]
        aug[col] = [v / piv for v in aug[col]]
        for r in range(9):
            if r != col:
                fac = aug[r][col]
                aug[r] = [aug[r][c] - fac * aug[col][c] for c in range(18)]
    g0 = [row[9:] for row in aug]

    foster_acc = Fraction(0)
    ratios: list[Fraction] = []
    for ui, vj, w, reff, geff, ratio in edge_parsed:
        guu = g0[ui - 1][ui - 1] if ui > 0 else Fraction(0)
        gvv = g0[vj - 1][vj - 1]
        guv = g0[ui - 1][vj - 1] if ui > 0 else Fraction(0)
        exp_reff = guu + gvv - 2 * guv
        require_ok(
            reff == exp_reff and geff == Fraction(1) / exp_reff and ratio == geff / Fraction(w),
            "P3_EDGE_MATH_FAIL",
            "edge resistance/compounding mismatch",
        )
        foster_acc += Fraction(w) * reff
        ratios.append(ratio)

    foster_q = parse_canonical_rational(p3.get("foster_resistance_sum"), "foster_resistance_sum")
    require_ok(foster_q == foster_acc, "P3_FOSTER_MISMATCH", "Foster sum mismatch")
    require_ok(
        parse_canonical_rational(p3.get("min_compounding_ratio"), "min_compounding_ratio") == min(ratios)
        and parse_canonical_rational(p3.get("max_compounding_ratio"), "max_compounding_ratio") == max(ratios)
        and p3.get("all_45_edges_strictly_compounded") is True,
        "P3_EXTREMA_MISMATCH",
        "min/max compounding ratio or strict flag mismatch",
    )

    # Independent Order-2 (120 triangles) & Order-3 (210 tetrahedra Z_2 Bianchi) audit from edges
    tri_par: dict[tuple[int, int, int], int] = {}
    tri_counts = {
        "exact_transitive": 0,
        "conditional_consistent": 0,
        "frustrated_odd_obstruction": 0,
        "multi_wall_even_obstruction": 0,
    }
    for i in range(10):
        for j in range(i + 1, 10):
            for k in range(j + 1, 10):
                t_cls = (edge_cls_map[(i, j)], edge_cls_map[(i, k)], edge_cls_map[(j, k)])
                n_obs = sum(1 for c in t_cls if c == "EXACT_OBSTRUCTION")
                n_com = sum(1 for c in t_cls if c == "EXACT_COMMUTE")
                par = n_obs % 2
                tri_par[(i, j, k)] = par
                if par == 1:
                    tri_counts["frustrated_odd_obstruction"] += 1
                elif n_obs == 2:
                    tri_counts["multi_wall_even_obstruction"] += 1
                elif n_com == 3:
                    tri_counts["exact_transitive"] += 1
                else:
                    tri_counts["conditional_consistent"] += 1
    require_ok(
        p3.get("triangle_count") == 120 and p3.get("triangle_holonomy_counts") == tri_counts,
        "P3_TRIANGLE_MISMATCH",
        "triangle holonomy counts mismatch",
    )

    tet_zero = 0
    tet_dist = {"0": 0, "2": 0, "4": 0}
    for i in range(10):
        for j in range(i + 1, 10):
            for k in range(j + 1, 10):
                for l_idx in range(k + 1, 10):
                    f1 = tri_par[(i, j, k)]
                    f2 = tri_par[(i, j, l_idx)]
                    f3 = tri_par[(i, k, l_idx)]
                    f4 = tri_par[(j, k, l_idx)]
                    tet_zero += 1 - (f1 ^ f2 ^ f3 ^ f4)
                    tet_dist[str(f1 + f2 + f3 + f4)] += 1
    require_ok(
        p3.get("tetrahedron_count") == 210
        and p3.get("tetrahedral_bianchi_zero_count") == tet_zero
        and p3.get("tetrahedral_frustrated_face_distribution") == tet_dist,
        "P3_BIANCHI_MISMATCH",
        "tetrahedral Bianchi count or face distribution mismatch",
    )

    silo = p3.get("silo_cut_five_five")
    require_ok(type(silo) is dict, "BAD_P3_SILO", "silo_cut must be dict")
    require_ok(
        parse_canonical_rational(silo.get("edges_cut_fraction"), "cut_e") == Fraction(5, 9)
        and parse_canonical_rational(silo.get("triangles_cut_fraction"), "cut_t") == Fraction(5, 6)
        and parse_canonical_rational(silo.get("tetrahedra_cut_fraction"), "cut_tet") == Fraction(20, 21),
        "P3_SILO_CUT_MISMATCH",
        "5|5 silo-cut fractions mismatch",
    )
    cross = p3.get("cross_millennium_10x8_s83")
    require_ok(
        type(cross) is dict
        and _is_lower_hex64(cross.get("s83_cert_file_sha256"))
        and _is_lower_hex64(cross.get("s83_cert_digest"))
        and type(cross.get("pairs")) is list
        and len(cross["pairs"]) == 80,
        "P3_CROSS_MISMATCH",
        "10x8 cross-millennium section invalid",
    )
    seen_cross: set[tuple[str, str]] = set()
    cross_counts = {
        "EXACT_OPERATOR_ISOMORPHISM": 0,
        "CONDITIONAL_TRANSPOSITION": 0,
        "EXACT_LAW5_OBSTRUCTION": 0,
    }
    for pr in cross["pairs"]:
        require_ok(type(pr) is dict, "BAD_P3_CROSS_PAIR", "cross pair must be dict")
        c_id = pr.get("classical")
        m_id = pr.get("modern")
        mcls = pr.get("mapping_class")
        require_ok(
            type(c_id) is str
            and type(m_id) is str
            and c_id in _K10_NODE_IDX
            and m_id in _S83_NODE_IDS
            and (c_id, m_id) not in seen_cross
            and type(mcls) is str
            and mcls in _CROSS_CLASSES,
            "BAD_P3_CROSS_PAIR",
            "invalid or duplicate 10x8 cross pair",
        )
        seen_cross.add((c_id, m_id))
        cross_counts[mcls] += 1
    require_ok(
        cross.get("total_pairs") == 80 and cross.get("class_counts") == cross_counts,
        "P3_CROSS_COUNTS_MISMATCH",
        "10x8 cross-millennium counts mismatch",
    )

    # Pillar 4 Lean 4 & Law-4 novelty honesty audit
    p4 = payload["pillar4_lean4_and_novelty"]
    require_ok(type(p4) is dict, "BAD_P4_TYPE", "pillar4 must be dict")
    require_ok(
        _is_lower_hex64(p4.get("lean_sha256")) and hmac.compare_digest(p4["lean_sha256"], LEAN_FILE_SHA256),
        "BAD_P4_LEAN_SHA",
        "lean_sha256 pin mismatch",
    )
    require_ok(
        p4.get("theorem_count") == len(LEAN_THEOREMS),
        "BAD_P4_THM_COUNT",
        "theorem_count mismatch",
    )
    require_ok(
        p4.get("max_novelty_class") == "N1" and _is_strict_int(p4.get("n2_claims_count")) and p4["n2_claims_count"] == 0,
        "BAD_P4_NOVELTY",
        "Law-4 novelty lock violated",
    )
    return {"secondary_audit": "PASS", "edges_verified": 45, "foster_sum": "9", "cross_pairs": 80}


def verify_certificate_dict(cert: Any, *, full_replay: bool = True) -> dict[str, Any]:
    """
    Verify an in-memory Track S89 certificate dict (Surfaces FR1 & FR0).
      - full_replay=True  (FR1): envelope digests + secondary audit + full oracle replay check
      - full_replay=False (FR0): envelope digests + secondary audit only (no build_payload replay)
    """
    if type(full_replay) is not bool:
        raise S89Error("INVALID_FULL_REPLAY_FLAG", "full_replay must be strict bool")
    if type(cert) is not dict:
        raise S89Error("NON_DICT_CERT", "certificate must be strict dict")
    _check_container_safety(cert)
    payload = _verify_envelope_digests(cert)
    secondary_audit_payload(cert)
    if full_replay:
        replayed = build_payload()
        if not hmac.compare_digest(canonical_json_bytes(payload), canonical_json_bytes(replayed)):
            raise S89Error("REPLAY_MISMATCH", "payload does not match deterministic oracle replay")
    return cert


def check_certificate_file(path: Path, *, full_replay: bool = True) -> dict[str, Any]:
    raw = read_regular_file_bytes(path, max_bytes=MAX_JSON_BYTES)
    cert = parse_strict_json_bytes(raw, require_canonical=True)
    return verify_certificate_dict(cert, full_replay=full_replay)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Track S89 Islamic Scientific Heritage Atlas Verifier")
    mode = parser.add_mutually_exclusive_group(required=False)
    mode.add_argument("--standalone", action="store_true", help="Emit canonical certificate JSON to stdout")
    mode.add_argument("--write", type=Path, help="Atomically write 0o600 canonical certificate JSON")
    mode.add_argument("--check", type=Path, help="Verify canonical certificate JSON fail-closed")
    mode.add_argument("--verify-lean", type=Path, help="Run R10+ static + live Lean 4.36.0 verification")
    mode.add_argument("--verify-corpus", type=Path, help="Read-only verify live heritage text corpus dir")
    parser.add_argument("--inventory", type=Path, help="Path to file_inventory.json (with --verify-corpus)")
    parser.add_argument("--json", action="store_true", help="Emit compact JSON receipt")
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        if args.write is not None:
            cert = build_certificate()
            verify_certificate_dict(cert, full_replay=True)
            write_atomic_0600_bytes(args.write, canonical_json_bytes(cert) + b"\n")
            if args.json:
                sys.stdout.buffer.write(
                    canonical_json_bytes({"status": "WRITTEN", "certificate_sha256": cert["certificate_sha256"]}) + b"\n"
                )
            return 0
        if args.check is not None:
            cert = check_certificate_file(args.check, full_replay=True)
            if args.json:
                sys.stdout.buffer.write(
                    canonical_json_bytes({"status": "PASS", "certificate_sha256": cert["certificate_sha256"]}) + b"\n"
                )
            return 0
        if args.verify_lean is not None:
            res = verify_lean_file(args.verify_lean, check_pinned_sha=True)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res) + b"\n")
            return 0
        if args.verify_corpus is not None:
            require_ok(args.inventory is not None, "MISSING_INVENTORY_ARG", "--inventory is required with --verify-corpus")
            res = s89.verify_live_corpus_on_disk(args.verify_corpus, args.inventory)
            if args.json:
                sys.stdout.buffer.write(canonical_json_bytes(res) + b"\n")
            return 0
        cert = build_certificate()
        verify_certificate_dict(cert, full_replay=True)
        sys.stdout.buffer.write(canonical_json_bytes(cert) + b"\n")
        return 0
    except S89Error as exc:
        sys.stderr.write(f"ERROR [{exc.code}]: {exc.message}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

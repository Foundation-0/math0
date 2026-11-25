"""Zone-B R10+ hardened auditor & canonical certificate verifier for Track S82 (R2).

Provides:
  - Canonical-only exact rational (parse_q) & decimal (_parse_dec_str) parsers
    rejecting '-0', leading zeros, reducible fractions ('2/4', '3/1', '0/2'),
    Unicode digits, NaN/Inf, and >1000-digit DOS.
  - Hardened O_NOFOLLOW|O_NONBLOCK regular-file I/O with $PWD-aware dir_fd
    step-down atomic 0o600 writes + pre-replace lstat TOCTOU check + dir fsync.
  - Full R10+ Lean 4.36.0 static anti-bypass lexer (blocking import, notation/infix/
    prefix/postfix, declare_syntax_cat/syntax/elab/macro, guillemet-unwrapped debug.*,
    comment/whitespace-separated bang-strings, raw strings, unterminated literals/
    guillemets, initialize, run_cmd/run_meta, dbg_trace/throwError, native:=!false
    with zero FP on native:=false, exact-set #print axioms) + zero-TOCTOU private
    temp live execution pinned to VpVnpPropagationCerts.lean SHA-256.
  - Genuine 4-surface verification APIs: CLI (--check), FR1 (full_replay=True),
    FR0 (full_replay=False), and SEC (field-complete 39/39-leaf audit_certificate_semantics),
    enforcing strict bool full_replay, lowercase 64-hex + hmac.compare_digest.
"""

from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import hashlib
import hmac
import json
import math
import os
import re
import secrets
import shutil
import stat
import subprocess
import sys
import tempfile
from typing import Dict, List, Mapping, Optional, Sequence, Set, Tuple

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import s82_vpvnp_propagation_oracle as oracle

SCHEMA_VERSION = "s82-vpvnp-cross-field-propagation-v1"
EXPECTED_LEAN_SHA256 = "5c774b978e9eaf918edfd63b4d85d01ce0740b45469c7c48b934f85c380f1dd8"
MAX_INT_DIGITS = 1000
MAX_FILE_BYTES = 2 * 1024 * 1024
_MAX_JSON_DEPTH = 32
_MAX_INT_BITS = 3300
_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
_DEC_RE = re.compile(r"^-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?$")
ALLOWED_AXIOMS: Set[str] = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_LEAN_THEOREMS: Tuple[str, ...] = (
    "S82VpVnpPropagationCerts.strassen_2x2_exact_rerouting",
    "S82VpVnpPropagationCerts.strassen_exponent_strictly_subcubic",
    "S82VpVnpPropagationCerts.linear_code_rank_metric_non_euclidean",
    "S82VpVnpPropagationCerts.lem_F2_cnot1d_long_range_E03",
    "S82VpVnpPropagationCerts.cnot1d_involution",
    "S82VpVnpPropagationCerts.real_shear_minimal_poly_and_non_orthogonality",
    "S82VpVnpPropagationCerts.real_shear_kappa_exceeds_26_tenths",
    "S82VpVnpPropagationCerts.circularep_zero_residual_cancels_pole",
    "S82VpVnpPropagationCerts.m4_laurent_cutoff_valuation_bound",
    "S82VpVnpPropagationCerts.prop_N4_sigma_r_isolates_pole",
    "S82VpVnpPropagationCerts.prop_E10_unweighted_balanced_cut",
    "S82VpVnpPropagationCerts.weighted_moe_zipf_cut_beats_unweighted_floor",
    "S82VpVnpPropagationCerts.aletheia_v23_trust_gate_fail_closed",
)
_BANNED_LEAN_PATTERNS: Tuple[Tuple[str, re.Pattern[str]], ...] = (
    ("import", re.compile(r"\bimport\b")),
    ("sorry", re.compile(r"\b(?:sorry|sorryAx|mkSorry)\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"\baxiom\b")),
    ("opaque", re.compile(r"\bopaque\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("plus_native", re.compile(r"\+native\b")),
    ("native_assign", re.compile(r"\bnative\s*:=(?!\s*false\b)")),
    ("DecideConfig", re.compile(r"\bDecideConfig\b")),
    ("ofReduce", re.compile(r"\bofReduce(?:Bool|Nat)\b")),
    ("trustCompiler", re.compile(r"\btrustCompiler\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("csimp", re.compile(r"\bcsimp\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("partial", re.compile(r"\bpartial\b")),
    ("debug_opt", re.compile(r"\bdebug\s*\.")),
    ("elab", re.compile(r"\belab(?:_rules)?\b")),
    ("macro", re.compile(r"\bmacro(?:_rules)?\b")),
    ("syntax", re.compile(r"\b(?:declare_syntax_cat|syntax)\b")),
    ("notation", re.compile(r"\b(?:notation|prefix|infixl?|infixr|postfix)\b")),
    ("initialize", re.compile(r"\b(?:builtin_)?initialize\b")),
    ("hash_eval", re.compile(r"#eval\b")),
    ("hash_reduce", re.compile(r"#reduce\b")),
    ("hash_exit", re.compile(r"#exit\b")),
    ("run_cmd", re.compile(r"\brun_(?:cmd|meta)\b")),
    ("interp_kw", re.compile(r"\b(?:dbg_trace|throwError)\b")),
    ("non_axiom_print", re.compile(r"#print\s+(?!axioms\b)")),
)
_PRINT_AXIOMS_DECL_RE = re.compile(r"#print\s+axioms\s+([A-Za-z0-9_.]+)")
_AXIOM_NONE_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")
_AXIOM_LIST_RE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$")


class VerifyError(ValueError):
    """Typed fail-closed error for all I/O, schema, Lean, and oracle violations."""


def _is_ascii_digits(s: str) -> bool:
    if not s:
        return False
    for ch in s:
        if ch < "0" or ch > "9":
            return False
    return True


def parse_q(raw: object) -> Fraction:
    """Strictly parse a canonical exact integer or reduced 'p/q' rational string."""
    if type(raw) is not str:
        raise VerifyError("Rational value must be a string")
    parts = raw.split("/")
    if len(parts) > 2:
        raise VerifyError("Rational string must have at most one '/'")
    num_s = parts[0]
    neg = num_s.startswith("-")
    mag_s = num_s[1:] if neg else num_s
    if not _is_ascii_digits(mag_s) or len(mag_s) > MAX_INT_DIGITS:
        raise VerifyError("Invalid or oversized numerator in rational string")
    if len(mag_s) > 1 and mag_s[0] == "0":
        raise VerifyError("Non-canonical leading zero in numerator")
    num_val = -int(mag_s) if neg else int(mag_s)
    if neg and num_val == 0:
        raise VerifyError("Non-canonical negative zero '-0' rejected")
    if len(parts) == 1:
        return Fraction(num_val, 1)
    den_s = parts[1]
    if not _is_ascii_digits(den_s) or len(den_s) > MAX_INT_DIGITS:
        raise VerifyError("Invalid or oversized denominator in rational string")
    if den_s[0] == "0":
        raise VerifyError("Non-canonical leading zero in denominator")
    den_val = int(den_s)
    if den_val <= 1:
        raise VerifyError("Denominator must be an integer >= 2 in reduced 'p/q' form")
    if math.gcd(abs(num_val), den_val) != 1:
        raise VerifyError("Non-canonical reducible rational string rejected")
    return Fraction(num_val, den_val)


def _parse_dec_str(raw: object) -> Decimal:
    """Strictly parse a canonical ASCII decimal string without float conversion."""
    if type(raw) is not str or len(raw) > MAX_INT_DIGITS or not _DEC_RE.match(raw):
        raise VerifyError("Invalid canonical decimal string")
    return Decimal(raw)


def _validate_path(path: object) -> str:
    if type(path) is not str or not path:
        raise VerifyError("Path must be a non-empty string")
    if "\x00" in path:
        raise VerifyError("Path must not contain NUL bytes")
    try:
        path.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise VerifyError("Path contains invalid UTF-8 surrogate") from exc
    return path


def _open_parent_dir_fd(clean_path: str) -> Tuple[int, str]:
    """Step down ancestor directories using O_DIRECTORY|O_NOFOLLOW ($PWD-symlink-aware)."""
    if os.path.isabs(clean_path):
        abs_p = clean_path
    else:
        try:
            cwd = os.getcwd()
        except OSError as exc:
            raise VerifyError(f"Cannot resolve working directory: {exc}") from exc
        pwd = os.environ.get("PWD", "")
        if pwd.startswith(os.sep):
            try:
                if os.path.samefile(pwd, cwd):
                    cwd = pwd
            except OSError:
                pass
        abs_p = os.path.join(cwd, clean_path)
    parts = [p for p in abs_p.split(os.sep) if p]
    if not parts:
        raise VerifyError("Path must name a file")
    for p in parts:
        if p == "..":
            raise VerifyError("Path traversal '..' segments are disallowed")
    leaf = parts[-1]
    dir_parts = [p for p in parts[:-1] if p != "."]
    dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK
    cur_fd = -1
    try:
        cur_fd = os.open(os.sep, dir_flags)
        for comp in dir_parts:
            nxt_fd = os.open(comp, dir_flags, dir_fd=cur_fd)
            os.close(cur_fd)
            cur_fd = nxt_fd
        return cur_fd, leaf
    except OSError as exc:
        if cur_fd >= 0:
            try:
                os.close(cur_fd)
            except OSError:
                pass
        raise VerifyError(f"Parent directory step-down rejected: {exc}") from exc


def _read_bytes_safe(path: str, max_bytes: int = MAX_FILE_BYTES) -> bytes:
    clean_path = _validate_path(path)
    dir_fd, leaf = _open_parent_dir_fd(clean_path)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    fd = -1
    try:
        fd = os.open(leaf, flags, dir_fd=dir_fd)
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise VerifyError("Target path must be a regular file")
        if st.st_nlink != 1:
            raise VerifyError("Target file must not be hard-linked")
        if st.st_size > max_bytes:
            raise VerifyError("Target file exceeds maximum permitted size")
        chunks: List[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, 65536)
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise VerifyError("Target file grew beyond maximum permitted size")
            chunks.append(chunk)
        return b"".join(chunks)
    except VerifyError:
        raise
    except OSError as exc:
        raise VerifyError(f"Safe read failed: {exc}") from exc
    finally:
        if fd >= 0:
            try:
                os.close(fd)
            except OSError:
                pass
        try:
            os.close(dir_fd)
        except OSError:
            pass


def _check_target_leaf_safe(dir_fd: int, leaf: str) -> None:
    try:
        ex_st = os.lstat(leaf, dir_fd=dir_fd)
    except FileNotFoundError:
        return
    except OSError as exc:
        raise VerifyError(f"Cannot inspect existing target file: {exc}") from exc
    if not stat.S_ISREG(ex_st.st_mode) or ex_st.st_nlink != 1:
        raise VerifyError("Refusing to overwrite non-regular or hard-linked target")


def _write_bytes_atomic_safe(path: str, payload: bytes) -> None:
    clean_path = _validate_path(path)
    base = os.path.basename(clean_path)
    if not base or base in (".", ".."):
        raise VerifyError("Output path must name a regular file")
    dir_fd, leaf = _open_parent_dir_fd(clean_path)
    tmp_name = f".{leaf}.tmp.{secrets.token_hex(8)}"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK
    fd = -1
    try:
        _check_target_leaf_safe(dir_fd, leaf)
        try:
            fd = os.open(tmp_name, flags, 0o600, dir_fd=dir_fd)
        except OSError as exc:
            raise VerifyError(f"Cannot create atomic temp file: {exc}") from exc
        try:
            st = os.fstat(fd)
            if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
                raise VerifyError("Temp file failed regular/single-link invariant")
            view = memoryview(payload)
            written = 0
            while written < len(payload):
                n = os.write(fd, view[written:])
                if n <= 0:
                    raise VerifyError("Short write while writing atomic temp file")
                written += n
            os.fchmod(fd, 0o600)
            os.fsync(fd)
            os.close(fd)
            fd = -1
            _check_target_leaf_safe(dir_fd, leaf)
            os.replace(tmp_name, leaf, src_dir_fd=dir_fd, dst_dir_fd=dir_fd)
            os.fsync(dir_fd)
        except BaseException as exc:
            if fd >= 0:
                try:
                    os.close(fd)
                except OSError:
                    pass
            try:
                os.unlink(tmp_name, dir_fd=dir_fd)
            except OSError:
                pass
            if isinstance(exc, OSError):
                raise VerifyError(f"Atomic write failed: {exc}") from exc
            raise
    finally:
        try:
            os.close(dir_fd)
        except OSError:
            pass


def _skip_ws_and_comments(src: str, pos: int) -> int:
    """Advance past ASCII whitespace, line comments, and nested block comments."""
    n = len(src)
    k = pos
    while k < n:
        c = src[k]
        if c in " \t\r\n":
            k += 1
            continue
        if src.startswith("--", k):
            nl = src.find("\n", k + 2)
            k = n if nl < 0 else nl + 1
            continue
        if src.startswith("/-", k):
            depth = 1
            k += 2
            while depth > 0:
                nxt_c = src.find("-/", k)
                if nxt_c == -1:
                    raise VerifyError("Unterminated Lean block comment")
                nxt_o = src.find("/-", k, nxt_c)
                if nxt_o != -1:
                    depth += 1
                    k = nxt_o + 2
                else:
                    depth -= 1
                    k = nxt_c + 2
            continue
        break
    return k


def strip_lean_comments_and_literals(src: str) -> str:
    """R10+ Lean 4 lexer stripping comments/strings/Chars, unwrapping guillemets, blocking bang/raw strings."""
    out: List[str] = []
    n = len(src)
    i = 0
    block_depth = 0
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            nl = src.find("\n", i + 2)
            end = n if nl < 0 else nl
            out.append(" " * (end - i))
            i = end
            continue
        if ch == "!":
            k_bang = _skip_ws_and_comments(src, i + 1)
            if k_bang < n and src[k_bang] == '"':
                raise VerifyError("Interpolated bang-string literal disallowed in pure-Init Lean cert")
        if ch == "r" and (nxt == '"' or nxt == "#"):
            prev_r = src[i - 1] if i > 0 else " "
            if not (prev_r.isalnum() or prev_r == "_"):
                raise VerifyError("Raw string literal disallowed in pure-Init Lean cert")
        if ch == '"':
            out.append(" ")
            i += 1
            closed = False
            while i < n:
                c = src[i]
                if c == "\\":
                    out.append("  ")
                    i += 2
                    continue
                if c == '"':
                    out.append(" ")
                    i += 1
                    closed = True
                    break
                out.append("\n" if c == "\n" else " ")
                i += 1
            if not closed:
                raise VerifyError("Unterminated Lean string literal")
            continue
        if ch == "\u00ab":
            end_g = src.find("\u00bb", i + 1)
            if end_g == -1:
                raise VerifyError("Unterminated Lean guillemet identifier")
            out.append(" ")
            out.append(src[i + 1 : end_g])
            out.append(" ")
            i = end_g + 1
            continue
        prev_ch = src[i - 1] if i > 0 else " "
        if ch == "'" and not (prev_ch.isalnum() or prev_ch in "_'\u00bb!?"):
            j = i + 1
            if j < n and src[j] == "\\":
                j += 1
                if j < n and src[j] == "x":
                    j += 3
                elif j < n and src[j] == "u":
                    j += 5
                else:
                    j += 1
            else:
                j += 1
            if j < n and src[j] == "'":
                out.append(" " * (j - i + 1))
                i = j + 1
                continue
        out.append(ch)
        i += 1
    if block_depth != 0:
        raise VerifyError("Unterminated Lean block comment")
    return "".join(out)


def audit_lean_source(src: str) -> Dict[str, object]:
    """Run static R10+ anti-bypass checks on Lean 4 source text."""
    if type(src) is not str or not src.strip():
        raise VerifyError("Lean source must be non-empty")
    stripped = strip_lean_comments_and_literals(src)
    for tag, pat in _BANNED_LEAN_PATTERNS:
        if pat.search(stripped):
            raise VerifyError(f"Banned Lean construct detected: {tag}")
    declared_prints = _PRINT_AXIOMS_DECL_RE.findall(stripped)
    if len(declared_prints) != len(EXPECTED_LEAN_THEOREMS) or set(declared_prints) != set(EXPECTED_LEAN_THEOREMS):
        raise VerifyError("Static #print axioms declarations must exactly match EXPECTED_LEAN_THEOREMS")
    return {
        "static_clean": True,
        "expected_theorems_declared": len(EXPECTED_LEAN_THEOREMS),
    }


def _find_lean_binary() -> str:
    found = shutil.which("lean")
    if found:
        return found
    home = os.environ.get("HOME", "")
    if home:
        for rel in (".local/bin/lean", ".elan/bin/lean"):
            cand = os.path.join(home, rel)
            if os.path.isfile(cand) and os.access(cand, os.X_OK):
                return cand
    raise VerifyError("Lean 4 binary not found in PATH, ~/.local/bin/lean, or ~/.elan/bin/lean")


def _coalesce_axiom_lines(stdout: str) -> List[str]:
    """Join Lean 4 line-wrapped '#print axioms' brackets cleanly without swallowing noise."""
    joined: List[str] = []
    pending = ""
    for raw_line in stdout.splitlines():
        sline = raw_line.strip()
        if not sline:
            continue
        if pending:
            pending = f"{pending} {sline}"
            if "]" in sline:
                joined.append(pending)
                pending = ""
            continue
        if "depends on axioms: [" in sline and "]" not in sline:
            pending = sline
        else:
            joined.append(sline)
    if pending:
        joined.append(pending)
    return joined


def verify_lean_file(
    lean_path: str,
    timeout_sec: int = 60,
    *,
    require_pinned_sha: bool = True,
) -> Dict[str, object]:
    """Static R10+ audit + pinned-SHA check + zero-TOCTOU live Lean 4.36.0 execution."""
    if type(require_pinned_sha) is not bool:
        raise VerifyError("require_pinned_sha must be a bool")
    clean_path = _validate_path(lean_path)
    raw = _read_bytes_safe(clean_path)
    try:
        src = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerifyError(f"Lean file is not valid UTF-8: {exc}") from exc
    static_info = audit_lean_source(src)
    lean_sha256 = hashlib.sha256(raw).hexdigest()
    if require_pinned_sha and not hmac.compare_digest(lean_sha256, EXPECTED_LEAN_SHA256):
        raise VerifyError("Lean file SHA-256 does not match pinned certificate artifact")
    lean_bin = _find_lean_binary()
    clean_env = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "HOME": os.environ.get("HOME", ""),
        "OPENBLAS_NUM_THREADS": "1",
        "OMP_NUM_THREADS": "1",
    }
    try:
        with tempfile.TemporaryDirectory(prefix="s82_lean_") as td:
            snap_lean = os.path.join(td, "VpVnpPropagationCerts.lean")
            _write_bytes_atomic_safe(snap_lean, raw)
            proc = subprocess.run(
                [lean_bin, snap_lean],
                capture_output=True,
                text=True,
                timeout=timeout_sec,
                env=clean_env,
                check=False,
            )
    except (OSError, subprocess.SubprocessError) as exc:
        raise VerifyError(f"Live Lean invocation failed: {exc}") from exc
    if proc.returncode != 0:
        raise VerifyError(f"Lean exited with status {proc.returncode}")
    if proc.stderr.strip():
        raise VerifyError(f"Unexpected Lean stderr output: {proc.stderr.strip()[:200]}")
    if "warning:" in proc.stdout.lower():
        raise VerifyError("Lean emitted a compiler warning on stdout")

    observed: Dict[str, List[str]] = {}
    for sline in _coalesce_axiom_lines(proc.stdout):
        m_none = _AXIOM_NONE_RE.match(sline)
        if m_none:
            thm_name = m_none.group(1)
            if thm_name in observed:
                raise VerifyError(f"Duplicate axiom report for {thm_name}")
            observed[thm_name] = []
            continue
        m_list = _AXIOM_LIST_RE.match(sline)
        if m_list:
            thm_name = m_list.group(1)
            if thm_name in observed:
                raise VerifyError(f"Duplicate axiom report for {thm_name}")
            ax_raw = [tok.strip() for tok in m_list.group(2).split(",") if tok.strip()]
            for ax in ax_raw:
                if ax not in ALLOWED_AXIOMS:
                    raise VerifyError(f"Disallowed axiom {ax!r} in {thm_name}")
            observed[thm_name] = ax_raw
            continue
        raise VerifyError(f"Unexpected Lean stdout line: {sline[:160]}")

    if set(observed.keys()) != set(EXPECTED_LEAN_THEOREMS):
        raise VerifyError("Live Lean axiom report set does not exactly match EXPECTED_LEAN_THEOREMS")

    return {
        "static_clean": static_info["static_clean"],
        "lean_sha256": lean_sha256,
        "theorems_verified": len(EXPECTED_LEAN_THEOREMS),
        "axioms_by_theorem": observed,
    }


def _strict_parse_json_int(raw: str) -> int:
    mag = raw[1:] if raw.startswith("-") else raw
    if len(mag) > MAX_INT_DIGITS:
        raise VerifyError("JSON integer exceeds maximum digit limit")
    return int(raw)


def _reject_json_float(_raw: str) -> object:
    raise VerifyError("Floating-point literals are disallowed in certificate JSON")


def _reject_json_constant(_raw: str) -> object:
    raise VerifyError("Non-finite JSON constants are disallowed")


def _strict_json_object_pairs(pairs: Sequence[Tuple[str, object]]) -> Dict[str, object]:
    out: Dict[str, object] = {}
    for k, v in pairs:
        if k in out:
            raise VerifyError(f"Duplicate JSON object key rejected: {k!r}")
        out[k] = v
    return out


def _validate_plain_json_tree(obj: object) -> None:
    """Strictly enforce exact primitive/container types (blocks subclasses, floats, surrogates, DOS)."""
    stack: List[Tuple[object, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > _MAX_JSON_DEPTH:
            raise VerifyError("JSON nesting depth exceeds maximum permitted bound")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():  # type: ignore[union-attr]
                if type(k) is not str:
                    raise VerifyError("JSON object keys must be exact str")
                try:
                    k.encode("utf-8")
                except UnicodeEncodeError as exc:
                    raise VerifyError("JSON object key contains lone surrogate") from exc
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:  # type: ignore[union-attr]
                stack.append((item, depth + 1))
        elif t is int:
            if cur.bit_length() > _MAX_INT_BITS:  # type: ignore[union-attr]
                raise VerifyError("Integer value exceeds maximum bit-length bound")
        elif t is str:
            try:
                cur.encode("utf-8")  # type: ignore[union-attr]
            except UnicodeEncodeError as exc:
                raise VerifyError("JSON string value contains lone surrogate") from exc
        elif t is bool or cur is None:
            continue
        else:
            raise VerifyError(f"Disallowed or subclassed value type in certificate: {t.__name__}")


_CERT_SCHEMA: Dict[str, object] = {
    "schema_version": str,
    "payload_sha256": str,
    "payload": {
        "schema_version": str,
        "portal": str,
        "pillars_passed": int,
        "pillars": {
            "pillar_1_m1_m2_cat0_rerouting_codes": {
                "strassen_basis_checks": int,
                "strassen_rank_vs_naive": [int],
                "strassen_7_cubed_vs_8_cubed": [int],
                "hamming_8_4_4_min_distance": int,
                "hamming_16_11_4_parity_rank": int,
                "hamming_16_11_4_code_dim": int,
                "code_subspace_cat0_gram_det": str,
                "qkvo_crossing_ranks_n0_n16_x1": [int],
            },
            "pillar_2_m3_cnot1d_and_real_shear": {
                "synthesized_counts_by_n": {"n4": int, "n5": int, "n6": int, "n8": int},
                "total_cnot_circuits_verified": int,
                "max_endpoint1_gate_mult": int,
                "max_general_gate_mult": int,
                "cnot_0_to_7_gate_len": int,
                "real_shear_8x8_gram_trace": int,
                "real_shear_minpoly": str,
                "real_shear_kappa2_bracket_dec": [str],
                "wht_orthogonal_kappa2": str,
            },
            "pillar_3_m4_laurent_circularep_rocket": {
                "circularep_clean_eps0_grad_q": str,
                "circularep_lem_n2_cutoff_n": int,
                "circularep_dirty_pole_coeff_q": str,
                "prop_n4_r1_min_exp": int,
                "prop_n4_r3_min_exp": int,
                "prop_n4_r3_eps0_q": str,
                "bf16_normal_min_exp2": int,
                "bf16_4round_sigma3_exp2": int,
            },
            "pillar_4_m5_m6_moe_cheeger_trust_gates": {
                "moe_k_experts": int,
                "unweighted_prop_e10_floor_q": str,
                "unweighted_half_cut_q": str,
                "zipf1_cross_frac_dec": str,
                "zipf1_drop_vs_floor_dec": str,
                "zipf1_conductance_dec": str,
                "zipf2_cross_frac_dec": str,
                "zipf2_drop_vs_floor_dec": str,
                "zipf2_conductance_dec": str,
                "trust_gate_positive_passed": bool,
                "trust_gate_negative_controls_killed": int,
            },
        },
    },
}


def _check_schema(obj: object, spec: object) -> None:
    """Enforce exact keys and exact runtime types (blocks bool-for-int swaps & hollow payloads)."""
    if type(spec) is dict:
        if type(obj) is not dict or set(obj.keys()) != set(spec.keys()):
            raise VerifyError("Certificate object schema keys or type mismatch")
        for k, sub in spec.items():
            _check_schema(obj[k], sub)
    elif type(spec) is list:
        if type(obj) is not list:
            raise VerifyError("Certificate list schema type mismatch")
        elem_t = spec[0]
        for item in obj:
            if type(item) is not elem_t:
                raise VerifyError("Certificate list element type mismatch")
    elif type(obj) is not spec:
        raise VerifyError("Certificate leaf field type mismatch")


def _canonical_json_bytes(obj: Mapping[str, object]) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("utf-8")


def _compute_payload_sha256(payload: Mapping[str, object]) -> str:
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def audit_certificate_semantics(cert: object) -> Dict[str, object]:
    """Secondary semantic audit surface (SEC): enforces full 39/39 pillar-leaf invariants."""
    _validate_plain_json_tree(cert)
    _check_schema(cert, _CERT_SCHEMA)
    cert_d = cert  # type: ignore[assignment]
    payload = cert_d["payload"]
    if cert_d["schema_version"] != SCHEMA_VERSION or payload["schema_version"] != SCHEMA_VERSION:
        raise VerifyError("Certificate schema_version mismatch")
    if not _HEX64_RE.match(cert_d["payload_sha256"]):
        raise VerifyError("Certificate payload_sha256 must be lowercase 64-char hex")
    pillars = payload["pillars"]
    p1 = pillars["pillar_1_m1_m2_cat0_rerouting_codes"]
    p2 = pillars["pillar_2_m3_cnot1d_and_real_shear"]
    p3 = pillars["pillar_3_m4_laurent_circularep_rocket"]
    p4 = pillars["pillar_4_m5_m6_moe_cheeger_trust_gates"]

    kb = p2["real_shear_kappa2_bracket_dec"]
    if len(kb) != 2:
        raise VerifyError("real_shear_kappa2_bracket_dec must have exactly 2 endpoints")
    k_lo = _parse_dec_str(kb[0])
    k_hi = _parse_dec_str(kb[1])
    z1_c = _parse_dec_str(p4["zipf1_cross_frac_dec"])
    z1_d = _parse_dec_str(p4["zipf1_drop_vs_floor_dec"])
    z1_g = _parse_dec_str(p4["zipf1_conductance_dec"])
    z2_c = _parse_dec_str(p4["zipf2_cross_frac_dec"])
    z2_d = _parse_dec_str(p4["zipf2_drop_vs_floor_dec"])
    z2_g = _parse_dec_str(p4["zipf2_conductance_dec"])

    counts = p2["synthesized_counts_by_n"]
    exact_checks: Tuple[Tuple[object, object], ...] = (
        (payload["pillars_passed"], 4),
        (p1["strassen_basis_checks"], 16),
        (p1["strassen_rank_vs_naive"], [7, 8]),
        (p1["strassen_7_cubed_vs_8_cubed"], [343, 512]),
        (p1["hamming_8_4_4_min_distance"], 4),
        (p1["hamming_16_11_4_parity_rank"], 5),
        (p1["hamming_16_11_4_code_dim"], 11),
        (parse_q(p1["code_subspace_cat0_gram_det"]), Fraction(-1, 4)),
        (p1["qkvo_crossing_ranks_n0_n16_x1"], [1, 4, 4]),
        (counts, {"n4": 23, "n5": 72, "n6": 25, "n8": 64}),
        (p2["total_cnot_circuits_verified"], sum(counts.values())),
        (p2["max_endpoint1_gate_mult"], 4),
        (p2["max_general_gate_mult"], 16),
        (p2["real_shear_8x8_gram_trace"], 9),
        (p2["real_shear_minpoly"], "lambda^2 - 3*lambda + 1 = 0"),
        (parse_q(p2["wht_orthogonal_kappa2"]), Fraction(1)),
        (parse_q(p3["circularep_clean_eps0_grad_q"]), Fraction(-7, 3)),
        (p3["circularep_lem_n2_cutoff_n"], 8),
        (parse_q(p3["circularep_dirty_pole_coeff_q"]), Fraction(-1, 100)),
        (p3["prop_n4_r1_min_exp"], -1),
        (p3["prop_n4_r3_min_exp"], 0),
        (parse_q(p3["prop_n4_r3_eps0_q"]), Fraction(9, 4)),
        (p3["bf16_normal_min_exp2"], -126),
        (p3["bf16_4round_sigma3_exp2"], -162),
        (p4["moe_k_experts"], 128),
        (parse_q(p4["unweighted_prop_e10_floor_q"]), Fraction(2, 9)),
        (parse_q(p4["unweighted_half_cut_q"]), Fraction(1, 4)),
        (p4["trust_gate_positive_passed"], True),
        (p4["trust_gate_negative_controls_killed"], 6),
    )
    for actual, expected in exact_checks:
        if actual != expected:
            raise VerifyError("Semantic invariant check failed")

    order_checks: Tuple[bool, ...] = (
        p2["cnot_0_to_7_gate_len"] > 0,
        Decimal("2.6") < k_lo < k_hi < Decimal("2.7"),
        Decimal("0") < z2_c < z1_c < Decimal("0.222223"),
        z1_d > Decimal("2"),
        z2_d > Decimal("45"),
        Decimal("0.5") < z1_g < z2_g < Decimal("1"),
    )
    for ok_ord in order_checks:
        if not ok_ord:
            raise VerifyError("Semantic ordering invariant failed")
    return {"semantic_ok": True, "pillars_checked": 4}


def build_certificate() -> Dict[str, object]:
    """Run all 4 pure-Z/Q/F_2 Track S82 pillars and construct canonical certificate."""
    pillars = oracle.run_all_s82_oracles()
    payload: Dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "portal": "Portal 89 / Track S82 — Portal-78 (vp-vnp) Cross-Field Operator Propagation M1..M6",
        "pillars_passed": 4,
        "pillars": pillars,
    }
    digest = _compute_payload_sha256(payload)
    cert: Dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "payload_sha256": digest,
        "payload": payload,
    }
    audit_certificate_semantics(cert)
    return cert


def verify_certificate_dict(cert: object, *, full_replay: bool = True) -> Dict[str, object]:
    """Strictly verify certificate dict (FR1 full_replay=True; FR0 full_replay=False)."""
    if type(full_replay) is not bool:
        raise VerifyError("full_replay must be a bool")
    audit_certificate_semantics(cert)
    cert_d = cert  # type: ignore[assignment]
    digest: str = cert_d["payload_sha256"]
    payload: Mapping[str, object] = cert_d["payload"]
    if not hmac.compare_digest(_compute_payload_sha256(payload), digest):
        raise VerifyError("Certificate payload_sha256 digest mismatch")
    if full_replay:
        fresh = build_certificate()
        if cert != fresh:
            raise VerifyError("Certificate payload differs from clean-room recomputation")
    return {"ok": True, "payload_sha256": digest, "pillars_passed": 4}


def verify_certificate_file(cert_path: str, *, full_replay: bool = True) -> Dict[str, object]:
    if type(full_replay) is not bool:
        raise VerifyError("full_replay must be a bool")
    raw = _read_bytes_safe(cert_path)
    try:
        text = raw.decode("utf-8")
        parsed = json.loads(
            text,
            parse_int=_strict_parse_json_int,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
            object_pairs_hook=_strict_json_object_pairs,
        )
    except VerifyError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise VerifyError(f"Malformed certificate JSON: {exc}") from exc
    res = verify_certificate_dict(parsed, full_replay=full_replay)
    if raw != _canonical_json_bytes(parsed):
        raise VerifyError("Certificate file bytes are not in exact canonical JSON format")
    return res


def write_certificate_file(cert_path: str) -> Dict[str, object]:
    cert = build_certificate()
    _write_bytes_atomic_safe(cert_path, _canonical_json_bytes(cert))
    return {"ok": True, "payload_sha256": cert["payload_sha256"], "pillars_passed": 4}


def _default_dir() -> str:
    return os.path.dirname(os.path.abspath(__file__))


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    base_dir = _default_dir()
    default_cert = os.path.join(base_dir, "s82_vpvnp_propagation_certificate.json")
    default_lean = os.path.join(base_dir, "VpVnpPropagationCerts.lean")

    mode = ""
    as_json = False
    cert_path = default_cert
    lean_path = default_lean
    i = 0
    while i < len(args):
        tok = args[i]
        if tok in ("--standalone", "--write", "--check", "--verify-lean"):
            if mode:
                sys.stderr.write("Error: specify at most one primary mode flag\n")
                return 2
            mode = tok
            i += 1
            if tok in ("--write", "--check") and i < len(args) and not args[i].startswith("-"):
                cert_path = args[i]
                i += 1
            elif tok == "--verify-lean" and i < len(args) and not args[i].startswith("-"):
                lean_path = args[i]
                i += 1
        elif tok == "--json":
            as_json = True
            i += 1
        elif tok == "--cert" and i + 1 < len(args):
            cert_path = args[i + 1]
            i += 2
        elif tok == "--lean" and i + 1 < len(args):
            lean_path = args[i + 1]
            i += 2
        else:
            sys.stderr.write(f"Error: unknown or incomplete argument: {tok}\n")
            return 2

    if not mode:
        mode = "--standalone"

    try:
        if mode == "--standalone":
            cert = build_certificate()
            res = verify_certificate_dict(cert)
            out: Dict[str, object] = {"mode": "standalone", **res}
        elif mode == "--write":
            res = write_certificate_file(cert_path)
            out = {"mode": "write", **res}
        elif mode == "--check":
            res = verify_certificate_file(cert_path)
            out = {"mode": "check", **res}
        else:
            res = verify_lean_file(lean_path)
            out = {"mode": "verify-lean", "ok": True, **res}
    except (VerifyError, oracle.PropagationError) as exc:
        sys.stderr.write(f"Verification failed: {exc}\n")
        return 1

    if as_json:
        sys.stdout.write(json.dumps(out, sort_keys=True) + "\n")
    else:
        sys.stdout.write(f"PASS mode={out['mode']}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

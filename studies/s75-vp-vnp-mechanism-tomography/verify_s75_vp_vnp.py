"""Hardened standalone auditor & canonical certificate verifier for VP != VNP mechanism study.

Provides:
  - Strict canonical exact rational parser (`parse_q`) immune to CPython 4300-digit int DOS,
    Unicode digits, leading zeros, `-0`, `n/1`, and unreduced fractions.
  - Atomic `dir_fd` (`O_RDONLY | O_DIRECTORY | O_NOFOLLOW`) traversal + `$PWD` symlink check +
    `O_NOFOLLOW | O_NONBLOCK` regular-file I/O with `st_nlink == 1` & durable `0o600` atomic writes
    rejecting symlinks, FIFOs, directories, and hardlinks.
  - Full R9+ Lean 4.36.0 static anti-bypass tokenizer/scanner (raw strings, unary `!r`/`!s!`,
    interpolated strings `s!`/`f!`/`m!`, unknown `ident!"..."` bang strings, `import`,
    `macro`/`elab`/`syntax`, `debug.*`, `initialize`/`builtin_initialize`, multi-flag `decide`,
    balanced attributes) + multi-line `#print axioms` live kernel verifier with exact set equality.
  - Four genuine verification surfaces: CLI (`--check`), `FR1` (`full_replay=True`),
    `FR0` (`full_replay=False`), and `SEC` (`secondary_audit` / `secondary_audit_payload`).
"""

from __future__ import annotations

import errno
from fractions import Fraction
import hashlib
import hmac
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import stat
import subprocess
import sys
import threading
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

import s75_vp_vnp_mechanism_probe as probe

SCHEMA_VERSION = "s75-vp-vnp-mechanism-v1"
PORTAL_LABEL = "Portal 78 — anthropics/formal-math/vp-vnp"
MAX_INT_DIGITS = 1000
MAX_FILE_BYTES = 2 * 1024 * 1024
_MAX_JSON_DEPTH = 32
_MAX_INT_BITS = 3300
_READ_CHUNK_BYTES = 65_536
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_TEMP_NAME_LOCK = threading.Lock()
_TEMP_COUNTER = 0
_DARWIN_SYSTEM_ROOT_ALIASES: Tuple[Tuple[str, str], ...] = (
    ("/var", "/private/var"),
    ("/tmp", "/private/tmp"),
    ("/etc", "/private/etc"),
)

ALLOWED_AXIOMS: Set[str] = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_LEAN_THEOREMS: Tuple[str, ...] = (
    "S75VpVnpMechanismCerts.meixner_reciprocal_verified_5x5",
    "S75VpVnpMechanismCerts.meixner_orthogonality_verified_R5",
    "S75VpVnpMechanismCerts.remark_D3_rank_metric_non_euclidean",
    "S75VpVnpMechanismCerts.prop_E1_squarefree_factor2",
    "S75VpVnpMechanismCerts.prop_E1_char2_collapse",
    "S75VpVnpMechanismCerts.char2_hc3_separates_from_perm3_and_det3",
    "S75VpVnpMechanismCerts.char0_perm3_separates_from_det3",
    "S75VpVnpMechanismCerts.prop_E10_balanced_cut_bound",
    "S75VpVnpMechanismCerts.thm_E11_exponent_scaling",
    "S75VpVnpMechanismCerts.lem_F2_U4_rank1_word",
    "S75VpVnpMechanismCerts.sec25_boolean_garbage_vanishes_on_bits",
    "S75VpVnpMechanismCerts.sec25_boolean_garbage_corrupts_formal_deg3",
    "S75VpVnpMechanismCerts.lem_N2_cutoff_preserves_nonpositive_exponents",
    "S75VpVnpMechanismCerts.thm_K6_diagonalization_int",
    "S75VpVnpMechanismCerts.thm_K6_diagonalization_mod",
)

# ---------------------------------------------------------------------------
# Full R9+ Lean 4 Static Scanner Rules
# ---------------------------------------------------------------------------

_LEAN4_IDENT_EXTRA = "_.'"
_LEAN4_CHAR_PREV_IDENT = "_'»!?"
_LEAN4_HEX_DIGITS = frozenset("0123456789abcdefABCDEF")
_LEAN4_SIMPLE_GUILLEMET_INNER_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_']*\Z")
_LEAN4_GUILLEMET_IDENT_RE = re.compile(r"«([A-Za-z_][A-Za-z0-9_']*)»")

_LEAN4_HARD_LINE_RULES: Tuple[Tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\bsorry\b"), "LEAN4_SORRY"),
    (re.compile(r"\badmit\b"), "LEAN4_ADMIT"),
    (re.compile(r"(?<!\.)\baxiom\b"), "LEAN4_AXIOM"),
    (re.compile(r"(?<!\.)\bopaque\b"), "LEAN4_OPAQUE"),
    (re.compile(r"(?<!\.)\bunsafe\b"), "LEAN4_UNSAFE"),
    (re.compile(r"\bnative_decide\b"), "LEAN4_NATIVE_DECIDE"),
    (re.compile(r"\bsorryAx\b"), "LEAN4_SORRY_AX"),
    (re.compile(r"\bLean\.Meta\.mkSorry\b|\bmkSorry\b"), "LEAN4_MK_SORRY"),
    (re.compile(r"\bLean\.ofReduceBool\b|\bofReduceBool\b"), "LEAN4_OF_REDUCE_BOOL"),
    (re.compile(r"\bLean\.ofReduceNat\b|\bofReduceNat\b"), "LEAN4_OF_REDUCE_NAT"),
    (re.compile(r"\bLean\.trustCompiler\b|\btrustCompiler\b"), "LEAN4_TRUST_COMPILER"),
    (
        re.compile(
            r"(?<!\.)\b(?:macro|macro_rules|elab|elab_rules|syntax|dbg_trace|throwError|trace_goal)\b"
            r"|\b(?:Macro\.)?trace\s*\[|\binterpolatedStr\b"
        ),
        "LEAN4_META_SYNTAX_ESCAPE",
    ),
)
_LEAN4_PARTIAL_DECL_RE = re.compile(r"(?<!\.)\bpartial\s+(?:def|instance|abbrev)\b", flags=re.DOTALL)
_LEAN4_SKIP_KERNEL_TC_RE = re.compile(
    r"\bdebug\s*\.\s*(?:skipKernelTC|byAsSorry|proofAsSorry|terminalTacticsAsSorry)\b",
    flags=re.DOTALL,
)
_LEAN4_IMPORT_FULL_RE = re.compile(
    r"(?:^|\n)[ \t]*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)",
    flags=re.DOTALL,
)
_LEAN4_PRINT_AXIOMS_KW_BLOCK = (
    "def|theorem|lemma|axiom|inductive|structure|class|instance|opaque|abbrev|example|"
    "namespace|section|end|open|variable|universe|import|set_option|attribute|"
    "local|scoped|private|protected|noncomputable|partial|unsafe|meta|where|by|in|let|have"
)
_LEAN4_EVAL_SPOOF_RE = re.compile(
    r"#(?:eval!?(?![\w'!?])|reduce(?![\w'!?])|exit(?![\w'!?])|"
    r"print(?![\w'!?])(?!\s+axioms[ \t]+(?!(?:"
    + _LEAN4_PRINT_AXIOMS_KW_BLOCK
    + r")(?![\w'!?]))[A-Za-z_]))"
    r"|(?<!\.)\b(?:run_cmd|run_meta|initialize|builtin_initialize)\b",
    flags=re.DOTALL,
)
_LEAN4_ATTR_OPEN_RE = re.compile(r"(?:@|(?<!\.)\battribute\s*)\[", flags=re.DOTALL)
_LEAN4_HARD_ATTR_KW_RE = re.compile(r"\b(extern|implemented_by)\b")
_LEAN4_CSIMP_ATTR_KW_RE = re.compile(r"\b(csimp)\b")
_LEAN4_DECIDE_KW_RE = re.compile(r"\bdecide\b")
_LEAN4_FLAG_TOK_RE = re.compile(r"[+-][A-Za-z0-9_]+")
_LEAN4_OPT_PREFIX_RE = re.compile(r"\s*([A-Za-z0-9_]+)\s*:=")
_LEAN4_CONFIG_NATIVE_RE = re.compile(r"\bnative\b(?:\s*:=\s*([^},]*))?")
_LEAN4_CONFIG_AFTER_COMMA_RE = re.compile(r",\s*(?:\Z|[A-Za-z_][A-Za-z0-9_']*\s*:=)")
_LEAN4_CONFIG_WITH_RE = re.compile(r"\bwith\b")
_LEAN4_DECIDE_CONFIG_BIND_RE = re.compile(
    r"\b(?:DecideConfig|Decide\.Config)\b[ \t)]*:=\s*(?:\(\s*)*\{[^}{]*\bnative\s*:=\s*([^}{,]*)(?:,[^}{]*)?\}"
    r"|\{[^}{]*\bnative\s*:=\s*([^}{,]*)(?:,[^}{]*)?\}\s*:\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*(?:DecideConfig|Decide\.Config)\b"
    r"|\{[^}{]*\bnative\s*:=\s*([^}{,:]*)(?:,[^}{]*)?:\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*(?:DecideConfig|Decide\.Config)\b[^}{]*\}",
    flags=re.DOTALL,
)
_LEAN4_VACUOUS_THM_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+[A-Za-z0-9_.']+\b[^:\n]*:\s*(?:False\s*(?:→|->)|True\s*:=)"
)
_LEAN4_EXISTS_IMP_RE = re.compile(r"∃[^,\n]+,\s*(?!.*(?:∀|∧))[^,\n]*(?:→|->)")
_AXIOM_BLOCK_RE = re.compile(
    r"'([^']+)'\s+(?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]*)\])",
    flags=re.DOTALL,
)

# Strict schema keysets for field-complete FR0 & SEC secondary audit
_CERT_KEYS = frozenset({"schema_version", "payload_sha256", "payload"})
_PAYLOAD_KEYS = frozenset({"schema_version", "portal", "oracles_passed", "oracles"})
_ORACLES_KEYS = frozenset({
    "oracle_1_meixner_crossing",
    "oracle_2_cat0_mat_f2_dichotomy",
    "oracle_3_flat_perm_and_hubs",
    "oracle_4_char2_perm_vs_hc_and_s41",
    "oracle_5_contracting_unitriangular",
    "oracle_6_lowdeg_parse_tree_and_diag",
    "oracle_7_border_laurent_closure",
})
_O1_KEYS = frozenset({
    "ad_bc_rank_profile",
    "max_ad_bc_rank",
    "max_deg_psi",
    "orth_checks",
    "p_energy_0_to_6",
    "recip_checks",
    "reflection_checks",
    "theta",
    "x1_matched_count",
    "x1_sign",
})
_O2_KEYS = frozenset({
    "cube_pairs_verified",
    "mat2_rank_hist",
    "mat3_rank_hist",
    "non_euclidean_gram_det",
    "non_euclidean_quad_form",
    "tree_cn_gap",
})
_O3_KEYS = frozenset({
    "balanced_cuts_checked",
    "char2_cleared_perm_mod2",
    "char2_true_sum_mod2",
    "direct_grid_sum",
    "exponent_scaling_checks",
    "f31_monomial_count",
    "fp_matches",
    "min_81_normsq_over_k3",
    "perm_q_exact",
    "prop_e1_matrix_dim",
})
_O4_KEYS = frozenset({
    "char2_3x3_det_perm_hc",
    "char2_4x4_det_perm_hc",
    "prop_m2_direct_sum",
    "prop_m2_hc_exact_z",
    "prop_m2_mod_checks",
    "prop_m2_vertices",
    "s41_polya_3x3_valid_sign_maps",
})
_O5_KEYS = frozenset({
    "max_endpoint1_gen_mult",
    "max_general_gen_mult",
    "sl3_tower_commutator_checks",
    "u4_u5_endpoint1_checked",
    "u4_u5_general_rank1_checked",
})
_O6_KEYS = frozenset({
    "boolean_f_deg3_terms",
    "boolean_g_deg3_terms",
    "boolean_points_identical",
    "finite_field_squaring_periods",
    "output_degree",
    "rings_verified",
})
_O7_KEYS = frozenset({
    "lem_n2_cutoff_n",
    "lem_n2_rings_verified",
    "lem_n3_cover_n32_lhs",
    "lem_n3_cover_n32_rhs",
    "prop_n4_eps0_after_sigma_r",
    "prop_n4_min_exp_after_sigma_r",
    "prop_n4_mod_2w_extracted_eps0",
    "prop_n4_sigma_r",
})


class VerifyError(ValueError):
    """Typed fail-closed error for all I/O, schema, Lean, and oracle violations."""


# ---------------------------------------------------------------------------
# Strict Canonical Rational, Hex Digest & Path Primitives
# ---------------------------------------------------------------------------

def _parse_canonical_ascii_int(s: str, *, allow_negative: bool = True) -> int:
    neg = s.startswith("-")
    if neg and not allow_negative:
        raise VerifyError("Negative sign disallowed here")
    mag = s[1:] if neg else s
    if not mag or len(mag) > MAX_INT_DIGITS:
        raise VerifyError("Invalid or oversized integer token")
    if len(mag) > 1 and mag[0] == "0":
        raise VerifyError("Leading zeros are disallowed in canonical integer token")
    for ch in mag:
        if ch not in _ASCII_DIGITS:
            raise VerifyError("Non-ASCII digit in integer token")
    if neg and mag == "0":
        raise VerifyError("Negative zero '-0' is disallowed")
    val = 0
    for ch in mag:
        val = val * 10 + (ord(ch) - 48)
    res = -val if neg else val
    if res.bit_length() > _MAX_INT_BITS:
        raise VerifyError("Integer exceeds maximum bit-length bound")
    return res


def parse_q(raw: object) -> Fraction:
    """Strictly parse a canonical exact integer or reduced 'p/q' (q > 1) rational string."""
    if type(raw) is not str:
        raise VerifyError("Rational value must be a string")
    if "/" not in raw:
        return Fraction(_parse_canonical_ascii_int(raw, allow_negative=True), 1)
    parts = raw.split("/")
    if len(parts) != 2:
        raise VerifyError("Rational string must have at most one '/'")
    num_val = _parse_canonical_ascii_int(parts[0], allow_negative=True)
    den_val = _parse_canonical_ascii_int(parts[1], allow_negative=False)
    if den_val <= 1:
        raise VerifyError("Canonical rational denominator must be > 1")
    q = Fraction(num_val, den_val)
    if q.denominator != den_val:
        raise VerifyError("Rational string must be reduced to lowest terms")
    return q


def _require_sha256_hex(val: object, label: str) -> str:
    if type(val) is not str or len(val) != 64:
        raise VerifyError(f"{label} must be 64-char lowercase hex")
    for ch in val:
        if ch not in _HEX_LOWER:
            raise VerifyError(f"{label} must be 64-char lowercase hex")
    return val


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


def _open_dir_chain_nofollow(parts: Tuple[str, ...]) -> int:
    try:
        cur_fd = os.open("/", _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise VerifyError(f"Cannot open directory root: {exc}") from exc
    for comp in parts:
        if comp in ("", "."):
            continue
        if comp == "..":
            os.close(cur_fd)
            raise VerifyError("Path traversal '..' segments are disallowed")
        try:
            next_fd = os.open(comp, _DIR_OPEN_FLAGS, dir_fd=cur_fd)
        except OSError as exc:
            is_sym = exc.errno == errno.ELOOP
            if exc.errno == errno.ENOTDIR:
                try:
                    is_sym = stat.S_ISLNK(os.lstat(comp, dir_fd=cur_fd).st_mode)
                except OSError:
                    is_sym = False
            os.close(cur_fd)
            if is_sym:
                raise VerifyError(f"Symlink component rejected: {comp!r}") from exc
            if exc.errno == errno.ENOTDIR:
                raise VerifyError(f"Output parent must be a real directory: {comp!r}") from exc
            raise VerifyError(f"Directory unavailable: {exc}") from exc
        os.close(cur_fd)
        cur_fd = next_fd
    return cur_fd


def _verify_pwd_not_symlink() -> None:
    pwd = os.environ.get("PWD")
    if not pwd or not pwd.startswith("/"):
        return
    _validate_path(pwd)
    try:
        st_dot = os.stat(".")
    except OSError as exc:
        raise VerifyError(f"Cannot stat current directory: {exc}") from exc
    try:
        st_logical = os.stat(pwd)
    except OSError:
        return
    if (st_logical.st_dev, st_logical.st_ino) != (st_dot.st_dev, st_dot.st_ino):
        return
    norm_pwd = _normalize_darwin_system_prefix(Path(pwd), allow_exact=True)
    parts = tuple(p for p in norm_pwd.parts if p != "/")
    dfd = _open_dir_chain_nofollow(parts)
    try:
        st_pwd = os.fstat(dfd)
    finally:
        os.close(dfd)
    if (st_pwd.st_dev, st_pwd.st_ino) != (st_dot.st_dev, st_dot.st_ino):
        raise VerifyError("$PWD changed during symlink verification")


def _open_parent_dir_fd(clean_path: str) -> Tuple[int, str]:
    if os.path.basename(clean_path) in ("", ".", ".."):
        raise VerifyError("Output path must name a regular file")
    path_obj = Path(clean_path)
    if path_obj.is_absolute():
        norm = _normalize_darwin_system_prefix(path_obj)
        parts = tuple(p for p in norm.parts if p != "/")
        return (_open_dir_chain_nofollow(parts[:-1]), parts[-1])
    _verify_pwd_not_symlink()
    try:
        cwd = os.getcwd()
    except OSError as exc:
        raise VerifyError(f"Cannot resolve working directory: {exc}") from exc
    norm_cwd = _normalize_darwin_system_prefix(Path(cwd), allow_exact=True)
    full_parts = tuple(p for p in norm_cwd.parts if p != "/") + path_obj.parts
    return (_open_dir_chain_nofollow(full_parts[:-1]), full_parts[-1])


def _read_bytes_safe(path: str, max_bytes: int = MAX_FILE_BYTES) -> bytes:
    """Read regular non-symlink non-hardlinked file via atomic dir_fd + O_NOFOLLOW + O_NONBLOCK."""
    clean_path = _validate_path(path)
    dfd, fname = _open_parent_dir_fd(clean_path)
    try:
        flags = os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_NONBLOCK", 0)
        try:
            fd = os.open(fname, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise VerifyError(f"Symlink target rejected: {fname!r}") from exc
            raise VerifyError(f"Safe read failed: {exc}") from exc
        try:
            try:
                st = os.fstat(fd)
            except OSError as exc:
                raise VerifyError(f"Safe read fstat failed: {exc}") from exc
            if not stat.S_ISREG(st.st_mode):
                raise VerifyError("Target path must be a regular file")
            if st.st_nlink > 1:
                raise VerifyError("Target file must not be hard-linked")
            chunks: List[bytes] = []
            total = 0
            while True:
                try:
                    chunk = os.read(fd, _READ_CHUNK_BYTES)
                except OSError as exc:
                    raise VerifyError(f"Safe read failed: {exc}") from exc
                if not chunk:
                    break
                total += len(chunk)
                if total > max_bytes:
                    raise VerifyError("Target file exceeds maximum permitted size")
                chunks.append(chunk)
            return b"".join(chunks)
        finally:
            os.close(fd)
    finally:
        os.close(dfd)


def _next_temp_name(base_name: str) -> str:
    global _TEMP_COUNTER
    with _TEMP_NAME_LOCK:
        _TEMP_COUNTER += 1
        seq = _TEMP_COUNTER
    return f".{base_name}.tmp.{os.getpid()}.{seq}.{secrets.token_hex(8)}"


def _write_bytes_atomic_safe(path: str, payload: bytes) -> None:
    """Durable 0o600 atomic write via dir_fd, refusing symlinks, FIFOs, dirs, and hardlinks."""
    clean_path = _validate_path(path)
    dfd, fname = _open_parent_dir_fd(clean_path)
    tmp_name: Optional[str] = None
    tmp_fd: Optional[int] = None
    try:
        try:
            lst = os.lstat(fname, dir_fd=dfd)
        except FileNotFoundError:
            lst = None
        except OSError as exc:
            raise VerifyError(f"Cannot inspect write target: {exc}") from exc
        if lst is not None:
            if stat.S_ISLNK(lst.st_mode):
                raise VerifyError("Refusing symlink write target")
            if not stat.S_ISREG(lst.st_mode):
                raise VerifyError("Refusing non-regular write target")
            if lst.st_nlink > 1:
                raise VerifyError("Refusing hard-linked write target")

        create_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
        for _ in range(32):
            cand = _next_temp_name(fname)
            try:
                tmp_fd = os.open(cand, create_flags, 0o600, dir_fd=dfd)
                tmp_name = cand
                break
            except FileExistsError:
                continue
            except OSError as exc:
                raise VerifyError(f"Cannot create atomic temp file: {exc}") from exc
        if tmp_fd is None:
            raise VerifyError("Exhausted temp filename retries")

        try:
            view = memoryview(payload)
            written = 0
            while written < len(payload):
                n = os.write(tmp_fd, view[written:])
                if n <= 0:
                    raise VerifyError("Short write while writing atomic temp file")
                written += n
            os.fchmod(tmp_fd, 0o600)
            os.fsync(tmp_fd)
            st_tmp = os.fstat(tmp_fd)
            if not stat.S_ISREG(st_tmp.st_mode) or st_tmp.st_nlink != 1:
                raise VerifyError("Temp file failed regular/single-link invariant")
            os.close(tmp_fd)
            tmp_fd = None

            try:
                lst2 = os.lstat(fname, dir_fd=dfd)
            except FileNotFoundError:
                lst2 = None
            if lst2 is not None:
                if stat.S_ISLNK(lst2.st_mode):
                    raise VerifyError("Symlink appeared at write target")
                if not stat.S_ISREG(lst2.st_mode):
                    raise VerifyError("Non-regular file appeared at write target")
                if lst2.st_nlink > 1:
                    raise VerifyError("Hard-link appeared at write target")

            os.replace(tmp_name, fname, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except VerifyError:
            raise
        except OSError as exc:
            raise VerifyError(f"Atomic write failed: {exc}") from exc
    finally:
        if tmp_fd is not None:
            os.close(tmp_fd)
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Full R9+ Lean 4 Lexer, Static Anti-Bypass Scanner & Live Kernel Verifier
# ---------------------------------------------------------------------------

def _is_lean4_ident_prev(source: str, pos: int) -> bool:
    """True iff `source[pos]` continues a Lean 4 identifier (distinguishes `foo!r` from unary `!r`)."""
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


def _is_lean4_native_rhs_false_span(text: str, lo: int, hi: int) -> bool:
    s = text[lo:hi].strip()
    while s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    return s in ("false", "Bool.false")


def _is_lean4_safe_config_span(text: str, lo: int, hi: int, match_rparen: Dict[int, int]) -> bool:
    while lo < hi:
        sub = text[lo:hi]
        lo += len(sub) - len(sub.lstrip())
        hi -= len(sub) - len(sub.rstrip())
        if match_rparen.get(lo) == hi - 1:
            lo += 1
            hi -= 1
            continue
        break
    span = text[lo:hi]
    if not (span.startswith("{") and span.endswith("}")):
        return False
    body_lo = lo + 1
    body_hi = hi - 1
    body = text[body_lo:body_hi]
    if "{" in body or "}" in body:
        return False
    if _LEAN4_CONFIG_WITH_RE.search(text, body_lo, body_hi) is not None:
        return False
    for m_nv in _LEAN4_CONFIG_NATIVE_RE.finditer(text, body_lo, body_hi):
        if not _is_lean4_native_rhs_false_span(text, m_nv.start(1), m_nv.end(1)):
            return False
        sep = m_nv.end()
        if sep != body_hi and not _LEAN4_CONFIG_AFTER_COMMA_RE.match(text, sep, body_hi):
            return False
    return True


def _scan_lean4_decide_native(cleaned: str) -> List[Tuple[int, int]]:
    if "decide" not in cleaned:
        return []
    n = len(cleaned)
    match_rparen: Dict[int, int] = {}
    paren_stack: List[int] = []
    for idx, ch in enumerate(cleaned):
        if ch == "(":
            paren_stack.append(idx)
        elif ch == ")" and paren_stack:
            match_rparen[paren_stack.pop()] = idx

    spans: List[Tuple[int, int]] = []
    for m_dec in _LEAN4_DECIDE_KW_RE.finditer(cleaned):
        start = m_dec.start()
        pos = m_dec.end()
        native_hit = False
        while True:
            ws = pos
            while ws != n and cleaned[ws].isspace():
                ws += 1
            if ws == n:
                break
            ch = cleaned[ws]
            if ch in "+-":
                m_flag = _LEAN4_FLAG_TOK_RE.match(cleaned, ws)
                if m_flag is None:
                    break
                if m_flag.group(0) == "+native":
                    native_hit = True
                pos = m_flag.end()
                continue
            if ch == "(":
                close_idx = match_rparen.get(ws)
                if close_idx is None:
                    break
                m_pfx = _LEAN4_OPT_PREFIX_RE.match(cleaned, ws + 1, close_idx)
                if m_pfx is None:
                    break
                opt_key = m_pfx.group(1)
                rhs_lo = m_pfx.end()
                if opt_key == "native":
                    if not _is_lean4_native_rhs_false_span(cleaned, rhs_lo, close_idx):
                        native_hit = True
                elif opt_key == "config":
                    if not _is_lean4_safe_config_span(cleaned, rhs_lo, close_idx, match_rparen):
                        native_hit = True
                pos = close_idx + 1
                continue
            break
        if native_hit:
            spans.append((start, pos))
    return spans


def _iter_lean4_attr_blocks(cleaned: str) -> List[Tuple[int, int, int]]:
    match_rbrack: Dict[int, int] = {}
    brack_stack: List[int] = []
    for idx, ch in enumerate(cleaned):
        if ch == "[":
            brack_stack.append(idx)
        elif ch == "]" and brack_stack:
            match_rbrack[brack_stack.pop()] = idx
    blocks: List[Tuple[int, int, int]] = []
    for m_open in _LEAN4_ATTR_OPEN_RE.finditer(cleaned):
        lb = m_open.end() - 1
        rb = match_rbrack.get(lb)
        if rb is not None:
            blocks.append((m_open.start(), lb + 1, rb))
    return blocks


def _match_lean4_char_literal_end(source: str, i: int, n: int) -> Optional[int]:
    if i + 2 < n and source[i + 1] != "\\" and source[i + 1] != "\n" and source[i + 2] == "'":
        return i + 3
    if i + 3 < n and source[i + 1] == "\\":
        if source[i + 3] == "'" and source[i + 2] != "\n":
            return i + 4
        esc = source[i + 2]
        if (
            esc == "x"
            and i + 5 < n
            and source[i + 5] == "'"
            and all(c in _LEAN4_HEX_DIGITS for c in source[i + 3 : i + 5])
        ):
            return i + 6
        if (
            esc == "u"
            and i + 7 < n
            and source[i + 7] == "'"
            and all(c in _LEAN4_HEX_DIGITS for c in source[i + 3 : i + 7])
        ):
            return i + 8
    return None


def strip_lean_comments_and_literals(src: str) -> str:
    """R9+ state-machine Lean 4 lexer stripping comments/strings/raw/interp/char/guillemets fail-closed."""
    out: List[str] = []
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    in_interp = False
    pending_interp = False
    interp_stack: List[List[int]] = []
    raw_hashes = -1
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
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
            if src.startswith(close_seq, i):
                out.append(" " * len(close_seq))
                i += len(close_seq)
                raw_hashes = -1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_str:
            if ch == "\\":
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
                interp_stack.append([1])
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
        if interp_stack:
            if ch == "{":
                pending_interp = False
                interp_stack[-1][0] += 1
                out.append(ch)
                i += 1
                continue
            if ch == "}":
                pending_interp = False
                interp_stack[-1][0] -= 1
                out.append(ch)
                i += 1
                if interp_stack[-1][0] == 0:
                    interp_stack.pop()
                    in_interp = True
                continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            nl = src.find("\n", i + 2)
            end_c = n if nl == -1 else nl
            out.append(" " * (end_c - i))
            i = end_c
        elif ch == "r" and not _is_lean4_ident_prev(src, i - 1):
            pending_interp = False
            j = i + 1
            while j < n and src[j] == "#":
                j += 1
            if j < n and src[j] == '"':
                raw_hashes = j - (i + 1)
                out.append(" " * (j - i + 1))
                i = j + 1
            else:
                out.append(ch)
                i += 1
        elif ch == "!" and i >= 1 and src[i - 1] in "smf" and not _is_lean4_ident_prev(src, i - 2):
            pending_interp = True
            out.append(ch)
            i += 1
        elif ch == '"':
            if pending_interp:
                in_interp = True
                pending_interp = False
            else:
                if _is_lean4_ident_prev(src, i - 2) and src[i - 1] == "!":
                    is_panic = src.endswith("panic!", 0, i) and not _is_lean4_ident_prev(src, i - 7)
                    if not is_panic:
                        raise VerifyError("Banned Lean construct detected: LEAN4_UNKNOWN_BANG_STRING")
                in_str = True
            out.append(" ")
            i += 1
        elif ch == "«":
            pending_interp = False
            end_g = src.find("»", i + 1)
            if end_g == -1:
                raise VerifyError("Unterminated Lean guillemet identifier")
            inner = src[i + 1 : end_g]
            if _LEAN4_SIMPLE_GUILLEMET_INNER_RE.match(inner) is not None and inner != "axioms":
                out.append(src[i : end_g + 1])
            else:
                out.append(" " + "".join("\n" if c == "\n" else " " for c in inner) + " ")
            i = end_g + 1
        elif ch == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in _LEAN4_CHAR_PREV_IDENT)):
            pending_interp = False
            char_end = _match_lean4_char_literal_end(src, i, n)
            if char_end is not None:
                out.append(" " * (char_end - i))
                i = char_end
            else:
                out.append(ch)
                i += 1
        else:
            if not ch.isspace():
                pending_interp = False
            out.append(ch)
            i += 1
    if depth > 0:
        raise VerifyError("Unterminated Lean block comment")
    if in_str or in_interp or raw_hashes >= 0 or interp_stack:
        raise VerifyError("Unterminated Lean string literal")
    return "".join(out)


def audit_lean_source(src: str) -> Dict[str, object]:
    """Run full R9+ static anti-bypass checks on Lean 4 source text."""
    if type(src) is not str or not src.strip():
        raise VerifyError("Lean source must be non-empty")
    cleaned = strip_lean_comments_and_literals(src)
    cleaned = _LEAN4_GUILLEMET_IDENT_RE.sub(r"\1", cleaned)

    for line in cleaned.splitlines():
        for pat, code in _LEAN4_HARD_LINE_RULES:
            if pat.search(line):
                raise VerifyError(f"Banned Lean construct detected: {code}")
        if _LEAN4_VACUOUS_THM_RE.search(line):
            raise VerifyError("Banned Lean construct detected: LEAN4_VACUOUS_SIGNATURE_NOTICE")
        if _LEAN4_EXISTS_IMP_RE.search(line):
            raise VerifyError("Banned Lean construct detected: LEAN4_EXISTS_IMPLICATION_NOTICE")

    if _LEAN4_IMPORT_FULL_RE.search(cleaned) is not None:
        raise VerifyError("Banned Lean construct detected: LEAN4_FORBIDDEN_IMPORT")
    if _LEAN4_PARTIAL_DECL_RE.search(cleaned) is not None:
        raise VerifyError("Banned Lean construct detected: LEAN4_PARTIAL")
    if _LEAN4_SKIP_KERNEL_TC_RE.search(cleaned) is not None:
        raise VerifyError("Banned Lean construct detected: LEAN4_SKIP_KERNEL_TC")
    if _LEAN4_EVAL_SPOOF_RE.search(cleaned) is not None:
        raise VerifyError("Banned Lean construct detected: LEAN4_EVAL_SPOOF")

    decide_spans = _scan_lean4_decide_native(cleaned)
    if decide_spans:
        raise VerifyError("Banned Lean construct detected: LEAN4_DECIDE_NATIVE")
    for m_dc in _LEAN4_DECIDE_CONFIG_BIND_RE.finditer(cleaned):
        if any(grp is not None and not _is_lean4_native_rhs_false_span(grp, 0, len(grp)) for grp in m_dc.groups()):
            raise VerifyError("Banned Lean construct detected: LEAN4_DECIDE_NATIVE")

    for _, b_lo, b_hi in _iter_lean4_attr_blocks(cleaned):
        if _LEAN4_HARD_ATTR_KW_RE.search(cleaned, b_lo, b_hi) is not None:
            raise VerifyError("Banned Lean construct detected: LEAN4_ATTR_TRUST_ESCAPE")
        if _LEAN4_CSIMP_ATTR_KW_RE.search(cleaned, b_lo, b_hi) is not None:
            raise VerifyError("Banned Lean construct detected: LEAN4_CSIMP_REWRITE_NOTICE")

    for thm in EXPECTED_LEAN_THEOREMS:
        if f"#print axioms {thm}" not in cleaned:
            raise VerifyError(f"Missing required #print axioms declaration for {thm}")
    return {
        "static_clean": True,
        "expected_theorems_declared": len(EXPECTED_LEAN_THEOREMS),
    }


def _find_lean_binary() -> str:
    env_lean = os.environ.get("LEAN_BIN", "")
    if os.path.isfile(env_lean) and os.access(env_lean, os.X_OK):
        return env_lean
    found = shutil.which("lean")
    if found:
        return found
    home = os.environ.get("HOME", "")
    if home:
        cand = os.path.join(home, ".local", "bin", "lean")
        if os.path.isfile(cand) and os.access(cand, os.X_OK):
            return cand
    raise VerifyError("Lean 4 binary not found in PATH or ~/.local/bin/lean")


def _parse_lean_axioms_stdout(stdout_text: str) -> Dict[str, List[str]]:
    """Strictly parse multi-line Lean 4.36.0 `#print axioms` output; reject warnings, stray text, & duplicates."""
    observed: Dict[str, List[str]] = {}
    spans: List[Tuple[int, int]] = []
    for m_ax in _AXIOM_BLOCK_RE.finditer(stdout_text):
        spans.append((m_ax.start(), m_ax.end()))
        thm_name = m_ax.group(1)
        if thm_name in observed:
            raise VerifyError(f"Duplicate axiom report for {thm_name!r}")
        if m_ax.group(2) is not None:
            observed[thm_name] = []
        else:
            ax_raw = [tok.strip() for tok in m_ax.group(3).split(",") if tok.strip()]
            for ax in ax_raw:
                if ax not in ALLOWED_AXIOMS:
                    raise VerifyError(f"Disallowed axiom {ax!r} in {thm_name}")
            observed[thm_name] = ax_raw

    cursor = 0
    leftover: List[str] = []
    for s_lo, s_hi in spans:
        leftover.append(stdout_text[cursor:s_lo])
        cursor = s_hi
    leftover.append(stdout_text[cursor:])
    if "".join(leftover).strip():
        raise VerifyError("Unexpected Lean stdout output or compiler warning")
    if set(observed.keys()) != set(EXPECTED_LEAN_THEOREMS):
        raise VerifyError("Live Lean axiom theorem set does not match expected manifest")
    return observed


def verify_lean_file(lean_path: str, timeout_sec: int = 60) -> Dict[str, object]:
    """Full R9+ static audit + live Lean 4.36.0 kernel execution & strict multi-line axiom audit."""
    clean_path = _validate_path(lean_path)
    raw = _read_bytes_safe(clean_path)
    try:
        src = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerifyError(f"Lean file is not valid UTF-8: {exc}") from exc
    static_info = audit_lean_source(src)
    lean_bin = _find_lean_binary()
    clean_env = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "HOME": os.environ.get("HOME", ""),
        "OPENBLAS_NUM_THREADS": "1",
        "OMP_NUM_THREADS": "1",
    }
    try:
        proc = subprocess.run(
            [lean_bin, clean_path],
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

    observed = _parse_lean_axioms_stdout(proc.stdout)
    lean_sha256 = hashlib.sha256(raw).hexdigest()
    return {
        "static_clean": static_info["static_clean"],
        "lean_sha256": lean_sha256,
        "theorems_verified": len(EXPECTED_LEAN_THEOREMS),
        "axioms_by_theorem": observed,
    }


# ---------------------------------------------------------------------------
# Strict JSON Validation, Field-Complete Secondary Audit (FR0/SEC) & FR1
# ---------------------------------------------------------------------------

def _strict_parse_json_int(raw: str) -> int:
    return _parse_canonical_ascii_int(raw, allow_negative=True)


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


def _check_json_nesting_depth(raw_text: str) -> None:
    depth = 0
    in_str = False
    esc = False
    for ch in raw_text:
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch in "{[":
                depth += 1
                if depth > _MAX_JSON_DEPTH:
                    raise VerifyError("JSON nesting depth exceeds maximum permitted bound")
            elif ch in "}]":
                if depth > 0:
                    depth -= 1


def _validate_plain_json_tree(obj: object) -> None:
    """Iterative fail-closed exact primitive/container check (blocks subclasses, floats, surrogates, DOS)."""
    stack: List[Tuple[object, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > _MAX_JSON_DEPTH:
            raise VerifyError("JSON nesting depth exceeds maximum permitted bound")
        if isinstance(cur, float):
            raise VerifyError(f"Disallowed floating-point value: {type(cur).__name__}")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():  # type: ignore[union-attr]
                if type(k) is not str:
                    raise VerifyError("JSON object keys must be exact str")
                try:
                    k.encode("utf-8")
                except UnicodeEncodeError as exc:
                    raise VerifyError("JSON key contains lone surrogate") from exc
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
                raise VerifyError("JSON string contains lone surrogate") from exc
        elif t is bool or cur is None:
            continue
        else:
            raise VerifyError(f"Disallowed or subclassed value type in certificate: {t.__name__}")


def _canonical_json_bytes(obj: Mapping[str, object]) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("utf-8")


def _compute_payload_sha256(payload: Mapping[str, object]) -> str:
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def _require_exact_dict(obj: object, expected_keys: frozenset[str], name: str) -> Dict[str, Any]:
    if type(obj) is not dict or frozenset(obj.keys()) != expected_keys:
        raise VerifyError(f"{name} schema keys mismatch")
    return obj


def _require_exact_int(obj: object, expected: int, name: str) -> None:
    if type(obj) is not int or obj != expected:
        raise VerifyError(f"{name} integer value mismatch")


def _require_exact_int_list(obj: object, expected: List[int], name: str) -> None:
    if type(obj) is not list or len(obj) != len(expected):
        raise VerifyError(f"{name} integer list mismatch")
    for item, exp in zip(obj, expected):
        if type(item) is not int or item != exp:
            raise VerifyError(f"{name} integer list mismatch")


def _require_exact_str_list(obj: object, expected: List[str], name: str) -> None:
    if type(obj) is not list or len(obj) != len(expected):
        raise VerifyError(f"{name} string list mismatch")
    for item, exp in zip(obj, expected):
        if type(item) is not str or item != exp:
            raise VerifyError(f"{name} string list mismatch")


def _require_exact_int_map(obj: object, expected: Dict[str, int], name: str) -> None:
    d = _require_exact_dict(obj, frozenset(expected.keys()), name)
    for k, exp in expected.items():
        _require_exact_int(d[k], exp, f"{name}.{k}")


def secondary_audit_payload(payload: object) -> Dict[str, object]:
    """Field-complete strict-keyset independent algebraic audit (FR0 & SEC surface)."""
    _validate_plain_json_tree(payload)
    p = _require_exact_dict(payload, _PAYLOAD_KEYS, "payload")
    if p["schema_version"] != SCHEMA_VERSION:
        raise VerifyError("Payload schema_version mismatch")
    if p["portal"] != PORTAL_LABEL:
        raise VerifyError("Payload portal label mismatch")
    _require_exact_int(p["oracles_passed"], 7, "oracles_passed")
    oracles = _require_exact_dict(p["oracles"], _ORACLES_KEYS, "oracles")

    # Oracle 1: Meixner crossing-wires
    o1 = _require_exact_dict(oracles["oracle_1_meixner_crossing"], _O1_KEYS, "oracle_1")
    _require_exact_int_list(
        o1["ad_bc_rank_profile"],
        [1, 0, 3, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4],
        "o1.ad_bc_rank_profile",
    )
    _require_exact_int_list(o1["p_energy_0_to_6"], [1, 1, 2, 2, 4, 4, 7], "o1.p_energy_0_to_6")
    _require_exact_int(o1["max_ad_bc_rank"], 4, "o1.max_ad_bc_rank")
    _require_exact_int(o1["max_deg_psi"], 16, "o1.max_deg_psi")
    _require_exact_int(o1["orth_checks"], 216, "o1.orth_checks")
    _require_exact_int(o1["recip_checks"], 36, "o1.recip_checks")
    _require_exact_int(o1["reflection_checks"], 16, "o1.reflection_checks")
    _require_exact_int(o1["theta"], 16, "o1.theta")
    _require_exact_int(o1["x1_matched_count"], 4, "o1.x1_matched_count")
    _require_exact_int(o1["x1_sign"], 1, "o1.x1_sign")

    # Oracle 2: CAT(0) Mat_mu(F_2) dichotomy & Remark D.3
    o2 = _require_exact_dict(oracles["oracle_2_cat0_mat_f2_dichotomy"], _O2_KEYS, "oracle_2")
    _require_exact_int(o2["cube_pairs_verified"], 64, "o2.cube_pairs_verified")
    _require_exact_int_list(o2["mat2_rank_hist"], [1, 9, 6], "o2.mat2_rank_hist")
    _require_exact_int_list(o2["mat3_rank_hist"], [1, 49, 294, 168], "o2.mat3_rank_hist")
    if (
        parse_q(o2["non_euclidean_gram_det"]) != Fraction(-1, 4)
        or parse_q(o2["non_euclidean_quad_form"]) != Fraction(-1, 1)
        or parse_q(o2["tree_cn_gap"]) != Fraction(2, 1)
    ):
        raise VerifyError("Oracle 2 rational witness mismatch")

    # Oracle 3: Flat-case permanent & balanced cuts
    o3 = _require_exact_dict(oracles["oracle_3_flat_perm_and_hubs"], _O3_KEYS, "oracle_3")
    _require_exact_int(o3["balanced_cuts_checked"], 334, "o3.balanced_cuts_checked")
    _require_exact_int(o3["char2_cleared_perm_mod2"], 0, "o3.char2_cleared_perm_mod2")
    _require_exact_int(o3["char2_true_sum_mod2"], 1, "o3.char2_true_sum_mod2")
    _require_exact_int(o3["direct_grid_sum"], 31075, "o3.direct_grid_sum")
    _require_exact_int(o3["exponent_scaling_checks"], 5, "o3.exponent_scaling_checks")
    _require_exact_int(o3["f31_monomial_count"], 8, "o3.f31_monomial_count")
    _require_exact_int_map(o3["fp_matches"], {"F_3": 1, "F_5": 0}, "o3.fp_matches")
    _require_exact_int(o3["prop_e1_matrix_dim"], 9, "o3.prop_e1_matrix_dim")
    if (
        parse_q(o3["min_81_normsq_over_k3"]) != Fraction(21, 4)
        or parse_q(o3["perm_q_exact"]) != Fraction(31075, 1)
    ):
        raise VerifyError("Oracle 3 rational witness mismatch")

    # Oracle 4: Characteristic-2 perm vs HC & Prop M.2
    o4 = _require_exact_dict(oracles["oracle_4_char2_perm_vs_hc_and_s41"], _O4_KEYS, "oracle_4")
    _require_exact_int_list(o4["char2_3x3_det_perm_hc"], [0, 0, 1], "o4.char2_3x3_det_perm_hc")
    _require_exact_int_list(o4["char2_4x4_det_perm_hc"], [0, 0, 1], "o4.char2_4x4_det_perm_hc")
    _require_exact_int(o4["prop_m2_direct_sum"], 27, "o4.prop_m2_direct_sum")
    _require_exact_int(o4["prop_m2_hc_exact_z"], 27, "o4.prop_m2_hc_exact_z")
    _require_exact_int_map(o4["prop_m2_mod_checks"], {"F_2": 1, "F_3": 0, "F_5": 2}, "o4.prop_m2_mod_checks")
    _require_exact_int(o4["prop_m2_vertices"], 39, "o4.prop_m2_vertices")
    _require_exact_int(o4["s41_polya_3x3_valid_sign_maps"], 0, "o4.s41_polya_3x3_valid_sign_maps")

    # Oracle 5: Contracting unitriangular & SL_3 tower
    o5 = _require_exact_dict(oracles["oracle_5_contracting_unitriangular"], _O5_KEYS, "oracle_5")
    _require_exact_int(o5["max_endpoint1_gen_mult"], 4, "o5.max_endpoint1_gen_mult")
    _require_exact_int(o5["max_general_gen_mult"], 16, "o5.max_general_gen_mult")
    _require_exact_int(o5["sl3_tower_commutator_checks"], 54, "o5.sl3_tower_commutator_checks")
    _require_exact_int(o5["u4_u5_endpoint1_checked"], 44, "o5.u4_u5_endpoint1_checked")
    _require_exact_int(o5["u4_u5_general_rank1_checked"], 95, "o5.u4_u5_general_rank1_checked")

    # Oracle 6: Low-degree parse tree & Boolean barrier
    o6 = _require_exact_dict(oracles["oracle_6_lowdeg_parse_tree_and_diag"], _O6_KEYS, "oracle_6")
    _require_exact_int(o6["boolean_f_deg3_terms"], 1, "o6.boolean_f_deg3_terms")
    _require_exact_int(o6["boolean_g_deg3_terms"], 0, "o6.boolean_g_deg3_terms")
    _require_exact_int(o6["boolean_points_identical"], 8, "o6.boolean_points_identical")
    _require_exact_int_map(
        o6["finite_field_squaring_periods"], {"F_3": 1, "F_5": 1, "F_7": 2}, "o6.finite_field_squaring_periods"
    )
    _require_exact_int(o6["output_degree"], 5, "o6.output_degree")
    _require_exact_str_list(o6["rings_verified"], ["Z", "F_2", "F_3", "F_5"], "o6.rings_verified")

    # Oracle 7: Border Laurent closure
    o7 = _require_exact_dict(oracles["oracle_7_border_laurent_closure"], _O7_KEYS, "oracle_7")
    _require_exact_int(o7["lem_n2_cutoff_n"], 16, "o7.lem_n2_cutoff_n")
    _require_exact_str_list(o7["lem_n2_rings_verified"], ["Z", "F_2"], "o7.lem_n2_rings_verified")
    _require_exact_int(o7["lem_n3_cover_n32_lhs"], 276922881, "o7.lem_n3_cover_n32_lhs")
    _require_exact_int(o7["lem_n3_cover_n32_rhs"], 4294967296, "o7.lem_n3_cover_n32_rhs")
    _require_exact_int(o7["prop_n4_eps0_after_sigma_r"], 7, "o7.prop_n4_eps0_after_sigma_r")
    _require_exact_int(o7["prop_n4_min_exp_after_sigma_r"], 0, "o7.prop_n4_min_exp_after_sigma_r")
    _require_exact_int(o7["prop_n4_mod_2w_extracted_eps0"], 17, "o7.prop_n4_mod_2w_extracted_eps0")
    _require_exact_int(o7["prop_n4_sigma_r"], 3, "o7.prop_n4_sigma_r")

    return {"ok": True, "secondary_audit_passed": True, "oracles_passed": 7}


def secondary_audit(cert: object) -> Dict[str, object]:
    """Direct SEC surface auditing a certificate envelope and every payload field independently of replay."""
    _validate_plain_json_tree(cert)
    c = _require_exact_dict(cert, _CERT_KEYS, "certificate")
    if c["schema_version"] != SCHEMA_VERSION:
        raise VerifyError("Certificate schema_version mismatch")
    _require_sha256_hex(c["payload_sha256"], "Certificate payload_sha256")
    return secondary_audit_payload(c["payload"])


def build_certificate() -> Dict[str, object]:
    """Run all 7 pure-Z/Q/F_p mechanism oracles and construct canonical certificate."""
    oracles = probe.run_all_mechanism_probes()
    o2 = oracles["oracle_2_cat0_mat_f2_dichotomy"]
    o3 = oracles["oracle_3_flat_perm_and_hubs"]
    if type(o2) is not dict or type(o3) is not dict:
        raise VerifyError("Malformed oracle return payload")
    gram_det = parse_q(o2["non_euclidean_gram_det"])
    quad_val = parse_q(o2["non_euclidean_quad_form"])
    min_ratio = parse_q(o3["min_81_normsq_over_k3"])
    if gram_det >= 0 or quad_val >= 0 or min_ratio < Fraction(4, 1):
        raise VerifyError("Core rational inequality invariant failed")
    payload: Dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "portal": PORTAL_LABEL,
        "oracles_passed": 7,
        "oracles": oracles,
    }
    digest = _compute_payload_sha256(payload)
    return {
        "schema_version": SCHEMA_VERSION,
        "payload_sha256": digest,
        "payload": payload,
    }


def verify_certificate_dict(cert: object, *, full_replay: bool = True) -> Dict[str, object]:
    """Verify certificate against schema, strict hex + constant-time digest, FR0 secondary audit, and optional FR1 replay."""
    if type(full_replay) is not bool:
        raise VerifyError("full_replay must be exact bool")
    _validate_plain_json_tree(cert)
    if type(cert) is not dict:
        raise VerifyError("Certificate root must be a plain dict")
    if frozenset(cert.keys()) != _CERT_KEYS:
        raise VerifyError("Certificate root keys mismatch")
    if cert["schema_version"] != SCHEMA_VERSION:
        raise VerifyError("Certificate schema_version mismatch")
    digest = _require_sha256_hex(cert["payload_sha256"], "Certificate payload_sha256")
    payload = cert["payload"]
    if type(payload) is not dict:
        raise VerifyError("Certificate payload must be a plain dict")
    actual_digest = _compute_payload_sha256(payload)
    if not hmac.compare_digest(actual_digest, digest):
        raise VerifyError("Certificate payload_sha256 digest mismatch")
    secondary_audit_payload(payload)
    if full_replay:
        fresh = build_certificate()
        if not hmac.compare_digest(str(fresh["payload_sha256"]), digest):
            raise VerifyError("Certificate payload differs from clean-room recomputation")
    return {
        "ok": True,
        "payload_sha256": digest,
        "oracles_passed": 7,
        "full_replay": full_replay,
        "secondary_audit_passed": True,
    }


def verify_certificate_file(cert_path: str) -> Dict[str, object]:
    raw = _read_bytes_safe(cert_path)
    try:
        text = raw.decode("utf-8")
        if "\r" in text:
            raise VerifyError("CRLF bytes are disallowed in canonical certificate JSON")
        _check_json_nesting_depth(text)
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
    res = verify_certificate_dict(parsed, full_replay=True)
    if raw != _canonical_json_bytes(parsed):
        raise VerifyError("Certificate file bytes are not in exact canonical JSON format")
    return res


def write_certificate_file(cert_path: str) -> Dict[str, object]:
    cert = build_certificate()
    _write_bytes_atomic_safe(cert_path, _canonical_json_bytes(cert))
    return {"ok": True, "payload_sha256": cert["payload_sha256"], "oracles_passed": 7}


def _default_dir() -> str:
    return os.path.dirname(os.path.abspath(__file__))


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    base_dir = _default_dir()
    default_cert = os.path.join(base_dir, "s75_vp_vnp_certificate.json")
    default_lean = os.path.join(base_dir, "VpVnpMechanismCerts.lean")

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
            res = verify_certificate_dict(cert, full_replay=True)
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
    except (VerifyError, probe.ProbeError) as exc:
        sys.stderr.write(f"Verification failed: {exc}\n")
        return 1

    if as_json:
        sys.stdout.write(json.dumps(out, sort_keys=True) + "\n")
    else:
        sys.stdout.write(f"PASS mode={out['mode']}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

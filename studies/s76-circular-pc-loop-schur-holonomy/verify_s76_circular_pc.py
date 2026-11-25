#!/usr/bin/env python3
"""Zone-B Hardened Standalone CLI, Live Lean 4.36.0 & Secondary Auditor for Track S76.

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero .isdigit(),
zero mathematical RNG (secrets.token_hex used strictly for atomic temp filenames).
"""
from __future__ import annotations

import errno
from fractions import Fraction
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
from typing import Any, Sequence

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import s76_circular_pc_tomography as oracle  # noqa: E402

MAX_JSON_BYTES = 4 * 1024 * 1024
MAX_ALLOWED_CAP_BYTES = 64 * 1024 * 1024
_READ_CHUNK_BYTES = 65_536
_EXACT_PATH_TYPES = (Path, type(Path()))
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
_DARWIN_SYSTEM_ROOT_ALIASES: tuple[tuple[str, str], ...] = (
    ("/var", "/private/var"),
    ("/tmp", "/private/tmp"),
    ("/etc", "/private/etc"),
)
_TEMP_NAME_LOCK = threading.Lock()
_TEMP_SEQ = 0
_ALLOWED_LEAN_AXIOMS = frozenset({"propext", "Quot.sound"})

_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
_PAYLOAD_KEYS = frozenset({
    "schema_version",
    "track_id",
    "oracle_class",
    "novelty_classification",
    "pinned_artifacts",
    "pillar1_loop_schur_and_holonomy",
    "pillar2_ep_bias_and_truncation",
    "pillar3_krein_bifurcation_nonnormal_curl",
    "pillar4_live_circularep_anchor",
})
_PINNED_KEYS = frozenset({
    "lean_source",
    "lean_source_sha256",
    "lean_toolchain",
    "lean_toolchain_sha256",
    "lakefile_sha256",
    "live_anchor_file",
    "live_anchor_sha256",
    "lean_theorem_count",
    "lean_theorem_names",
})
_P1_KEYS = frozenset({"l2_noncommuting_2x2", "l3_noncommuting_2x2"})
_P1_BLOCK_KEYS = frozenset({
    "n_layers",
    "block_dim",
    "loop_schur_identity_exact",
    "naive_without_gloop_strictly_differs",
    "det_h_eq_det_imm_sq",
    "det_h_q",
    "det_imm_q",
    "det_g_loop_q",
    "g_loop_inertia",
    "h_pc_inertia",
    "schur_inertia",
    "adjoint_gloop_cancellation_exact",
    "non_commuting_holonomy",
    "monodromy_trace_cyclic_invariant",
    "monodromy_det_cyclic_invariant",
    "monodromy_trace_q",
    "monodromy_det_q",
})
_P2_KEYS = frozenset({
    "theta_q",
    "c_q",
    "q_cost_q",
    "exact_ift_grad_q",
    "exact_phase_rows",
    "truncated_free_delta0_q",
    "truncated_free_e0_q",
    "truncated_free_grad_q",
    "truncated_phase_rows",
    "centered_pole_cancelled_beta_invariant",
})
_P2_EXACT_ROW_KEYS = frozenset({
    "beta_q", "one_sided_q", "centered_q", "one_sided_bias_q", "centered_bias_q", "bias_matches_formula",
})
_P2_TRUNC_ROW_KEYS = frozenset({
    "beta_q", "nosub_inherited_abs_err_q", "sub_converged_nudge_abs_err_q", "centered_inherited_abs_err_q",
})
_P3_KEYS = frozenset({
    "contractive_gd_cliff",
    "critical_bifurcation_shadow",
    "krein_lagrangian_inertia",
    "non_normal_transient_amplification",
    "elliptic_complex_curl_obstruction",
})
_P4_KEYS = frozenset({
    "upstream_repo",
    "upstream_commit_sha",
    "best_json_sha256",
    "puzzles_json_sha256",
    "float32_parity_verified",
    "shipped_solved_count",
    "shipped_converged_wrong_count",
    "shipped_solved_pct_dec2",
    "contractive_at_equilibrium",
    "eq_rho_max_dec6",
    "eq_norm2_max_dec6",
    "non_normality_median_dec4",
    "non_normality_max_dec4",
    "complex_dominant_count",
    "complex_dominant_pct_dec2",
    "wrong_vs_solved_median_rho_pct_dec2",
    "loop_schur_300_verified",
    "loop_schur_300_max_abs_err_sci",
    "g_loop_softening_max_dec4",
    "plain_gd_eta_0p8_converged_le_2p5_exact",
    "plain_gd_eta_0p8_diverged_gt_2p5_exact",
    "power_iter_complex_vs_real_error_ratio_dec0",
    "ep_gradient_summary",
})
_P4_EP_KEYS = frozenset({
    "exact_1s_ratio_0p01_over_0p002_dec2",
    "exact_centered_ratio_0p01_over_0p002_dec2",
    "t10_beta_0p0005_nosub_err_dec4",
    "t10_beta_0p0005_sub_err_dec2",
    "t10_beta_0p0005_centered_err_dec4",
    "default_E1e6_beta_0p0005_sub_err_dec4",
    "default_E1e6_beta_0p0005_centered_err_dec4",
    "centered_advantage_vs_nosub_t10_dec1",
})

# Lean 4 R10 static trust-escape rules (pure-Init theorem file: no strings/guillemets/macros/imports)
_LEAN4_BANNED_RE = re.compile(
    r"(?<!\.)\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|ofReduceBool|ofReduceNat|"
    r"trustCompiler|mkSorry|run_cmd|run_meta|initialize|builtin_initialize|"
    r"macro|macro_rules|elab|elab_rules|syntax|interpolatedStr|dbg_trace|throwError|"
    r"notation|prefix|infix|infixl|infixr|postfix|csimp|opaque)\b"
    r"|\bdebug\s*\.\s*(?:skipKernelTC|byAsSorry|proofAsSorry|terminalTacticsAsSorry)\b"
    r"|(?:@|(?<!\.)\battribute\s*)\[[^\]]*\b(?:extern|implemented_by)\b"
    r"|\bpartial\s+(?:def|instance|abbrev)\b"
    r"|(?<!\w)\+\s*native\b|\bnative\s*:=\s*(?!false\b)|\bDecide(?:Config|\.Config)\b|\bdecide\s*\(\s*config\b"
    r"|#(?:eval!?(?![\w'!?])|reduce(?![\w'!?])|exit(?![\w'!?])|print(?![\w'!?])(?!\s+axioms[ \t]+[A-Za-z_]))"
    r"|(?:^|\n)[ \t]*(?:(?:public|private|meta)\s+)*import\s+"
    r'|["«»]',
    flags=re.DOTALL,
)
_LEAN4_AXIOM_NONE_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")
_LEAN4_AXIOM_DEP_RE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$")


# ---------------------------------------------------------------------------
# Zone-B Path, Darwin Alias Normalization, CWD, Atomic dir_fd & Atomic Write
# ---------------------------------------------------------------------------

def _require_concrete_path(path: Any, label: str) -> Path:
    oracle.require_ok(type(path) in _EXACT_PATH_TYPES, "INVALID_PATH_TYPE", f"{label}: concrete Path required")
    raw_s = oracle.require_exact_str(str(path), label)
    oracle.require_ok("\x00" not in raw_s, "NUL_BYTE_FORBIDDEN", f"{label}: NUL byte forbidden")
    return path


def _normalize_darwin_system_prefix(path: Path, *, allow_exact: bool = False) -> Path:
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


def _safe_cwd(label: str) -> Path:
    try:
        cwd = Path.cwd()
    except OSError as exc:
        raise oracle.S76Error("CWD_UNAVAILABLE", f"{label}: CWD unavailable") from exc
    oracle.require_exact_str(str(cwd), f"{label} CWD")
    return cwd


def _check_pwd_no_symlinks(label: str) -> None:
    pwd = os.environ.get("PWD", "")
    if not pwd.startswith("/"):
        return
    oracle.require_exact_str(pwd, f"{label} PWD")
    oracle.require_ok("\x00" not in pwd, "NUL_BYTE_FORBIDDEN", f"{label} PWD: NUL byte forbidden")
    pwd_path = _normalize_darwin_system_prefix(Path(pwd), allow_exact=True)
    try:
        pwd_st = os.stat(pwd_path)
        cwd_st = os.stat(".")
    except OSError:
        return
    if (pwd_st.st_dev, pwd_st.st_ino) != (cwd_st.st_dev, cwd_st.st_ino):
        return
    try:
        dfd = os.open("/", _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise oracle.S76Error("CWD_UNAVAILABLE", f"{label}: cannot open root for PWD") from exc
    try:
        for part in pwd_path.parts[1:]:
            try:
                next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
            except OSError as exc:
                if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise oracle.S76Error("SYMLINK_ANCESTOR_FORBIDDEN", f"{label}: symlink PWD ancestor") from exc
                raise oracle.S76Error("CWD_UNAVAILABLE", f"{label}: PWD ancestor unavailable") from exc
            os.close(dfd)
            dfd = next_fd
    finally:
        os.close(dfd)


def _open_dir_chain(target: Path, label: str, *, create_parents: bool) -> tuple[int, str]:
    if target.is_absolute():
        parts = _normalize_darwin_system_prefix(target).parts[1:]
    else:
        cwd = _normalize_darwin_system_prefix(_safe_cwd(label), allow_exact=True)
        _check_pwd_no_symlinks(label)
        parts = cwd.parts[1:] + target.parts
    oracle.require_ok(
        len(parts) >= 1 and parts[-1] != "..",
        "NOT_A_REGULAR_FILE",
        f"{label}: path does not name a regular file leaf",
    )
    parent_parts, leaf = parts[:-1], parts[-1]
    err_code = "FILE_WRITE_ERROR" if create_parents else "FILE_READ_ERROR"
    try:
        dfd = os.open("/", _DIR_OPEN_FLAGS)
    except OSError as exc:
        raise oracle.S76Error(err_code, f"{label}: cannot open root") from exc
    try:
        for part in parent_parts:
            try:
                next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
            except OSError as exc:
                if create_parents and exc.errno == errno.ENOENT:
                    try:
                        os.mkdir(part, 0o755, dir_fd=dfd)
                    except FileExistsError:
                        pass
                    except OSError as mk_exc:
                        raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: mkdir failed") from mk_exc
                    try:
                        next_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=dfd)
                    except OSError as re_exc:
                        raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: open created dir failed") from re_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise oracle.S76Error("SYMLINK_FORBIDDEN", f"{label}: symlink ancestor forbidden") from exc
                else:
                    raise oracle.S76Error(err_code, f"{label}: ancestor unavailable") from exc
            os.close(dfd)
            dfd = next_fd
        return dfd, leaf
    except BaseException:
        os.close(dfd)
        raise


def read_regular_bytes_capped(path: Path, label: str = "file", max_bytes: int = MAX_JSON_BYTES) -> bytes:
    target = _require_concrete_path(path, label)
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1, hi=MAX_ALLOWED_CAP_BYTES)
    dfd, leaf = _open_dir_chain(target, label, create_parents=False)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            fd = os.open(leaf, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise oracle.S76Error("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.S76Error("FILE_READ_ERROR", f"{label}: open failed") from exc
    finally:
        os.close(dfd)

    chunks: list[bytes] = []
    total = 0
    try:
        st_f = os.fstat(fd)
        oracle.require_ok(stat.S_ISREG(st_f.st_mode), "NOT_A_REGULAR_FILE", f"{label}: not a regular file")
        oracle.require_ok(st_f.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlink forbidden")
        oracle.require_ok(st_f.st_size <= max_bytes, "FILE_TOO_LARGE", f"{label}: size exceeds cap")
        while total <= max_bytes:
            chunk = os.read(fd, min(_READ_CHUNK_BYTES, max_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
    except oracle.S76Error:
        raise
    except OSError as exc:
        raise oracle.S76Error("FILE_READ_ERROR", f"{label}: read failed") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: stream exceeds cap")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str = "output") -> None:
    global _TEMP_SEQ
    oracle.require_ok(type(payload) is bytes, "INVALID_PAYLOAD_BYTES", f"{label}: exact bytes required")
    target = _require_concrete_path(path, label)
    dfd, leaf = _open_dir_chain(target, label, create_parents=True)
    tmp_name: str | None = None
    try:
        try:
            st_existing = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st_existing = None
        except OSError as exc:
            raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: lstat failed") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink <= 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target")

        pid = os.getpid()
        for _ in range(64):
            with _TEMP_NAME_LOCK:
                _TEMP_SEQ += 1
                seq_num = _TEMP_SEQ
                cand = f".s76.{pid}.{seq_num}.{secrets.token_hex(8)}.tmp"
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
                raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: temp open failed") from exc
        else:
            raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: temp slots exhausted")

        try:
            os.fchmod(fd, 0o600)
            view = memoryview(payload)
            written = 0
            while written < len(view):
                n_written = os.write(fd, view[written:])
                oracle.require_ok(n_written > 0, "FILE_WRITE_ERROR", f"{label}: short write 0")
                written += n_written
            os.fsync(fd)
            st_tmp = os.fstat(fd)
            oracle.require_ok(st_tmp.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: temp nlink altered")
        except oracle.S76Error:
            raise
        except OSError as exc:
            raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: write/fsync failed") from exc
        finally:
            os.close(fd)

        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
            os.fsync(dfd)
        except OSError as exc:
            raise oracle.S76Error("FILE_WRITE_ERROR", f"{label}: atomic replace failed") from exc
    finally:
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Strict Zero-Float Canonical JSON & Rational Parsers
# ---------------------------------------------------------------------------

def _parse_bounded_int(token: str) -> int:
    s = oracle.require_exact_str(token, "json_int")
    neg = s.startswith("-")
    body = s[1:] if neg else s
    oracle.require_ok(oracle.is_ascii_digits(body), "INVALID_INT_TOKEN", "non-ASCII digits")
    oracle.require_ok(len(body) <= oracle.MAX_INT_DIGITS, "INT_TOO_LARGE", "int digits cap")
    oracle.require_ok(not (len(body) > 1 and body[0] == "0"), "NONCANONICAL_INT", "leading zero")
    oracle.require_ok(not (neg and body == "0"), "NONCANONICAL_INT", "negative zero")
    val = int(s)
    oracle.require_ok(val.bit_length() <= oracle.MAX_INT_BITS, "INT_TOO_LARGE", "int bits cap")
    return val


def _reject_float(token: str) -> Any:
    raise oracle.S76Error("FLOAT_FORBIDDEN", f"IEEE-754 float forbidden: {token!r}")


def _reject_const(token: str) -> Any:
    raise oracle.S76Error("NONFINITE_JSON_CONSTANT", f"JSON constant forbidden: {token!r}")


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        oracle.require_ok(k not in out, "DUPLICATE_JSON_KEY", f"duplicate key {k!r}")
        out[k] = v
    return out


def parse_strict_json_bytes(raw: bytes, label: str = "json", *, require_canonical: bool = True) -> dict[str, Any]:
    oracle.require_ok(type(raw) is bytes, "INVALID_BYTES", f"{label}: exact bytes required")
    oracle.require_ok(not raw.startswith(b"\xef\xbb\xbf"), "BOM_FORBIDDEN", f"{label}: UTF-8 BOM forbidden")
    oracle.require_ok(b"\r" not in raw, "CRLF_FORBIDDEN", f"{label}: CR forbidden")
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as exc:
        raise oracle.S76Error("INVALID_UTF8", f"{label}: invalid UTF-8") from exc
    try:
        obj = json.loads(
            text,
            parse_float=_reject_float,
            parse_int=_parse_bounded_int,
            parse_constant=_reject_const,
            object_pairs_hook=_no_dup_pairs,
        )
    except oracle.S76Error:
        raise
    except (ValueError, RecursionError) as exc:
        raise oracle.S76Error("INVALID_JSON", f"{label}: malformed JSON") from exc
    oracle.require_ok(type(obj) is dict, "INVALID_ROOT_TYPE", f"{label}: root must be dict")
    oracle.validate_strict_json_tree(obj, label)
    if require_canonical:
        oracle.require_ok(
            hmac.compare_digest(raw, oracle.canonical_json_bytes(obj)),
            "NONCANONICAL_JSON",
            f"{label}: not canonical ASCII LF JSON",
        )
    return obj


def parse_canonical_rational_str(val: Any, label: str) -> Fraction:
    s = oracle.require_exact_str(val, label)
    oracle.require_ok(len(s) > 0, "INVALID_RATIONAL", f"{label}: empty")
    if "/" in s:
        parts = s.split("/")
        oracle.require_ok(len(parts) == 2, "INVALID_RATIONAL", f"{label}: multiple slashes")
        num_s, den_s = parts[0], parts[1]
        num = _parse_bounded_int(num_s)
        oracle.require_ok(not den_s.startswith("-"), "INVALID_RATIONAL", f"{label}: negative den")
        den = _parse_bounded_int(den_s)
        oracle.require_ok(den > 1, "NONCANONICAL_RATIONAL", f"{label}: den must be > 1")
        q = Fraction(num, den)
        oracle.require_ok(q.denominator == den, "NONCANONICAL_RATIONAL", f"{label}: not reduced")
        return q
    return Fraction(_parse_bounded_int(s), 1)


def _require_exact_dict(obj: Any, keys: frozenset[str], label: str) -> dict[str, Any]:
    oracle.require_ok(type(obj) is dict, "INVALID_SCHEMA_DICT", f"{label}: exact dict required")
    oracle.require_ok(frozenset(obj.keys()) == keys, "INVALID_SCHEMA_KEYS", f"{label}: keyset mismatch")
    return obj


# ---------------------------------------------------------------------------
# Live Lean 4.36.0 & R9 Static Lean Gate
# ---------------------------------------------------------------------------

def _strip_lean4_for_static_gate(source: str) -> str:
    """Strip Lean 4 nested block comments and line comments fail-closed (quotes/guillemets banned downstream)."""
    out: list[str] = []
    i = 0
    n = len(source)
    depth = 0
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
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            out.append("  ")
            i += 2
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(ch)
            i += 1
    oracle.require_ok(depth == 0, "LEAN4_UNTERMINATED_LEX", "unterminated Lean block comment")
    return "".join(out)


def static_gate_lean4_source(source: str) -> None:
    s = oracle.require_exact_str(source, "lean_source")
    oracle.require_ok("\r" not in s and "\x00" not in s, "LEAN4_BAD_CHARS", "CR/NUL in Lean source")
    cleaned = _strip_lean4_for_static_gate(s)
    m = _LEAN4_BANNED_RE.search(cleaned)
    oracle.require_ok(m is None, "LEAN4_TRUST_ESCAPE", f"banned Lean construct: {m.group(0)!r}" if m else "")
    for thm in oracle.LEAN_THEOREM_NAMES:
        short = thm.split(".")[-1]
        oracle.require_ok(f"theorem {short}" in cleaned, "LEAN4_MISSING_THEOREM", f"missing {short}")
        oracle.require_ok(f"#print axioms {thm}" in cleaned, "LEAN4_MISSING_PRINT_AXIOMS", f"missing #print axioms {thm}")


def resolve_lean_binary() -> str:
    env_bin = os.environ.get("ALETHEIA_LEAN_BIN")
    if env_bin is not None:
        oracle.require_exact_str(env_bin, "ALETHEIA_LEAN_BIN")
        p = Path(env_bin)
        oracle.require_ok(p.is_file() and os.access(str(p), os.X_OK), "LEAN_BINARY_UNAVAILABLE", "ALETHEIA_LEAN_BIN unusable")
        return str(p)
    found = shutil.which("lean")
    if found is not None and os.access(found, os.X_OK):
        return found
    for rel in ((".local", "bin", "lean"), (".elan", "bin", "lean")):
        cand = Path.home().joinpath(*rel)
        if cand.is_file() and os.access(str(cand), os.X_OK):
            return str(cand)
    raise oracle.S76Error("LEAN_BINARY_UNAVAILABLE", "lean executable not found")


def verify_lean4_file_live(lean_path: Path) -> dict[str, Any]:
    raw = read_regular_bytes_capped(lean_path, "lean_source", max_bytes=1024 * 1024)
    try:
        src = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as exc:
        raise oracle.S76Error("INVALID_UTF8", "Lean source not UTF-8") from exc
    static_gate_lean4_source(src)
    lean_bin = resolve_lean_binary()
    try:
        v_proc = subprocess.run([lean_bin, "--version"], capture_output=True, text=True, timeout=30, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise oracle.S76Error("LEAN_EXEC_ERROR", "lean --version failed") from exc
    oracle.require_ok(v_proc.returncode == 0 and "4.36.0" in v_proc.stdout, "LEAN_VERSION_MISMATCH", "Lean 4.36.0 required")
    try:
        proc = subprocess.run([lean_bin, str(lean_path)], capture_output=True, text=True, timeout=120, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise oracle.S76Error("LEAN_EXEC_ERROR", "lean elaboration failed") from exc
    oracle.require_ok(proc.returncode == 0, "LEAN_COMPILE_FAIL", f"lean rc={proc.returncode}")
    oracle.require_ok(proc.stderr.strip() == "", "LEAN_STDERR_NONEMPTY", "lean stderr must be empty")
    oracle.require_ok("warning:" not in proc.stdout.lower(), "LEAN_WARNING_FORBIDDEN", "lean warning forbidden")

    # Rejoin Lean 4 line-wrapped `[a,\n b]` axiom lists and reject duplicates fail-closed
    joined_lines: list[str] = []
    pending = ""
    for raw_line in proc.stdout.splitlines():
        s_line = raw_line.strip()
        if not s_line:
            continue
        if pending:
            pending = f"{pending} {s_line}"
            if "]" in s_line:
                joined_lines.append(pending)
                pending = ""
        elif "[" in s_line and "]" not in s_line:
            pending = s_line
        else:
            joined_lines.append(s_line)
    oracle.require_ok(pending == "", "LEAN_UNEXPECTED_STDOUT", "unterminated axiom list")

    seen: dict[str, list[str]] = {}
    for s_line in joined_lines:
        m_none = _LEAN4_AXIOM_NONE_RE.match(s_line)
        if m_none is not None:
            thm_name = m_none.group(1)
            oracle.require_ok(thm_name not in seen, "LEAN_DUPLICATE_THEOREM", f"duplicate axiom line: {thm_name}")
            seen[thm_name] = []
            continue
        m_dep = _LEAN4_AXIOM_DEP_RE.match(s_line)
        oracle.require_ok(m_dep is not None, "LEAN_UNEXPECTED_STDOUT", f"unexpected lean line: {s_line[:80]}")
        thm_name = m_dep.group(1)
        oracle.require_ok(thm_name not in seen, "LEAN_DUPLICATE_THEOREM", f"duplicate axiom line: {thm_name}")
        axs = [a.strip() for a in m_dep.group(2).split(",") if a.strip()]
        for ax in axs:
            oracle.require_ok(ax in _ALLOWED_LEAN_AXIOMS, "LEAN_FORBIDDEN_AXIOM", f"forbidden axiom {ax}")
        seen[thm_name] = axs
    oracle.require_ok(frozenset(seen.keys()) == frozenset(oracle.LEAN_THEOREM_NAMES), "LEAN_THEOREM_SET_MISMATCH", "axioms set mismatch")
    return {
        "lean_version": v_proc.stdout.strip().splitlines()[0],
        "theorems_verified": len(seen),
        "lean_source_sha256": oracle.sha256_hex(raw),
    }


# ---------------------------------------------------------------------------
# Fail-Closed Secondary Audit & Full Replay Verifier
# ---------------------------------------------------------------------------

def _require_inertia(val: Any, expected: list[int], label: str) -> None:
    oracle.require_ok(type(val) is list and len(val) == 3, "INVALID_INERTIA", label)
    for elem in val:
        oracle.require_exact_int(elem, label, lo=0, hi=10)
    oracle.require_ok(val == expected, "INERTIA_MISMATCH", f"{label}: expected {expected}")


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Fail-closed semantic + algebraic auditor enforced under BOTH full_replay=True and False."""
    oracle.require_ok(type(payload) is dict, "INVALID_PAYLOAD_TYPE", "payload must be exact dict")
    oracle.validate_strict_json_tree(payload, "payload")
    _require_exact_dict(payload, _PAYLOAD_KEYS, "payload")
    oracle.require_ok(payload["schema_version"] == oracle.SCHEMA_VERSION, "SCHEMA_MISMATCH", "schema_version")
    oracle.require_ok(payload["track_id"] == oracle.TRACK_ID, "SCHEMA_MISMATCH", "track_id")
    oracle.require_ok(payload["oracle_class"] == "exact+anchor", "SCHEMA_MISMATCH", "oracle_class")
    oracle.require_ok(payload["novelty_classification"] == "N1", "SCHEMA_MISMATCH", "novelty")

    pa = _require_exact_dict(payload["pinned_artifacts"], _PINNED_KEYS, "pinned_artifacts")
    oracle.require_ok(pa["lean_source"] == "CircularPCLoopSchur.lean", "SCHEMA_MISMATCH", "lean_source")
    oracle.require_hex64(pa["lean_source_sha256"], "lean_source_sha256")
    oracle.require_ok(pa["lean_toolchain"] == oracle.EXPECTED_LEAN_TOOLCHAIN, "SCHEMA_MISMATCH", "lean_toolchain")
    oracle.require_hex64(pa["lean_toolchain_sha256"], "lean_toolchain_sha256")
    oracle.require_hex64(pa["lakefile_sha256"], "lakefile_sha256")
    oracle.require_ok(pa["live_anchor_file"] == "s76_circularep_live_anchor.json", "SCHEMA_MISMATCH", "live_anchor_file")
    oracle.require_hex64(pa["live_anchor_sha256"], "live_anchor_sha256")
    thm_n = oracle.require_exact_int(pa["lean_theorem_count"], "lean_theorem_count", lo=len(oracle.LEAN_THEOREM_NAMES), hi=len(oracle.LEAN_THEOREM_NAMES))
    thms = pa["lean_theorem_names"]
    oracle.require_ok(type(thms) is list and tuple(thms) == oracle.LEAN_THEOREM_NAMES, "THEOREM_LIST_MISMATCH", "lean_theorem_names")

    # Pillar 1 algebraic invariants
    p1 = _require_exact_dict(payload["pillar1_loop_schur_and_holonomy"], _P1_KEYS, "pillar1")
    for bkey, exp_L in (("l2_noncommuting_2x2", 2), ("l3_noncommuting_2x2", 3)):
        blk = _require_exact_dict(p1[bkey], _P1_BLOCK_KEYS, bkey)
        oracle.require_exact_int(blk["n_layers"], f"{bkey}.n_layers", lo=exp_L, hi=exp_L)
        oracle.require_exact_int(blk["block_dim"], f"{bkey}.block_dim", lo=2, hi=2)
        for bk in (
            "loop_schur_identity_exact",
            "naive_without_gloop_strictly_differs",
            "det_h_eq_det_imm_sq",
            "adjoint_gloop_cancellation_exact",
            "non_commuting_holonomy",
            "monodromy_trace_cyclic_invariant",
            "monodromy_det_cyclic_invariant",
        ):
            oracle.require_ok(oracle.require_bool(blk[bk], f"{bkey}.{bk}") is True, "PILLAR1_FALSE", f"{bkey}.{bk}")
        dh = parse_canonical_rational_str(blk["det_h_q"], f"{bkey}.det_h_q")
        dimm = parse_canonical_rational_str(blk["det_imm_q"], f"{bkey}.det_imm_q")
        dg = parse_canonical_rational_str(blk["det_g_loop_q"], f"{bkey}.det_g_loop_q")
        parse_canonical_rational_str(blk["monodromy_trace_q"], f"{bkey}.trace")
        parse_canonical_rational_str(blk["monodromy_det_q"], f"{bkey}.det")
        oracle.require_ok(dh == dimm * dimm and dh > 0 and dg > 1, "PILLAR1_ALGEBRA_MISMATCH", bkey)
        _require_inertia(blk["g_loop_inertia"], [2, 0, 0], f"{bkey}.g_loop_inertia")
        _require_inertia(blk["h_pc_inertia"], [2 * exp_L, 0, 0], f"{bkey}.h_pc_inertia")
        _require_inertia(blk["schur_inertia"], [2, 0, 0], f"{bkey}.schur_inertia")

    # Pillar 2 exact EP bias & truncation algebra
    p2 = _require_exact_dict(payload["pillar2_ep_bias_and_truncation"], _P2_KEYS, "pillar2")
    theta = parse_canonical_rational_str(p2["theta_q"], "theta_q")
    d = Fraction(1) - theta
    oracle.require_ok(d > 0, "PILLAR2_RANGE", "1 - theta must be > 0")
    c_val = parse_canonical_rational_str(p2["c_q"], "c_q")
    q_cost = parse_canonical_rational_str(p2["q_cost_q"], "q_cost_q")
    g_ift = parse_canonical_rational_str(p2["exact_ift_grad_q"], "exact_ift_grad_q")
    oracle.require_ok(g_ift == c_val * q_cost / (d * d), "PILLAR2_IFT_MISMATCH", "g_ift != c*q/d^2")
    ex_rows = p2["exact_phase_rows"]
    oracle.require_ok(type(ex_rows) is list and len(ex_rows) == 3, "PILLAR2_ROWS", "exact_phase_rows len 3")
    for idx, row in enumerate(ex_rows):
        rr = _require_exact_dict(row, _P2_EXACT_ROW_KEYS, f"p2.ex[{idx}]")
        b = parse_canonical_rational_str(rr["beta_q"], "beta_q")
        g1 = parse_canonical_rational_str(rr["one_sided_q"], "one_sided_q")
        gc = parse_canonical_rational_str(rr["centered_q"], "centered_q")
        b1 = parse_canonical_rational_str(rr["one_sided_bias_q"], "one_sided_bias_q")
        bc = parse_canonical_rational_str(rr["centered_bias_q"], "centered_bias_q")
        oracle.require_ok(oracle.require_bool(rr["bias_matches_formula"], "bias_matches") is True, "PILLAR2_FALSE", "bias_matches")
        oracle.require_ok(b > 0 and b1 == g1 - g_ift and bc == gc - g_ift and bc == 0, "PILLAR2_BIAS_MISMATCH", "centered bias != 0")
        oracle.require_ok(b1 == -(q_cost * q_cost) * b / (d * d * d), "PILLAR2_BIAS_MISMATCH", "one-sided bias mismatch")

    d0 = parse_canonical_rational_str(p2["truncated_free_delta0_q"], "delta0")
    e0 = parse_canonical_rational_str(p2["truncated_free_e0_q"], "e0")
    gf = parse_canonical_rational_str(p2["truncated_free_grad_q"], "gf")
    oracle.require_ok(d0 > 0 and e0 == d * d0 and gf == -(c_val / d + d0) * e0, "PILLAR2_TRUNC_MISMATCH", "truncated free grad")
    tr_rows = p2["truncated_phase_rows"]
    oracle.require_ok(type(tr_rows) is list and len(tr_rows) == 3, "PILLAR2_ROWS", "truncated_phase_rows len 3")
    c_errs: list[Fraction] = []
    prev_nosub = Fraction(-1)
    prev_sub = Fraction(-1)
    for idx, row in enumerate(tr_rows):
        rr = _require_exact_dict(row, _P2_TRUNC_ROW_KEYS, f"p2.tr[{idx}]")
        b = parse_canonical_rational_str(rr["beta_q"], "tr.beta_q")
        en = parse_canonical_rational_str(rr["nosub_inherited_abs_err_q"], "nosub_err")
        es = parse_canonical_rational_str(rr["sub_converged_nudge_abs_err_q"], "sub_err")
        ec = parse_canonical_rational_str(rr["centered_inherited_abs_err_q"], "cent_err")
        oracle.require_ok(b > 0 and en > prev_nosub and es > prev_sub and ec > 0, "PILLAR2_BLOWUP_MISMATCH", "blowup order")
        prev_nosub, prev_sub = en, es
        c_errs.append(ec)
    oracle.require_ok(
        oracle.require_bool(p2["centered_pole_cancelled_beta_invariant"], "pole_cancel") is True
        and c_errs[0] == c_errs[1] == c_errs[2],
        "PILLAR2_POLE_MISMATCH",
        "centered error must be beta-invariant",
    )

    # Pillar 3 Krein, bifurcation, non-normal & curl invariants
    p3 = _require_exact_dict(payload["pillar3_krein_bifurcation_nonnormal_curl"], _P3_KEYS, "pillar3")
    cg = _require_exact_dict(p3["contractive_gd_cliff"], frozenset({"rho_q", "h_pc_inertia", "det_h_q", "lambda_max_h_q", "plain_gd_eta_crit_q"}), "p3.gd")
    rho_c = parse_canonical_rational_str(cg["rho_q"], "rho_c")
    lmax_c = parse_canonical_rational_str(cg["lambda_max_h_q"], "lmax_c")
    etac_c = parse_canonical_rational_str(cg["plain_gd_eta_crit_q"], "etac_c")
    det_c = parse_canonical_rational_str(cg["det_h_q"], "det_c")
    oracle.require_ok(0 < rho_c < 1 and det_c > 0 and lmax_c > 2 and etac_c * lmax_c == 2, "PILLAR3_GD_MISMATCH", "GD cliff")
    _require_inertia(cg["h_pc_inertia"], [2, 0, 0], "p3.gd.inertia")

    bf = _require_exact_dict(p3["critical_bifurcation_shadow"], frozenset({"h_pc_inertia", "det_h_q", "shadow_vector_in_ker_jr", "shadow_vector_in_ker_hpc"}), "p3.bif")
    _require_inertia(bf["h_pc_inertia"], [1, 0, 1], "p3.bif.inertia")
    oracle.require_ok(
        parse_canonical_rational_str(bf["det_h_q"], "bif.det") == 0
        and oracle.require_bool(bf["shadow_vector_in_ker_jr"], "ker_jr") is True
        and oracle.require_bool(bf["shadow_vector_in_ker_hpc"], "ker_hpc") is True,
        "PILLAR3_BIF_MISMATCH",
        "bifurcation shadow",
    )

    kr = _require_exact_dict(p3["krein_lagrangian_inertia"], frozenset({"contractive_k_inertia", "contractive_det_k_q", "bifurcation_k_inertia", "bifurcation_det_k_q"}), "p3.krein")
    _require_inertia(kr["contractive_k_inertia"], [2, 2, 0], "p3.krein.con")
    _require_inertia(kr["bifurcation_k_inertia"], [1, 1, 2], "p3.krein.bif")
    oracle.require_ok(
        parse_canonical_rational_str(kr["contractive_det_k_q"], "krein.det_con") > 0
        and parse_canonical_rational_str(kr["bifurcation_det_k_q"], "krein.det_bif") == 0,
        "PILLAR3_KREIN_MISMATCH",
        "Krein det",
    )

    nn = _require_exact_dict(p3["non_normal_transient_amplification"], frozenset({"spectral_radius_q", "norm_sq_e2_by_step", "overshoot_t1_to_t3_then_decay_t10"}), "p3.nn")
    oracle.require_ok(parse_canonical_rational_str(nn["spectral_radius_q"], "nn.rho") < 1, "PILLAR3_NN_MISMATCH", "rho < 1")
    steps = _require_exact_dict(nn["norm_sq_e2_by_step"], frozenset({"t1", "t2", "t3", "t10"}), "p3.nn.steps")
    oracle.require_ok(
        oracle.require_bool(nn["overshoot_t1_to_t3_then_decay_t10"], "nn.flag") is True
        and parse_canonical_rational_str(steps["t1"], "t1") > 1
        and parse_canonical_rational_str(steps["t2"], "t2") > 1
        and parse_canonical_rational_str(steps["t3"], "t3") > 1
        and parse_canonical_rational_str(steps["t10"], "t10") < 1,
        "PILLAR3_NN_MISMATCH",
        "non-normal overshoot",
    )

    cu = _require_exact_dict(p3["elliptic_complex_curl_obstruction"], frozenset({"rho_sq_q", "norm_sq_e1_q", "norm_sq_e2_q", "skew_curl_entry_q", "strict_oscillation_bracket"}), "p3.curl")
    rsq = parse_canonical_rational_str(cu["rho_sq_q"], "curl.rho_sq")
    n1 = parse_canonical_rational_str(cu["norm_sq_e1_q"], "curl.n1")
    n2 = parse_canonical_rational_str(cu["norm_sq_e2_q"], "curl.n2")
    sk = parse_canonical_rational_str(cu["skew_curl_entry_q"], "curl.skew")
    oracle.require_ok(
        oracle.require_bool(cu["strict_oscillation_bracket"], "curl.flag") is True
        and n1 < rsq < n2 and rsq < 1 and sk != 0,
        "PILLAR3_CURL_MISMATCH",
        "curl oscillation bracket",
    )

    # Pillar 4 live CircularEP anchor invariants
    p4 = _require_exact_dict(payload["pillar4_live_circularep_anchor"], _P4_KEYS, "pillar4")
    oracle.require_ok(p4["upstream_repo"] == "rel-int/CircularEP", "PILLAR4_MISMATCH", "upstream_repo")
    oracle.require_hex_len(p4["upstream_commit_sha"], 40, "commit_sha")
    oracle.require_hex64(p4["best_json_sha256"], "p4.best_sha")
    oracle.require_hex64(p4["puzzles_json_sha256"], "p4.puz_sha")
    for bf_k in ("float32_parity_verified", "contractive_at_equilibrium", "loop_schur_300_verified"):
        oracle.require_ok(oracle.require_bool(p4[bf_k], f"p4.{bf_k}") is True, "PILLAR4_FALSE", bf_k)
    s_cnt = oracle.require_exact_int(p4["shipped_solved_count"], "p4.solved", lo=1, hi=300)
    w_cnt = oracle.require_exact_int(p4["shipped_converged_wrong_count"], "p4.wrong", lo=0, hi=300)
    oracle.require_ok(s_cnt + w_cnt == 300, "PILLAR4_COUNTS", "solved+wrong != 300")
    oracle.require_ok(p4["shipped_solved_pct_dec2"] == oracle.dec_from_q(Fraction(s_cnt * 100, 300), 2), "PILLAR4_DEC", "solved_pct")
    cx_n = oracle.require_exact_int(p4["complex_dominant_count"], "p4.cx", lo=1, hi=300)
    oracle.require_ok(p4["complex_dominant_pct_dec2"] == oracle.dec_from_q(Fraction(cx_n * 100, 300), 2), "PILLAR4_DEC", "cx_pct")
    oracle.require_ok(oracle.parse_decimal_or_sci_to_q(p4["eq_rho_max_dec6"], "eq_rho_max") < 1, "PILLAR4_BOUND", "rho_max")
    oracle.require_ok(oracle.parse_decimal_or_sci_to_q(p4["eq_norm2_max_dec6"], "eq_norm2_max") < 1, "PILLAR4_BOUND", "norm2_max")
    nn_m = oracle.parse_decimal_or_sci_to_q(p4["non_normality_median_dec4"], "nn_med")
    nn_x = oracle.parse_decimal_or_sci_to_q(p4["non_normality_max_dec4"], "nn_max")
    oracle.require_ok(nn_m > 1 and nn_x >= nn_m, "PILLAR4_BOUND", "non-normality")
    oracle.require_ok(oracle.parse_decimal_or_sci_to_q(p4["wrong_vs_solved_median_rho_pct_dec2"], "w_vs_s") > 0, "PILLAR4_BOUND", "wrong > solved")
    oracle.require_ok(oracle.parse_decimal_or_sci_to_q(p4["loop_schur_300_max_abs_err_sci"], "sch_err") < Fraction(1, 10**12), "PILLAR4_BOUND", "schur_err")
    oracle.require_ok(oracle.parse_decimal_or_sci_to_q(p4["g_loop_softening_max_dec4"], "g_soft") > 1, "PILLAR4_BOUND", "g_soft")
    oracle.require_ok(oracle.parse_decimal_or_sci_to_q(p4["power_iter_complex_vs_real_error_ratio_dec0"], "pi_rat") > 10**8, "PILLAR4_BOUND", "pi_ratio")
    gd_c_parts = oracle.require_exact_str(p4["plain_gd_eta_0p8_converged_le_2p5_exact"], "gd_conv").split("/")
    oracle.require_ok(len(gd_c_parts) == 2 and oracle.is_ascii_digits(gd_c_parts[0]) and oracle.is_ascii_digits(gd_c_parts[1]), "PILLAR4_GD_FMT", "gd_conv")
    gd_c_num, gd_c_den = int(gd_c_parts[0]), int(gd_c_parts[1])
    oracle.require_ok(gd_c_den > 0 and gd_c_num == gd_c_den, "PILLAR4_GD_BOUND", "all converged must be <= 2.5")
    gd_d_parts = oracle.require_exact_str(p4["plain_gd_eta_0p8_diverged_gt_2p5_exact"], "gd_div").split("/")
    oracle.require_ok(len(gd_d_parts) == 2 and oracle.is_ascii_digits(gd_d_parts[0]) and oracle.is_ascii_digits(gd_d_parts[1]), "PILLAR4_GD_FMT", "gd_div")
    gd_d_num, gd_d_den = int(gd_d_parts[0]), int(gd_d_parts[1])
    oracle.require_ok(0 < gd_d_num <= gd_d_den and gd_c_den + gd_d_den == 300, "PILLAR4_GD_BOUND", "gd_div")
    ep_s = _require_exact_dict(p4["ep_gradient_summary"], frozenset({"test-0016", "test-0065"}), "p4.ep_summary")
    for pid in ("test-0016", "test-0065"):
        ep_r = _require_exact_dict(ep_s[pid], _P4_EP_KEYS, f"p4.ep.{pid}")
        r1 = oracle.parse_decimal_or_sci_to_q(ep_r["exact_1s_ratio_0p01_over_0p002_dec2"], f"{pid}.r1")
        rc = oracle.parse_decimal_or_sci_to_q(ep_r["exact_centered_ratio_0p01_over_0p002_dec2"], f"{pid}.rc")
        t_ns = oracle.parse_decimal_or_sci_to_q(ep_r["t10_beta_0p0005_nosub_err_dec4"], f"{pid}.t_ns")
        t_sb = oracle.parse_decimal_or_sci_to_q(ep_r["t10_beta_0p0005_sub_err_dec2"], f"{pid}.t_sb")
        t_ct = oracle.parse_decimal_or_sci_to_q(ep_r["t10_beta_0p0005_centered_err_dec4"], f"{pid}.t_ct")
        d_sb = oracle.parse_decimal_or_sci_to_q(ep_r["default_E1e6_beta_0p0005_sub_err_dec4"], f"{pid}.d_sb")
        d_ct = oracle.parse_decimal_or_sci_to_q(ep_r["default_E1e6_beta_0p0005_centered_err_dec4"], f"{pid}.d_ct")
        adv = oracle.parse_decimal_or_sci_to_q(ep_r["centered_advantage_vs_nosub_t10_dec1"], f"{pid}.adv")
        oracle.require_ok(Fraction(45, 10) <= r1 <= Fraction(55, 10), "PILLAR4_EP_BOUND", f"{pid}.r1")
        oracle.require_ok(Fraction(24, 1) <= rc <= Fraction(26, 1), "PILLAR4_EP_BOUND", f"{pid}.rc")
        oracle.require_ok(t_ns > 1 and t_sb > 1000 and d_sb > 5, "PILLAR4_EP_BOUND", f"{pid}.blowup")
        oracle.require_ok(Fraction(0) < t_ct < Fraction(1, 100) and Fraction(0) < d_ct < Fraction(1, 100), "PILLAR4_EP_BOUND", f"{pid}.centered")
        oracle.require_ok(adv > 100, "PILLAR4_EP_BOUND", f"{pid}.adv")

    return {
        "secondary_audit_passed": True,
        "lean_theorem_count": thm_n,
        "shipped_solved_count": s_cnt,
        "complex_dominant_count": cx_n,
    }


def _load_track_artifacts(track_dir: Path) -> tuple[dict[str, Any], str, str, str, str, dict[str, Any]]:
    anchor_raw = read_regular_bytes_capped(track_dir / "s76_circularep_live_anchor.json", "live_anchor")
    anchor_obj = parse_strict_json_bytes(anchor_raw, "live_anchor", require_canonical=True)
    tc_raw = read_regular_bytes_capped(track_dir / "lean-toolchain", "lean-toolchain", max_bytes=256)
    try:
        tc_text = tc_raw.decode("utf-8", "strict").strip()
    except UnicodeDecodeError as exc:
        raise oracle.S76Error("INVALID_UTF8", "lean-toolchain invalid UTF-8") from exc
    oracle.require_ok(tc_text == oracle.EXPECTED_LEAN_TOOLCHAIN, "TOOLCHAIN_MISMATCH", "unexpected lean-toolchain")
    lake_raw = read_regular_bytes_capped(track_dir / "lakefile.toml", "lakefile.toml", max_bytes=4096)
    lean_res = verify_lean4_file_live(track_dir / "CircularPCLoopSchur.lean")
    return (
        anchor_obj,
        oracle.sha256_hex(anchor_raw),
        lean_res["lean_source_sha256"],
        oracle.sha256_hex(tc_raw),
        oracle.sha256_hex(lake_raw),
        lean_res,
    )


def verify_certificate_dict(
    cert: Any,
    *,
    full_replay: bool = True,
    track_dir: Path | None = None,
) -> dict[str, Any]:
    oracle.require_bool(full_replay, "full_replay")
    oracle.require_ok(type(cert) is dict, "INVALID_CERT_TYPE", "certificate must be exact dict")
    oracle.validate_strict_json_tree(cert, "certificate")
    _require_exact_dict(cert, _CERT_KEYS, "certificate")
    oracle.require_ok(cert["schema_version"] == oracle.SCHEMA_VERSION, "SCHEMA_MISMATCH", "cert schema_version")
    oracle.require_ok(cert["track_id"] == oracle.TRACK_ID, "SCHEMA_MISMATCH", "cert track_id")

    p_sha = oracle.require_hex64(cert["payload_sha256"], "payload_sha256")
    c_sha = oracle.require_hex64(cert["certificate_sha256"], "certificate_sha256")
    payload = cert["payload"]
    sec_res = secondary_audit_payload(payload)

    recomputed_p = oracle.sha256_hex(oracle.canonical_json_bytes(payload))
    oracle.require_ok(hmac.compare_digest(p_sha, recomputed_p), "PAYLOAD_SHA_MISMATCH", "payload_sha256 mismatch")
    env = {
        "schema_version": cert["schema_version"],
        "track_id": cert["track_id"],
        "payload_sha256": p_sha,
        "payload": payload,
    }
    recomputed_c = oracle.sha256_hex(oracle.canonical_json_bytes(env))
    oracle.require_ok(hmac.compare_digest(c_sha, recomputed_c), "CERT_SHA_MISMATCH", "certificate_sha256 mismatch")

    replayed = False
    lean_live: dict[str, Any] | None = None
    if full_replay:
        root = Path(_THIS_DIR) if track_dir is None else _require_concrete_path(track_dir, "track_dir")
        anchor_obj, a_sha, l_sha, tc_sha, lk_sha, lean_live = _load_track_artifacts(root)
        expected = oracle.build_certificate(
            anchor=anchor_obj,
            anchor_sha256=a_sha,
            lean_source_sha256=l_sha,
            toolchain_sha256=tc_sha,
            lakefile_sha256=lk_sha,
        )
        oracle.require_ok(
            hmac.compare_digest(oracle.canonical_json_bytes(cert), oracle.canonical_json_bytes(expected)),
            "FULL_REPLAY_MISMATCH",
            "certificate does not match pure-Z/Q + Lean 4.36.0 replay",
        )
        replayed = True

    out: dict[str, Any] = {
        "valid": True,
        "full_replay": replayed,
        "payload_sha256": p_sha,
        "certificate_sha256": c_sha,
        "secondary_audit": sec_res,
    }
    if lean_live is not None:
        out["lean_live"] = lean_live
    return out


def write_certificate_file(path: Path, *, track_dir: Path | None = None) -> dict[str, Any]:
    root = Path(_THIS_DIR) if track_dir is None else _require_concrete_path(track_dir, "track_dir")
    anchor_obj, a_sha, l_sha, tc_sha, lk_sha, _ = _load_track_artifacts(root)
    cert = oracle.build_certificate(
        anchor=anchor_obj,
        anchor_sha256=a_sha,
        lean_source_sha256=l_sha,
        toolchain_sha256=tc_sha,
        lakefile_sha256=lk_sha,
    )
    raw = oracle.canonical_json_bytes(cert)
    write_regular_bytes_safe(path, raw, "certificate")
    return {
        "written": True,
        "bytes": len(raw),
        "file_sha256": oracle.sha256_hex(raw),
        "certificate_sha256": cert["certificate_sha256"],
    }


def check_certificate_file(path: Path, *, full_replay: bool = True, track_dir: Path | None = None) -> dict[str, Any]:
    raw = read_regular_bytes_capped(path, "certificate")
    cert = parse_strict_json_bytes(raw, "certificate", require_canonical=True)
    res = verify_certificate_dict(cert, full_replay=full_replay, track_dir=track_dir)
    res["file_sha256"] = oracle.sha256_hex(raw)
    return res


# ---------------------------------------------------------------------------
# Strict CLI Entrypoint
# ---------------------------------------------------------------------------

def _parse_cli_args(argv: Any) -> dict[str, Any]:
    oracle.require_ok(type(argv) is list, "INVALID_ARGV", "argv must be exact list")
    mode: str | None = None
    target_path: str | None = None
    want_json = False
    i = 0
    n = len(argv)
    while i < n:
        arg = oracle.require_exact_str(argv[i], "argv")
        oracle.require_ok("\x00" not in arg, "NUL_BYTE_FORBIDDEN", "NUL byte in argv")
        if arg == "--json":
            oracle.require_ok(not want_json, "DUPLICATE_FLAG", "--json repeated")
            want_json = True
            i += 1
        elif arg == "--standalone":
            oracle.require_ok(mode is None, "CONFLICTING_MODE", "conflicting mode flags")
            mode = "standalone"
            i += 1
        elif arg in ("--check", "--write"):
            oracle.require_ok(mode is None, "CONFLICTING_MODE", "conflicting mode flags")
            oracle.require_ok(i + 1 < n, "MISSING_PATH_ARG", f"{arg} requires a path")
            val = oracle.require_exact_str(argv[i + 1], f"{arg} path")
            oracle.require_ok("\x00" not in val, "NUL_BYTE_FORBIDDEN", f"NUL byte in {arg} path")
            oracle.require_ok(len(val) > 0 and not val.startswith("-"), "INVALID_PATH_ARG", f"invalid path {val!r}")
            mode = arg[2:]
            target_path = val
            i += 2
        elif arg.startswith("--check=") or arg.startswith("--write="):
            oracle.require_ok(mode is None, "CONFLICTING_MODE", "conflicting mode flags")
            flag_name, val = arg.split("=", 1)
            oracle.require_ok(len(val) > 0 and not val.startswith("-"), "INVALID_PATH_ARG", f"invalid path {val!r}")
            mode = flag_name[2:]
            target_path = val
            i += 1
        else:
            raise oracle.S76Error("UNKNOWN_FLAG", f"unsupported flag: {arg!r}")
    return {"mode": mode or "default", "target": target_path, "json": want_json}


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv: Any = list(sys.argv[1:]) if argv is None else argv
    try:
        opts = _parse_cli_args(raw_argv)
        mode = opts["mode"]
        if mode == "standalone":
            root = Path(_THIS_DIR)
            anchor_obj, a_sha, l_sha, tc_sha, lk_sha, _ = _load_track_artifacts(root)
            cert = oracle.build_certificate(
                anchor=anchor_obj,
                anchor_sha256=a_sha,
                lean_source_sha256=l_sha,
                toolchain_sha256=tc_sha,
                lakefile_sha256=lk_sha,
            )
            sys.stdout.write(oracle.canonical_json_bytes(cert).decode("ascii"))
            return 0
        if mode == "write":
            res = write_certificate_file(Path(opts["target"]))
            if opts["json"]:
                sys.stdout.write(oracle.canonical_json_bytes(res).decode("ascii"))
            else:
                sys.stdout.write(f"WROTE {res['file_sha256']}\n")
            return 0
        if mode == "check":
            res = check_certificate_file(Path(opts["target"]), full_replay=True)
            if opts["json"]:
                sys.stdout.write(oracle.canonical_json_bytes(res).decode("ascii"))
            else:
                sys.stdout.write(f"OK {res['certificate_sha256']}\n")
            return 0
        res = check_certificate_file(Path(_THIS_DIR) / "s76_circular_pc_certificate.json", full_replay=True)
        if opts["json"]:
            sys.stdout.write(oracle.canonical_json_bytes(res).decode("ascii"))
        else:
            sys.stdout.write(f"OK {res['certificate_sha256']}\n")
        return 0
    except oracle.S76Error as exc:
        err_obj = {"error": True, "code": exc.code, "detail": exc.detail}
        sys.stderr.write(json.dumps(err_obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

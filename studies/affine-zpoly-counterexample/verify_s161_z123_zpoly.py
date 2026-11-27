#!/usr/bin/env python3
"""Track S161 (EXP-Q44a) fail-closed verifier: Zone-B strict I/O, pure-Z/Q
certificate replay, static Lean 4.36.0 R12/R13b audit, and live Lean kernel +
lake build verification without mutating the track directory.

Standard library only. Zero floating-point literals or calls, zero bare asserts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import stat
import subprocess
import sys
import tempfile

_HERE = Path(__file__).parent
_BASE_STR = str(_HERE if _HERE.is_absolute() else (Path(os.getcwd()) / _HERE))
sys.path.insert(0, _BASE_STR)

import s161_z123_zpoly_oracle as oracle  # noqa: E402
from s161_z123_zpoly_oracle import ZPolyError, require_ok  # noqa: E402

ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound"})
MAX_BYTES = 1048576
MAX_DEPTH = 32
MAX_INT_DIGITS = 256
CERT_NAME = oracle.CERT_FILE_NAME

_FORBIDDEN_LEAN_RE = re.compile(
    r'["«»]'
    r"|(?<![A-Za-z0-9_])(?:sorry|admit|sorryAx|mkSorry|unsafe|partial|opaque|noncomputable|native_decide|bv_decide|bv_check"
    r"|Classical|ofReduceBool|ofReduceNat|trustCompiler|implemented_by|extern|csimp|export|initialize|builtin_initialize"
    r"|macro|macro_rules|elab|elab_rules|syntax|declare_syntax_cat|notation|prefix|infix|infixl|infixr|postfix"
    r"|set_option|dbg_trace|dbg_sleep|dbg_stack_trace|panic|unreachable|run_cmd|run_meta|run_elab|run_tac|by_elab|skipKernelTC)(?![A-Za-z0-9_])"
    r"|\bdebug\s*\.\s*skipKernelTC\b"
    r"|(?<![A-Za-z0-9_.])axiom(?![A-Za-z0-9_])"
    r"|(?<![A-Za-z0-9_])import(?![A-Za-z0-9_])"
    r"|#\s*(?:eval|reduce|exit|check_failure|check|synth|guard_msgs|guard_expr|guard)(?![A-Za-z0-9_])"
    r"|(?<!\w)\+\s*native(?![A-Za-z0-9_])"
    r"|(?<![A-Za-z0-9_])native\s*:="
)
_PUB_THM_RE = re.compile(r"(?:^|\n)[ \t]*(?:@\[[^\]]*\][ \t\n]*)*theorem[ \t]+([A-Za-z0-9_.']+)")
_PRINT_RE = re.compile(r"(?:^|\n)[ \t]*#print[ \t]+axioms[ \t]+ZPolyCounterexample\.([A-Za-z0-9_.']+)")
_RAW_PRINT_RE = re.compile(r"(?:^|\n)[ \t]*#[ \t]*print\b")
_TOML_REQUIRE_RE = re.compile(
    r"(?:^|\n)[ \t]*(?:\[\[?\s*(?:require|extern_lib|lean_exe|target)\s*\]?\]"
    r"|(?:require|precompileModules|moreLeanArgs|moreLeancArgs|moreLinkArgs|moreServerArgs|moreGlobalServerArgs|extraDepTargets|needs)\s*=)"
)


def track_base() -> Path:
    here = Path(__file__).parent
    if here.is_absolute():
        return here
    return Path(os.getcwd()) / here


def _unnormalized_parts(path: object) -> tuple[str, ...]:
    s = str(path) if isinstance(path, Path) else path
    require_ok(type(s) is str, "BAD_PATH_TYPE", "path must be str or Path")
    require_ok(len(s) > 0 and "\x00" not in s, "BAD_PATH_STR", "empty or NUL path rejected")
    raw = Path(s)
    if raw.is_absolute():
        return raw.parts
    return (Path.cwd() / raw).parts


def check_no_symlink_ancestors(path: object) -> None:
    parts = _unnormalized_parts(path)
    cur = Path("/")
    for seg in parts[1:]:
        cur = cur / seg
        require_ok(cur.is_symlink() is False, "SYMLINK_ANCESTOR", "symlink in path ancestors")


def _open_parent_nofollow(path: object) -> tuple[int, str]:
    parts = _unnormalized_parts(path)
    require_ok(len(parts) >= 2, "READ_OPEN", "cannot open root directory as file")
    dfd = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        for seg in parts[1:-1]:
            nxt = os.open(seg, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
            os.close(dfd)
            dfd = nxt
    except OSError:
        os.close(dfd)
        raise ZPolyError("PARENT_OPEN", "cannot open parent directory")
    return dfd, parts[-1]


def read_strict_bytes(path: object) -> bytes:
    check_no_symlink_ancestors(path)
    dfd, leaf = _open_parent_nofollow(path)
    try:
        try:
            fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError:
            raise ZPolyError("READ_OPEN", "cannot open file")
    finally:
        os.close(dfd)
    chunks: list[bytes] = []
    try:
        info = os.fstat(fd)
        require_ok(stat.S_ISREG(info.st_mode), "NOT_REGULAR", "not a regular file")
        require_ok(info.st_nlink == 1, "HARDLINK_FILE", "hardlinked file rejected")
        total = 0
        while True:
            chunk = os.read(fd, 65536)
            if chunk == b"":
                break
            total = total + len(chunk)
            require_ok(total <= MAX_BYTES, "TOO_LARGE", "file exceeds size cap")
            chunks.append(chunk)
    finally:
        os.close(fd)
    return b"".join(chunks)


def decode_strict_text(raw: bytes) -> str:
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        raise ZPolyError("BAD_UTF8", "invalid utf-8")
    require_ok(text.startswith("\ufeff") is False, "BAD_BOM", "byte order mark rejected")
    require_ok("\r" not in text, "BAD_LF", "carriage return rejected")
    require_ok(text.endswith("\n"), "BAD_FINAL_LF", "missing final newline")
    return text


def read_strict_text(path: object) -> str:
    return decode_strict_text(read_strict_bytes(path))


def scan_json_text(text: str) -> None:
    depth = 0
    in_str = False
    escaped = False
    digit_run = 0
    saw_float = False
    prev_digit = False
    for ch in text:
        if in_str:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_str = False
            digit_run = 0
            prev_digit = False
            continue
        if ch == '"':
            in_str = True
            digit_run = 0
            prev_digit = False
            continue
        if ch == "{":
            depth = depth + 1
        if ch == "[":
            depth = depth + 1
        if ch == "}":
            depth = depth - 1
        if ch == "]":
            depth = depth - 1
        require_ok(depth >= 0 and depth <= MAX_DEPTH, "JSON_DEPTH_BOUNDS", "json nesting depth out of bounds")
        if ch.isdigit():
            digit_run = digit_run + 1
            require_ok(digit_run <= MAX_INT_DIGITS, "INT_DIGITS", "integer digit bound exceeded")
            prev_digit = True
        else:
            if prev_digit:
                if ch == ".":
                    saw_float = True
                if ch == "e":
                    saw_float = True
                if ch == "E":
                    saw_float = True
            digit_run = 0
            prev_digit = False
    require_ok(depth == 0, "UNBALANCED_FINAL", "unbalanced json nesting")
    require_ok(saw_float is False, "FLOAT_TOKEN", "floating-point token rejected")
    require_ok(in_str is False, "UNTERMINATED_JSON_STRING", "unterminated json string")


def dup_free_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, val in pairs:
        require_ok(key not in out, "DUP_KEY", "duplicate json key")
        out[key] = val
    return out


def reject_constant(_value: str) -> None:
    raise ZPolyError("BAD_CONSTANT", "non-json constant rejected")


def parse_strict_json(text: str) -> dict[str, object]:
    scan_json_text(text)
    try:
        data = json.loads(text, object_pairs_hook=dup_free_object, parse_constant=reject_constant)
    except ZPolyError:
        raise
    except (json.JSONDecodeError, ValueError):
        raise ZPolyError("BAD_JSON", "malformed json")
    require_ok(isinstance(data, dict), "NOT_OBJECT", "top level must be object")
    return data


def read_strict_json(path: object) -> dict[str, object]:
    return parse_strict_json(read_strict_text(path))


def strict_json_equal(a: object, b: object) -> bool:
    """Recursive type-exact JSON equality preventing bool/int confusion (True != 1, False != 0)."""
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        if set(a.keys()) != set(b.keys()):
            return False
        for key in a:
            if not strict_json_equal(a[key], b[key]):
                return False
        return True
    if isinstance(a, list):
        if len(a) != len(b):
            return False
        for item_a, item_b in zip(a, b):
            if not strict_json_equal(item_a, item_b):
                return False
        return True
    return a == b


def strip_lean_comments(src: str) -> str:
    """Strip only -- and nested /- -/ comments, preserving strings/guillemets so _FORBIDDEN_LEAN_RE catches them."""
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/":
                if nxt == "-":
                    depth = depth + 1
                    out.append("  ")
                    i = i + 2
                    continue
            if ch == "-":
                if nxt == "/":
                    depth = depth - 1
                    out.append("  ")
                    i = i + 2
                    continue
            out.append("\n" if ch == "\n" else " ")
            i = i + 1
            continue
        if ch == "-":
            if nxt == "-":
                while i < n:
                    if src[i] == "\n":
                        break
                    out.append(" ")
                    i = i + 1
                continue
        if ch == "/":
            if nxt == "-":
                depth = 1
                out.append("  ")
                i = i + 2
                continue
        out.append(ch)
        i = i + 1
    require_ok(depth == 0, "UNTERMINATED_BLOCK_COMMENT", "unterminated Lean block comment")
    return "".join(out)


def validate_axiom_lines(
    lines: list[str],
    expected_count: int = oracle.EXPECTED_LEAN_THEOREMS,
    expected_theorems: list[str] | tuple[str, ...] | None = None,
) -> dict[str, int]:
    non_empty = [ln.strip() for ln in lines if ln.strip() != ""]
    require_ok(len(non_empty) == expected_count, "AXIOM_LINE_COUNT", "axiom line count mismatch")
    zero_count = 0
    listed_count = 0
    seen_theorems: list[str] = []
    for ln in non_empty:
        require_ok(ln.startswith("'"), "AXIOM_THM_PREFIX", "missing quoted theorem prefix")
        end_q = ln.find("' ", 1)
        require_ok(end_q > 1, "AXIOM_THM_PREFIX", "invalid quoted theorem prefix")
        seen_theorems.append(ln[1:end_q])
        rest = ln[end_q + 2:]
        if rest == "does not depend on any axioms":
            zero_count = zero_count + 1
            continue
        require_ok(rest.startswith("depends on axioms:"), "AXIOM_LINE_FORMAT", "unrecognized axiom line")
        rhs = rest.split("depends on axioms:", 1)[1].strip()
        require_ok(rhs.startswith("["), "AXIOM_LBRACKET", "missing opening bracket")
        require_ok(rhs.endswith("]"), "AXIOM_RBRACKET", "missing closing bracket")
        for part in rhs[1:-1].split(","):
            item = part.strip()
            if item != "":
                require_ok(item in ALLOWED_AXIOMS, "FORBIDDEN_AXIOM", "axiom not allowlisted")
        listed_count = listed_count + 1
    if expected_theorems is not None:
        require_ok(seen_theorems == list(expected_theorems), "AXIOM_THM_MISMATCH", "axiom theorem names mismatch")
    return {"zero_axiom": zero_count, "listed": listed_count}


def default_live_lean_runner(staged_files: dict[str, bytes]) -> dict[str, object]:
    home = os.path.expanduser("~")
    elan_bin = str(Path(home) / ".elan" / "bin")
    local_bin = str(Path(home) / ".local" / "bin")
    env = {
        "PATH": elan_bin + ":" + local_bin + ":/usr/bin:/bin",
        "HOME": home,
        "CUDA_VISIBLE_DEVICES": "",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        os.chmod(tmp_path, 0o755)
        for fname in (oracle.LEAN_FILE_NAME, "lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            pinned_bytes = staged_files[fname]
            dst_fd = os.open(str(tmp_path / fname), os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
            try:
                view = memoryview(pinned_bytes)
                written = 0
                while written < len(pinned_bytes):
                    written = written + os.write(dst_fd, view[written:])
            finally:
                os.close(dst_fd)
        version = subprocess.run(["lean", "--version"], cwd=tmp, env=env, capture_output=True, text=True, timeout=60, check=False)
        build = subprocess.run(["lake", "build"], cwd=tmp, env=env, capture_output=True, text=True, timeout=180, check=False)
        audit = subprocess.run(["lean", oracle.LEAN_FILE_NAME], cwd=tmp, env=env, capture_output=True, text=True, timeout=180, check=False)
    return {
        "version_rc": version.returncode,
        "version_output": version.stdout + version.stderr,
        "build_rc": build.returncode,
        "build_output": build.stdout + build.stderr,
        "axiom_rc": audit.returncode,
        "axiom_stderr": audit.stderr,
        "axiom_stdout": audit.stdout,
    }


def verify_lean_package(
    base: Path,
    *,
    run_live_lean: bool = False,
    lean_runner: object = None,
    enforce_sha_pins: bool = True,
) -> dict[str, object]:
    tc_raw = read_strict_bytes(base / "lean-toolchain")
    tc_text = decode_strict_text(tc_raw).strip()
    require_ok(tc_text == oracle.EXPECTED_TOOLCHAIN, "BAD_TOOLCHAIN", "lean-toolchain mismatch")

    lf_raw = read_strict_bytes(base / "lakefile.toml")
    lf_text = decode_strict_text(lf_raw)
    require_ok(_TOML_REQUIRE_RE.search(lf_text) is None, "LAKEFILE_REQUIRE", "external require forbidden in lakefile.toml")

    mf_raw = read_strict_bytes(base / "lake-manifest.json")
    mf_data = parse_strict_json(decode_strict_text(mf_raw))
    require_ok(mf_data.get("packages") == [], "NONEMPTY_PACKAGES", "lake-manifest packages must be empty")

    lean_files = [p for p in sorted(base.rglob("*.lean")) if ".lake" not in p.parts]
    require_ok(len(lean_files) == 1, "LEAN_FILE_COUNT", "expected exactly one .lean module")
    require_ok(lean_files[0].name == oracle.LEAN_FILE_NAME, "LEAN_FILE_NAME", "unexpected .lean filename")

    lean_raw = read_strict_bytes(lean_files[0])
    lean_src = decode_strict_text(lean_raw)
    cleaned = strip_lean_comments(lean_src)
    require_ok(_FORBIDDEN_LEAN_RE.search(cleaned) is None, "LEAN_ESCAPE", "forbidden construct in Lean source")

    pub_thms = _PUB_THM_RE.findall(cleaned)
    audited = _PRINT_RE.findall(cleaned)
    raw_prints = _RAW_PRINT_RE.findall(cleaned)
    require_ok(len(raw_prints) == len(audited), "UNEXPECTED_PRINT_CMD", "non-axiom #print forbidden")
    require_ok(len(pub_thms) == oracle.EXPECTED_LEAN_THEOREMS, "THM_COUNT", "public theorem count mismatch")
    require_ok(len(audited) == oracle.EXPECTED_LEAN_THEOREMS, "AUDIT_COUNT", "audited theorem count mismatch")
    require_ok(set(pub_thms) == set(audited), "AUDIT_SET", "theorem vs #print axioms set mismatch")

    tc_sha = hashlib.sha256(tc_raw).hexdigest()
    lf_sha = hashlib.sha256(lf_raw).hexdigest()
    mf_sha = hashlib.sha256(mf_raw).hexdigest()
    lean_sha = hashlib.sha256(lean_raw).hexdigest()
    if enforce_sha_pins:
        require_ok(tc_sha == oracle.PINNED_TOOLCHAIN_SHA256, "PIN_TOOLCHAIN_SHA", "lean-toolchain sha256 mismatch")
        require_ok(lf_sha == oracle.PINNED_LAKEFILE_SHA256, "PIN_LAKEFILE_SHA", "lakefile.toml sha256 mismatch")
        require_ok(mf_sha == oracle.PINNED_MANIFEST_SHA256, "PIN_MANIFEST_SHA", "lake-manifest.json sha256 mismatch")
        require_ok(lean_sha == oracle.PINNED_LEAN_SHA256, "PIN_LEAN_SHA", "ZPolyCounterexample.lean sha256 mismatch")

    res: dict[str, object] | None = None
    if lean_runner is not None:
        res = lean_runner(base)
    elif run_live_lean:
        staged_files = {
            oracle.LEAN_FILE_NAME: lean_raw,
            "lean-toolchain": tc_raw,
            "lakefile.toml": lf_raw,
            "lake-manifest.json": mf_raw,
        }
        res = default_live_lean_runner(staged_files)
    if res is not None:
        require_ok(res["version_rc"] == 0, "LEAN_VERSION_RC", "lean --version failed")
        require_ok("4.36.0" in res["version_output"], "BAD_LEAN_VERSION", "Lean 4.36.0 required")
        require_ok(res["build_rc"] == 0, "LAKE_BUILD_FAIL", "lake build failed")
        require_ok("warning:" not in res["build_output"].lower(), "LAKE_BUILD_WARNING", "lake build emitted warning")
        require_ok(res["axiom_rc"] == 0, "AXIOM_RC", "lean axiom check failed")
        require_ok(res["axiom_stderr"] == "", "AXIOM_STDERR", "lean axiom check emitted stderr")
        expected_thms = [oracle.LEAN_MODULE + "." + name for name in audited]
        validate_axiom_lines(res["axiom_stdout"].splitlines(), oracle.EXPECTED_LEAN_THEOREMS, expected_thms)

    return {
        "toolchain": tc_text,
        "lean_module": oracle.LEAN_MODULE,
        "lean_files": 1,
        "lean_loc": len(lean_src.splitlines()),
        "public_theorems": len(pub_thms),
        "lean_sha256": lean_sha,
        "toolchain_sha256": tc_sha,
        "lakefile_sha256": lf_sha,
        "manifest_sha256": mf_sha,
    }


def build_payload(
    base: Path | None = None,
    *,
    run_live_lean: bool = False,
    lean_runner: object = None,
) -> dict[str, object]:
    if base is None:
        base = track_base()
    sections = oracle.compute_oracle_sections()
    lean_info = verify_lean_package(base, run_live_lean=run_live_lean, lean_runner=lean_runner)
    payload: dict[str, object] = {
        "schema": oracle.SCHEMA_VERSION,
        "track": oracle.TRACK_ID,
        "queue_id": oracle.QUEUE_ID,
        "oracle_class": oracle.ORACLE_CLASS,
        "novelty_classification": oracle.NOVELTY_CLASS,
        "lean": lean_info,
        "oracle": sections,
    }
    canon = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    payload["payload_sha256"] = hashlib.sha256(canon).hexdigest()
    return payload


def write_cert(path: Path, payload: dict[str, object]) -> None:
    check_no_symlink_ancestors(path)
    dfd, leaf = _open_parent_nofollow(path)
    tmp_name: str | None = None
    try:
        require_ok(leaf != "..", "BAD_PATH_LEAF", "parent traversal leaf rejected")
        try:
            existing = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            existing = None
        if existing is not None:
            require_ok(stat.S_ISREG(existing.st_mode), "NOT_REGULAR", "target is not a regular file")
            require_ok(existing.st_nlink == 1, "HARDLINK_TARGET", "hardlinked target rejected")
        raw = (json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")
        cand_name = ".s161_cert_tmp_" + str(os.getpid()) + "_" + secrets.token_hex(8)
        fd = os.open(cand_name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644, dir_fd=dfd)
        tmp_name = cand_name
        try:
            view = memoryview(raw)
            written = 0
            while written < len(raw):
                written = written + os.write(fd, view[written:])
        finally:
            os.close(fd)
        os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
        tmp_name = None
    finally:
        if tmp_name is not None:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


class _FailClosedVerifierParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        raise ZPolyError("BAD_CLI_ARGS", message)


def emit_error(code: str, message: str) -> None:
    line = json.dumps({"status": "FAIL", "code": code, "message": message}, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n"
    os.write(2, line.encode("utf-8"))


def resolve_cert_path(base: Path, given: str | None) -> Path:
    if given is None:
        return base / CERT_NAME
    cand = Path(given)
    if cand.is_absolute():
        return cand
    return base / cand


def run_cli(argv: list[str] | None = None) -> int:
    parser = _FailClosedVerifierParser(
        description="Track S161 EXP-Q44a Z-polynomial counterexample verifier",
        add_help=False,
        allow_abbrev=False,
    )
    parser.add_argument("--check", nargs="?", const=CERT_NAME, default=None)
    parser.add_argument("--write", nargs="?", const=CERT_NAME, default=None)
    parser.add_argument("--standalone", action="store_true")
    parser.add_argument("--json", action="store_true", dest="json_out")
    parser.add_argument("--live-lean", action="store_true")
    args, unknown = parser.parse_known_args(argv)
    require_ok(len(unknown) == 0, "BAD_CLI_ARGS", "unknown verifier cli argument")

    modes = 0
    if args.check is not None:
        modes = modes + 1
    if args.write is not None:
        modes = modes + 1
    if args.standalone:
        modes = modes + 1
    require_ok(modes <= 1, "MODE_COUNT", "at most one mode allowed")

    check_given = CERT_NAME if modes == 0 else args.check
    base = track_base()
    payload = build_payload(base=base, run_live_lean=args.live_lean)
    if args.write is not None:
        write_cert(resolve_cert_path(base, args.write), payload)
    if check_given is not None:
        cert = read_strict_json(resolve_cert_path(base, check_given))
        require_ok(strict_json_equal(cert, payload), "CERT_MISMATCH", "certificate mismatch")

    if args.json_out:
        os.write(1, (json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8"))
    else:
        os.write(1, ("PASS " + oracle.SCHEMA_VERSION + "\n").encode("utf-8"))
    return 0


def main(argv: list[str] | None = None) -> int:
    try:
        return run_cli(argv)
    except ZPolyError as exc:
        emit_error(exc.code, str(exc))
        return 2
    except RecursionError:
        emit_error("RECURSION", "recursion limit exceeded")
        return 2
    except subprocess.SubprocessError as exc:
        emit_error("SUBPROCESS_ERROR", type(exc).__name__)
        return 2
    except (OSError, UnicodeDecodeError) as exc:
        emit_error("OS_ERROR", type(exc).__name__)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

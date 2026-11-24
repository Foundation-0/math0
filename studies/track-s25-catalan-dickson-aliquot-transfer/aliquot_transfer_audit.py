#!/usr/bin/env python3
"""Zone-B hardened standalone CLI & certificate verifier for Track S25 (AUDIT-125).

100% pure Python 3 stdlib, zero IEEE-754 floats, zero bare asserts, zero RNG.
Uniform Zone-B Gold Standard built in from R1:
  - Concrete pathlib.Path check + NUL-byte and lone UTF-16 surrogate path refusal
  - Deleted-CWD OSError wrapping -> CWD_UNAVAILABLE (rc=2)
  - Relative-path PWD symlink walk + atomic per-component dir_fd openat
    (O_RDONLY | O_DIRECTORY | O_NOFOLLOW, ELOOP/ENOTDIR handling)
  - Leaf dir_fd O_RDONLY | O_NOFOLLOW | O_NONBLOCK + fstat S_ISREG + capped os.read
  - Atomic write: dir_fd lstat (SYMLINK_FORBIDDEN, NOT_A_REGULAR_FILE, HARDLINK_FORBIDDEN)
    -> fresh O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK temp file in same dfd
    -> atomic os.replace(tmp, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
  - Strict exact-str argv validation, flag-like & equals-syntax CLI path refusal
    (--write --json, --write=--json, --check=--json -> rc=2, 0 files created)
  - Strict 64-char lowercase ASCII hex check BEFORE hmac.compare_digest + full
    pure-Q deterministic replay + secondary algebraic cross-check
"""
from __future__ import annotations

import errno
import hashlib
import hmac
import json
import os
from pathlib import Path
import stat
import sys
from typing import Any

_ROOT_DIR = str(Path(__file__).resolve().parent)
if _ROOT_DIR not in sys.path:
    sys.path.insert(0, _ROOT_DIR)

import aliquot_transfer_oracle as oracle  # noqa: E402

MAX_JSON_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_JSON_INT_DIGITS = 1_205
_EXACT_PATH_TYPES = (Path, type(Path()))
_HEX_LOWER = frozenset("0123456789abcdef")
_ASCII_DIGITS = frozenset("0123456789")
_CERT_KEYS = frozenset({"schema_version", "track_id", "payload_sha256", "certificate_sha256", "payload"})
DEFAULT_CERT_NAME = "aliquot_transfer_certificate.json"


def _require_utf8_no_surrogate(text: str, label: str) -> None:
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise oracle.AliquotTransferError("INVALID_UTF8_SURROGATE", f"{label}: lone UTF-16 surrogate forbidden") from exc


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
        raise oracle.AliquotTransferError("CWD_UNAVAILABLE", f"{label}: CWD unavailable ({exc})") from exc


def _check_pwd_no_symlinks(label: str) -> None:
    pwd = os.environ.get("PWD")
    if pwd and os.path.isabs(pwd):
        _require_utf8_no_surrogate(pwd, f"{label} PWD")
        pwd_path = Path(pwd)
        cur = Path(pwd_path.anchor)
        for part in pwd_path.parts[1:]:
            cur = cur / part
            oracle.require_ok(
                not os.path.islink(cur),
                "SYMLINK_ANCESTOR_FORBIDDEN",
                f"{label}: symlink PWD ancestor forbidden",
            )


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
        raise oracle.AliquotTransferError(err_code, f"{label}: cannot open root ({exc})") from exc
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
                        raise oracle.AliquotTransferError("FILE_WRITE_ERROR", f"{label}: mkdir failed ({mk_exc})") from mk_exc
                    try:
                        next_fd = os.open(part, dir_flags, dir_fd=dfd)
                    except OSError as reopen_exc:
                        raise oracle.AliquotTransferError(
                            "FILE_WRITE_ERROR", f"{label}: cannot open created dir ({reopen_exc})"
                        ) from reopen_exc
                elif exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    try:
                        is_lnk = stat.S_ISLNK(os.lstat(part, dir_fd=dfd).st_mode)
                    except OSError:
                        is_lnk = exc.errno == errno.ELOOP
                    if is_lnk:
                        raise oracle.AliquotTransferError("SYMLINK_FORBIDDEN", f"{label}: symlink component forbidden") from exc
                    raise oracle.AliquotTransferError(err_code, f"{label}: non-directory ancestor ({exc})") from exc
                else:
                    raise oracle.AliquotTransferError(err_code, f"{label}: cannot open ancestor ({exc})") from exc
            os.close(dfd)
            dfd = next_fd
        return dfd, leaf
    except BaseException:
        os.close(dfd)
        raise


def read_regular_bytes_capped(path: Path, label: str, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Read regular file bytes under strict cap using atomic dir_fd openat O_NOFOLLOW|O_NONBLOCK + fstat S_ISREG."""
    target = _require_concrete_path(path, label)
    oracle.require_exact_int(max_bytes, "max_bytes", lo=1)
    dfd, leaf = _open_dir_chain(target, label, create_parents=False)
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    try:
        try:
            fd = os.open(leaf, flags, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise oracle.AliquotTransferError("SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden") from exc
            raise oracle.AliquotTransferError("FILE_READ_ERROR", f"{label}: cannot open ({exc})") from exc
    finally:
        os.close(dfd)
    chunks: list[bytes] = []
    total = 0
    try:
        st_f = os.fstat(fd)
        oracle.require_ok(stat.S_ISREG(st_f.st_mode), "NOT_A_REGULAR_FILE", f"{label}: not a regular file")
        while total <= max_bytes:
            chunk = os.read(fd, max_bytes + 1 - total)
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
    except oracle.AliquotTransferError:
        raise
    except OSError as exc:
        raise oracle.AliquotTransferError("FILE_READ_ERROR", f"{label}: read failed ({exc})") from exc
    finally:
        os.close(fd)
    oracle.require_ok(total <= max_bytes, "FILE_TOO_LARGE", f"{label}: exceeds {max_bytes} bytes")
    return b"".join(chunks)


def write_regular_bytes_safe(path: Path, payload: bytes, label: str) -> None:
    """Write bytes atomically via dir_fd O_CREAT|O_EXCL|O_NOFOLLOW + os.replace (zero TOCTOU/hardlink clobber)."""
    target = _require_concrete_path(path, label)
    dfd, leaf = _open_dir_chain(target, label, create_parents=True)
    tmp_name: str | None = None
    try:
        try:
            st_existing = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st_existing = None
        except OSError as exc:
            raise oracle.AliquotTransferError("FILE_WRITE_ERROR", f"{label}: stat failed ({exc})") from exc
        if st_existing is not None:
            oracle.require_ok(not stat.S_ISLNK(st_existing.st_mode), "SYMLINK_FORBIDDEN", f"{label}: symlink leaf forbidden")
            oracle.require_ok(stat.S_ISREG(st_existing.st_mode), "NOT_A_REGULAR_FILE", f"{label}: non-regular target")
            oracle.require_ok(st_existing.st_nlink == 1, "HARDLINK_FORBIDDEN", f"{label}: hardlinked target forbidden")
        pid = os.getpid()
        for seq in range(64):
            cand = f".{leaf}.s25_tmp_{pid}_{seq}"
            try:
                fd = os.open(
                    cand,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                    0o644,
                    dir_fd=dfd,
                )
                tmp_name = cand
                break
            except FileExistsError:
                continue
            except OSError as exc:
                raise oracle.AliquotTransferError("FILE_WRITE_ERROR", f"{label}: create temp failed ({exc})") from exc
        else:
            raise oracle.AliquotTransferError("FILE_WRITE_ERROR", f"{label}: exhausted temp file slots")
        try:
            view = memoryview(payload)
            written = 0
            while written < len(view):
                written += os.write(fd, view[written:])
        except OSError as exc:
            raise oracle.AliquotTransferError("FILE_WRITE_ERROR", f"{label}: write failed ({exc})") from exc
        finally:
            os.close(fd)
        try:
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            tmp_name = None
        except OSError as exc:
            raise oracle.AliquotTransferError("FILE_WRITE_ERROR", f"{label}: atomic replace failed ({exc})") from exc
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
    digits = token[1:] if token.startswith("-") else token
    oracle.require_ok(len(digits) >= 1, "INVALID_JSON_INT", "JSON int token has no digits")
    oracle.require_ok(len(digits) <= MAX_JSON_INT_DIGITS, "INT_DIGIT_LIMIT", "JSON int exceeds digit cap")
    for ch in digits:
        oracle.require_ok(ch in _ASCII_DIGITS, "INVALID_JSON_INT", "JSON int token must contain ASCII digits 0-9 only")
    return int(token)


def _reject_nonfinite(token: str) -> Any:
    raise oracle.AliquotTransferError("NONFINITE_JSON", f"non-finite JSON constant {token!r}")


def _reject_float(token: str) -> Any:
    raise oracle.AliquotTransferError("FLOAT_FORBIDDEN", f"JSON float token forbidden: {token!r}")


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
            raise oracle.AliquotTransferError("INVALID_JSON_VALUE", f"{label}: unsupported type {t.__name__}")


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
    except oracle.AliquotTransferError:
        raise
    except (ValueError, RecursionError) as exc:
        raise oracle.AliquotTransferError("INVALID_JSON", f"{label}: {exc}") from exc
    if require_object:
        oracle.require_ok(type(parsed) is dict, "JSON_ROOT_NOT_OBJECT", f"{label}: JSON root must be dict")
    _validate_json_tree(parsed, label)
    return parsed


def canonical_json_bytes(obj: Any) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n").encode("utf-8")


def build_certificate() -> dict[str, Any]:
    payload = oracle.compute_s25_payload()
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


def _secondary_algebraic_crosscheck(payload: dict[str, Any]) -> None:
    """Secondary structural & algebraic cross-check on parsed payload fields."""
    p1 = payload["pillar1_catalan_dickson_transfer"]
    p2 = payload["pillar2_sylvester_zsigmondy"]
    p3 = payload["pillar3_pomerance_pseudorandomness"]
    p4 = payload["pillar4_harmonic_ore"]
    p5 = payload["pillar5_cyclotomic_kirchhoff"]
    ok_all = all(
        (
            p1["all_verified"] is True,
            p2["all_verified"] is True,
            p3["all_verified"] is True,
            p4["all_verified"] is True,
            p5["all_verified"] is True,
            p1["parity_vs_sigma_exceptions"] == 0,
            p1["parity_vs_escape_exceptions"] == 0,
            p1["trajectory_138"]["peak"] == 179_931_895_322,
            p1["trajectory_138"]["reaches_1_step"] == 177,
            len(p2["sylvester_wall_table"]) == len(oracle.SYLVESTER_Q_LIST),
            p3["odd_m_series_pi2_coeff"] == "3/16",
            [s["m"] for s in p3["pomerance_alpha1_solutions"]] == [1, 3003],
            p4["lte_exceptions"] == 0,
            p4["ore_numbers_count"] == 18,
            p4["odd_ore_numbers_le_limit"] == [1],
            p5["descartes_kirchhoff"]["external_leak_product"] == 22_021,
            p5["phi3_forward_cascade_depth5"][-1] == [3348577],
        )
    )
    oracle.require_ok(ok_all, "ALGEBRAIC_CROSSCHECK_FAILED", "secondary algebraic cross-check failed")


def verify_certificate_dict(cert: Any, *, expected: dict[str, Any] | None = None) -> dict[str, Any]:
    """Fail-closed in-memory certificate verifier (hex64 check + full pure-Q replay + cross-check)."""
    oracle.require_ok(type(cert) is dict, "INVALID_CERT_TYPE", "certificate must be exact dict")
    oracle.require_ok(set(cert.keys()) == _CERT_KEYS, "INVALID_CERT_KEYS", "unexpected or missing cert keys")
    _validate_json_tree(cert, "cert")
    got_psha = require_hex64_lower_ascii(cert["payload_sha256"], "payload_sha256")
    got_csha = require_hex64_lower_ascii(cert["certificate_sha256"], "certificate_sha256")
    exp = build_certificate() if expected is None else expected
    oracle.require_ok(
        hmac.compare_digest(got_psha, exp["payload_sha256"]),
        "PAYLOAD_SHA_MISMATCH",
        "payload_sha256 mismatch",
    )
    oracle.require_ok(
        hmac.compare_digest(got_csha, exp["certificate_sha256"]),
        "CERTIFICATE_SHA_MISMATCH",
        "certificate_sha256 mismatch",
    )
    oracle.require_ok(
        hmac.compare_digest(canonical_json_bytes(cert), canonical_json_bytes(exp)),
        "CERTIFICATE_MISMATCH",
        "certificate does not match freshly computed exact oracle output",
    )
    _secondary_algebraic_crosscheck(cert["payload"])
    return {
        "valid": True,
        "payload_sha256": exp["payload_sha256"],
        "certificate_sha256": exp["certificate_sha256"],
    }


def verify_certificate_file(cert_path: Path) -> dict[str, Any]:
    """Fail-closed file certificate verifier (atomic dir_fd read + LF-only canonical bytes + replay)."""
    raw = read_regular_bytes_capped(cert_path, "certificate")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise oracle.AliquotTransferError("INVALID_UTF8", f"certificate: invalid UTF-8 ({exc})") from exc
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
        raise oracle.AliquotTransferError(
            "INVALID_CLI_ARGS",
            "usage: aliquot_transfer_audit.py (--standalone --json | --write <path> | --check <path>)",
        )
    except oracle.AliquotTransferError as exc:
        sys.stderr.write(f"[FAIL] {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

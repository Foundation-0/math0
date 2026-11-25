#!/usr/bin/env python3
"""
Track S21e — Fail-Closed CLI Certifier (`metamorphosis_symmetry_audit.py`).

Commands:
  --standalone [--json]   Run exact-Q oracle and print summary or canonical JSON
  --write <path>          Write canonical zero-float certificate (fail-closed path checks)
  --check <path>          Verify canonical certificate bytes, digests, and full oracle replay
"""
from __future__ import annotations

import os
from pathlib import Path
import stat
import sys
from typing import Any

_HERE = str(Path(__file__).resolve().parent)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from metamorphosis_symmetry_oracle import (  # noqa: E402
    SymmetryBridgeError,
    build_certificate,
    canonical_json_bytes,
    require_exact_str,
    require_no_symlink_path,
    verify_certificate_file,
)


def _validate_argv(argv: Any) -> list[str]:
    if argv is None:
        raw = sys.argv[1:]
    elif type(argv) in (list, tuple):
        raw = list(argv)
    else:
        raise SymmetryBridgeError("INVALID_ARGV", "argv must be strict list, tuple, or None")
    out: list[str] = []
    for idx, item in enumerate(raw):
        s = require_exact_str(item, f"argv[{idx}]")
        if "\x00" in s:
            raise SymmetryBridgeError("INVALID_ARGV_NUL", f"argv[{idx}] contains NUL")
        out.append(s)
    return out


def _parse_cli_args(args: list[str]) -> tuple[str, bool, str | None]:
    mode: str | None = None
    emit_json = False
    target: str | None = None
    i = 0
    while i < len(args):
        tok = args[i]
        if tok == "--standalone":
            if mode is not None:
                raise SymmetryBridgeError("CONFLICTING_MODE", "specify only one mode")
            mode = "standalone"
            i += 1
        elif tok == "--json":
            emit_json = True
            i += 1
        elif tok in ("--write", "--check"):
            if mode is not None:
                raise SymmetryBridgeError("CONFLICTING_MODE", "specify only one mode")
            if i + 1 >= len(args):
                raise SymmetryBridgeError("MISSING_ARG", f"{tok} requires a path")
            mode = "write" if tok == "--write" else "check"
            target = args[i + 1]
            i += 2
        else:
            raise SymmetryBridgeError("UNKNOWN_FLAG", f"unrecognized argument: {tok!r}")
    if mode is None:
        mode = "standalone"
    if emit_json and mode != "standalone":
        raise SymmetryBridgeError("INVALID_FLAG_COMBO", "--json is only valid with --standalone")
    return mode, emit_json, target


def write_certificate_file(path: Any) -> dict[str, Any]:
    p = require_no_symlink_path(path, "write_path")
    parent = p.parent
    try:
        pst = os.lstat(parent)
    except OSError as exc:
        raise SymmetryBridgeError("PARENT_MISSING", f"parent directory missing: {exc}") from exc
    if stat.S_ISLNK(pst.st_mode) or not stat.S_ISDIR(pst.st_mode):
        raise SymmetryBridgeError("INVALID_PARENT", "parent must be a real non-symlink directory")
    if os.path.lexists(p):
        st = os.lstat(p)
        if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
            raise SymmetryBridgeError("INVALID_WRITE_TARGET", "write target exists and is not a regular file")
    cert = build_certificate()
    raw = canonical_json_bytes(cert)
    tmp = parent / f".{p.name}.tmp.{os.getpid()}"
    try:
        tmp.write_bytes(raw)
        os.replace(tmp, p)
    except OSError as exc:
        if os.path.lexists(tmp):
            tmp.unlink()
        raise SymmetryBridgeError("WRITE_FAILED", f"failed writing certificate: {exc}") from exc
    return cert


def main(argv: Any = None) -> int:
    try:
        args = _validate_argv(argv)
        mode, emit_json, target = _parse_cli_args(args)
        if mode == "standalone":
            cert = build_certificate()
            if emit_json:
                sys.stdout.write(canonical_json_bytes(cert).decode("ascii"))
            else:
                sys.stdout.write(
                    f"PASS {cert['track_id']} payload_sha256={cert['payload_sha256']} "
                    f"certificate_sha256={cert['certificate_sha256']}\n"
                )
            return 0
        if mode == "write":
            cert = write_certificate_file(target)
            sys.stdout.write(
                f"WROTE {Path(str(target)).name} certificate_sha256={cert['certificate_sha256']}\n"
            )
            return 0
        cert = verify_certificate_file(target)
        sys.stdout.write(
            f"OK {cert['track_id']} certificate_sha256={cert['certificate_sha256']}\n"
        )
        return 0
    except SymmetryBridgeError as exc:
        sys.stderr.write(f"FAIL {exc}\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""
Standalone CLI for SU(2)_k Chern-Simons, Jones Polynomials,
Poincare-Disk SL(2,Z) Modularity, and Exact NTT+CRT Convolutions.

Zero floats, zero bare `assert`s, strict Zone-B fail-closed validation,
race-free per-component `dir_fd` (`openat`) traversal eliminating intermediate-symlink
`renameat2` TOCTOU and atomic `O_CREAT | O_EXCL` temp + `os.replace(..., src_dir_fd, dst_dir_fd)`
writes eliminating hardlink post-`nlink` races, immune to deleted CWD (`CWD_UNAVAILABLE`),
space- and equals-syntax flag-like/empty path arguments (`--check --json`, `--write=--json`,
`--write=`), hardlinks, FIFOs, symlinks, symlinked PWD, and non-canonical bytes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Sequence

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from jones_cs_poincare_ntt_oracle import (
    JonesPoincareNTTError,
    build_certificate,
    canonical_json_bytes,
    load_safe_bytes,
    parse_strict_json_text,
    require_safe_path,
    require_str,
    safe_write_bytes,
    validate_certificate_payload,
)

DEFAULT_CERT_PATH = _HERE / "jones_cs_poincare_ntt_certificate.json"
_EXIT_CODE_2_ERRORS = frozenset({"INVALID_CLI_ARGS", "CWD_UNAVAILABLE"})


def verify_certificate_file(
    cert_path: Path,
    *,
    full_replay: bool = True,
) -> dict[str, object]:
    """Fail-closed Zone-B verification of a canonical LF-only certificate file."""
    raw = load_safe_bytes(cert_path, "certificate_file")
    if b"\r" in raw:
        raise JonesPoincareNTTError("CR_FORBIDDEN", "certificate file must use LF endings only")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise JonesPoincareNTTError("INVALID_UTF8", "certificate file is not valid UTF-8") from exc
    obj = parse_strict_json_text(text, require_object=True)
    expected_raw = canonical_json_bytes(obj) + b"\n"
    if raw != expected_raw:
        raise JonesPoincareNTTError("NON_CANONICAL_CERT_BYTES", "certificate file bytes are not canonical JSON + LF")
    res = validate_certificate_payload(obj, full_replay=full_replay)
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    return res


def _reject_flag_like_path_args(tokens: list[str]) -> None:
    """Reject empty or flag-like path values for --check / --write (space or equals syntax)."""
    for idx, tok in enumerate(tokens):
        if tok in ("--check", "--write"):
            if idx + 1 < len(tokens):
                nxt = tokens[idx + 1]
                if not nxt or nxt.startswith("-"):
                    raise JonesPoincareNTTError("INVALID_CLI_ARGS", f"{tok} requires a non-empty non-flag path argument")
        elif tok.startswith(("--check=", "--write=")):
            flag, _, val = tok.partition("=")
            if not val or val.startswith("-"):
                raise JonesPoincareNTTError("INVALID_CLI_ARGS", f"{flag} requires a non-empty non-flag path argument")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Jones/CS/Poincare/NTT Exact Certifier CLI",
        allow_abbrev=False,
    )
    mode = parser.add_mutually_exclusive_group(required=False)
    mode.add_argument("--standalone", action="store_true", help="Certify all 3 theorems and emit canonical certificate JSON")
    mode.add_argument("--write", nargs="?", const=str(DEFAULT_CERT_PATH), metavar="OUT_PATH", help="Write canonical certificate JSON to file")
    mode.add_argument("--check", metavar="CERT_PATH", help="Verify canonical certificate JSON (full replay by default)")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON output")
    parser.add_argument("--no-replay", action="store_true", help="With --check, validate schema and digests without full replay")

    try:
        if argv is None:
            src_argv: Sequence[object] = sys.argv[1:]
        else:
            if type(argv) not in (list, tuple):
                raise JonesPoincareNTTError("INVALID_CLI_ARGS", "argv must be a strict list or tuple")
            src_argv = argv
        raw_argv: list[str] = [require_str(x, "argv", min_len=0) for x in src_argv]
        _reject_flag_like_path_args(raw_argv)
        args = parser.parse_args(raw_argv)

        if args.no_replay and (args.standalone or args.write is not None):
            raise JonesPoincareNTTError("INVALID_CLI_ARGS", "--no-replay is valid only with --check")

        if args.standalone:
            cert = build_certificate()
            sys.stdout.write(canonical_json_bytes(cert).decode("ascii") + "\n")
            return 0

        if args.write is not None:
            out_path = require_safe_path(Path(args.write), "write_path", "FILE_WRITE_ERROR")
            cert = build_certificate()
            raw = canonical_json_bytes(cert) + b"\n"
            safe_write_bytes(out_path, raw, "write_path")
            summary = {
                "written": True,
                "file_sha256": hashlib.sha256(raw).hexdigest(),
                "payload_sha256": cert["payload_sha256"],
                "certificate_sha256": cert["certificate_sha256"],
                "all_theorems_passed": cert["payload"]["all_theorems_passed"],
            }
            print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
            return 0

        target_cert = args.check if args.check is not None else str(DEFAULT_CERT_PATH)
        res = verify_certificate_file(Path(target_cert), full_replay=not args.no_replay)
        print(json.dumps(res, sort_keys=True, separators=(",", ":")))
        return 0
    except JonesPoincareNTTError as exc:
        print(json.dumps({"valid": False, "error_code": exc.code, "error": exc.message}, sort_keys=True), file=sys.stderr)
        return 2 if exc.code in _EXIT_CODE_2_ERRORS else 1


if __name__ == "__main__":
    raise SystemExit(main())

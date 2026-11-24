#!/usr/bin/env python3
"""Track S22a (AUDIT-122A R2) CLI Audit Runner for perfect_quasi_modular_oracle.py.

Exact accepted CLI forms (strict fail-closed, D6 closed):
  (no arguments)        Emit canonical zero-float certificate JSON to stdout
  --standalone --json   Emit canonical zero-float certificate JSON to stdout
  --write [PATH]        Atomically write canonical 0o600 certificate JSON safely
  --check PATH          Strictly verify an existing certificate JSON file (fail-closed)

Rejects dash-prefixed or empty PATH arguments (including `--check --json`), stray or
duplicate `--json` flags (`--check PATH --json`, `--write PATH --json`), conflicting
modes, and unknown flags.

100% pure Python 3 stdlib, zero floats, zero bare asserts.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import perfect_quasi_modular_oracle as oracle  # noqa: E402

DEFAULT_CERT_PATH = HERE / "perfect_quasi_modular_certificate.json"

# Re-export key Zone-B verification and I/O primitives for uniform audit ergonomics
PerfectModularError = oracle.PerfectModularError
canonical_json_bytes = oracle.canonical_json_bytes
parse_strict_json_text = oracle.parse_strict_json_text
read_regular_bytes_capped = oracle.read_regular_bytes_capped
write_regular_bytes_safe = oracle.write_regular_bytes_safe
secondary_audit_payload = oracle.secondary_audit_payload
validate_certificate_payload = oracle.validate_certificate_payload
verify_certificate_dict = oracle.verify_certificate_dict
verify_certificate_file = oracle.verify_certificate_file


def validate_cli_argv(raw_argv: Any) -> list[str]:
    if type(raw_argv) is not list:
        raise oracle.PerfectModularError("INVALID_ARGV_TYPE", "argv must be exact list[str]")
    out: list[str] = []
    for idx, item in enumerate(raw_argv):
        out.append(oracle.require_str(item, f"argv[{idx}]"))
    return out


def _validate_path_arg(raw_path: str, flag: str) -> Path:
    oracle.require_ok(
        len(raw_path) > 0 and not raw_path.startswith("-"),
        "INVALID_PATH_ARG",
        f"{flag} requires a non-empty non-flag path argument",
    )
    return Path(raw_path)


def _parse_args(argv: list[str]) -> tuple[str, Path]:
    if argv in ([], ["--standalone", "--json"]):
        return "standalone", DEFAULT_CERT_PATH
    if argv == ["--write"]:
        return "write", DEFAULT_CERT_PATH
    if len(argv) == 2 and argv[0] == "--write":
        return "write", _validate_path_arg(argv[1], "--write")
    if len(argv) == 2 and argv[0] == "--check":
        return "check", _validate_path_arg(argv[1], "--check")
    raise oracle.PerfectModularError(
        "INVALID_CLI_ARGS",
        "usage: perfect_quasi_modular_audit.py ([--standalone --json] | --write [PATH] | --check PATH)",
    )


def main(raw_argv: list[str] | None = None) -> int:
    try:
        argv = validate_cli_argv(sys.argv[1:] if raw_argv is None else raw_argv)
        mode, target = _parse_args(argv)
        if mode == "standalone":
            cert = oracle.build_certificate()
            sys.stdout.buffer.write(oracle.canonical_json_bytes(cert) + b"\n")
            sys.stdout.buffer.flush()
            return 0
        if mode == "write":
            cert = oracle.build_certificate()
            oracle.write_regular_bytes_safe(target, oracle.canonical_json_bytes(cert) + b"\n")
            out = {
                "status": "WROTE",
                "payload_sha256": cert["payload_sha256"],
                "certificate_sha256": cert["certificate_sha256"],
            }
            sys.stdout.write(json.dumps(out, sort_keys=True, separators=(",", ":")) + "\n")
            return 0
        res = oracle.verify_certificate_file(target)
        sys.stdout.write(json.dumps(res, sort_keys=True, separators=(",", ":")) + "\n")
        return 0
    except oracle.PerfectModularError as exc:
        err = {"status": "FAIL", "code": exc.code, "error": exc.detail}
        sys.stderr.write(json.dumps(err, sort_keys=True, separators=(",", ":")) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

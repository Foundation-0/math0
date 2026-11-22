"""Deterministic CLI certifier for Track S11 (AUDIT-110): Erlang/OTP Supervision Tree Semantics.

Modes:
  --json            Emit canonical certificate JSON to stdout (default).
  --output <path>   Write canonical certificate JSON (LF-terminated) to <path>.
  --check <path>    Validate an existing certificate JSON file and verify exact
                    recomputation parity against build_erlang_otp_supervision_certificate().

Pure Python 3 stdlib. Zero floats. Zero bare assert statements.
"""
from __future__ import annotations

import argparse
import json
import os
import sys

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

from erlang_otp_supervision_oracle import (  # noqa: E402
    OtpSupervisionError,
    build_erlang_otp_supervision_certificate,
    validate_certificate,
)


def format_pretty_json(cert: dict) -> str:
    return json.dumps(cert, indent=2, sort_keys=True, allow_nan=False) + "\n"


def _load_strict_json(raw_text: str):
    def _no_dup_keys(pairs):
        out = {}
        for k, v in pairs:
            if k in out:
                raise OtpSupervisionError("ERR_CERT_JSON", f"duplicate JSON key {k!r}")
            out[k] = v
        return out

    def _reject_float(token: str):
        raise OtpSupervisionError("ERR_CERT_FLOAT", f"float literal forbidden: {token!r}")

    try:
        return json.loads(
            raw_text,
            object_pairs_hook=_no_dup_keys,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except OtpSupervisionError:
        raise
    except (ValueError, TypeError) as exc:
        raise OtpSupervisionError("ERR_CERT_JSON", f"invalid JSON: {exc}") from exc


def check_certificate_file(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as fh:
        raw_text = fh.read()
    loaded = _load_strict_json(raw_text)
    validate_certificate(loaded)
    fresh = build_erlang_otp_supervision_certificate()
    if raw_text != format_pretty_json(fresh):
        raise OtpSupervisionError("ERR_CERT_DRIFT", "file bytes differ from canonical fresh recomputation")
    return loaded


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Track S11 (AUDIT-110) Pure-Z/Q Erlang/OTP Supervision Tree Semantics Certifier"
    )
    parser.add_argument("--json", action="store_true", help="Print canonical JSON to stdout")
    parser.add_argument("--output", metavar="PATH", help="Write canonical JSON certificate to PATH")
    parser.add_argument("--check", metavar="PATH", help="Validate & recompute-verify certificate PATH")
    args = parser.parse_args(argv)

    if args.check:
        cert = check_certificate_file(args.check)
        if args.json:
            sys.stdout.write(format_pretty_json(cert))
        else:
            sys.stdout.write(
                f"OK AUDIT-110 canonical_sha256={cert['canonical_sha256']} "
                f"pillars={cert['summary']['pillars_passed']} "
                f"controls={cert['summary']['must_fail_controls_verified']}\n"
            )
        return 0

    cert = build_erlang_otp_supervision_certificate()
    rendered = format_pretty_json(cert)
    if args.output:
        with open(args.output, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(rendered)
    if args.json or not args.output:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Sole CLI entrypoint, standalone certifier & fail-closed Zone-B verifier for Track S21b.

Track S21b: Escher Self-Application Fixed-Point Tomography (Drawing Hands / Print Gallery)
& Negative-Space Dual Complex Miner (Sky & Water) on Foundation-0/aletheia-corpus.
(Note: `escher_dual_miner_oracle.py` is a pure library module; invoke CLI commands here.)

Usage:
  python3 -I -B escher_dual_miner_audit.py --standalone --json
  python3 -I -B escher_dual_miner_audit.py --check escher_dual_miner_certificate.json
  python3 -I -B escher_dual_miner_audit.py --live-disk .. --json
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from escher_dual_miner_oracle import (
    EscherMinerError,
    canonical_json_bytes,
    canonical_sha256,
    compute_escher_dual_miner_payload,
    constant_time_hex64_equal,
    parse_strict_json_text,
    read_strict_utf8_file,
    require_exact_dict,
    require_str,
    verify_live_disk_parity,
)

SCHEMA_VERSION = "aletheia.track_s21b.escher_self_application_dual_miner.v1"
TRACK_ID = "track-s21b-escher-self-application-dual-miner"
REQUIRED_CERT_KEYS = frozenset((
    "schema_version",
    "track_id",
    "oracle_class",
    "novelty_tier",
    "payload",
    "payload_sha256",
    "certificate_sha256",
))


def build_certificate() -> dict[str, Any]:
    """Deterministically build the pinned exact Z/Q Track S21b certificate."""
    payload = compute_escher_dual_miner_payload()
    payload_sha = canonical_sha256(payload)
    body: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "oracle_class": "exact+empirical-corpus",
        "novelty_tier": "N1",
        "payload": payload,
        "payload_sha256": payload_sha,
    }
    cert_sha = canonical_sha256(body)
    body["certificate_sha256"] = cert_sha
    return body


def verify_certificate_dict(cert: Any) -> dict[str, Any]:
    """Fail-closed Zone-B verification of an in-memory certificate dictionary."""
    parsed = require_exact_dict(cert, "certificate")
    canonical_json_bytes(parsed)
    if frozenset(parsed.keys()) != REQUIRED_CERT_KEYS:
        raise EscherMinerError("CERT_KEYS_MISMATCH", "certificate top-level key set mismatch")

    expected = build_certificate()
    parsed_payload = require_exact_dict(parsed["payload"], "certificate.payload")
    recomputed_payload_sha = canonical_sha256(parsed_payload)
    if not constant_time_hex64_equal(parsed["payload_sha256"], recomputed_payload_sha, "payload_sha256"):
        raise EscherMinerError("PAYLOAD_SHA_MISMATCH", "recorded payload_sha256 does not match payload")

    body_without_cert_sha = {k: v for k, v in parsed.items() if k != "certificate_sha256"}
    recomputed_cert_sha = canonical_sha256(body_without_cert_sha)
    if not constant_time_hex64_equal(parsed["certificate_sha256"], recomputed_cert_sha, "certificate_sha256"):
        raise EscherMinerError("CERTIFICATE_SHA_MISMATCH", "recorded certificate_sha256 does not match body")

    if not constant_time_hex64_equal(recomputed_payload_sha, expected["payload_sha256"], "expected_payload_sha256"):
        raise EscherMinerError("PAYLOAD_RECOMPUTATION_MISMATCH", "payload diverges from deterministic recomputation")

    if not constant_time_hex64_equal(recomputed_cert_sha, expected["certificate_sha256"], "expected_cert_sha256"):
        raise EscherMinerError("CERT_RECOMPUTATION_MISMATCH", "certificate diverges from deterministic recomputation")

    return {
        "valid": True,
        "payload_sha256": recomputed_payload_sha,
        "certificate_sha256": recomputed_cert_sha,
    }


def verify_certificate_file(path: Path) -> dict[str, Any]:
    """Fail-closed verification of canonical JSON bytes, digests, and exact recomputation."""
    raw, text = read_strict_utf8_file(path)
    parsed = require_exact_dict(parse_strict_json_text(text, require_object=True), "certificate")
    canonical_raw = canonical_json_bytes(parsed)
    if raw not in (canonical_raw, canonical_raw + b"\n"):
        raise EscherMinerError("NON_CANONICAL_CERT_BYTES", "certificate file is not canonical JSON")
    return verify_certificate_dict(parsed)


def validate_cli_argv(argv: Any) -> list[str]:
    """Enforce exact list[str] CLI arguments with valid UTF-8 (rejects non-list, non-str, subclasses, surrogates)."""
    raw_argv = list(sys.argv[1:]) if argv is None else argv
    if type(raw_argv) is not list:
        raise EscherMinerError("INVALID_ARGV_TYPE", "argv must be exact list[str] or None")
    return [require_str(item, f"argv[{idx}]") for idx, item in enumerate(raw_argv)]


def main(argv: list[str] | None = None) -> int:
    try:
        clean_argv = validate_cli_argv(argv)
    except EscherMinerError as exc:
        sys.stderr.write(f"FAIL {exc.code}: {exc.detail}\n")
        return 1
    parser = argparse.ArgumentParser(description="Track S21b Escher Self-Application & Dual Complex Certifier")
    mode = parser.add_mutually_exclusive_group(required=False)
    mode.add_argument("--standalone", action="store_true", help="Compute and emit certificate")
    mode.add_argument("--check", type=Path, help="Verify a committed canonical certificate JSON file")
    mode.add_argument("--live-disk", type=Path, help="Verify live read-only parity against expedition root")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON output")
    args = parser.parse_args(clean_argv)

    if args.live_disk is not None:
        try:
            live_verdict = verify_live_disk_parity(args.live_disk)
        except EscherMinerError as exc:
            sys.stderr.write(f"FAIL {exc.code}: {exc.detail}\n")
            return 1
        if args.json:
            sys.stdout.write(canonical_json_bytes(live_verdict).decode("ascii") + "\n")
            return 0
        sys.stdout.write(
            f"OK live-disk-parity payload_sha256={live_verdict['payload_sha256']} "
            f"live_audits={live_verdict['live_audits_matched']}\n"
        )
        return 0

    if args.check is None:
        cert = build_certificate()
        if args.json:
            sys.stdout.write(canonical_json_bytes(cert).decode("ascii") + "\n")
            return 0
        sys.stdout.write(
            f"OK track-s21b payload_sha256={cert['payload_sha256']} "
            f"certificate_sha256={cert['certificate_sha256']}\n"
        )
        return 0

    try:
        verdict = verify_certificate_file(args.check)
    except EscherMinerError as exc:
        sys.stderr.write(f"FAIL {exc.code}: {exc.detail}\n")
        return 1

    if args.json:
        sys.stdout.write(canonical_json_bytes(verdict).decode("ascii") + "\n")
        return 0
    sys.stdout.write(
        f"OK verified payload_sha256={verdict['payload_sha256']} "
        f"certificate_sha256={verdict['certificate_sha256']}\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

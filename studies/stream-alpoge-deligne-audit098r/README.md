# Alpöge–Deligne Elliptic Curve Local-to-Global Exact Audit (`AUDIT-098R`)

> **Status:** Independently `VERIFIED` (`AUDIT-098R`, `honest_novelty_tier: N0`, `oracle_class: exact` + `anchor`).
> **Seats:** Author `spectral-prover` · Independent Clean-Room Verifier `verifier`.
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats, zero bare `assert`s, zero network calls).

## What This Study Verifies

Independent zero-shared-code pure-$\mathbb{Z}$ / pure-$\mathbb{Q}$ verification of the finite-field, Kummer-extension, and local-to-global arithmetic invariants (`W1`–`W6`) from the Alpöge–Deligne audit, including an erratum note on Hexagon v1 `AD-03`. See [`AUDIT_098_ALPOGE_DELIGNE_REPORT.md`](AUDIT_098_ALPOGE_DELIGNE_REPORT.md) for the complete mathematical audit and primary-source citations.

## Exact Reproduction (Offline, 3-Mode Isolated `-I` R4 Parity)

From this directory:

```bash
# 3-mode isolated determinism check (all 3 stdout streams match alpoge_deligne_certificate.json byte-for-byte):
python3 -I -B alpoge_deligne_certifier.py --json | sha256sum
python3 -I -O -B alpoge_deligne_certifier.py --json | sha256sum
python3 -I -B -W error alpoge_deligne_certifier.py --json | sha256sum
sha256sum alpoge_deligne_certificate.json

# R5 mutation-killing & bypass-rejection test suite (5/5 OK):
python3 -I -O -B -W error test_alpoge_deligne_r5.py
```

## Verification Receipts

- **Committed Certificate:** [`alpoge_deligne_certificate.json`](alpoge_deligne_certificate.json) (`sha256: b2c0ba0b662024c2d74256b9fc3c935701eca6b6d0862a23d1105ccd35924bf4`, matches 3-mode `-I` stdout byte-for-byte).
- **External `aletheia v2.0.0` Mutation Receipt:** `47 / 47` (`100.0%`) AST mutants killed + `23 / 23` (`100.0%`) AST `BoolOp` sub-clause deletions killed (`0` survivors).

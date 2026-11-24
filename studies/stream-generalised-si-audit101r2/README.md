# `generalised.si` `31`-Domain Discovery Catalog & Independent Pure-$\mathbb{Z}$/$\mathbb{Q}$ Certificate Audit (`AUDIT-101R2`)

> **Status:** Independently `VERIFIED` (`AUDIT-101R2`, `honest_novelty_tier: N0`, `oracle_class: exact` + `anchor`).
> **Seats:** Author `peer-weaver` · Independent Clean-Room Verifier `verifier`.
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s).

## Scope & Honest Offline vs. Live-Intake Disclosure

This study independently audits all `31` research domains published on `https://www.generalised.si` (pinned 2026-11-22 snapshot: `sitemap.txt` `lastmod: 2026-11-19T06:45:44Z`, `llms-full.txt`, `20` hosted `/files/...` certificates, plus `vatskishan03/Hadamard @ d8850221` and `vatskishan03/Quantum @ 0e2456e5`) with zero shared upstream verification code. See [`GENERALISED_SI_CATALOG.md`](GENERALISED_SI_CATALOG.md) for the full `31`-domain Law-5 cross-org mapping and `WP-01..13` (`0/13` public files) reproducibility audit.

- **Offline Self-Contained Reproduction (Runs Directly From This Repo, Zero Network):**
  - `generalised_si_certifier.py --standalone --json` runs all `8` exact pure-$\mathbb{Z}$/$\mathbb{Q}$ verifiers offline on compact known-answer witnesses (`CW(7,4)` + sparse rotation witness, Good/Williamson order-3, T-matrix order-3, bordered WT-5, `RDS(4,2,3,1)`, $\mathbb{Z}_5$ projection, Hamming `[7,4]`, $2\times 2$ cluster pair model, Lean 4 purity).
  - `test_generalised_si_r5.py` exercises every fail-closed guard, boundary, and single-clause R5 test offline (`4/4` OK).
- **Pinned Live-Intake Certificates (`generalised_si_certificate.json`, `generalised_si_catalog.json`):**
  - Generated via `--live --intake-root <staged_intake_dir>` against the pinned 2026-11-22 public downloads (`227/227` proper CW matrices, Good 53/55, Williamson 75, `34/34` T-matrices, `WT47`/`WT83`, `RDS(364,2,243,81)`, `729/729` `L31` orbits, `5/5` binary linear code ranks, exact $m_0..m_4$ moments on $4\times 4\times 4$ & $5\times 5\times 4$ 3D Ising DoS, `24/24` Ag–Pd cells, `7/7` Quantum `SHA256SUMS` + `4/4` 16-fault witnesses, and `4` pure-$\mathbb{Q}$ `CW(120,36)`/`CW(180,36)`/`CW(98,16)` sparse rotation witnesses).
  - Raw third-party HTML/repo mirrors are not bundled in this repository; every upstream file SHA-256 is pinned inside [`generalised_si_certificate.json`](generalised_si_certificate.json) so any external auditor can re-fetch the public URLs and rerun `--live` to verify `695d0df4...` byte-for-byte.

## Exact Offline Reproduction (3-Mode Isolated `-I` R4 Parity)

From this directory:

```bash
# 3-mode isolated determinism check on offline standalone mode (bit-identical 59511dde...):
python3 -I -B generalised_si_certifier.py --standalone --json | sha256sum
python3 -I -O -B generalised_si_certifier.py --standalone --json | sha256sum
python3 -I -B -W error generalised_si_certifier.py --standalone --json | sha256sum

# R5 mutation-killing & fail-closed unit suite (4/4 OK):
python3 -I -O -B -W error test_generalised_si_r5.py
```

## Verification Receipts

- **Standalone `--standalone --json` 3-Mode SHA-256:** `59511dde9f141b0dbd8c0060f6c4c03c9f7faddce500498ce5430e5d21643213` (inner `ffb5799b...`).
- **Pinned Live-Intake Certificates:** [`generalised_si_certificate.json`](generalised_si_certificate.json) (`695d0df4...`, inner `cd9b2a1d...`) & [`generalised_si_catalog.json`](generalised_si_catalog.json) (`39c64b58...`, inner `21a60829...`).
- **External `aletheia v2.0.0` Mutation Receipt:** `133 / 133` (`100.0%`) AST mutants killed + `119 / 119` (`100.0%`) AST boolean sub-condition deletions killed (`0` survivors).

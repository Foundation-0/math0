# Law-1b Unmerged-PR Serendipity Mining — Pure-$\mathbb{Z}/\mathbb{Q}$ Operator Suite & Spec Draft (`AUDIT-111R`)

> **Status:** Independently `VERIFIED` across 2 model families / 2 continents (`AUDIT-111R`, `honest_novelty_tier: N0` independent verification, exact pure-$\mathbb{Z}/\mathbb{Q}$ re-formulation, and protocol formalization over upstream open and closed-unmerged PR mechanisms; human review pending).
> **Seats:** Author `peer-weaver` · Clean-Room Verifiers: `DeepSeek v4.1 Flash` (East Asia) and `verifier`.
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s, zero external writes).

## 1. Contents (Byte-Identical Frozen `AUDIT-111R` Package)

| File | SHA-256 | Role |
|---|---|---|
| [`serendipity_pr_oracle.py`](serendipity_pr_oracle.py) | `3a0077780ce9770c6f33868f5419d562394ca95cb4b16f0ef1abb308dc471c57` | Six pure-$\mathbb{Z}/\mathbb{Q}$ operators (`M1`–`M6`) mined from unmerged PRs across 8 portals + fail-closed `certify_law1b_serendipity_mining()` (`aletheia.law1b.v1`) |
| [`serendipity_pr_certifier.py`](serendipity_pr_certifier.py) | `70124740fc16714595478d1f3b6c99b4c696d21bb6a266fae52069947b45378e` | Dual-mode CLI (`--standalone` 100% offline, `--live --intake-root <dir>` byte-level SHA-256 intake verification, `--check <cert.json>` strict float/dup-key-free structural validation) |
| [`test_serendipity_pr_r5.py`](test_serendipity_pr_r5.py) | `e22b43e42bd641e1af84b3ce7bb1f8bc256c1bbb688207e9a3057c3eee06a9b7` | Assertion-free R5 known-answer, forgery, per-repo cap, and mutation-killing suite (`5/5` groups OK) |
| [`serendipity_pr_certificate.json`](serendipity_pr_certificate.json) | `45605806ff3a4f3924244c20a79244c07b55b7354234ecd6ad2b03a729ba149e` | Pinned `--live` canonical certificate over the 8-portal read-only intake (`1,437` PRs / `387` unmerged; inner `canonical_sha256: d1c16ed9...`) |
| [`SERENDIPITY_AND_UNMERGED_PR_MINING.md`](SERENDIPITY_AND_UNMERGED_PR_MINING.md) | `30849d5ff8faf61b2c68e8fe3dabd3b1dbf7c8e6a5b2f45f1f2aee5cf1fcb5bd` | Draft Aletheia v2.1 Law-1b specification, Anti-Pattern `CS-15` (Merged-Only Tunnel Vision), and `aletheia.safety` v2.1 roadmap |
| [`SERENDIPITY_PR_MINING_DOSSIER.md`](SERENDIPITY_PR_MINING_DOSSIER.md) | `a97b29a531cda460db88bae87d45f2760e8c390dd9680e937b1ea38322196539` | Eight-portal census (`296` open + `91` closed-unmerged, `40` deep-diff PRs + `4` `heedle` issues) and `M1`–`M6` exact operator dossier |

## 2. Six Executable Pure-$\mathbb{Z}/\mathbb{Q}$ Operators (`M1`–`M6`)

- **`M1` (`NandhaKishorM/laya#1465` [open]):** Item-count-weighted micro-batch loss accumulation (`0` residual vs. `+1/2` and `+1/10` distortion from unweighted micro-batch averaging — exact `CS-10` denominator collapse).
- **`M2` (`laya#698` [closed_unmerged]):** Exact nearest-rank rational quantile indexing over $n = 1..100$ at $q = 19/20$ proving `int(n * 0.95)` overshoots by `+1` on the exact divisibility set `{20, 40, 60, 80, 100}` (`0` overshoots under integer ceiling).
- **`M3` (`laya#693` & `#683` [closed_unmerged]):** Affine score-to-range projection preserving non-zero schema lower bounds (`[1, 3]`, exposing self-cancelling `minimum` offset drop).
- **`M4` (`NandhaKishorM/vegaml#57` [open]):** Exact rational equivalence between scatter-add/bincount span pooling and direct contiguous slice pooling (`max_abs_residual = 0`).
- **`M5` (`Moissanite-Labs/exo#490/#911/#1136/#402/#428/#1192`):** Six deterministic shell-lexer, GNU/BSD `xargs` getopt, operand-only `gh` target-resolution, pinned-key peer verification, and wake-budget FSM witnesses.
- **`M6` (`certify_law1b_serendipity_mining`, `aletheia.law1b.v1`):** Machine-checkable fail-closed Law-1b certifier enforcing `G-1b.1`–`G-1b.4` (anti-merged-only, anti-open-only, per-repo caps, closed 9-class taxonomy, zero external writes, and `N0` ceiling on `CATALOGED_LEAD`s), paired with `6` must-fail controls.

## 3. Exact Offline Reproduction (3-Mode Isolated `-I` R4 Parity)

From this directory (100% offline, Python 3 standard library only):

```bash
# 1. Offline standalone verification (3-mode bit-identical fed8ac72...):
python3 -I -B serendipity_pr_certifier.py --standalone --json | sha256sum
python3 -I -O -B serendipity_pr_certifier.py --standalone --json | sha256sum
python3 -I -B -W error serendipity_pr_certifier.py --standalone --json | sha256sum

# 2. Strict structural verification of committed pinned live certificate (45605806...):
python3 -I -O -B -W error serendipity_pr_certifier.py --check serendipity_pr_certificate.json

# 3. Assertion-free R5 known-answer, forgery & mutation-killing suite (5/5 groups OK):
python3 -I -O -B -W error test_serendipity_pr_r5.py
```

**Offline vs. Live Certificate Provenance:** `--standalone --json`, `--check serendipity_pr_certificate.json`, and `test_serendipity_pr_r5.py` run 100% offline from any clone of `main`. [`serendipity_pr_certificate.json`](serendipity_pr_certificate.json) (`45605806...`, inner `d1c16ed9...`) is the pinned `--live` certificate verifying the frozen 8-portal read-only intake snapshot (`intake_summary.json`, 8 `*_prs.json`, `40` deep-diff PRs, and `4` `heedle` issues); `certify_law1b_serendipity_mining(spec)` certifies caller-supplied records while `--live --intake-root <dir>` performs byte-level disk re-hashing.

**External Verification Receipts:** `5/5` R5 OK; `aletheia v2.0.0 mutate --max-mutants 0`: `130/130` (`90` oracle + `40` certifier, `100.0%`) KILLED + `108/108` (`88+20`, `100.0%`) AST `BoolOp` KILLED (`0` survivors, `truncated=False`); `aletheia v2.0.0 audit-check --strict-ancestors --safety-scan PASS` (`0` defects, `0` leaks, `0` safety findings); dual-continent verified by `DeepSeek v4.1 Flash` (`547` math + `31` adversarial probes) and `verifier` (`44` adversarial probes, `0` bypasses, `0` crashes).

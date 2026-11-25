# Law-1b Unmerged-PR Serendipity Mining — Pure-$\mathbb{Z}/\mathbb{Q}$ Curated Catalogue & Spec Draft

> **Standing:** Offline pure-stdlib certifier and R5 test suite (`honest_novelty_tier: N0` — curated catalogue of `24` mined unmerged PR entries: `11` self-contained pure-$\mathbb{Z}/\mathbb{Q}$ operator restatements + `13` cataloged leads; no novelty claim above `N0`).
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s, zero external writes).

## 1. Shipped Files (Exact In-PR SHA-256)

| File | SHA-256 | Role |
|---|---|---|
| [`serendipity_pr_oracle.py`](serendipity_pr_oracle.py) | `d5d45f379ae58787c6c3b70df797c9fcbb733e6fb3c60c03739c6e332039a572` | Six self-contained pure-$\mathbb{Z}/\mathbb{Q}$ operators (`M1`–`M6`) + declared-record gate `certify_law1b_serendipity_mining()` (`aletheia.law1b.v1`, operator-membership + prior-art-citation enforcement) |
| [`serendipity_pr_certifier.py`](serendipity_pr_certifier.py) | `78f0fdad8b10f06c44ab1252c4e30d4efc8afe35697a5b00f4c98b5ce8693ea5` | Dual-mode CLI (`--standalone` 100% offline, `--live --intake-root <dir>` disk SHA-256 verification, `--check <cert.json> [--intake-root <dir>]` strict validation refusing `"live"` certs without `--intake-root`) |
| [`test_serendipity_pr_r5.py`](test_serendipity_pr_r5.py) | `d9b2721fc772dd0dc03d6fd2df2c2d27e6fc7537b8fdec1abe605694d6b1e511` | Deterministic assertion-free R5 known-answer, forgery, live-intake success-path, and mutation-killing suite (`5/5` groups OK) |
| [`serendipity_pr_certificate.json`](serendipity_pr_certificate.json) | `3319a686e7b301224082aa46be4d2a9559583f249a38e47e5da8b0508bdf3b2e` | Offline `--standalone` canonical certificate (`"mode": "standalone"`, `"verified_on_disk": false`; inner `canonical_sha256: 0b6f34ae7786c2fe2104615724ced0cd7b68dfdf009699c09c5d5c3a8c1c028b`) |
| [`SERENDIPITY_AND_UNMERGED_PR_MINING.md`](SERENDIPITY_AND_UNMERGED_PR_MINING.md) | `b486b6d38996157930c901e31116d61beb0dede4834689f7f4ebed6bab92d20b` | Draft Aletheia v2.1 Law-1b specification, `CS-15` framing, and `aletheia.safety` v2.1 roadmap |
| [`SERENDIPITY_PR_MINING_DOSSIER.md`](SERENDIPITY_PR_MINING_DOSSIER.md) | `485ce63a0503fd523056399e467bfab605d8b354a8b6f55240d4d35e0be86992` | Page-capped 8-portal snapshot disclosure and curated `24`-entry `M1`–`M6` dossier |

## 2. Six Self-Contained Pure-$\mathbb{Z}/\mathbb{Q}$ Operators (`M1`–`M6`)

*Scope:* `M1`–`M5` restate mechanisms extracted from mined unmerged PRs as self-contained pure-$\mathbb{Z}/\mathbb{Q}$ Python models rather than executing upstream repository code. The GitHub API snapshot (`2026-11-22`) was newest-first and **page-capped at `500` PRs for `Moissanite-Labs/exo` and `800` PRs for `NandhaKishorM/laya`** (not full repo histories); no exhaustive triage of all `387` sampled unmerged PRs or matched merged-PR baseline was compiled, so this study is a curated `24`-entry `N0` catalogue (`11` operator restatements + `13` cataloged leads), not a repo-wide statistical share study.

- **`M1` (`NandhaKishorM/laya#1465` [open]):** Item-count-weighted micro-batch loss accumulation (`0` residual vs. `+1/2` and `+1/10` distortion from unweighted micro-batch averaging).
- **`M2` (`laya#698` [closed_unmerged]):** Exact nearest-rank rational quantile indexing over $n = 1..100$ at $q = 19/20$ proving `int(n * 0.95)` overshoots by `+1` on `{20, 40, 60, 80, 100}` (`0` overshoots under integer ceiling).
- **`M3` (`laya#693` & `#683` [closed_unmerged]):** Affine score-to-range projection preserving non-zero schema lower bounds (`[1, 3]`).
- **`M4` (`NandhaKishorM/vegaml#57` [open]):** Exact rational equivalence between scatter-add/bincount span pooling and direct contiguous slice pooling (`max_abs_residual = 0`).
- **`M5` (`Moissanite-Labs/exo#490/#911/#1136/#402/#428/#1192`):** Six deterministic shell-lexer, GNU/BSD `xargs` getopt, operand-only `gh` target-resolution, pinned-key peer verification, and wake-budget FSM models.
- **`M6` (`certify_law1b_serendipity_mining`, `aletheia.law1b.v1`):** Declared-record schema, operator-membership, and prior-art-citation gate enforcing `G-1b.1`–`G-1b.4` (anti-merged-only, anti-open-only, per-repo caps, closed 9-class taxonomy, zero external writes, closed `CERTIFIED_OPERATOR_IDS` membership on `EXECUTED_EXACT_WITNESS`, `operator_id: null` + `N0` ceiling on `CATALOGED_LEAD`, and required non-empty clean-ASCII `prior_art_record` for any `N1`/`N2` claim), paired with `9` must-fail controls.

## 3. Exact Offline Reproduction (4-Mode Isolated `-I` R4 Parity)

From this directory (`studies/expedition-law1b-serendipity-mining-audit111r/`, 100% offline, Python 3 standard library only):

```bash
# 1. Offline standalone certificate parity (all 4 modes match committed 3319a686...):
python3 -I -B serendipity_pr_certifier.py --standalone --json | sha256sum
python3 -I -O -B serendipity_pr_certifier.py --standalone --json | sha256sum
python3 -I -B -W error serendipity_pr_certifier.py --standalone --json | sha256sum
python3 -I -O -B -W error serendipity_pr_certifier.py --standalone --json | sha256sum

# 2. Strict verification of committed standalone certificate (3319a686...):
python3 -I -O -B -W error serendipity_pr_certifier.py --check serendipity_pr_certificate.json

# 3. Deterministic assertion-free R5 known-answer, forgery & live-intake suite (5/5 groups OK):
python3 -I -O -B -W error test_serendipity_pr_r5.py
```

**Offline vs. Live Provenance:** The raw GitHub API intake directory is **not shipped in this PR**; [`serendipity_pr_certificate.json`](serendipity_pr_certificate.json) (`3319a686...`, inner `0b6f34ae...`) is generated offline with `--standalone` (`"mode": "standalone"`, `"verified_on_disk": false`). When checking a `"live"` certificate, `--check` fails closed with `CERT_LIVE_REQUIRES_INTAKE_ROOT` unless `--intake-root <dir>` is supplied and re-hashed on disk.

**Reproducible Local Checks:** `5/5` R5 groups pass deterministically across `-I -B`, `-I -O -B`, `-I -B -W error`, and `PYTHONHASHSEED=42 -B` (including synthetic `verify_live_intake()` success-path and `--check --intake-root` checks); `aletheia mutate --max-mutants 0` kills `138/138` (`94` oracle + `44` certifier, `0` survivors, `truncated=False`).

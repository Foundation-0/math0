# AUDIT-078 — Pure-Rational Epistemic Safety & Survey-Weighting Audit (`github.com/jdpru`)

- **Audit ID:** `AUDIT-078R` (Wave 2 Round 9, Arm R9-1; all 5 red-team defect classes `JDPRU-BYPASS-01..05` closed)
- **Epistemic Tier:** `N1` (Verified pure-$\mathbb{Q}$ executable oracles, deterministic static safety scanners, verbatim repository & tabular anchors, `79/79` `100.0%` R5 mutation kill across both Python modules; prior-art statistical/security theorems quarantined transparently as `N0`)
- **Governance Standard:** `Foundation-0/aletheia v1.4.0` (Laws 1–5: zero floats on trust paths or JSON certificates, zero bare `assert`s, `4/4` isolated `-I` R4 parity, `100.0%` R5 mutation kill, `audit-check --strict-ancestors PASS`)
- **External Write Count:** `0` (strictly read-only inspection of pinned clones)
- **Live Certificate SHA-256:** `0a58dfd9e60fbe7f64c6e7b88b30f76d5b6bf9de1f3cbcf490edc196182dc7cb` (`jdpru_epistemic_certificate.json`)
- **Standalone Certificate SHA-256:** `8b94cc8ac265027cb80474597cd6017ffdd3b7547d90777fe5a4332b7c96c21d` (`--standalone`)

---

## 1. Pinned Corpus & Law-4 Transparent Repository Classification

| Repository (`github.com/jdpru`) | Status | Pinned `HEAD` SHA | Scope in `AUDIT-078` |
|---|---|---|---|
| `cover-your-ais` | Original (`isFork: false`) | `aafd6217a61071beca2faa191e692bfc44651991` | **Pillar 1 primary target** — verbatim audit of all 11 checks + 1 consequence rule against `aletheia v1.4.0` |
| `CES-Accuracy-Analysis` | Original (`isFork: false`) | `9375b1bbd5a239c23cf7d442c4e7dd4094c9400c` | **Pillar 2 primary target** — exact pure-$\mathbb{Q}$ survey weighting, Kish $n_{\mathrm{eff}}$, Meng paradox, Simpson worsening, tail conservation, README-vs-CSV drift, and live `CLAUDE.md` self-audit |
| `CS-230-DynaRT` | Original (`isFork: false`) | `c024875d595c6529c3e82a43e7e10dafd173fb5b` | Background context (cognitive reaction-time RNN/LSTM/DVAE notebooks; `README.md:1-38`, SHA-256 pinned) |
| `fmriprepviz`, `fmri-aim4-outlier-detector`, `fmchisel-modal`, `iSPOT-Autoencoder` | Forks (`isFork: true`, Law-4 flagged) | Cataloged only (not cloned) | Excluded from original-authorship claims under Law-4 provenance quarantine |

### Verified Read-Only Artifact Digests (SHA-256)

| Repo-Relative Path | SHA-256 |
|---|---|
| `cover-your-ais/README.md` | `cb6c0825c03f3751f293304c6d4dc19df72f6d28f8fc9d7c8c9c4169d1ed66a9` |
| `cover-your-ais/prompts/ai-codebase-safety-audit.md` | `9aba164510e58e425e6056c82f0b9ec41248db30e20c2c999652e8f3c65518dc` |
| `CES-Accuracy-Analysis/CLAUDE.md` | `163ffa6f4ed8c127caa54f379665b084e6846935884a7a4999938585fa4c7b40` |
| `CES-Accuracy-Analysis/sensitivity_analyses/README.md` | `f56fe0bc254f4d3be6d45fa46b330ebaf99aaf93ecfc0a633a1d147c135b0598` |
| `CES-Accuracy-Analysis/sensitivity_analyses/results/headline_by_variant.csv` | `f244384f02908d07eb0cf6e345fd0c0baaed21270dd28e6d3d9f98b1b388cb95` |
| `CES-Accuracy-Analysis/sensitivity_analyses/results/prose_numbers_by_variant.csv` | `4176ed8f70500b7ba4723be99feb715ca8d294b6acaeca0c6f328b0a770784cf` |
| `CES-Accuracy-Analysis/tables_and_figures/input_tables/vars_used_by_anesrake.xlsx` | `b5b238173dc5685f746d131dc3cb3849ec5544d5ad7a6c8c2faa9d7cf45489b0` |
| `CS-230-DynaRT/README.md` | `2bc4245e84bc27e1a241f17af8fdc12eab612cb2a0aec05285cdc43d7f5e8d1b` |

---

## 2. Law-2 Steelman Credit (Genuine Strengths Observed)

Before enumerating gaps and exact failure witnesses, four genuine methodological strengths across JD Pruett's original repositories merit explicit credit:

1. **Honest Epistemic Boundary Statement (`cover-your-ais/README.md:15`):** The repository explicitly warns: *"Prompts are not security boundaries. Pair them with least-privilege credentials, sandboxing, backups, and enforced access controls."* Check 5 (`prompts/ai-codebase-safety-audit.md:21-22`) directly challenges prose-only rules (*"What enforces each one outside the model?"*), independently aligning with `AUDIT-069R` (`OpenResearch` `SKILL.md`) and `AUDIT-076R` (LangChain Knowledge Factory governance).
2. **Independent Multi-Agent Verifier Convergence (`CES-Accuracy-Analysis/CLAUDE.md:47-48`):** JD's 2024 data-defect workflow independently converged on read-only parallel workers plus independent verifier agents (*"phase 1 runs about 8 parallel agents; phase 2 has independent agents verify the hits; ... Agents are read-only on the repo and write their results to a scratch folder."*).
3. **Rigorous Primary-vs-Secondary Evaluation Design (`CES-Accuracy-Analysis`):** Benchmarking `10,487` state/district estimates (`3,927` demographic + `917` voting/admin + `5,643` candidate choice) while separating variables used in neither matching nor weighting (`7,208` observations across `16` secondary variables) avoids circular in-sample calibration evaluation.
4. **Forensic Guide-Copy-Paste Detection (`CES-Accuracy-Analysis/supplementary_material.tex:524-575`):** The authors caught real historical documentation drift in official CES guides: the 2012 guide states *"Weights larger than 7 were trimmed"* (`p. 17`) despite codebook `V103` reporting `max = 20.00044` (`p. 27`), and the 2014 guide verbatim copy-pasted the 2012 `V103` table (`N = 54,535` instead of `56,200`; `max = 20.00044` exceeding the stated `15` trim cap).

---

## 3. Pillar 1 — `cover-your-ais` ↔ `Foundation-0/aletheia v1.4.0` & `AUDIT-076R`

### 3.1 Verbatim 12-Item Coverage Matrix (`prompts/ai-codebase-safety-audit.md:9-42`)

Exact pure-$\mathbb{Q}$ accounting via `evaluate_prompt_vs_oracle_coverage`:
- **Total items:** `12` (`11` numbered checks + `1` final consequence-warning rule at `L42`)
- **Covered by `aletheia v1.4.0`:** `2/12` (`1/6` = `16.67%`)
- **Partial in `aletheia v1.4.0`:** `4/12` (`1/3` = `33.33%`; covered + partial = `1/2` = `50.00%`)
- **Genuine `aletheia v1.5` static-scanner gaps (`GAP_V15`):** `6/12` (`1/2` = `50.00%`)
- **Prompt-only blind spots (`prompt_blind_spot = True`):** `12/12` (`1/1` = `100.00%` lack external deterministic enforcement when run purely as prose)

| Item (`ai-codebase-safety-audit.md`) | Threat Class | `aletheia v1.4.0` Status | Mapped `v1.5` Candidate Gap |
|---|---|---|---|
| Check 1 (`L9-10`) | Non-local/prod DB in test/dev configs | `PARTIAL` (`CS-12` Trust-Boundary Shadow) | `CYA-GAP-05` |
| Check 2 (`L12-13`) | Shell-readable prod creds (`~/.aws`, `~/.kube`, `~/.netrc`, etc.) | `PARTIAL` (`CS-12`, Law-5 hygiene) | `CYA-GAP-05` |
| Check 3 (`L15-16`) | Unguarded `rm -rf "$VAR"` without `${VAR:?}` / `set -u` | **`GAP_V15`** | **`CYA-GAP-03`** |
| Check 4 (`L18-19`) | One-command infra destruction (`*.tfstate`, `--auto-approve`) | `PARTIAL` (`CS-12`) | `CYA-GAP-05` |
| Check 5 (`L21-22`) | Prose-only rules in `AGENTS.md`/`CLAUDE.md`/`.cursorrules` | **`GAP_V15`** | **`CYA-GAP-05`** |
| Check 6 (`L24-25`) | Unprotected `main` & over-scoped `gh` token | `PARTIAL` (`CS-12`) | `CYA-GAP-05` |
| Check 7 (`L27-28`) | Cloud-synced folder (`iCloud`/`Dropbox`/`OneDrive`) 0-byte stubs | **`GAP_V15`** | **`CYA-GAP-06`** |
| Check 8 (`L30-31`) | Unpinned MCP (`@latest`, `npx -y`), hooks, `--yolo`, **hidden Unicode** | **`GAP_V15`** | **`CYA-GAP-01` / `CYA-GAP-02`** |
| Check 9 (`L33-34`) | CI `pull_request_target` on untrusted input with secrets/write | **`GAP_V15`** | **`CYA-GAP-04`** |
| Check 10 (`L36-37`) | Auto-approve modes & non-interactive shell `alias rm=` traps | **`GAP_V15`** | **`CYA-GAP-06`** |
| Check 11 (`L39-40`) | Uncapped money/message tools lacking allowlist/units/confirmation | `COVERED` (`CS-11`, `CS-12`, `AUDIT-076R` gate) | `NONE` |
| Final Rule (`L42`) | Consequence-naming output warnings (*"The study found..."*) | `COVERED` (deterministic refusal codes + Law-4 citation check) | `NONE` |

### 3.2 Six Reverse-Extracted `aletheia v1.5` Candidate Scanners (`CYA-GAP-01..06`)

Implemented deterministically in `jdpru_epistemic_weighting_oracle.py` (`scan_hidden_unicode_exact` + `audit_agent_safety_surface`):

1. **`CYA-GAP-01` (Hidden / Trojan-Source Unicode Scanner):** Detects zero-width & BOM formatters (`U+200B..U+200F`, `U+2060`, `U+FEFF`), CVE-2021-42574 BiDi controls (`U+061C`, `U+202A..U+202E`, `U+2066..U+2069`), and Unicode Tag prompt-smuggling characters (`U+E0000..U+E007F`) with exact `(line, col, codepoint, category)`. Live scan of `cover-your-ais/prompts/ai-codebase-safety-audit.md` confirms `clean: true` (`0` hidden characters).
2. **`CYA-GAP-02` (Unpinned MCP / Permission-Bypass Scanner):** Flags `@latest`, `npx` with `-y`/`--yes`/`-qy` (including intervening flags like `npx -q -y`), `--dangerously-skip-permissions`, `--yolo`, and `SessionStart` hooks across every match on every line.
3. **`CYA-GAP-03` (Unguarded Recursive-Delete Scanner):** Tracks `nounset` state line-by-line and segment-by-segment (`set -u`/`set -o nounset` enables; `set +u`/`set +o nounset` disables; comments stripped), and flags any mixed short/long recursive+force `rm` (`-rf`, `-fr`, `-r -f`, `--recursive -f`, `-f --recursive`, `-r --force`, `--recursive --force`) referencing `$VAR` unless protected by active `nounset` or per-argument `${VAR:?}` expansion (closing `JDPRU-BYPASS-01`).
4. **`CYA-GAP-04` (Untrusted CI Agent Privilege Scanner):** Flags `pull_request_target` combined with `secrets.*`, bracket `secrets['...']`, `toJSON(secrets)`, `write-all`, or any `<scope>: write` permission (closing `JDPRU-BYPASS-02`).
5. **`CYA-GAP-05` (Prose-Only Governance & Host-Path Scanner):** Flags unbacked imperative prose rules (`commit only when asked`, `no PRs`, `code freeze`, `never push`, `ask before`, `git add -A`) and `~/` host-home path dependencies in rule files.
6. **`CYA-GAP-06` (Shell Alias Illusion & Cloud-Sync Scanner):** Flags `alias rm=` profile safety-net illusions (absent in non-interactive `bash -c`) and `iCloud`/`Dropbox`/`OneDrive` synced-repo hazards.

### 3.3 Five Prompt-Only Blind Spots (`PROMPT-BLIND-01..05`)

1. **`PROMPT-BLIND-01` (Self-Auditing Paradox, `L6-7`):** Asking the same LLM agent to obey *"audit first and change nothing"* is vulnerable to indirect prompt injection embedded in the very repo files (including Check 8 hidden Unicode) it reads during the audit.
2. **`PROMPT-BLIND-02` (Zero R4/R5 Determinism):** Prose audits produce non-reproducible natural-language summaries with no isolated `-I` bit-identical verification and no mutation-tested enforcement gates.
3. **`PROMPT-BLIND-03` (Zero Canonical SHA-256 Receipts):** No cryptographic binding connects findings to exact pinned commit SHAs and file digests.
4. **`PROMPT-BLIND-04` (Unanchored Empirical Citation, `L42`):** *"The study found that kind of warning cut agent harm far more than restating a rule"* omits author, title, year, DOI/URL, and effect size — an explicit Law-4 `N0` unanchored claim.
5. **`PROMPT-BLIND-05` (Silent Prose-vs-Artifact Drift):** Prose audits do not cross-check hand-typed markdown tables against regenerated CSV/XLSX outputs — demonstrated directly on JD's own `CES-Accuracy-Analysis` repository below.

### 3.4 Live Self-Audit of `CES-Accuracy-Analysis/CLAUDE.md` (`9375b1bb`)

Running `audit_agent_safety_surface` live on `CES-Accuracy-Analysis/CLAUDE.md` triggers **`5` concrete findings** (`risk_level: "ELEVATED"`, `gap_ids_present: ["CYA-GAP-05"]`):

| `CLAUDE.md` Line | Verbatim Excerpt | Triggered `cover-your-ais` Check | Finding Detail |
|---|---|---|---|
| `L9` | `delete the ~/ces_sens_scratch/_cache pickles` | Check 2 / Check 3 | `host_home_tilde_dependency` |
| `L17` | `lives at ~/Downloads/Governor_Returns_2024.xlsx, outside the repo` | Check 2 | `host_home_tilde_dependency` |
| `L29` | `Commit only when asked.` | Check 5 (prose-only rule) | `Commit only when asked` |
| `L30` | `Work on main and merge directly. No PRs.` | Check 5 & Check 6 (unprotected `main`) | `No PRs` |
| `L32` | `Stage with git add -A.` | Check 2 & Check 4 (stray-file staging hazard) | `git add -A` |

---

## 4. Pillar 2 — Exact Pure-$\mathbb{Q}$ Survey-Weighting Audit (`CES-Accuracy-Analysis`)

All results below are proved in exact reduced rational arithmetic (`fractions.Fraction`) with zero floating-point operations, directly bridging `CES-Accuracy-Analysis @ 9375b1bb` to `AUDIT-069R` (weighting/aggregation invariance) and `AUDIT-022/023` (`weft-loom#42` Simpson's paradox).

### 4.1 Live Verified Dataset & ANESRake Counts

- **Exact Observation Partition (`prose_numbers_by_variant.csv:15-18`):**
  $$3{,}927\text{ (Demographic)} + 917\text{ (Voting/Admin)} + 5{,}643\text{ (Candidate Choice)} = 10{,}487 = \texttt{NObsTotal}.$$
- **Secondary ("Neither") Variables (`prose_numbers_by_variant.csv:19-20, 29-31`):** `16` variables, `7,208` observations; cell pairs: `62` improved + `32` worsened + `3` unchanged = `97`, so exact fraction worsened is **`32/97`** (`32.99%`).
- **Live Pure-Stdlib XLSX Parse (`tables_and_figures/input_tables/vars_used_by_anesrake.xlsx`):** Exact `"Used"` counts per election year are `2006: 6, 2008: 6, 2010: 9, 2012: 9, 2014: 9, 2016: 8, 2018: 8, 2020: 8, 2022: 7`, confirming `AnesrakeUsedRange = 6--9` (`prose_numbers_by_variant.csv:14`) verbatim.

### 4.2 Exact Kish Effective Sample Size from Published 2012 CES `V103` Statistics

From `supplementary_material.tex:540, 556-560`, the 2012 CES common-content weight `V103` codebook reports $N = 54{,}535$, $\mu_w = 1$, $\mathrm{SD} = 1.31757$, $\min = 0.00001$, $\max = 20.00044$. Using `compute_kish_from_summary_stats_exact`:

| SD Convention | Exact Kish $\mathrm{DEFF}$ | Decimal $\mathrm{DEFF}$ | Exact Kish $n_{\mathrm{eff}}$ | Decimal $n_{\mathrm{eff}}$ | Sample Loss |
|---|---|---|---|---|---|
| Sample SD ($s_w = 131757/100000$) | `746027585505083/272675000000000` | **`2.735959`** | `14870331125000000000/746027585505083` | **`19,932.68`** | **`63.45%`** |
| Population SD ($\sigma_w = 131757/100000$) | `27359907049/10000000000` | **`2.735991`** | `545350000000000/27359907049` | **`19,932.45`** | **`63.45%`** |

Weight dispersion alone destroys **`63.45%`** of the `54,535`-respondent CES sample (`2.74x` variance inflation) *before* accounting for nonprobability selection bias.

### 4.3 Exact Bhatia–Davis Extremal $\mathrm{DEFF}$ Bounds from Published Weight Caps

For any mean-`1` weight distribution supported on $[w_{\min}, w_{\max}]$, the Bhatia–Davis variance bound (`N0` classical theorem) yields exact worst-case $\mathrm{DEFF}_{\max} = 1 + (1 - w_{\min})(w_{\max} - 1) = w_{\min} + w_{\max} - w_{\min} w_{\max}$ and minimum retention $n_{\mathrm{eff}}/n \ge 1/\mathrm{DEFF}_{\max}$. Evaluated on all published CES caps (`manuscript.tex:795`, `supplementary_material.tex:331, 559-560`):

| Release / Scheme | $[w_{\min}, w_{\max}]$ | Exact $\mathrm{DEFF}_{\max}$ | Exact $\min(n_{\mathrm{eff}}/n)$ | Max Sample Loss |
|---|---|---|---|---|
| CES 2006 | `[0, 2.9]` | `29/10` (`2.9000`) | `10/29` (`34.48%`) | `65.52%` |
| CES 2008 | `[0, 6.5]` | `13/2` (`6.5000`) | `2/13` (`15.38%`) | `84.62%` |
| CES 2010 | `[0, 7.0]` | `7/1` (`7.0000`) | `1/7` (`14.29%`) | `85.71%` |
| CES 2012 (`V103`) | `[0.00001, 20.00044]` | `50000624989/2500000000` (`20.0002`) | `2500000000/50000624989` (`5.00%`) | **`95.00%`** |
| CES 2014–2020 | `[0, 15.0]` | `15/1` (`15.0000`) | `1/15` (`6.67%`) | `93.33%` |
| CES 2022 | `[0, 15.5]` | `31/2` (`15.5000`) | `2/31` (`6.45%`) | `93.55%` |
| `anesrake` (`cap = 5`) | `[0, 5.0]` | `5/1` (`5.0000`) | `1/5` (`20.00%`) | `80.00%` |

**Concrete Small-Domain Witness (`n = 50`, cap `15`):** `2` respondents at $w = 15$ and `48` respondents at $w = 5/12$ (exact mean `1`, `cap_exceeded = False`) attain exact Bhatia–Davis equality (`slack = 0/1`) with $\mathrm{DEFF} = \mathbf{55/6}$ (`9.1667`), $n_{\mathrm{eff}} = \mathbf{60/11}$ (`5.4545` — **`89.09%`** collapse). Under orthogonal raking ($\mathrm{Bias}_{\text{unwt}} = \mathrm{Bias}_{\text{wt}} = 3$, $\sigma_Y^2 = 100$), `audit_bias_variance_weighting_mse_exact` proves exact MSE jumps from **`11/1`** to **`82/3`** ($\Delta \mathrm{MSE} = \mathbf{+49/3} > 0$), explaining why raking on covariates uncorrelated with secondary outcomes strictly increases error (`AnesThreeVarIncrease = +0.3`, `AnesHighestYears = seven`, `32/97` worsened `Neither` cells).

### 4.4 Exact Meng (2018) Big-Data Paradox (`manuscript.tex:317`)

For $f = 1/100$ and data-defect correlation $\rho_{R,Y} = -1/200$ (`manuscript.tex:317`), `compute_meng_effective_n_exact` yields:
$$n_{\mathrm{eff}}^{\mathrm{Meng}} = \frac{f}{(1-f)\rho_{R,Y}^2} = \frac{1/100}{(99/100)(1/40{,}000)} = \mathbf{\frac{40{,}000}{99}} = 404.\overline{04}.$$
Against $n = 2{,}300{,}000$ respondents, exact efficiency is **`2/11385`** (`0.0176%`) — a **`99.9824%`** effective sample collapse!

### 4.5 Exact National-Raking-vs-State Simpson Worsening & `A2_named_only` Sign Flips

- **Pure-$\mathbb{Q}$ National-vs-State Witness (`audit_national_raking_state_simpson_exact`):** Two states (`S1`, `S2`), each with $n_A = 80, n_B = 20$ ($N = 200$, unweighted national share $p_A = 4/5$) raked to national target $\tau_A = 1/2$ produce exact national weights $w_A = 5/8, w_B = 5/2$ ($\mathrm{DEFF} = 25/16$, $n_{\mathrm{eff}} = 128$). National demographic bias drops from **`3/10`** to **`0/1`**, while **every state's outcome error worsens `2.5x`** (`S1`: `-2/25 -> -1/5`, `S2`: `+2/25 -> +1/5`; state MAE `2/25 -> 1/5`), directly illustrating why national `anesrake` calibration harms state-level secondary estimates (`CS-08` Simpson mechanism).
- **Live `A2_named_only` Trend Sign Flips (`headline_by_variant.csv:9, 11, 17`):** Removing party-level items flips BOTH secondary-variable trend slopes: matching-only $\beta$ flips from **`+111/1000`** (`+0.111`) to **`-3/100`** (`-0.030`), weighted $\beta$ flips from **`-19/1000`** (`-0.019`) to **`+23/1000`** (`+0.023`), and `AnesHighestYears` drops from `seven` to `two`.

### 4.6 Exact `|error| > 20` Tail-Error Conservation & Live `README.md`-vs-CSV Drift

- **Tail-Error Flow Conservation (`prose_numbers_by_variant.csv:20, 44-51`):** Across `7,208` `Neither` observations:
  $$357\text{ (matching)} - 106\text{ (moved below 20)} = 251\text{ (stayed } > 20\text{)}, \qquad 251 + 108\text{ (crossed above 20)} = \mathbf{359}\text{ (weighted)},$$
  with exact 4-cell non-negative 2×2 contingency verification (`stayed_le20 = 7208 - 357 - 108 = 6743`, `251 + 106 + 108 + 6743 = 7208`, closing `JDPRU-BYPASS-04`). Exact shares verify the prose macros verbatim: `357/7208 = 21/424` (`4.95%`), `251/7208` (`3.48%`), `359/7208` (`4.98%`). While mean error falls (`7.43 -> 6.80`), extreme tail failures **strictly increase** (`+2` net, `357 -> 359`).
- **Live Stale Hand-Typed Table Drift (`sensitivity_analyses/README.md:4, 39-44` vs `headline_by_variant.csv`):**
  1. `README.md:4` states *"This folder is untracked."* — false in commit `9375b1bb` (the entire folder is tracked).
  2. **`7` of `7` compared `base`-column headline metrics in `README.md:39-44` drifted from live `headline_by_variant.csv`** (reproduced after the Nov 15, 2026 bug fixes noted in `CLAUDE.md:18`):

| Macro (`base` column) | `sensitivity_analyses/README.md` | Live `headline_by_variant.csv` | Exact Delta (`CSV - README`) |
|---|---|---|---|
| `NeitherMeanAfter` | `8.2` (`41/5`, `L39`) | `8.1` (`81/10`, `L4`) | `-1/10` |
| `TrendSecMatchBeta` | `.113` (`113/1000`, `L41`) | `0.111` (`111/1000`, `L9`) | `-1/500` |
| `TrendSecMatchP` | `.089` (`89/1000`, `L41`, `L59`) | `0.095` (`19/200`, `L10`) | `+3/500` |
| `TrendSecWtdBeta` | `-.016` (`-2/125`, `L42`) | `-0.019` (`-19/1000`, `L11`) | `-3/1000` |
| `TrendSecWtdP` | `.701` (`701/1000`, `L42`) | `0.630` (`63/100`, `L12`) | `-71/1000` |
| `CesThreeVarReduction` | `1.1` (signed `-1.1`, `L43`) | `1.2` (`6/5`, `L15`) | `+1/10` |
| `GuideGapOverall` | `1.2` (`6/5`, `L44`, `L58`) | `1.3` (`13/10`, `L23`) | `+1/10` |

This mirrors the exact structural failure mode JD Pruett diagnosed in the official 2012/2014 CES Data Guides (`supplementary_material.tex:524-566`): hand-maintained prose summaries silently decouple from regenerated tabular data unless bound by deterministic certificate verification.

---

## 5. Law-4 Epistemic Quarantine (`N0` vs. `N1`)

- **`N1` (Mechanically Verified in `AUDIT-078R`):** All exact rational computations, hardened static scanner detections (`CYA-GAP-01..06`, `JDPRU-BYPASS-01..05` closed), live SHA-256 bindings with strict `.git/HEAD` ref-traversal & symlink containment, XLSX/CSV parses, `CLAUDE.md` self-audit findings, `7/7` README-vs-CSV drifts, `4/4` isolated `-I` R4 bit-identical parity, and `79/79` (`100.0%`) R5 mutation kill across `jdpru_epistemic_weighting_oracle.py` (`67/67`) and `jdpru_epistemic_audit.py` (`12/12`).
- **`N0` (Prior Art / Out-of-Scope / Unverified Claims Quarantined):**
  1. Kish (1965) effective sample size, Bhatia–Davis (2000) variance bound, Horvitz–Thompson / Hájek variance inflation, Simpson's paradox, and Meng (2018) Law of Large Populations are classical prior-art theorems (`N0`); our contribution is their zero-float pure-$\mathbb{Q}$ oracle realization and forensic application to `CES-Accuracy-Analysis`.
  2. CVE-2021-42574 (Trojan Source BiDi) and GitHub Actions `pull_request_target` security advisories are established prior art (`N0`).
  3. *"The study found that kind of warning cut agent harm far more than restating a rule"* (`cover-your-ais/prompts/ai-codebase-safety-audit.md:42`) lacks a citation and remains unverified `N0`.
  4. The 4 fork repositories on `github.com/jdpru` (`fmriprepviz`, `fmri-aim4-outlier-detector`, `fmchisel-modal`, `iSPOT-Autoencoder`) are excluded from original-authorship attribution (`N0`).
  5. Raw CES respondent microdata (Dataverse `.dta` files) are not bundled in `CES-Accuracy-Analysis` and were not downloaded; all microdata-level proofs operate on exact published summary tables and constructive witnesses (`N1` on released repo artifacts; microdata re-raking remains `N0`).

---

## 6. Reproduction & Falsification Criteria

### Exact Reproduction Commands (Run from `symbiosis/round9/arm1-jdpru/`)

```bash
# 1. Live read-only audit against pinned clones (regenerates canonical zero-float certificate)
python3 -I -B -W error jdpru_epistemic_audit.py --output jdpru_epistemic_certificate.json

# 2. Standalone pure-Q verification (zero external clones required)
python3 -I -B -W error jdpru_epistemic_audit.py --standalone --json

# 3. Full R5 & adversarial red-team test suite (-I -O -B -W error)
python3 -I -O -B -W error test_jdpru_epistemic_r5.py

# 4. Aletheia v1.4.0 mutation kill verification (requires PYTHONPATH=<aletheia-repo>)
python3 -B -W error -m aletheia mutate jdpru_epistemic_weighting_oracle.py \
  --test-cmd "python3 -I -O -B -W error test_jdpru_epistemic_r5.py" --add-cwd
python3 -B -W error -m aletheia mutate jdpru_epistemic_audit.py \
  --test-cmd "python3 -I -O -B -W error test_jdpru_epistemic_r5.py" --add-cwd
```

### Falsification Criteria

`AUDIT-078` is falsified if any of the following is demonstrated:
1. Any non-deterministic output across isolated `python3 -I -B -W error` runs of `jdpru_epistemic_audit.py` (live or `--standalone`).
2. Any IEEE-754 `float` accepted by any public oracle entry point or emitted anywhere in `jdpru_epistemic_certificate.json`.
3. Any bypass of `scan_hidden_unicode_exact`, `audit_agent_safety_surface` (`CYA-GAP-01..06`), or any pure-$\mathbb{Q}$ invariant check that causes an invalid input to return `"VERIFIED"` or `"CLEAN"` improperly.
4. Any surviving mutant under `aletheia v1.4.0 mutate --add-cwd` in either `jdpru_epistemic_weighting_oracle.py` or `jdpru_epistemic_audit.py`.
5. Any discrepancy between reported verbatim anchors/counts and the pinned `jdpru` commits (`aafd6217`, `9375b1bb`, `c024875d`).

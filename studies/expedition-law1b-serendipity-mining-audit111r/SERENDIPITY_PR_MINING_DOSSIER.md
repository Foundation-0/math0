# Track S12 — Law-1b Unmerged-PR Serendipity Dossier (8 Portals, 1,437 PRs Scanned)

**Audit Track:** Track S12 (`track-s12-serendipity-pr-mining`)  
**Protocol:** Aletheia Law 1b (Exhaustive Serendipity & Unmerged-PR Portal Mining — draft spec in [`SERENDIPITY_AND_UNMERGED_PR_MINING.md`](SERENDIPITY_AND_UNMERGED_PR_MINING.md))  
**External Writes:** `0` (strictly read-only GitHub API intake)  
**Honest Novelty Standing:** `N0` (independent verification, exact pure-$\mathbb{Z}/\mathbb{Q}$ re-formulation, and Law-5 cross-pollination of upstream open and closed-unmerged mechanisms)

---

## 1. Eight-Portal Read-Only Intake Census (`2026-11-22`)

Every portal below was queried with `state=all` (paginated) and frozen under `../intake-serendipity-prs/` with exact SHA-256 digests (`intake_summary.json`: `2456c15109f4...`, `DEEP_MINING_MANIFEST.json`: `c315b6621bf4...`, `Moissanite-Labs__heedle_issues.json`: `875808d793ef...`):

| Repository Portal | Fetched | Merged | Open | Closed-Unmerged | Unmerged Share | Frozen `*_prs.json` SHA-256 (prefix) |
|---|---:|---:|---:|---:|---:|---|
| `NandhaKishorM/laya` | 800 | 692 | 52 | 56 | `108/800` (`27/200`) | `d52729dcd73e...` |
| `Moissanite-Labs/exo` | 500 | 267 | 213 | 20 | `233/500` | `667e67a21034...` |
| `NandhaKishorM/vegaml` | 61 | 47 | 6 | 8 | `14/61` | `3fca3f41b058...` |
| `Moissanite-Labs/weft-loom` | 31 | 22 | 9 | 0 | `9/31` | `4f04a6e3f8c9...` |
| `Foundation-0/math0` | 20 | 9 | 10 | 1 | `11/20` | `976d6c50aac1...` |
| `Moissanite-Labs/siliquant` | 17 | 9 | 5 | 3 | `8/17` | `3e3c0f1e04ab...` |
| `chuanqisun/spaceship` | 4 | 1 | 0 | 3 | `3/4` | `60ec0ef10a46...` |
| `Moissanite-Labs/heedle` | 4 | 3 | 1 | 0 | `1/4` | `6056665aa73c...` |
| **Total (8 Portals)** | **1,437** | **1,050** | **296** | **91** | **`387/1437` (`129/479`)** | **`40` deep PRs (`19` open, `21` closed) + `4` `heedle` issues** |

Key structural takeaway: **`91` closed-unmerged PRs** across these 8 repositories — including `3/4` PRs on `chuanqisun/spaceship`, `56` on `laya`, `20` on `exo`, and `8` on `vegaml` — are completely invisible to any `main`-only or `open`-only audit.

---

## 2. Six Executable Pure-$\mathbb{Z}/\mathbb{Q}$ Operators & Verified Defect Witnesses (`M1`–`M6`)

All six operators below are implemented without floats or bare asserts in [`serendipity_pr_oracle.py`](serendipity_pr_oracle.py) and certified in [`serendipity_pr_certificate.json`](serendipity_pr_certificate.json):

### M1. Micro-Batch Item-Count Weighted Loss Accumulation (`NandhaKishorM/laya#1465` [open], `a0de0212...`)
- **Defect in Unmerged Patch (`laya/train.py`):** Dividing each micro-batch loss by `window_size` (number of micro-batches) rather than scaling by `len(batch) / window_items` gives tail items $2\times$ gradient weight on a `(4, 2)` tail window — an exact algebraic instance of Aletheia **`CS-10` (Sparse-Collision Denominator Collapse)**.
- **Exact $\mathbb{Q}$-Witnesses:**
  - On losses `[1, 1, 1, 1, 4, 4]` partitioned as `[4, 2]`: true full-batch mean = `2`, item-weighted accumulation = `2` (**residual `0`**), buggy unweighted mean = `5/2` (**distortion `+1/2`**).
  - On 3-item binary split `["1/5", "1/5", "4/5"]` partitioned as `[2, 1]`: true mean = `2/5`, item-weighted = `2/5` (**residual `0`**), buggy unweighted = `1/2` (**distortion `+1/10`**).

### M2. Nearest-Rank Rational Quantile Indexing (`NandhaKishorM/laya#698` [closed_unmerged], `b2209594...`)
- **Defect in Unmerged Patch (`laya/evals.py`):** Indexing p95 as `ordered[min(n - 1, int(n * 0.95))]` matches nearest-rank `ceil(19n/20) - 1` *only* when $20 \nmid n$. At every multiple of $20$, $19n/20$ is exact, causing a silent **+1 rank overshoot** (at $n = 20$, reports the maximum $x_{(20)}$ instead of $x_{(19)}$).
- **Exact $\mathbb{Z}$-Witness (`n = 1..100`, `q = 19/20`):** Buggy floor-index overshoots on the exact divisibility set `[20, 40, 60, 80, 100]` (`5/100` sizes, `exact_divisibility_match = True`); exact integer ceiling formula `(q_num * n + q_den - 1) // q_den - 1` has `0` overshoots.

### M3. Affine Score-to-Range Projection Offset Preservation (`NandhaKishorM/laya#693` & `#683` [closed_unmerged], `db63c862...`, `b9923438...`)
- **Defect in Two Independent Closed-Unmerged PRs (`laya/structured.py`):** Computing `idx = round(score) - minimum; value = minimum + idx` cancels `minimum` identically, dropping non-zero schema lower bounds!
- **Exact $\mathbb{Z}/\mathbb{Q}$-Witness (`[1, 3]`):** At 0-based score `0`, fixed projection returns `1` (in range) while buggy projection returns `0` (**out of schema range**, `offset_drop = 1`); at score `2`, fixed returns `3` while buggy returns `2`.

### M4. Direct Contiguous Span Pooling vs. Scatter-Add Equivalence (`NandhaKishorM/vegaml#57` [open], `a7d5ccba...`)
- **Mechanism (`vegaml/_common.py`):** Replaces $O(B \times L)$ dummy segment allocation, atomic `index_add_`, and `torch.bincount` with direct contiguous slice reductions, and clears `self._cap = {}` after `_run()` to prevent pinned layer-activation retention.
- **Exact $\mathbb{Q}$-Witness:** On a $6 \times 3$ rational hidden matrix with disjoint spans `[0, 2)` and `[3, 6)`, scatter-add + bincount and direct slice pooling produce identical rational outputs (`max_abs_residual = 0`, `exact_equivalence = True`).

### M5. Shell-Lexer, Getopt, Operand, Pinned-Key & Wake-Budget Witnesses (`Moissanite-Labs/exo` Unmerged PRs)
Six concrete security & state-machine mechanisms mined from unmerged `exo` PRs:
1. **`exo#490` [closed_unmerged] (`ed43f23f...`):** Odd backslash-newline inside backticks collapses before Bash lexing (`"un\\\nlink_sim --force"` $\to$ `"unlink_sim --force"`), whereas even backslashes keep one literal backslash and the newline (`"echo a\\\\\nb"` $\to$ `"echo a\\\nb"`).
2. **`exo#911` [open] (`518b1706...`):** Unquoted heredoc delimiter joins odd trailing backslash-newlines (`["payload", "E\\", "OF"]` closes `"EOF"` at index `2`), quoted delimiter does not (`-1`), and `<<-` strips leading tabs only on the joined logical line so `"E\\"` + `"\tF"` does NOT close `"EF"` (`-1`).
3. **`exo#1136` [open] (`f0df8ef7...`):** Full GNU/BSD `xargs` getopt parsing locates the invoked command `"sync_tool"` past `--max-args 1`, abbreviated `--max-a 1`, clustered `-rn 1`, and BSD `-J %`.
4. **`exo#402` [closed_unmerged] (`ecaa3ecc...`):** `gh` target resolution takes `-R`/`--repo` or positional URL operands only — ignoring GitHub URLs placed inside `--body` or `--duplicate-of` option values.
5. **`exo#428` [closed_unmerged] (`c8a89531...`):** Peer envelope verification checks strictly against the seat's pinned key directory, rejecting self-signed envelopes backed by a forged presence file (`REJECT_KEY_MISMATCH`) and holding unpinned seats (`HOLD_UNPINNED_SEAT`) — direct isomorphism to Aletheia `R6`/`R7`.
6. **`exo#1192` [open] (`2817df6e...`):** Wake-budget finite-state machine ensures `peer_turn`/`bus_turn`/`job_turn`/`stop` never reset the wake cap (`denied_wakes = 2` on exhausted cap), while only `principal_turn` renews it (`denied_wakes = 0`).

### M6. Fail-Closed Law-1b Serendipity-Mining Governance Gate (`certify_law1b_serendipity_mining`)
Certifies the complete 8-repo census (`1,437` PRs, `387` unmerged, `24` canonical pinned entries: `11` `EXECUTED_EXACT_WITNESS` + `13` `CATALOGED_LEAD`, `12` open + `12` closed-unmerged across all 9 mechanism classes) with `6/6` must-fail controls verified (`closed_unmerged` blind spot, non-zero external writes, lead claiming `N2`, uniform-hex placeholder SHA, float input, overlapping spans).

---

## 3. High-Signal Cataloged Unmerged Leads Across All 8 Portals (`N0`)

### 3.1 `chuanqisun/spaceship` Closed-Unmerged Gems (`3/4` PRs Closed-Unmerged!)
- **`spaceship#5` [closed_unmerged] (`7633dbee...`, `32f +3050/-94`) — Browser WebGPU Internal Activation Steering:** Runs LFM3 1.7B or Qwen3.5 2B directly in-browser on WebGPU; *knobs* add steering vectors to hidden states and *locked boxes* bias attention weights **without modifying the prompt**, running an unsteered counterfactual copy side-by-side and highlighting tokens flipped by steering. Direct bridge to Track S13 (`heedle` × `spaceship` × `laya/vegaml`).
- **`spaceship#3` [closed_unmerged] (`6521fc71...`, `314f +39670/-409`) — 4-Pane Parallel Model Comparison Arena (`spec-003`):** Shared opening prompt streamed across up to four independent provider/model panes with shared SSE parser and cached catalogs.
- **`spaceship#2` [closed_unmerged] (`278f +35244/-322`) — `pointerId`-Scoped Touch Gesture Arbitration:** Prevents secondary touches from cancelling/retargeting active gestures or firing synthesized `dblclick` deletions.

### 3.2 `Moissanite-Labs/heedle` Open PR `#8` & Issues `#2`, `#3`, `#6`, `#7`
- **`heedle#8` [open] (`7de102ec...`, `docs/session-queue.md`):** Proposed session queue beside the Heedle steering instrument while leaving the gate unchanged (`standing: proposed`).
- **`heedle#2` & `#3` [open]:** Bidirectional flow-to-parameter sensitivity mapping (*perturb data flow $\to$ observe parameter response; perturb parameter $\to$ observe data flow*) using a distilled shadow model to guide large-model strand pulling.
- **`heedle#6` [open] (`tide/1`):** Third Heedle host treating a color palette in OKLCH `(L, C, H)` as a model whose behavior is contrast across all foreground/background pairs checked **exhaustively** against a floor (finite-domain exact certifier!).
- **`heedle#7` [open]:** Cross-layer architectural weaving note linking to `siliconcordat/.github`.

### 3.3 Additional High-Signal Unmerged Gems (`laya`, `vegaml`, `siliquant`, `weft-loom`, `math0`)
- **`NandhaKishorM/laya`:**
  - `#1411` [closed_unmerged] (`bbb53b26...`): `10**400` JSON integer temperature raises `OverflowError` in `float()` (same root class as `warp-drive#30` Review `6011915046` huge-int JSON egress!).
  - `#925` [closed_unmerged] (`1db7c88d...`): `apply_confidence_gate` left stale `low_confidence: True` flags on re-gate; also caught transitive `import tensorflow` Bus Error (`USE_TF=0`).
  - `#783` [closed_unmerged] (`51ee966e...`) & `#747` [closed_unmerged] (`86f69ac2...`): Choice criteria permutation-invariance canonicalizer + identical-option slot-0 bias control (`choice_slot0_identical`).
  - `#1210` [open] (`74a2253c...`): Honest 3-seed refutation of single-seed soft-CE gain (`rlcd 0.7762 ± 0.0016` vs `soft-ce 0.7763 ± 0.0155`, paired difference flipped sign across seeds).
  - `#982` [open] (`4bcf3568...`): Three-way disjoint train / early-stopping validation / post-training temperature calibration split.
  - `#1524` [open] (`1d9aaae8...`) & `#1519` [open] (`216a723e...`): ONNX fused-export selected-checkpoint pinning & vega choice-label type round-trip preservation.
  - `#1282` [open] (`98b4677c...`) & `#1455` [closed_unmerged]: Exact evidence verification benchmark & outcome-logged per-question calibration loop.
- **`NandhaKishorM/vegaml`:** `#40` [open] (`aa1ad172...`, inference-only Rust port `2,367` LOC), `#10` [closed_unmerged] (`153657b1...`, fail-closed fine-tune validation preventing empty-batch crashes), `#42` [closed_unmerged] (clean CLI missing-file error), `#20` [closed_unmerged] (Pydantic structured question sheet).
- **`Moissanite-Labs/siliquant`:** `#11` [closed_unmerged] (`eb44099e...`, exact region-gain $\Phi$ integrals & closed-form scale bound later consolidated into `#12`) & `#6` [closed_unmerged] (`new ideas`).
- **`Moissanite-Labs/weft-loom`:** `#44` [open draft] (`e660cd3d...`, sign-lineage exact chance law for gated MLPs, two validity checks, and sign-flip evasion), `#36` [open] (`e0b431fd...`, C11 two-tiered Triangular Sum anchor gate against zero-fuel collapse), `#25` [open] (`ba1ca3e3...`, exemplary pre-freeze cancellation `FREEZE-DECISION-C.md` catching an information-theoretic identifiability trap *before* freezing!).
- **`Foundation-0/math0`:** `#3` [open] (`d94ad5d4...`, stdlib `gfq` exact minimum-distance checker over $\mathbb{F}_q$, $q \in \{2,3,4,5,7,8,9\}$, with Brouwer–Zimmermann codeword certificates), `#4` [open] (`232d5247...`, 15 smallest-gap Codetables attack), `#9` [open] (`3d319824...`, 66-room Sokoban Frontier open bounds `III-14`/`III-20`/`III-21`).

---

## 4. Clean-Room Verification Receipts (`aletheia v2.0.0`, `AUDIT-111R`)

- **Oracle, Certifier & Spec:** [`serendipity_pr_oracle.py`](serendipity_pr_oracle.py) (`3a007778...`), [`serendipity_pr_certifier.py`](serendipity_pr_certifier.py) (`70124740...`), [`test_serendipity_pr_r5.py`](test_serendipity_pr_r5.py) (`e22b43e4...`), [`serendipity_pr_certificate.json`](serendipity_pr_certificate.json) (`45605806...`), [`SERENDIPITY_AND_UNMERGED_PR_MINING.md`](SERENDIPITY_AND_UNMERGED_PR_MINING.md) (`30849d5f...`).
- **3-Mode Isolated `-I` R4 Parity (`-I -B`, `-I -O -B`, `-I -B -W error`):**
  - `--live --intake-root ../intake-serendipity-prs --json` == disk `serendipity_pr_certificate.json` bit-identically (`sha256: 45605806ff3a4f39...`, inner `canonical_sha256: d1c16ed9a5eb3782...`, `--check` `valid: true`, ZERO floats).
  - `--standalone --json` bit-identical offline (`sha256: fed8ac72d0b7e2fa...`, ZERO floats).
  - `test_serendipity_pr_r5.py`: **`5/5` OK** (`-I -O -B -W error`).
- **R5 Mutation & AST `BoolOp` Kill:** `aletheia v2.0.0 mutate --max-mutants 0 --add-cwd` **`90/90` (`oracle`) + `40/40` (`certifier`) = `130/130` (`100.0%`) KILLED, `0` survivors, `truncated=False`**; exhaustive AST `BoolOp` raise-guard sub-clause sweep **`88/88` (`oracle`) + `20/20` (`certifier`) = `108/108` (`100.0%`) KILLED, `0` survivors**.
- **Hygiene & Safety:** `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts serendipity_pr_certifier.py test_serendipity_pr_r5.py` **`PASS`** (`6` files, `2/2` R4, `0` defects, `0` leaks, `0` bare `assert`s, `0` safety findings, `PYCACHE=0`).

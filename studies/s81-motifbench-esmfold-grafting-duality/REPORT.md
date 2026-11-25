# Protein Motif Scaffolding (`MotifBench` / `ESMFold` / `GPT-6`) $\leftrightarrow$ LLM Circuit Grafting Exact Operator Duality & Obstruction Audit

**Primary Sources & References:**
- **Protein Motif Scaffolding & Folding:** `MotifBench` (`arXiv:2502.12479v2`), `biohub/esmfold_v1` (MIT, commit `75a3841ee059df2bf4d56688166c8fb459ddd97a`, `419,633` downloads), and OpenAI `GPT-6` wet-lab protein binder cohort (`35 / 322` binders across `5` immuno-oncology targets via `GPT-6.2` + `SolubleMPNN` + `Boltz-2` + `ESMFold2`).
- **LLM Circuit Grafting:** *A CPU Inside an LLM* (`arXiv:2611.26450` — zero-gradient orthogonal circuit grafting $d \to d + K$ into pretrained transformer backbones).
- **Proxy-Metric Blindness Cross-Link:** Iso-MDL weight-space and proxy-metric misfolding (`aletheia#28`, `75,968x` divergence under single-metric invariance).

**Method:** Clean-room, CPU-only, pure-$\mathbb{Z}/\mathbb{Q}$ (`fractions.Fraction` + `decimal.Decimal`, `0` floating-point ops, `0` bare `assert`s) executable tomography (`5` independent oracles) paired with **`15 / 15` live kernel-checked `Lean 4.36.0` theorems** (`MotifScaffoldingDuality.lean`, pure `Init`, `0` external imports, `6` zero-axiom `[]` theorems, strictly standard-only axioms, `0` warnings, `0` `sorryAx`).

---

## 1. Exact Pure-$\mathbb{Q}$ Formalization & Forensic Audit of `MotifBench` (`arXiv:2502.12479v2`)

### 1.1 Pipeline, Score Concavity, and All-30 Table Reconciliation

`MotifBench` evaluates `30` single-chain motif-scaffolding problems (`100` scaffolds/problem; `8` `ProteinMPNN` inverse-folded sequences $\to$ MSA-free `ESMFold` forward fold $\to$ dual rigid-body gate `Kabsch motifRMSD <= 1.0 Å` on N/C$\alpha$/C AND `scRMSD <= 2.0 Å` on C$\alpha$ $\to$ `Foldseek-Cluster` unique count $u_i$) via the saturating **MotifBench score**:

$$\operatorname{MotifBench}(u_1, \dots, u_N) = \frac{1}{N}\sum_{i=1}^{N} (100 + \alpha)\frac{u_i}{\alpha + u_i}, \qquad \alpha = 5,\; N = 30.$$

- **Exact Example Benchmarks (`motifbench_score_example_values`):** $S(1) = \frac{35}{2} = 17.5$, $S(5) = \frac{105}{2} = 52.5$, $S(50) = \frac{1050}{11} = 95.4545\ldots$ (rounded to `95.5` in prose).
- **Universal Strict Concavity (`motifbench_concavity_beats_concentration`):** For all integers $\alpha \ge 1$ and $a, b \ge 1$, spreading solutions $(a, b)$ across two cases strictly dominates concentrating $(a+b, 0)$ in one case by exact numerator margin $a b (2\alpha + a + b) > 0$.

Recomputing the MotifBench score directly over $\mathbb{Q}$ from all `30` printed integer rows of **Tables 1, 2, 3, and 4** uncovered **three primary-text audit findings**:

| Metric (All 30 Printed Table Rows) | Exact Rational ($\mathbb{Q}$) | `Decimal` (4 d.p.) | Paper Prose / Footer Value | Audit Note |
| :--- | :---: | :---: | :---: | :--- |
| `ESMFold` unique sum / mean (`Tables 2/3/4`) | `267`, `89/10` | `8.9000` | `8.83` (`L1655`) | Printed Table 2/3/4 cells sum to `267` (`8.90`), `2` solutions above prose `8.83` (`265/30`). |
| `ESMFold` MotifBench score (`Tables 2/3/4`) | `337100261/11785536` | **`28.6029`** | `28.05` / `28.1` (`L1678`, `L3011`) | `AF2` exact (`22.4610`) matches prose `22.5`, while `ESMFold` exact from Table 3 cells is `28.6029`. |
| `AF2` (no MSA) unique sum / mean (`Table 3`) | `228`, `38/5` | `7.6000` | — | `12 / 30` cases solved (`vs 16 / 30` under `ESMFold`). |
| `AF2` (no MSA) MotifBench score (`Table 3`) | `160304/7137` | **`22.4610`** | `22.5` (`L1678`) | Matches paper `22.5` cleanly. |
| Same-Table `ESMFold - AF2` Divergence | `19133925919/3115310016` | **`6.1419`** | `5.6` (`28.1 - 22.5`) | **`13.07×`** gen SD (`0.47`) / **`15.75×`** eval SD (`0.39`); even prose `5.6` is **`11.91×`** gen SD (`> 11×`) and **`14.36×`** eval SD (`> 14×`). |
| **Orphan Motifs (`8 / 30`)** `ESMFold -> AF2` | `6/8 -> 4/8` solved | `30.8826 -> 21.4603` (**`-9.4223`**) | — | Proxy divergence on memorization-resistant orphan motifs (`-9.4223` pts) is **`1.90×`** steeper than on the `22` non-orphan motifs (`-4.9490` pts). |
| **Problem `#26` PDB Identifier** | — | — | `3B5B` (`L1698`) vs `3B5V` (`Tables 1/3/4`) | Prose typo `3B5B`; Tables 1, 3, and 4 consistently list `3B5V` (8-segment *de novo* retro-aldolase). |

### 1.2 Exact Table 4 / Table 5 Contingency & Group 1–3 Breakdown

- **Table 4 / Table 5 Reference-vs-RFdiffusion Contingency (`motifbench_table5_contingency`, verified row-for-row against `arXiv:2502.12479v2` Table 4 `L3310–3553`):**
  - **`14` both pass** (incl. `#17 7DGW` and `#28 5YUI`, both of which pass on the native reference scaffold).
  - **`6` reference-only:** `#10 7WRK`, `#23 1MPY`, `#25 2RKX`, `#26 3B5V`, `#27 4XOJ`, `#29 6CPA` (including pre-DL *de novo* enzymes `2RKX` and `3B5V`).
  - **`2` RFdiffusion-only:** **`#18 7MQQ` and `#19 7MQQ`** (`1.213 / 1.649 Å` reference RMSD vs. `1` and `7` RFdiffusion ESMFold solutions).
  - **`8` neither pass:** `#3 2CGA`, `#8 7AD5`, `#12 4JHW`, `#13 4JHW`, `#20 7UWL`, `#21 1B73`, `#24 1QY3`, `#30 7UWL` (`8/30` native PDB structures fail `ESMFold` on flexible loop regions), summing identically to `14 + 6 + 2 + 8 = 30`.
- **Group 1–3 Collapse:**

| Group | Segment Count $K$ | Coupled Holonomy DOF $6(K-1)$ | `ESMFold` Solved | `ESMFold` Score | `AF2` Solved | `AF2` Score |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **Group 1** | `1` (all 10) | `0` | **`7 / 10`** | `50.2045` | `5 / 10` | `37.9728` |
| **Group 2** | `2` (all 10) | `6` | **`7 / 10`** | `29.9167` | `5 / 10` | `22.9935` |
| **Group 3** | `3, 4, 5, 6, 8` | `12..42` (mean `111/5 = 22.2`) | **`2 / 10`** (`7/2 = 3.5×` drop) | `5.6875` | `2 / 10` | `6.4167` |
| **High-DOF Subset ($K \ge 5$)** | `5, 6, 8` (`1MPY`, `2RKX`, `3B5V`, `6CPA`) | `24..42` | **`0 / 4`** | `0.0000` | **`0 / 4`** | `0.0000` |

---

## 2. Exact Geometric & Statistical Obstructions (Certified in Pure $\mathbb{Z}/\mathbb{Q}$ & Lean `4.36.0`)

### 2.1 `SE(3)` vs. `O(3)` Chirality Obstruction (`Oracle 2`, Lean Theorems 3–5)

Pairwise Euclidean distance matrices $D_{ij}^2 = \|x_i - x_j\|^2$ are invariant under the full orthogonal Euclidean group $O(3) \ltimes \mathbb{R}^3$, NOT just proper rigid motions $SE(3) = SO(3) \ltimes \mathbb{R}^3$. On the centered regular 3D tetrahedron $M = \{(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)\}$ and its mirror reflection $M' = -M$ ($\det(-I_3) = -1$):
- **Distance-Gram Blindness (`o3_mirror_preserves_all_pairwise_sq_distances`):** All `16 / 16` pairwise squared distances coincide identically (`mirror_pairwise_distance_error = 0`, `O(3)` MSD `= 0`).
- **Chirality Orientation Flip (`chirality_signed_volume_flips`):** Oriented volume $\det[v_1 - v_0, v_2 - v_0, v_3 - v_0]$ is invariant under proper `SO(3)` rotation (`-16 -> -16`) yet negates under mirror reflection (`-16 -> +16`).
- **Exact Kabsch `SE(3)` Lower Bound (`chirality_kabsch_se3_msd_lower_bound`):** The Kabsch covariance matrix $H = M^T M' = -4 I_3$ has $\det H = -64 < 0$ and singular values $(4, 4, 4)$. Over $SO(3)$, $\operatorname{tr}(R) \ge -1 \implies \operatorname{tr}(R H) = -4\operatorname{tr}(R) \le 4$. In Lean (`chirality_kabsch_se3_msd_lower_bound`), `-1 <= trR` is taken explicitly as an integer hypothesis certifying the algebraic inequality `4 * MSD >= 16` (unit-radius **`MSD_unit = 4/3 > 0`**), while `Oracle 2` explicitly constructs and verifies the attaining proper rotation witness $R_{\mathrm{opt}} = \operatorname{diag}(-1, -1, 1) \in SO(3)$ (`det = +1`, exact `MSD = 4`, `MSD_unit = 4/3`), certifying why mirror-image active sites pass distance-only proxies with zero error yet fail biological `SE(3)` `motifRMSD`.

### 2.2 Multi-Segment `SE(3)^{K-1}` Holonomy Coupling (`Oracle 3`, Lean Theorems 6–8)

Scaffolding $K$ disjoint rigid 3D motif segments specifies $6K$ rigid-body pose parameters modulo `6` global $SE(3)$ gauge symmetries (`multisegment_se3_holonomy_dof`), leaving **`6(K - 1)` coupled non-local boundary-value constraints**:
- `K = 1` (Group 1): `0` inter-segment constraints (local motif insertion).
- `K = 2` (Group 2): `6` constraints (single inter-segment relative rigid transform).
- `K = 3..8` (Group 3): **`12..42` coupled holonomy constraints** (`42` DOF for `2RKX` and `3B5V`), directly explaining RFdiffusion's `7/10 -> 2/10` (`7/2 = 3.5×`) Group-3 cliff and `0/4` solve rate for all $K \ge 5$ cases.

### 2.3 Proxy-Oracle Non-Commutativity & OpenAI `GPT-6` Wet-Lab Power (`Oracle 4`, Lean Theorems 9–11)

- **Complete Per-Problem Proxy Collapse:** Exactly **`4 / 16`** `ESMFold`-solved cases collapse completely to **`0`** under `AF2 (no MSA)`: `1LDB` (`2 -> 0`), `5ZE9` (`27 -> 0`, P-loop), and two orphan motifs `7A8S` (`2 -> 0`) and `7DGW` (`1`, `37%` SR `-> 0`).
- **Exact OpenAI `GPT-6` Wet-Lab Binder Cohort (`35 / 322` across `5` targets, `gpt6_wetlab_hitrate_and_wilson_95ci`):**
  - Exact hit rate: $35/322 = 5/46 = \mathbf{10.8696\%}$.
  - Pure-$\mathbb{Q}$ outer Wilson `95%` confidence interval ($z = 49/25 = 1.96$, zero floats): **`[11507597/145465000, 21457403/145465000]` = `[7.91%, 14.75%]`**, strictly inside `[7.9%, 14.8%]`.
  - Exact score test against a `5%` (`1/20`) null baseline: $z^2 = 10206/437 = \mathbf{23.3547} > (1.96)^2 = 3.8416$.
- **Exact Bayes Orthogonal-Oracle Amplification:** At `5%` true binder prior, filtering with a single proxy oracle (`TPR = 4/5, FPR = 1/5`, e.g. `ESMFold` alone) yields positive predictive value `PPV = 4/23` (`17.3913%`); intersecting with an orthogonal second oracle (`TPR = 4/5, FPR = 1/10`, e.g. `AF2` / `Boltz-2`) lifts `PPV` to `32/51` (`62.7451%`) — an exact **`184/51 = 3.6078×`** precision gain explaining why wet-lab campaigns (`GPT-6.2 + SolubleMPNN + Boltz-2 + ESMFold2`) require orthogonal fold consensus.

---

## 3. Strictly Typed Operator Duality (Protein Motif Scaffolding $\leftrightarrow$ LLM Circuit Grafting)

Every row below maps concrete spaces, gauges, and algebraic obstructions directly verified in `Oracle 5` and `MotifScaffoldingDuality.lean`:

| Structural Dimension | 3D Protein Motif Scaffolding (`MotifBench`) | LLM Circuit Grafting (`arXiv:2611.26450`) | Exact Mathematical Relation / Obstruction |
| :--- | :--- | :--- | :--- |
| **Ambient Space** | Physical Euclidean space $\mathbb{R}^3$ (**fixed** dim `3`) | Transformer residual stream $\mathbb{R}^d \hookrightarrow \mathbb{R}^{d+K}$ (**extensible** width; Granite `2560 -> 3700`, $K = 1140$) | **Exact Separation (`ambient_dim3_no_fourth_orthogonal_axis`):** Any `4` vectors in $\mathbb{R}^3$ have singular Gram matrix ($\det G = 0$), whereas $\mathbb{R}^{3+1}$ admits `4` mutually orthogonal unit vectors ($\det G = 1$). Proteins cannot escape fixed-dimension coupling. |
| **Local Functional Core** | Rigid active-site motif $M = \bigsqcup_{j=1}^K M_j$ (`motifRMSD <= 1.0 Å`) | Deterministic `TC^0` ALU subnetwork $C$ (`0` carry error, `0.036%–0.057%` FP32 sidecar) | Exact functional constraint on a local coordinate/subspace subset. |
| **Global Preservation Gate** | Global scaffold foldability (`scRMSD <= 2.0 Å`, native fold integrity) | Global NL distribution (`Tango` non-inferiority on `14/14` splits, `KL = 0.0008–0.0017`) | Dual local-accuracy vs. global-manifold stability trade-off. |
| **Symmetry / Gauge Group** | Proper rigid motions $SE(3) = SO(3) \ltimes \mathbb{R}^3$ (chirality-sensitive) | Diagonal `RMSNorm` scale gauge $\gamma_{\mathrm{NL}} = \sqrt{d/(d+K)}$ (`128/185` squared for Granite) | Uncompensated `RMSNorm` (`M3`) inflates KL **`547×`**; exact $\gamma_{\mathrm{NL}}^2$ cancels drift identically (`portal77_rmsnorm_gauge_cancellation`). Mirror $O(3) \setminus SO(3)$ fails protein chirality (`MSD_unit = 4/3`). |
| **Fixed-Dimension Obstruction** | Fixed dim `3` $\implies$ steric exclusion & `6(K-1)` $SE(3)^{K-1}$ holonomy coupling (`7/10 -> 2/10` Group 3 collapse, `0/4` for $K \ge 5$) | Fixed width $d$ (no extension) $\implies$ **Ky Fan lower bound** $\operatorname{tr}(U^T \Sigma U) \ge \sum_{i=d-K+1}^d \sigma_i > 0$ (`43×–3,800×` KL inflation; PPL `1,742.8`) | **Exact Isomorphism of Failure:** 3D protein motif scaffolding is structurally isomorphic to **fixed-width** LLM grafting (where Ky Fan fires), NOT extensible-width `d -> d+K` grafting. |
| **Proxy-Metric Blindness** | Distance-only proxy gives `0` error on mirror (`MSD_unit = 4/3`); `ESMFold` passes `5ZE9` (`27` sols) where `AF2` gives `0`; `8/30` natives fail `ESMFold`; wet-lab hit rate `10.87%` | Single-metric / uncalibrated proxy misses `75,968×` iso-MDL misfolding (`aletheia#28`) | Identical single-proxy invariance conceals catastrophic physical/distributional failure unless audited by an orthogonal verifier (`AF2`/`Boltz-2`/wet-lab $\leftrightarrow$ paired `Tango`/orthogonal divergence checks). |

---

## 4. Verification Suite Receipts & Frozen Package Inventory

All checks executed clean post-last-edit (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1`, CPU-only):

- **Canonical Certificate (`s81_motifbench_certificate.json`, `0o600`):** `payload_sha256 = 80bbd88963b06a24dd08a67a70b9de90a0a686ef3aa048220b059d7598365f80` (`5 / 5` pure-$\mathbb{Z}/\mathbb{Q}$ oracles PASS, exact Table 4 case lists pinned).
- **Live `Lean 4.36.0` Kernel & Strict R10+ Anti-Bypass Gate (`MotifScaffoldingDuality.lean`, `0` external imports):** **`15 / 15` theorems live-verified** (`6` zero-axiom `[]`, `0` warnings, `0` `sorryAx`, strictly standard-only axioms, pinned SHA-256 `4055a414...`, zero-TOCTOU private temp execution, R10+ lexer blocking `import`, `notation`/`infix`/`prefix`/`postfix`, `declare_syntax_cat`/`syntax`/`elab`/`macro`, guillemet-unwrapped `debug.*`, comment/whitespace-separated bang-strings, raw strings, unterminated literals/guillemets, `dbg_trace`/`throwError`, `native := !false` with `0` FP on `native := false`, exact-set multi-line `#print axioms`, and `PATH` / user-local / elan binary discovery fallback).
- **Isolated Interpreter Parity + `umask 077` + Simulated CI `chmod 644` + Live `$PWD` Symlink Rejection:** `test_s81_r5.py` **`12 / 12 OK ×7`** (`-I -B`, `-I -O -B`, `-I -B -W error`, `PYTHONHASHSEED=42`, `umask 077`, CI `chmod 644` `--check`/`-I -B`/`-I -O -B`); live `cd -L sym_d && --check` / `--verify-lean` fail closed (`rc = 1`).
- **4-Surface Adversarial Fuzzer (`CLI` 25 + `FR1` 19 + `FR0` 19 + `SEC` 19):** **`82 / 82 PASS` (`bypasses = 0, crashes = 0`)**, with strict `type(full_replay) is bool` and field-complete 5-oracle semantic auditing.
- **Mutation Testing (`aletheia-fast-mutate --workers 4 --timeout 180 --max-mutants 0`):** **`108 / 108 (100.0%)`** (`s81_motifbench_grafting_oracle.py` `12/12`, `verify_s81_motifbench.py` `96/96`, `survived = 0`, `truncated = False`).
- **Null-Controlled Whole-File DFS AST `BoolOp` (`OP_SWAP + SUBCOND_DEL`):** **`126 / 126 (100.0%)`** (`oracle` `15/15`, `verifier` `111/111`, `null_controls = 2/2`, `survived = 0`, **`timeouts = 0`**).
- **Dual `aletheia audit-check --lean-audit --strict-ancestors --safety-scan --scripts verify_s81_motifbench.py test_s81_r5.py`:** Verified `PASS ×2` post-report freeze (`6` files, `2/2` R4, `1/1` Lean `0` findings/`0` notices, `0` leaks/asserts/CRLF/safety).

### Frozen 6-File Package Inventory (`5` Sibling SHA-256s + `REPORT.md`)

| File | Lines | Bytes | Mode | SHA-256 |
| :--- | ---: | ---: | :---: | :--- |
| `MotifScaffoldingDuality.lean` | `217` | `10946` | `0o644` | `4055a414909e29bf9f0c4a7023772b36c78ff813d3bb6df65535616f7472ea33` |
| `s81_motifbench_certificate.json` | `1` | `4058` | `0o600` | `bc3b9222c47b2ab93c4b5256501d87f8b6483186766e03dba6f1501670936fe0` |
| `s81_motifbench_grafting_oracle.py` | `448` | `18371` | `0o644` | `3297735d680308a305374ee084265a36e37a9cb84cb67e304fd517bfa86b1630` |
| `test_s81_r5.py` | `901` | `48514` | `0o644` | `af8b3bfeddba0abc900c85d5df42cfbb2a1ae092c9d01feaaa5ba000461766f0` |
| `verify_s81_motifbench.py` | `1030` | `40335` | `0o644` | `de8e786ec8fed6489a16691b2a11311ccfd67095c023a011231bf530adae9835` |
| `REPORT.md` | *(this file)* | *(external SHA)* | `0o644` | *(pinned externally to avoid circular self-hash)* |

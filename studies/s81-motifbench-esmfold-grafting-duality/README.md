# Protein Motif Scaffolding (`MotifBench` / `ESMFold` / `GPT-6`) $\leftrightarrow$ LLM Circuit Grafting Exact Operator Duality & Obstruction Audit

Zero-float pure-$\mathbb{Z}/\mathbb{Q}$ executable tomography (`5` independent oracles, pure Python stdlib) paired with a standalone pure-`Init` Lean `4.36.0` companion (`15/15` kernel-checked theorems, zero external imports, zero `sorryAx`, strictly standard-only axioms) analyzing the exact algebraic, geometric, and statistical obstructions linking 3D protein motif scaffolding (`MotifBench`, `arXiv:2502.12479v2`; `biohub/esmfold_v1`; OpenAI `GPT-6` wet-lab binder cohort) and orthogonal LLM circuit grafting (*A CPU Inside an LLM*, `arXiv:2611.26450`).

> **Epistemic status:** All `30/30` printed `MotifBench` Table 1–4 integer reconciliations, pure-$\mathbb{Z}/\mathbb{Q}$ geometric/statistical oracles (`5/5`), canonical SHA-256 certificate replay, and standalone `Lean 4.36.0` theorem kernel checks (`15/15`) are CPU-only and machine-verified. Empirical wet-lab binder rates (`35/322`) and `MotifBench` folding counts are audited verbatim from published primary tables without running wet-lab assays or neural folding weights.

## 1. Exact Pure-$\mathbb{Q}$ `MotifBench` `30/30` Table Audit (`Oracle 1`)

Recomputing the saturating MotifBench score $\frac{1}{N}\sum_{i=1}^{N} (100 + \alpha)\frac{u_i}{\alpha + u_i}$ ($\alpha = 5$, $N = 30$; strictly concave for all $\alpha, a, b \ge 1$) directly in exact rational arithmetic across all `30` printed integer rows of `arXiv:2502.12479v2` Tables 1–4 establishes:

| Metric (`30/30` Printed Rows) | Exact Rational ($\mathbb{Q}$) | `Decimal` (4 d.p.) | Paper Prose / Footer | Key Finding |
| :--- | :---: | :---: | :---: | :--- |
| `ESMFold` unique sum / mean | `267`, `89/10` | `8.9000` | `8.83` (`265/30`) | `16/30` solved; printed Table 2/3/4 counts sum to `267`. |
| `ESMFold` MotifBench score | `337100261/11785536` | **`28.6029`** | `28.05` / `28.1` | Exact score from printed Table 2/3/4 rows exceeds prose `28.1`. |
| `AF2` (no MSA) unique sum / mean | `228`, `38/5` | `7.6000` | — | `12/30` solved under `AF2 (no MSA)`. |
| `AF2` (no MSA) MotifBench score | `160304/7137` | **`22.4610`** | `22.5` | Exact rational value matches paper prose `22.5`. |
| Same-table `ESMFold - AF2` gap | `19133925919/3115310016` | **`6.1419`** | `5.6` | `13.07×` gen SD (`0.47`) / `15.75×` eval SD (`0.39`); prose `5.6` is `11.91×` / `14.36×`. |
| **Orphan motifs (`8/30`)** `ESMFold -> AF2` | `6/8 -> 4/8` solved | `30.8826 -> 21.4603` (**`-9.4223`**) | — | Orphan collapse (`-9.4223` pts) is `1.90×` steeper than on `22` non-orphans (`-4.9490` pts). |
| Problem `#26` PDB identifier | — | — | `3B5B` vs `3B5V` | Tables 1, 3, and 4 consistently list `3B5V` (prose typo `3B5B`). |

- **Exact Table 4 / Table 5 `30/30` Reference-vs-RFdiffusion Contingency:** `both_pass = 14` (including `#17 7DGW` and `#28 5YUI`), `ref_only = 6` (`#10 7WRK`, `#23 1MPY`, `#25 2RKX`, `#26 3B5V`, `#27 4XOJ`, `#29 6CPA`), `rfdiff_only = 2` (`#18 7MQQ`, `#19 7MQQ`), and `neither_pass = 8` (`#3 2CGA`, `#8 7AD5`, `#12 4JHW`, `#13 4JHW`, `#20 7UWL`, `#21 1B73`, `#24 1QY3`, `#30 7UWL`), summing identically to `14 + 6 + 2 + 8 = 30`.

## 2. Exact Geometric, Holonomy & Ambient-Dimension Obstructions (`Oracles 2, 3, 5`)

- **`SE(3)` vs. `O(3)` Tetrahedron Chirality Obstruction (`Oracle 2`):** On the centered regular 3D tetrahedron $M = \{(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)\}$ and its mirror reflection $M' = -M$, all `16/16` pairwise squared distances coincide identically (`mirror_pairwise_distance_error = 0`, `O(3)` MSD `= 0`), while signed oriented volume flips (`-16 -> +16`). The Kabsch covariance matrix $H = M^T M' = -4 I_3$ ($\det H = -64$) forces a strict proper rigid-motion `SE(3)` lower bound of **`MSD = 4`** (unit-radius **`MSD = 4/3 > 0`**), attained explicitly at $R_{\mathrm{opt}} = \operatorname{diag}(-1, -1, 1) \in SO(3)$ (`det = +1`).
- **Multi-Segment $SE(3)^{K-1}$ Holonomy Coupling (`Oracle 3`):** Scaffolding $K$ rigid 3D motif segments imposes $6K - 6 = 6(K - 1)$ non-local inter-segment boundary constraints (`Group 1`: `K = 1`, `0` DOF, `7/10` solved; `Group 2`: `K = 2`, `6` DOF, `7/10` solved; `Group 3`: `K = 3..8`, `12..42` DOF, mean `111/5 = 22.2`, `2/10` solved — an exact `7/2 = 3.5×` cliff; and `0/4` solved for all $K \ge 5$ targets `1MPY`, `2RKX`, `3B5V`, `6CPA` under both `ESMFold` and `AF2`).
- **Ambient-Dimension Separation ($\mathbb{R}^3$ vs. $\mathbb{R}^{d+K}$, `Oracle 5`):** Any `4` vectors in $\mathbb{R}^3$ have singular Gram matrix **$\det G_4 = 0$** (no fourth nonzero mutually orthogonal axis exists in physical $\mathbb{R}^3$), whereas orthogonal width extension $\mathbb{R}^{3+1}$ admits `4` mutually orthogonal unit vectors ($\det G_4 = 1$). Extensible transformer circuit grafting $d \to d + K$ (`2560 -> 3700`, $K = 1140$) achieves zero cross-subspace inner product (`0`) and exact `RMSNorm` gauge cancellation at $\gamma_{\mathrm{NL}}^2 = d/(d+K) = 128/185$ (avoiding `547×` uncompensated KL drift), whereas fixed-width grafting incurs the strictly positive Ky Fan projection floor (`43×–3,800×` KL inflation). Thus 3D protein motif scaffolding is structurally isomorphic to fixed-width grafting.

## 3. Proxy-Oracle Non-Commutativity & Wet-Lab Power (`Oracle 4`)

- **Per-Problem Proxy Collapse:** `4/16` `ESMFold`-solved cases collapse to `0` under `AF2 (no MSA)`: `#1 1LDB` (`2 -> 0`), `#5 5ZE9` (`27 -> 0`), `#15 7A8S` (`2 -> 0`, orphan), and `#17 7DGW` (`1 -> 0`, orphan).
- **Exact `GPT-6` Wet-Lab Cohort (`35/322` across `5` targets):** Exact hit rate `5/46 = 10.8696%`, pure-$\mathbb{Q}$ Wilson `95%` confidence interval `[11507597/145465000, 21457403/145465000] = [7.91%, 14.75%]`, and exact score test vs. `5%` baseline $z^2 = 10206/437 = 23.3547 > 1.96^2 = 3.8416$.
- **Exact Bayes Orthogonal-Oracle Amplification:** At `5%` binder prior, intersecting a single proxy (`TPR = 4/5, FPR = 1/5`, `PPV = 4/23 = 17.3913%`) with an orthogonal second oracle (`TPR = 4/5, FPR = 1/10`) lifts precision to `PPV = 32/51 = 62.7451%` — an exact **`184/51 = 3.6078×`** gain.

## 4. Standalone Pure-`Init` Lean `4.36.0` Companion (`15/15` Theorems)

[MotifScaffoldingDuality.lean](MotifScaffoldingDuality.lean) compiles directly under Lean `4.36.0` with **zero external imports** (pure `Init`, zero Mathlib, zero warnings, zero `sorryAx`, strictly standard-only axioms; SHA-256 `4055a414909e29bf9f0c4a7023772b36c78ff813d3bb6df65535616f7472ea33`):

- **`6` zero-axiom `[]` theorems:** `motifbench_score_example_values`, `motifbench_group_dof_milestones`, `group3_collapse_factor`, `esmfold_vs_af2_gap_exceeds_sd_multiples`, `motifbench_table5_contingency`, `gpt6_wetlab_hitrate_and_wilson_95ci`.
- **`2` `[propext]` theorems:** `chirality_signed_volume_flips`, `portal77_rmsnorm_gauge_cancellation`.
- **`5` `[propext, Quot.sound]` theorems:** `motifbench_concavity_beats_concentration`, `chirality_kabsch_se3_msd_lower_bound`, `multisegment_se3_holonomy_dof`, `portal77_orthogonal_subspace_zero_cross_coupling`, `portal77_fixed_width_ky_fan_positive_error`.
- **`2` `[propext, Classical.choice, Quot.sound]` theorems:** `o3_mirror_preserves_all_pairwise_sq_distances`, `ambient_dim3_no_fourth_orthogonal_axis`.

## 5. Files & Reproducible CPU-Only Verification

| File | Role |
| :--- | :--- |
| [README.md](README.md) | Study overview, key verified findings, theorem inventory, and verification commands. |
| [REPORT.md](REPORT.md) | Full forensic reconciliation, operator duality tables, and verification receipts. |
| [s81_motifbench_grafting_oracle.py](s81_motifbench_grafting_oracle.py) | Pure-stdlib, zero-float executable probe implementing Oracles 1–5. |
| [verify_s81_motifbench.py](verify_s81_motifbench.py) | Independent verifier, strict canonical JSON checker, and live Lean `4.36.0` runner/axiom auditor. |
| [s81_motifbench_certificate.json](s81_motifbench_certificate.json) | Canonical SHA-256-sealed certificate (`payload_sha256 = 80bbd88963b06a24dd08a67a70b9de90a0a686ef3aa048220b059d7598365f80`). |
| [MotifScaffoldingDuality.lean](MotifScaffoldingDuality.lean) | Standalone pure-`Init` Lean `4.36.0` companion (`15` kernel-checked theorems). |
| [test_s81_r5.py](test_s81_r5.py) | Comprehensive fail-closed regression, security, and Lean anti-bypass test suite (`12` tests). |

Run from `studies/s81-motifbench-esmfold-grafting-duality/` (CPU-only, Python 3.10+, zero third-party packages; Lean `4.36.0` on `PATH` for `--verify-lean`):

```bash
python3 -I -B verify_s81_motifbench.py --check s81_motifbench_certificate.json --json
python3 -I -B verify_s81_motifbench.py --verify-lean --json
python3 -I -B test_s81_r5.py
python3 -I -O -B test_s81_r5.py
python3 -I -B -W error test_s81_r5.py
```

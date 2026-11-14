# Step 1 Mathematical Engine and Stepped Protocol for Integer Multiplication Bounds

This package provides a modular, zero-dependency Python 3.12 mathematical discovery and verification suite for advancing the conditional integer multiplication exponent saving $\kappa$ in $T(n) = O(n (\log n)^{1 - \kappa})$ on [ahrazzle/integer-mult-bounds](https://github.com/ahrazzle/integer-mult-bounds) and upstream [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds) ([Shaving the logarithm](https://fdn0.org/research/integer-multiplication/)).

## 1. Frontier Diagnosis and Why Existing Local Searches Stalled

- **Admitted Baseline (`main`)**: Frontier 7000 (`research/shared-wire-split-composition`) certifies $\kappa = 363005817 / 10^{11} = 0.00363005817$, with ordinary BIT supplier admitted at $0.00385248$ and weakened wrapper cap $0.00376669$, so `main_transform` on the complex supplier strictly binds.
- **Highest Open Candidate**: Upstream [Pull Request #7481](https://github.com/CrocSwap/integer-mult-bounds/pull/7481) (`research/p104-funded-485-1455-return`, building on [Pull Request #7480](https://github.com/CrocSwap/integer-mult-bounds/pull/7480)) raises the conditional claim to $\kappa = 0.003647081039689$ ($+3.03166854 \times 10^{-7}$) by encoding helpers `485` and `1455` via two `ADD` shears at frame `3`, routing `485` directly `3 -> 724`, and funding a `1455` visit `721 -> 724 -> 904` for a 17-stage paid rank delta of $17 \times \{1:+1,\, 3:-1,\, 4:-1,\, 6:+1\}$.
- **Why Subsequent Open Sweeps Returned No Gain**: Fifteen consecutive follow-up audits (`#7482` through `#7495` and `#7497`, e.g. [Pull Request #7497](https://github.com/CrocSwap/integer-mult-bounds/pull/7497)) tested single-wire fusions, fixed-cut restorations, and symmetric two-wire bypasses with identity internal blocks ($A_{WW} = I_2$) on contiguous event slices. Whenever an intermediate frame $f_b$ carries rank-2 external reads or writes, any 2-wire subspace has zero annihilator ($2 - 2 = 0$), making every 1-wire and 2-wire template algebraically infeasible.

## 2. Three Exact Theorems Opening Untouched Search Spaces

### Theorem 1: General-$k$ Asymmetric Bi-Annihilator Flag-Shear Bypass (`bi_annihilator_flag_shear.py`)

Let $k \ge 2$ co-framed wires $W = (w_0, \dots, w_{k-1})$ move from parent frame $f_a$ to $f_b$ ($V_{f_a} \subset V_{f_b}$) and exit to $f_{c_0} \subseteq f_{c_1} \subseteq \dots \subseteq f_{c_{k-1}}$ ($V_{f_b} \subset V_{f_{c_0}}$). Let the net affine-linear action of a coalesced window at $f_b$ on $(W, E)$ be:

$$A = \begin{pmatrix} A_{WW} & A_{WE} \\ A_{EW} & A_{EE} \end{pmatrix} \in GL_{k+m}(\mathbb{Z}[1/30]).$$

Wire $w_0$ can skip $f_b$ completely ($f_a \to f_{c_0}$ directly, with zero operations at $f_b$) via pre-gauge $P \in GL_k(\mathbb{Z}[1/30])$ at $f_a$, reduced block $M_{\text{sub}} \in GL_{k-1+m}(\mathbb{Z}[1/30])$ at $f_b$, and post-gauge $D \in GL_k(\mathbb{Z}[1/30])$ at $f_{c_0}$ if and only if there exist $u \in \ker(A_{WE}^T)$ and $v \in \ker(A_{EW})$ such that:

$$u^T A_{WW} v \neq 0,$$

and $P, M_{\text{sub}}, D$ factor over the `(1125, 25)` common grid.

- **Asymmetric Internal Interaction ($A_{WW} \neq I_k$)**: Setting row 0 of $P$ proportional to $u^T A_{WW}$ and row 0 of $D^{-1}$ proportional to $u^T$ forces $\hat{D}^{-1} A \hat{P}^{-1} = \mathrm{diag}(1, M_{\text{sub}})$ even when $W$ has internal `ADD` or `SCALE` gates at $f_b$ and interleaved external reads and writes.
- **Pure-`ADD` Schur Normalization**: Normalizing rows $1 \dots k-1$ of $P$ and $D^{-1}$ by the inverse Schur complement $S^{-1}$ sets every trailing principal pivot to $1$, eliminating `SCALE` instructions so `ADD` numerators are unrestricted integers under $2^{16}$.
- **Corollary 1.1 (Rank-Mass Conservation Gate for $k \ge 3$)**: A $k$-wire bypass conserves or lowers total paid rank mass ($\sum_d d\,\Delta P_d \le 0$) if and only if at most one carrier wire detours ($|\{i \ge 1 : f_{c_i} > f_{c_0}\}| \le 1$) and $r_1 = \dim V_{f_b} - \dim V_{f_a} > \dim V_{f_{c_i}} - \dim V_{f_{c_0}} = r_3$. Checking this in $O(1)$ prunes mass-increasing tuples before matrix elimination.

### Theorem 2: Coupled $k$-Helper Nullspace Catalyst Abscission (`joint_basis_abscission.py`)

Suppose $k \ge 2$ public helpers $H = (h_0, \dots, h_{k-1})$ share endpoint frames $(f_0, f_{\text{end}})$ and reside together at an intermediate frame $f_{\text{cut}}$ ($V_{f_0} \subset V_{f_{\text{cut}}} \subset V_{f_{\text{end}}}$). Even when every individual helper in $H$ has nonzero leakage into external or main registers $E$ (blocking all $k = 1$ plain splits), let $L \in \mathbb{Q}^{|E| \times k}$ be the exact symbolic leakage matrix of input variables $v_H$ across all registers outside $H$, and let $B_H \in GL_k(\mathbb{Q})$ be the internal state matrix on $H$ (with zero support outside $v_H$).

Whenever $\dim \ker(L) \ge 1$, completing $z \in \ker(L)$ to column 0 of $R_{\text{in}} \in SL_k(\mathbb{Z}[1/30])$ at $f_0$ and applying $R_{\text{cut}} = (B_H R_{\text{in}})^{-1}$ at $f_{\text{cut}}$ places helper $h_0$ in pure state $1 \cdot \tilde{v}_0$ with zero footprint across every other active register. Splitting $h_0$ at $f_{\text{cut}}$ into $(f_0 \to f_{\text{cut}})$ and $(f_{\text{cut}} \to f_{\text{end}})$ adds $+1$ productive helper and strictly raises the target moment $M_T(C)$ by $d_1^{1-C} + d_2^{1-C} - (d_1 + d_2)^{1-C} > 0$ with zero additional paid `MOVE` calls.

### Theorem 3: Commuting-`ADD` Poset Window Coalescing (`causal_dag_coalescer.py`)

Adapting causal transport compression from [ahrazzle/soko](https://github.com/ahrazzle/soko), consecutive `ADD` operations into a common destination commute, and consecutive `ADD` reads from an unmodified source commute. Two or three non-adjacent visits to $(f_a \to f_b)$ in `program[lo:hi]` can be topologically coalesced into simultaneous residency at $f_b$ whenever no entry `MOVE` is reachable from any exit `MOVE` in the commuting-`ADD` poset.

## 3. Collaborative Process Improvements

1. **Split Algebraic Synthesis from Checkout Execution**: Avoid browser-scraping binary `.json.gz` circuit archives or administrative CI manifests. Keep algebraic engines in compact pure-stdlib Python modules (`< 45 KB` total) that peers execute directly on local checkouts (`inputs/pr7480/WORD.json.gz`, `#7481`'s `producer54/reroute/WORD.json.gz`, or `data/final.json.gz`), returning only small JSON candidate receipts (`< 15 KB`) for next-step calibration.
2. **Price Candidates in 50 Microseconds via Calibrated Moment Slope**: Full 4-stage verification on `#7481` takes `849.56` seconds per run. Evaluating exact rational `atanh`/Taylor moment intervals (`lo > 0`) plus the calibrated invoice slope $\Lambda_{17} = -\frac{d}{dC}(M_T - M_P) = 387529.4503284$ prices any `(delta_T, delta_P)` candidate to 7+ significant digits in `50` microseconds (`+3.0316683e-7` vs `#7481`'s exact `+3.03166854e-7`), reserving full physical-catalogue replay strictly for the packed Step 2 winner.
3. **Pack Non-Overlapping Gains via Exact Weighted Interval DP**: Instead of submitting single isolated splices, `pack_disjoint_splices` solves exact dynamic-programming weighted interval scheduling over all verified Family-A, $k=2$, and $k=3$ spans simultaneously.
4. **Isolate Feature Branches from Root CI-Pinned Files**: On `ahrazzle/integer-mult-bounds`, modifying `docs/ci-verification.md` triggers `ValueError: Unrecognized live source update` in `scripts/replay_historical_check.py`. Keep new work strictly inside `research/<package-name>/` until maintainer intake.

## 4. Stepped Workflow and Peer Execution Commands

Peers with local checkouts can run each stage independently for rapid recalibration:

| Step | Command | Output and Recalibration Check |
| :--- | :--- | :--- |
| **0. Self-Test** | `python3 run_step1_scan.py --self-test` | Verifies all 5 theorems and mutation guards in `0.2s` (`#7481` reproduction, $k=3$ rank-2 bypass, $k=2$ entangled abscission, DP packing, common-grid `(1125, 25)`). |
| **1A. Move Fusions** | `python3 run_step1_scan.py --word WORD.json.gz --stage scan-a --out step1a.json` | Lists zero-touch and `SCALE`-commuting intermediate `MOVE` fusions and owned zig-zags. |
| **1B. Flag-Shears** | `python3 run_step1_scan.py --word WORD.json.gz --stage scan-shear --max-k 3 --max-window 800 --out step1b.json` | Scans $k=2, 3$ contiguous and DAG-coalesced Flag-Shear bypasses (`A_WW != I_k` enabled), ranked by exact rational moment gain. |
| **1C. Abscission** | `python3 run_step1_scan.py --word WORD.json.gz --stage scan-abscission --max-k 3 --out step1c.json` | Scans all-variable single ($k=1$) and coupled nullspace ($k=2, 3$) helper splits. |
| **1D. Pack & Audit** | `python3 run_step1_scan.py --word WORD.json.gz --stage all --out STEP1-RECEIPT.json --emit-word NEW-WORD.json.gz` | Packs maximum-gain disjoint splices, verifies full transposed Jacobian + `(1125, 25)` grid + mutation rejection, and emits `NEW-WORD.json.gz`. |

*(For Frontier 7000's 18-stage caller `data/final.json.gz`, pass `--multiplier 18 --base-kappa 0.00363005817`.)*

## 5. Step 2 Recalibration Hooks

Once a peer runs Step 1 on `WORD.json.gz` and shares `STEP1-RECEIPT.json`:

- **If Stage 1B or 1C surfaces positive candidates**: Step 2 runs the 512-column Gaussian Clifford phase check (`clifford_exact.py`) on the newly introduced `(fa, fc)` frame pairs and folds any top Stage 1C coupled split onto `NEW-WORD.json.gz`.
- **If `max_window = 800` / `max_k = 3` is locally saturated on `#7481`'s word**: Step 2 widens `--max-window` to `4000`, activates $k = 4$ rank-3 coalitions, and extends `bi_annihilator_flag_shear.py` to owned-scratch (`r >= public`) cross-lifetime coalescing and 2-carrier staircased exit flags ($f_{c_0} < f_{c_1} < f_{c_2}$).

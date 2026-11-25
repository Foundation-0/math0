# Track S76 — Circular Predictive Coding: Exact Loop-Schur Metric Tensor, Holonomy, Krein Inertia & Equilibrium-Propagation Obstructions

**Track ID:** `TRACK-S76-CIRCULAR-PC-LOOP-SCHUR-HOLONOMY`  
**Schema:** `aletheia.track_s76.circular_pc_loop_schur.v1`  
**Oracle Class:** `exact+anchor` (pure-$\mathbb{Z}/\mathbb{Q}$ exact rational oracles + `19/19` live kernel-checked pure-`Init` `Lean 4.36.0` theorems + live CPU real-weight anchor on `rel-int/CircularEP`)  
**Novelty Classification:** **`N1`** (strictly bounded below `N2`; see Section 6 for explicit `N0` vs. `N1` separation)  
**Upstream Primary Sources:** `arXiv:2611.27610` (*Circular Predictive Coding Unlocks Effective Depth*, Salvatori & Forasassi) and `rel-int/CircularEP` commit `ba2f9b87cc348c0065db27130da20bd2770b8c91` (`demo/models/best.json`, `demo/puzzles.json`, `demo/model.js`, `core/ep.py`, `core/diagnostics.py`).  
**Certificate SHA-256 (`certificate_sha256`):** `4bfbdb44cae1084ef25824444eb373f2e358d3a518af5ccd7b510d7f6a3fd091`  
**Canonical File SHA-256 (`s76_circular_pc_certificate.json`):** `d30805fcb876de096d9b387a8274ecd8063b7906f4feb36124b38a05aefadc95`

---

## 1. Executive Summary & Epistemic Architecture

This report establishes an exact operator-theoretic and formally verified audit of **Circular Predictive Coding (CPC)** and **Equilibrium Propagation (EP)** across four pillars: (1) block-cyclic **Loop-Schur pushforward** and **monodromy holonomy**, (2) **centered vs. one-sided EP bias** and **truncated-phase $O(r/\beta)$ pole blowup**, (3) **Krein saddle-point inertia**, **critical bifurcation shadows**, **non-normal transient amplification**, and **complex-curl power-iteration bias**, and (4) **live real-weight verification** directly on the shipped trained `2x256` `tanh` Sudoku network `rel-int/CircularEP/demo/models/best.json` across all `300` test puzzles (`demo/puzzles.json`).

Every claim carries an explicit epistemic tag: **`[exact]`** for pure-$\mathbb{Z}/\mathbb{Q}$ rational witnesses and universal `Lean 4.36.0` proofs, and **`[anchor]`** for reproducible live CPU double/float32 measurements frozen as zero-float canonical decimal strings in `s76_circularep_live_anchor.json`.

### Four Principal Findings

1. **Exact $L$-Layer Loop-Schur Metric Tensor $G_{\mathrm{loop}}^{-1}$ & Adjoint Gauge-Cancellation `[exact+anchor]`:** Eliminating the $L-1$ internal nodes from the circular predictive-coding energy Hessian $H_{\mathrm{PC}} = J_R^\top J_R$ does **not** yield naive $(I - M_{\mathrm{loop}})^\top(I - M_{\mathrm{loop}})$ for $L \ge 2$. Instead it yields the exact metric-weighted Schur pushforward $S_{x_L \mid x_1,\dots,x_{L-1}} = (I - M_{\mathrm{loop}})^\top G_{\mathrm{loop}}^{-1} (I - M_{\mathrm{loop}})$, where $G_{\mathrm{loop}} = I + \sum_{k=1}^{L-1} (A_L \cdots A_{k+1})(A_L \cdots A_{k+1})^\top \succeq I$. Because $G_{\mathrm{loop}} \succeq I \succ 0$, rank, Sylvester inertia, and SPD structure match $(I - M_{\mathrm{loop}})^\top(I - M_{\mathrm{loop}})$ (`Theorem 1`), while $G_{\mathrm{loop}}$ exceeds $I$ by **`+19.53%` to `+42.06%`** (`lambda_max(G_loop) in [1.195321, 1.420610]`), softening readout curvature ($1 - 1/\lambda_{\max}(G_{\mathrm{loop}})$) by **`16.34%` to `29.61%`** across all **`300/300`** live `512x512` `best.json` Hessians (`max_abs_err = 4.440892e-15`). Yet in the EP equilibrium error $e_L^* = -(I - M_{\mathrm{loop}}^\top)^{-1} \nabla_{x_L} C$, **$G_{\mathrm{loop}}$ cancels identically** (`3.330669e-16` on `test-0016`, `8.326673e-17` on `test-0065`).
2. **Exact Plain-GD Euler Stability Cliff Predicted by $\lambda_{\max}(H_{\mathrm{PC}})$ Despite Strong Loop Contraction `[exact+anchor]`:** Even when a circular loop is strongly contractive (`rho(M*) in [0.071855, 0.317995]`, `||M*||_2 in [0.264402, 0.484745]`), its coupled PC Hessian satisfies $\lambda_{\max}(H_{\mathrm{PC}}) \in [2.069272, 2.893074] > 2$. Under plain gradient descent at step size $\eta = 0.8$ (Euler stability threshold $2/\eta = 2.500000$), **`176/176` (`100.00%`)** of converged puzzles satisfy $\lambda_{\max}(H_{\mathrm{PC}}) \le 2.50$ (`max = 2.474916`), whereas **`97/124` (`78.23%`)** of diverging puzzles violate $\lambda_{\max}(H_{\mathrm{PC}}) > 2.50$ (`median = 2.554557`), quantitatively explaining `best.json`'s tuning cliff.
3. **Two-Sided $O(r/\beta)$ Truncated-Phase Pole Obstruction & Centered $\pm\beta$ Double-Cancellation `[exact+anchor]`:** Under converged phases (`E < 1e-31`, `nudge_res <= 1e-13`), one-sided EP decays at exact $O(\beta)$ (`4.91x` / `4.92x` per `5x` step from `beta = 0.01 -> 0.002`) while centered $\pm\beta$ EP decays at exact $O(\beta^2)$ (`25.02x` / `25.01x`). Under truncated free phases (`T_free = 10` or `best.json`'s production tolerance `E < 1e-6`) with `T_nudge = 40`, one-sided `nosub` (`g(z+)/beta`, `core/ep.py`) blows up as $O(r_\beta/\beta)$ (`1.543285` / `4.988707` at `beta = 0.0005`), while one-sided `sub` (`(g(z+) - g(z_free))/beta`, `demo/model.js`) suffers an even larger opposite $O(r_0/\beta)$ pole because the nudge phase relaxes $r_0 \to r_\beta \ll r_0$, exploding to **`6.033060`** (`test-0016`) and **`27.815013`** (`test-0065`) even at `E < 1e-6`, and **`2922.415954`** / **`10098.956616`** at `T10`. Centered $\pm\beta$ (`(g(z+) - g(z-))/(2*beta)`) double-cancels both the $O(\beta)$ bias and the symmetric inherited residual $r_0$, holding relative error at **`0.001284`** (`1201.9x` vs. `nosub`, `2276024.9x` vs. `sub`) and **`0.002141`** (`2330.1x` vs. `nosub`, `4716934.4x` vs. `sub`).
4. **Persistent Non-Normality & Complex-Curl Power-Iteration Bias (`2.912e+9x`) `[exact+anchor]`:** Across all `300` live equilibria, `M*` is persistently non-normal (`||M*||_2 / rho(M*) in [1.448734, 3.679652]`, median `2.174445`), and converged-wrong puzzles (`31/300`, `10.33%`) exhibit **`+21.34%`** higher median spectral radius (`0.191355` vs. `0.157705`; mean `+22.99%`). On the **`39/300` (`13.00%`)** puzzles with a strictly complex-conjugate dominant eigenvalue pair, `core/diagnostics.py`'s 60-step real power iteration cannot converge to a real eigenvector and suffers **`0.069364`** median (`0.228466` max) relative error vs. **`2.381711e-11`** median on the `261/300` (`87.00%`) real-dominant puzzles — a **`2912360064x` (`2.912e+9x`)** accuracy degradation.

---

## 2. Exact Pure-$\mathbb{Z}/\mathbb{Q}$ Oracle Witnesses (Pillars 1–3) `[exact]`

All exact algebraic witnesses are computed in `s76_circular_pc_tomography.py` over $\mathbb{Q}$ (`fractions.Fraction`) using exact Gaussian elimination and Bunch-Kaufman symmetric congruence (zero IEEE-754 floats).

### 2.1 Pillar 1 — Block-Cyclic Loop-Schur Metric Tensor, Holonomy & Adjoint Cancellation

For non-commuting $2\times 2$ rational transition blocks $A_1, A_2, A_3 \in \mathbb{Q}^{2\times 2}$ and cost gradient $g_s = (3/4, -5/6)^\top$:

| Witness | $L$ | $\det(I - M_{\mathrm{loop}})$ | $\det(H_{\mathrm{PC}}) = \det(I-M)^2$ | $\det(G_{\mathrm{loop}})$ | Inertia $(G, H_{\mathrm{PC}}, S)$ | Loop-Schur Exact | Naive Differs | Adjoint Cancels | Cyclic $\mathrm{tr}/\det$ Invariant |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `l2_noncommuting_2x2` | 2 | `509/900` | `259081/810000` | `599/360` (`1.6639`) | `[2, 0, 0]`, `[4, 0, 0]`, `[2, 0, 0]` | `True` | `True` | `True` | `True` / `True` (`119/240`, `221/3600`) |
| `l3_noncommuting_2x2` | 3 | `177751/216000` | `31595418001/46656000000` | `222271/144000` (`1.5435`) | `[2, 0, 0]`, `[6, 0, 0]`, `[2, 0, 0]` | `True` | `True` | `True` | `True` / `True` (`113/600`, `2431/216000`) |

### 2.2 Pillar 2 — Exact EP Bias Law & Truncated-Phase $O(r/\beta)$ Pole Blowup

For the exact linear circular-PC witness ($\theta = 1/3$, $d = 1 - \theta = 2/3$, $c = 2$, $q = 3/2$, exact IFT gradient $g_{\mathrm{IFT}} = 27/4 = 6.7500$):

**Converged Phases (Exact $O(\beta)$ One-Sided Bias vs. Identically Zero Centered Bias):**

| $\beta$ | One-Sided $g_1(\beta)$ | One-Sided Bias $-q^2\beta/d^3$ | Centered $g_{\pm}(\beta)$ | Centered Bias | Formula Match |
| :---: | :---: | :---: | :---: | :---: | :---: |
| `1/5` | `837/160` (`5.2313`) | `-243/160` (`-1.5188`) | `27/4` | `0` | `True` |
| `1/20` | `4077/640` (`6.3703`) | `-243/640` (`-0.3797`) | `27/4` | `0` | `True` |
| `1/100` | `21357/3200` (`6.6741`) | `-243/3200` (`-0.0759`) | `27/4` | `0` | `True` |

**Truncated Free Phase ($\delta_0 = 1/100$, $e_0 = 1/150$, nonzero free-phase parameter gradient $g_{\mathrm{free}} = -301/15000$):**

| $\beta$ | `nosub` Inherited $|\Delta g|$ ($\gamma=1/2$) | `sub` Converged-Nudge $|\Delta g|$ ($\gamma=0$) | Centered $\pm\beta$ Inherited $|\Delta g|$ |
| :---: | :---: | :---: | :---: |
| `1/50` | `121/192` (`0.6302`) | `4087/4800` (`0.8515`) | `9/400` (`0.0225`) |
| `1/500` | `240049/48000` (`5.0010`) | `480871/48000` (`10.0181`) | `9/400` (`0.0225`) |
| `1/5000` | `24029929/480000` (`50.0624`) | `48159271/480000` (`100.3318`) | `9/400` (`0.0225`) |

Centered $\pm\beta$ cancels the $1/\beta$ pole identically across all three orders of magnitude (`centered_pole_cancelled_beta_invariant = True`), holding error constant at `9/400 = 0.0225` while both one-sided rules diverge linearly in $1/\beta$.

### 2.3 Pillar 3 — Krein Inertia, Bifurcation Shadow, GD Cliff, Non-Normality & Elliptic Curl

- **Contractive GD Cliff (`a = b = 1/2`):** $\rho(M) = 1/4 < 1$, $\det(H_{\mathrm{PC}}) = 9/16$, inertia `[2, 0, 0]` (SPD), yet $\lambda_{\max}(H_{\mathrm{PC}}) = 9/4 = 2.2500 > 2$, forcing plain-GD Euler critical step $\eta_{\mathrm{crit}} = 8/9 \approx 0.8889$.
- **Critical Bifurcation Shadow (`a = 2, b = 1/2`):** $M = 1$, $\det(H_{\mathrm{PC}}) = 0$, inertia `[1, 0, 1]`, explicit nonzero kernel vector $v = (2, 1)^\top$ verified in both $\ker(J_R)$ (`True`) and $\ker(H_{\mathrm{PC}})$ (`True`).
- **Krein Saddle-Point Lagrangian Inertia:** Contractive $2\times 2$ DEQ KKT matrix $K$ has indefinite Krein signature `[2, 2, 0]` (`det = 1/4`); at rank-1 bifurcation (`M = diag(1, 1/2)`), signature collapses to `[1, 1, 2]` (`det = 0`).
- **Non-Normal Transient Amplification (`M = [[1/2, 2], [0, 1/2]]`):** $\rho(M) = 1/2 < 1$, yet $\|M^t e_2\|_2^2$ overshoots unity across $t = 1, 2, 3$ (`t1 = 17/4 = 4.2500`, `t2 = 65/16 = 4.0625`, `t3 = 145/64 = 2.2656`) before asymptotic decay (`t10 = 1601/1048576 = 0.001527`).
- **Elliptic Complex-Curl Power-Iteration Obstruction (`M = [[3/10, -8/5], [2/5, 3/10]]`):** Skew-symmetric curl entry `-1`, exact $\rho(M)^2 = 73/100 = 0.7300 < 1$, bracketed strictly by $\|M e_1\|_2^2 = 1/4 = 0.2500 < \rho^2 < 53/20 = 2.6500 = \|M e_2\|_2^2$ (`strict_oscillation_bracket = True`).

---

## 3. Live Real-Weight Tomography on `rel-int/CircularEP` (`best.json` + `puzzles.json`) `[anchor]`

Captured CPU-only via `s76_live_anchor_capture.py` directly on shipped `demo/models/best.json` (`sha256: fe5c2e9ba31605345ae25b0000987a6b4d9b9a57224a4c5d15a4d25d0f5b7eda`) and `demo/puzzles.json` (`sha256: eed9fb4be46736c1147fdfc292830bedaf5c0f4e640e0c8b2a06d7f12feeba76`), frozen as zero-float canonical JSON in `s76_circularep_live_anchor.json` (`sha256: c2eb18c5553be012ba0812d4cdfc72c80c29854575d0540a71800d92dee0ac66`). Model dimensions: `H = 256`, `N = 4`, `P = 16`, `din = 80`, `n_classes = 64`, activation `tanh`.

### 3.1 Exact Upstream Float32 Parity Check

| Check | Measured | Upstream Reference (`best.json`) | Discrepancy |
| :--- | :---: | :---: | :---: |
| Singular values $\sigma_{\max}(W_1), \sigma_{\max}(W_2)$ | `1.000000078`, `1.000000063` | `1.000000078`, `1.000000063` | `0` (9-digit exact) |
| `parity` (heavy-ball, `test-0016`) | `iters=44`, `E_nudge=0.009806`, `C_nudge=0.160871` | `iters=44`, `E_nudge=0.009806`, `C_nudge=0.160871` | `max|du|,|ds| <= 2.980232e-07`, `gnorm_err = 6.052438e-06` |
| `parity_alt` (plain GD, `test-0016`) | `iters=27`, `E_nudge=0.009803`, `C_nudge=0.160884` | `iters=27`, `E_nudge=0.009803`, `C_nudge=0.160884` | `max|du|,|ds| <= 2.384186e-07`, `gnorm_err = 3.708440e-06` |
| `300`-puzzle outcomes | `solved=269` (`89.67%`), `wrong=31` (`10.33%`), `stalled=0` | `solved=269`, `wrong=31` | `0` exact match |
| First-128 $\rho(M^*)$ (`med / mean / p90 / max`) | `0.165797 / 0.170547 / 0.231383 / 0.317995` | `0.165798 / 0.170547 / 0.231385 / 0.317997` | `<= 2e-6` |

### 3.2 Full 300-Puzzle Spectral, Loop-Schur, GD-Cliff & Complex-Curl Tomography

| Metric (`N = 300` live equilibria) | Min | Median | P90 | Max |
| :--- | :---: | :---: | :---: | :---: |
| Loop spectral radius $\rho(M^*)$ (equilibrium) | `0.071855` | `0.161550` | `0.227759` | `0.317995` |
| Loop operator norm $\|M^*\|_2$ (equilibrium) | `0.264402` | `0.350971` | `0.397968` | `0.484745` |
| Non-normality ratio $\|M^*\|_2 / \rho(M^*)$ | `1.448734` | `2.174445` | `3.030077` | `3.679652` |
| Initial feedforward $\rho(M_{\mathrm{ff}})$ / $\|M_{\mathrm{ff}}\|_2$ | `0.089235` / `0.285917` | `0.181626` / `0.364670` | — | `0.340381` / `0.487846` |
| $512\times 512$ $H_{\mathrm{PC}}$ $\lambda_{\min}$ / $\lambda_{\max}$ | `0.148251` / `2.069272` | — | — | `0.443548` / `2.893074` |
| $256\times 256$ $G_{\mathrm{loop}}$ $\lambda_{\max}$ (curvature softening) | `1.195321` (`+19.53%`) | — | — | `1.420610` (`+42.06%`) |
| $256\times 256$ Loop-Schur $S_{s \mid u}$ $\lambda_{\min}$ | `0.308018` | — | — | `0.728729` |

- **Loop-Schur Identity Verification (`300/300`):** `max ||S_direct - (I - M*)^T G_loop^(-1) (I - M*)||_max = 4.440892e-15`.
- **Solved vs. Converged-Wrong Separation:** Solved (`269`) median $\rho = 0.157705$ (mean `0.160729`, median non-normality `2.236270`) vs. converged-wrong (`31`) median $\rho = 0.191355$ (`+21.34%`, mean `0.197680` `+22.99%`, median non-normality `1.888970`).
- **Plain-GD $\eta = 0.8$ Euler Cliff ($2/\eta = 2.500000$):** `176/300` (`58.67%`) converge with **`176/176` (`100.00%`)** satisfying $\lambda_{\max}(H_{\mathrm{PC}}) \le 2.50$ (`median = 2.265260`, `max = 2.474916`); `124/300` (`41.33%`) diverge, with **`97/124` (`78.23%`)** strictly above `2.50` (`median = 2.554557`, `min = 2.446027`).
- **60-Step Power Iteration Complex-Curl Bias (`core/diagnostics.py`):** On `261/300` (`87.00%`) real-dominant equilibria, median relative error is `2.381711e-11` (`max = 0.139851`); on `39/300` (`13.00%`) complex-conjugate dominant equilibria, median relative error jumps to `0.069364` (`max = 0.228466`), a **`2912360064x` (`2.912e+9x`)** blowup.

### 3.3 Live EP $\beta$-Scaling & Truncated-Phase $O(r/\beta)$ Blowup (`test-0016` & `test-0065`)

**Exact Converged Phases (`E_free < 1e-31`, `max_nudge_res < 1e-13`, float64 IFT ground truth):**

| Puzzle | Adjoint $G_{\mathrm{loop}}$ Cancel Err | $\beta$ | One-Sided Rel Err (`cos`) | Centered $\pm\beta$ Rel Err (`cos`) |
| :--- | :---: | :---: | :---: | :---: |
| `test-0016` | `3.330669e-16` | `0.2` | `0.28850074` (`0.99747697`) | `0.21585972` (`0.99137618`) |
| `test-0016` | `3.330669e-16` | `0.05` | `0.09284561` (`0.99957877`) | `0.01443732` (`0.99994921`) |
| `test-0016` | `3.330669e-16` | `0.01` | `0.02026256` (`0.99997741`) | `0.00056504` (`0.99999992`) |
| `test-0016` | `3.330669e-16` | `0.002` | `0.00413088` (`0.99999904`) | `0.00002258` (`1.00000000`) |
| `test-0065` | `8.326673e-17` | `0.2` | `0.22614802` (`0.99739107`) | `0.14081720` (`0.99887732`) |
| `test-0065` | `8.326673e-17` | `0.05` | `0.07216833` (`0.99977365`) | `0.00822460` (`0.99999520`) |
| `test-0065` | `8.326673e-17` | `0.01` | `0.01559100` (`0.99999004`) | `0.00032658` (`0.99999999`) |
| `test-0065` | `8.326673e-17` | `0.002` | `0.00316895` (`0.99999959`) | `0.00001306` (`1.00000000`) |

Consecutive `5x` step ratios (`0.05 -> 0.01` / `0.01 -> 0.002`): `test-0016` one-sided `4.58x / 4.91x` vs. centered `25.55x / 25.02x`; `test-0065` one-sided `4.63x / 4.92x` vs. centered `25.18x / 25.01x` (matching theoretical `5.00x` for $O(\beta)$ and `25.00x` for $O(\beta^2)$).

**Truncated Free Phase + Finite Nudge (`T_nudge = 40`, evaluated at `beta = 0.0005`):**

| Puzzle | Free-Phase Regime | `E_free` | `nosub` (`core/ep.py`) Rel Err (`cos`) | `sub` (`demo/model.js`) Rel Err (`cos`) | Centered $\pm\beta$ Rel Err (`cos`) | Centered Gain vs. `nosub` / `sub` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| `test-0016` | `T10` (`iters=10`) | `1.394173e-01` | `1.543285` (`0.576657`) | `2922.415954` (`-0.082988`) | `0.001284` (`0.999999`) | `1201.9x` / `2276024.9x` |
| `test-0016` | `default_E_lt_1e6` (`iters=44`) | `7.051408e-07` | `0.003384` (`0.999995`) | `6.033060` (`0.310822`) | `0.000888` (`1.000000`) | `3.8x` / `6794.0x` |
| `test-0065` | `T10` (`iters=10`) | `1.180477e-01` | `4.988707` (`0.102383`) | `10098.956616` (`-0.008430`) | `0.002141` (`0.999998`) | `2330.1x` / `4716934.4x` |
| `test-0065` | `default_E_lt_1e6` (`iters=43`) | `9.531290e-07` | `0.020208` (`0.999796`) | `27.815013` (`-0.114721`) | `0.001286` (`0.999999`) | `15.7x` / `21629.1x` |

---

## 4. Live Kernel-Checked Pure-`Init` `Lean 4.36.0` Theorem Ledger (`19/19`) `[exact]`

File: `CircularPCLoopSchur.lean` (`sha256: 573c9ce1a8c6b62882554ea7ebbda10cda19ac7e558def8bb72e7d2a9e15da92`), toolchain `leanprover/lean4:v4.36.0`, zero external imports (`Init` only), `0` warnings, `0` stderr bytes, `0` `sorryAx` / `Classical.choice` / `Lean.ofReduceBool` / `Lean.trustCompiler`. Live `lean` and isolated scratch `lake build` (`4 jobs`) both verify all `19/19` universal theorems (`18` `[propext, Quot.sound]`, `1` `[propext]`):

| # | Theorem (`CircularPCLoopSchur.*`) | Exact Axioms | Verified Statement |
| :---: | :--- | :---: | :--- |
| 1 | `loop_schur_2node_metric_exact` | `[propext, Quot.sound]` | Exact 2-node Loop-Schur metric identity (1 - a*b)^2 / (1 + b^2) |
| 2 | `loop_schur_2node_metric_softening` | `[propext, Quot.sound]` | Strict curvature softening 1 + b^2 > 1 for every nonzero closing edge b |
| 3 | `loop_schur_3node_metric_exact` | `[propext, Quot.sound]` | Exact 3-node Loop-Schur with G_loop = 1 + a3^2 + (a3*a2)^2 |
| 4 | `loop_hessian_2node_det_eq_monodromy_sq` | `[propext, Quot.sound]` | det(H_PC) = (1 - a*b)^2 = det(I - M_loop)^2 |
| 5 | `loop_adjoint_gloop_cancellation` | `[propext, Quot.sound]` | Exact G_loop cancellation in DEQ adjoint (1 - a*b)*e2 = -gs |
| 6 | `loop_zero_energy_deq_bijection_2node` | `[propext, Quot.sound]` | Zero-energy circular PC <-> 2-node DEQ fixed-point bijection (Theorem 1) |
| 7 | `loop_zero_energy_deq_bijection_3node` | `[propext, Quot.sound]` | Zero-energy circular PC <-> 3-node DEQ fixed-point bijection (Theorem 1) |
| 8 | `ep_cubic_jet_centered_cancels_order1` | `[propext, Quot.sound]` | Centered +/-beta EP cancels O(beta) bias identically, leaving O(beta^2) |
| 9 | `ep_exact_linear_circular_pc_bias_law` | `[propext, Quot.sound]` | Exact closed-form linear circular-PC one-sided bias vs zero centered bias |
| 10 | `ep_truncated_phase_pole_and_centered_cancellation` | `[propext, Quot.sound]` | Truncated free-phase O(r/beta) pole + exact centered double-cancellation |
| 11 | `ep_truncated_pole_nonzero` | `[propext]` | Strict non-vanishing of the O(r/beta) pole for nonzero x* and residual r |
| 12 | `contractive_loop_spd_hessian` | `[propext, Quot.sound]` | Contractive loop (|a*b| < 1) implies strictly positive-definite H_PC |
| 13 | `critical_bifurcation_zero_mode_shadow` | `[propext, Quot.sound]` | At a*b = 1, det(H_PC) = 0 with explicit nonzero zero-mode shadow v = (a, 1) |
| 14 | `krein_deq_lagrangian_indefinite_inertia` | `[propext, Quot.sound]` | DEQ KKT saddle-point Lagrangian has indefinite Krein signature (+, -) with det < 0 |
| 15 | `non_normal_contractive_transient_amplification` | `[propext, Quot.sound]` | Jordan nilpotent shift with rho < 1 exhibits arbitrarily large transient overshoot |
| 16 | `complex_curl_power_iter_oscillation` | `[propext, Quot.sound]` | Elliptic complex-curl monodromy forces strict power-iteration norm oscillation |
| 17 | `hessian_gd_stability_cliff_despite_contraction` | `[propext, Quot.sound]` | Contractive loop (rho = 1/4) has lambda_max(H_PC) = 9/4 > 2 (eta_crit = 8/9) |
| 18 | `monodromy_2x2_trace_cyclic_invariance` | `[propext, Quot.sound]` | Cyclic holonomy basepoint invariance tr(A2*A1) = tr(A1*A2) |
| 19 | `monodromy_2x2_det_cyclic_invariance` | `[propext, Quot.sound]` | Cyclic holonomy basepoint invariance det(A2*A1) = det(A1*A2) |

---

## 5. Verification & Hardening Receipts (`100.0% PASS`)

- **Pure-$\mathbb{Z}/\mathbb{Q}$ Hygiene:** `0` bare `assert`s, `0` AST `float` literals or `float()` calls, `0` `.isdigit()` calls, `0` `random` imports, `0` CRLF bytes across `s76_circular_pc_tomography.py`, `verify_s76_circular_pc.py`, and `test_s76_circular_pc_r5.py`; `0` bare `assert`s in `s76_live_anchor_capture.py`.
- **4-Mode `-I` Parity + `umask 077` + CI `chmod 644` Checkout Simulation:** `test_s76_circular_pc_r5.py` passes **`19/19 OK`** across all 6 environments (`-I -B`, `-I -O -B`, `-I -B -W error`, `PYTHONHASHSEED=42 -I -B`, `umask 077`, and simulated git `chmod 644 *.json`); `verify_s76_circular_pc.py --standalone` matches disk `s76_circular_pc_certificate.json` bit-for-bit (`d30805fcb876de096d9b387a8274ecd8063b7906f4feb36124b38a05aefadc95`) across all 4 modes, and `--check --json` output is bit-identical (`319419956e6d4465616cce4a8140d689c8e7db2ea368804c9c45156be9c8f525`) across all 4 modes.
- **4-Surface v2.1 Zero-Bypass Fuzzing (`ZBF`):** **`82/82 PASS`** (`CLI 25/25`, `FR1 19/19`, `FR0 19/19`, `SEC 19/19`; `0` bypasses, `0` crashes) exercising all four genuine verification surfaces.
- **Live Guard Mutation Testing (`aletheia mutate --guards require_ok --workers 4 --timeout 180 --max-mutants 0`):** **`258/258 (100.0%)`** killed (`s76_circular_pc_tomography.py` `65/65`, `verify_s76_circular_pc.py` `193/193`; `survived=0`, `timeout=0`, `truncated=False`, `null_mutant=passed` on both).
- **Null-Checked Whole-File DFS AST Boolean-Expression Mutation (boolean operator flip + sub-condition deletion):** **`202/202 (100.0%)`** killed (`s76_circular_pc_tomography.py` `56/56`, `verify_s76_circular_pc.py` `146/146`; `null_ok=True` on both, `survived=0`, `timeout=0`).
- **R10 Lean 4 Static & Live Hardening:** Embedded static gate strips only nested block/line comments and forbids all quotes, guillemets, imports, meta/macro/elab/syntax escapes, `opaque`, `csimp`, `debug.*`, inline `partial`, and all native-decide forms (`+native` with any preceding flags, `DecideConfig`/`Decide.Config`, `decide (config := ...)`, `native := !false/(true)`); live parser rejoins line-wrapped `[a,\n b]` axiom lists, rejects duplicates, and enforces exact 19-theorem set equality. Dual `aletheia audit-check --lean-audit --strict-ancestors --safety-scan --scripts verify_s76_circular_pc.py test_s76_circular_pc_r5.py` passes cleanly (`0` findings, `0` lean findings/notices, `0` safety findings, `0` leaks).

---

## 6. Novelty & Scope Boundary (`N0` vs. `N1`)

- **`N0` (Established Baseline / Classical Foundations):** Predictive coding energy minimization, Deep Equilibrium (DEQ) Implicit Function Theorem adjoints, Laborieux et al. centered $\pm\beta$ EP $O(\beta^2)$ cancellation, classical Schur complement and Bunch-Kaufman Sylvester inertia, non-normal Jordan transient growth, and Salvatori & Forasassi's `arXiv:2611.27610` Theorem 1 zero-energy fixed-point bijection.
- **`N1` (Verified Syntheses & Concrete Empirical/Formal Diagnostics in Track S76):**
  1. Exact $L$-layer block-cyclic Loop-Schur metric factor $G_{\mathrm{loop}}^{-1} = (I + \sum_{k=1}^{L-1} P_k P_k^\top)^{-1}$ ($G_{\mathrm{loop}}$ exceeding $I$ by `+19.53%–+42.06%`, softening readout curvature $1 - 1/\lambda_{\max}(G_{\mathrm{loop}})$ by `16.34%–29.61%` on live `best.json`) paired with its exact gauge cancellation in the EP/DEQ adjoint (`Lean 4.36.0` + `300/300` live `512x512` Hessians).
  2. Quantitative prediction of `best.json`'s plain-GD $\eta = 0.8$ convergence cliff from coupled Hessian $\lambda_{\max}(H_{\mathrm{PC}}) \le 2.50$ (`176/176` converged vs. `97/124` diverged above `2.50`) despite uniform loop contraction ($\rho < 0.32$, $\|M^*\|_2 < 0.49$).
  3. Live demonstration and formal proof of the two-sided $O(r_0/\beta)$ vs. $O(r_\beta/\beta)$ truncation pole asymmetry between `demo/model.js` (`sub`) and `core/ep.py` (`nosub`), showing `sub` explodes even at `best.json`'s production tolerance `E < 1e-6`, and exact double-cancellation by centered $\pm\beta$.
  4. Live identification of the `39/300` (`13.00%`) complex-conjugate dominant equilibrium regime causing a `2.912e+9x` median accuracy collapse in `core/diagnostics.py`'s real power iteration, alongside the `+21.34%` higher median $\rho(M^*)$ on converged-wrong puzzles.
- **Explicit Boundary:** Live real-weight measurements (`[anchor]`) hold for the shipped `2x256` `tanh` Sudoku model `best.json`; generalizing the exact spectral cliff thresholds to other architectures or activations requires re-evaluating $\lambda_{\max}(H_{\mathrm{PC}})$ and $G_{\mathrm{loop}}$ on those weights.

---

## 7. Frozen Artifact Manifest (9 Core Files + `REPORT.md`)

| File | Lines | Bytes | Mode | SHA-256 |
| :--- | ---: | ---: | :---: | :--- |
| `CircularPCLoopSchur.lean` | 657 | 30046 | `0o644` | `573c9ce1a8c6b62882554ea7ebbda10cda19ac7e558def8bb72e7d2a9e15da92` |
| `lakefile.toml` | 6 | 131 | `0o644` | `eab58f344caad012af054a84e82c410663c95f4ff0773cb48cc57252e4852704` |
| `lean-toolchain` | 1 | 25 | `0o644` | `582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a` |
| `s76_circular_pc_certificate.json` | 1 | 7006 | `0o600` | `d30805fcb876de096d9b387a8274ecd8063b7906f4feb36124b38a05aefadc95` |
| `s76_circular_pc_tomography.py` | 842 | 35844 | `0o644` | `08f7e44367e05a24387a900cbc7e47816fb3f598cd1b3edaf0841cc62812cc89` |
| `s76_circularep_live_anchor.json` | 1 | 13818 | `0o600` | `c2eb18c5553be012ba0812d4cdfc72c80c29854575d0540a71800d92dee0ac66` |
| `s76_live_anchor_capture.py` | 581 | 27127 | `0o644` | `6193d6bffcc40c77bf3dee95ccc29a65156978fc23abb2800c4079e182d2b93e` |
| `test_s76_circular_pc_r5.py` | 1154 | 75712 | `0o644` | `1e9ddc883a03725871f6c749d803a2bcaa2e5a7c41fcb39c89a07fcc0e369218` |
| `verify_s76_circular_pc.py` | 1035 | 49510 | `0o644` | `7a305658b01a39348b31519a157d7e1c553c2092d0fad7a79bdffd1333eec3e8` |
| `REPORT.md` | *(self)* | *(self)* | `0o644` | *(recorded externally in submission summary)* |

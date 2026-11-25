# Circular Predictive Coding: Loop-Schur Metric Tensor, Holonomy, Krein Inertia & Equilibrium-Propagation Obstructions

Machine-checkable operator-theoretic study uniting pure-$\mathbb{Z}/\mathbb{Q}$ exact rational oracles (`0` floats, pure Python stdlib), **`19/19` universal pure-`Init` Lean `4.36.0` theorems** (`0` Mathlib, `0` warnings, `0` `sorryAx`/`Classical.choice`), and a reproducible CPU real-weight anchor across all **`300/300`** test puzzles of the shipped `2×256` `tanh` Sudoku model in [`rel-int/CircularEP`](https://github.com/rel-int/CircularEP/tree/ba2f9b87cc348c0065db27130da20bd2770b8c91) (commit `ba2f9b87`), examining Circular Predictive Coding (`arXiv:2611.27610`, Salvatori & Forasassi) and Equilibrium Propagation (EP).

> **Epistemic boundary:** Exact rational witnesses and `19/19` Lean `4.36.0` proofs hold universally as algebraic theorems (`[exact]`). Live real-weight spectral and EP measurements (`[anchor]`) hold specifically for the shipped `2×256` `tanh` Sudoku weights `demo/models/best.json` across `demo/puzzles.json` and are frozen as zero-float canonical decimal strings in [s76_circularep_live_anchor.json](s76_circularep_live_anchor.json).

## 1. Principal Findings

1. **Exact $L$-Layer Loop-Schur Metric Tensor $G_{\mathrm{loop}}^{-1}$ & Adjoint Gauge-Cancellation:** Eliminating the $L-1$ internal nodes from the circular predictive-coding energy Hessian $H_{\mathrm{PC}} = J_R^\top J_R$ yields the metric-weighted Schur pushforward
   $$S_{x_L \mid x_1,\dots,x_{L-1}} = (I - M_{\mathrm{loop}})^\top G_{\mathrm{loop}}^{-1} (I - M_{\mathrm{loop}}), \qquad G_{\mathrm{loop}} = I + \sum_{k=1}^{L-1} (A_L \cdots A_{k+1})(A_L \cdots A_{k+1})^\top \succeq I,$$
   rather than naive $(I - M_{\mathrm{loop}})^\top(I - M_{\mathrm{loop}})$ for $L \ge 2$. Across all `300/300` live `512×512` `best.json` Hessians (`max_abs_err = 4.440892e-15`), $G_{\mathrm{loop}}$ exceeds $I$ by `+19.53%` to `+42.06%` ($\lambda_{\max}(G_{\mathrm{loop}}) \in [1.195321, 1.420610]$), softening readout curvature ($1 - 1/\lambda_{\max}(G_{\mathrm{loop}})$) by `16.34%` to `29.61%`. Yet in the EP/DEQ equilibrium adjoint $e_L^* = -(I - M_{\mathrm{loop}}^\top)^{-1}\nabla_{x_L} C$, $G_{\mathrm{loop}}$ cancels identically (`3.330669e-16` on `test-0016`, `8.326673e-17` on `test-0065`).
2. **Plain-GD Euler Stability Cliff Despite Strong Loop Contraction:** Even when the loop monodromy is strongly contractive ($\rho(M^*) \in [0.071855, 0.317995]$, $\|M^*\|_2 \in [0.264402, 0.484745]$), the coupled PC Hessian satisfies $\lambda_{\max}(H_{\mathrm{PC}}) \in [2.069272, 2.893074] > 2$. Under plain gradient descent at $\eta = 0.8$ (Euler threshold $2/\eta = 2.500000$), `176/176` (`100.00%`) of converged puzzles satisfy $\lambda_{\max}(H_{\mathrm{PC}}) \le 2.50$ (`max = 2.474916`), whereas `97/124` (`78.23%`) of diverging puzzles violate $\lambda_{\max}(H_{\mathrm{PC}}) > 2.50$ (`median = 2.554557`).
3. **Two-Sided $O(r/\beta)$ Truncated-Phase Pole Obstruction & Centered $\pm\beta$ Double-Cancellation:** Under converged phases (`E < 1e-31`, `nudge_res <= 1e-13`), one-sided EP decays as $O(\beta)$ (`4.91×`/`4.92×` per `5×` $\beta$-step) while centered $\pm\beta$ EP decays as $O(\beta^2)$ (`25.02×`/`25.01×`). Under truncated free phases (`T_free = 10` or production `E < 1e-6`, `T_nudge = 40`, `beta = 0.0005`), one-sided `nosub` (`core/ep.py`) diverges as $O(r_\beta/\beta)$ (`1.543285`/`4.988707` at `T10`), while one-sided `sub` (`demo/model.js`) suffers an even larger opposite $O(r_0/\beta)$ pole (`6.033060`/`27.815013` even at `E < 1e-6`; `2922.415954`/`10098.956616` at `T10`). Centered $\pm\beta$ cancels both the $O(\beta)$ bias and the symmetric $O(r/\beta)$ pole, holding relative error at `0.001284` (`test-0016`) and `0.002141` (`test-0065`).
4. **Persistent Non-Normality & Complex-Curl Power-Iteration Bias (`2.912e+9×`):** Across all `300/300` equilibria, `M*` is persistently non-normal ($\|M^*\|_2/\rho(M^*) \in [1.448734, 3.679652]$, median `2.174445`), and converged-wrong puzzles (`31/300`, `10.33%`) show `+21.34%` higher median $\rho(M^*)$ (`0.191355` vs. `0.157705`). On the `39/300` (`13.00%`) equilibria with a strictly complex-conjugate dominant eigenvalue pair, `core/diagnostics.py`'s 60-step real power iteration jumps from `2.381711e-11` median relative error (on `261/300` real-dominant puzzles) to `0.069364` median (`0.228466` max) — a `2,912,360,064×` (`2.912e+9×`) accuracy collapse.

## 2. Standalone Pure-`Init` Lean `4.36.0` Theorem Ledger (`19/19`)

[CircularPCLoopSchur.lean](CircularPCLoopSchur.lean) compiles directly under Lean `4.36.0` with zero external imports (`Init` only, `0` warnings, `0` `sorryAx`, `0` `Classical.choice`, `18` `[propext, Quot.sound]` + `1` `[propext]`):

- **Loop-Schur, Determinant & Adjoint Cancellation:** `loop_schur_2node_metric_exact`, `loop_schur_2node_metric_softening`, `loop_schur_3node_metric_exact`, `loop_hessian_2node_det_eq_monodromy_sq`, `loop_adjoint_gloop_cancellation`, `loop_zero_energy_deq_bijection_2node`, `loop_zero_energy_deq_bijection_3node`
- **EP Order Cancellation & Truncated-Phase Pole:** `ep_cubic_jet_centered_cancels_order1`, `ep_exact_linear_circular_pc_bias_law`, `ep_truncated_phase_pole_and_centered_cancellation`, `ep_truncated_pole_nonzero`
- **Krein / Sylvester Inertia, Non-Normality, Curl & Holonomy:** `contractive_loop_spd_hessian`, `critical_bifurcation_zero_mode_shadow`, `krein_deq_lagrangian_indefinite_inertia`, `non_normal_contractive_transient_amplification`, `complex_curl_power_iter_oscillation`, `hessian_gd_stability_cliff_despite_contraction`, `monodromy_2x2_trace_cyclic_invariance`, `monodromy_2x2_det_cyclic_invariance`

## 3. Files & Reproducible Verification

| File | Role |
|---|---|
| [README.md](README.md) | Study summary, epistemic scope, theorem ledger, and reproduction commands. |
| [REPORT.md](REPORT.md) | Complete quantitative tables, proof summaries, and novelty boundary (`N0` vs. `N1`). |
| [CircularPCLoopSchur.lean](CircularPCLoopSchur.lean) | Standalone pure-`Init` Lean `4.36.0` formalization (`19` universal theorems). |
| [lakefile.toml](lakefile.toml) / [lean-toolchain](lean-toolchain) | Pinned `leanprover/lean4:v4.36.0` build specification. |
| [s76_circular_pc_tomography.py](s76_circular_pc_tomography.py) | Pure-$\mathbb{Z}/\mathbb{Q}$ stdlib oracle (`0` floats, `0` bare asserts, `0` RNG). |
| [verify_s76_circular_pc.py](verify_s76_circular_pc.py) | Hardened 4-surface verifier (`--standalone`, `--write`, `--check`) with embedded R10 static + live Lean `4.36.0` audit. |
| [s76_circular_pc_certificate.json](s76_circular_pc_certificate.json) | Canonical zero-float certificate (`certificate_sha256 = 4bfbdb44...`). |
| [s76_live_anchor_capture.py](s76_live_anchor_capture.py) | Reproducible CPU-only capture script for `rel-int/CircularEP` (`best.json` + `puzzles.json`). |
| [s76_circularep_live_anchor.json](s76_circularep_live_anchor.json) | Frozen zero-float canonical JSON anchor across all `300` live equilibria. |
| [test_s76_circular_pc_r5.py](test_s76_circular_pc_r5.py) | Assertion-free R5 verification, tamper, filesystem, and live-Lean test suite (`19` test groups). |

Run from `studies/s76-circular-pc-loop-schur-holonomy/` (Python 3.10+, zero third-party packages; Lean `4.36.0` on `PATH`):

```bash
# Full certificate replay + live Lean 4.36.0 kernel check (19/19 universal theorems)
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -B verify_s76_circular_pc.py --check s76_circular_pc_certificate.json --json

# Direct Lean 4.36.0 kernel verification
lean CircularPCLoopSchur.lean

# Run full R5 suite across all three isolated Python modes
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -B test_s76_circular_pc_r5.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -O -B test_s76_circular_pc_r5.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -B -W error test_s76_circular_pc_r5.py
```

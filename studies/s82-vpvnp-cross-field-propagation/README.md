# Cross-Field Operator Propagation from `anthropics/formal-math/vp-vnp` (`M1`–`M6`)

- **Issue Reference:** Refs [`Foundation-0/math0#38`](https://github.com/Foundation-0/math0/issues/38)
- **Arithmetic & Proof Discipline:** Pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2$ Python 3 standard library only (`int`, `fractions.Fraction`, `decimal.Decimal`; zero production floats, zero bare `assert`s, zero external Python dependencies) paired with `13` live kernel-checked pure-`Init` `Lean 4.36.0` theorems (`0` external imports, `0` warnings).
- **Canonical Certificate:** [`s82_vpvnp_propagation_certificate.json`](s82_vpvnp_propagation_certificate.json) (`payload_sha256 = ecf05db1bb683b19a4047850154f3fc2a6b87ae404536d52634e030cbc213502`).

---

## Overview & Four Propagation Engines (`M1`–`M6`)

This study propagates six algebraic, combinatorial, and formal-verification mechanisms (`M1`–`M6`) extracted from `anthropics/formal-math/vp-vnp` into four executable exact-arithmetic engines, explicitly proving and witnessing every non-commutativity and finite-precision boundary where lifting an operator across fields, weights, or floating-point formats breaks an invariant. Full derivations, tables, and proofs are documented in [`REPORT.md`](REPORT.md).

1. **Pillar 1 (`M1` + `M2`) — `CAT(0)` Rank-Metric Curvature, Strassen `⟨2,2,2⟩` Rerouting & 4-Party `(Q, K, V, O)` Crossing Wires (`Thm D.2`, `Thm C.1`, `Prop B.2`):**
   - **Strassen `⟨2,2,2⟩` Exact Rerouting:** Verified across all `16/16` elementary $2 \times 2$ basis pairs plus dense integer witnesses using `7` scalar products instead of `8` (`7^3 = 343 < 512 = 8^3`, `7^10 < 2^29`, $\omega < 2.9$).
   - **Linear-Code Rank-Metric `CAT(0)` Curvature:** Verifies minimum weight `4` for extended Hamming `[8, 4, 4]` and exact parity-check rank `5` (dimension `11`) for `[16, 11, 4]`, embedding a 5-point `Mat_2(F_2)` rank-metric witness with exact Gram determinant $\det G = -1/4 < 0$ and negative quadratic form $u^\top (2G) u = -2 < 0$ (blocking isometric Euclidean/$L_2$ embedding).
   - **4-Party `(Q, K, V, O)` Meixner Crossing-Wires Toy:** Exact integral determinant polynomial $\Psi(X) = \det M \in \mathbb{Z}[X]$ yields `QO|KV` flattening ranks `[1, 4, 4]` at $X^0$, $X^{16}$, and $X = 1$.

2. **Pillar 2 (`M3`) — Constructive `Lem F.2` 1D Nearest-Neighbor `CNOT` Compiler & Real-Shear Obstruction:**
   - **1D Nearest-Neighbor `CNOT` Synthesis over $U_n(\mathbb{F}_2)$:** `184/184` matrix-verified circuits (`23/23` exhaustive for $n = 4$, `72/72` exhaustive for $n = 5$, `25/25` for $n = 6$, `64/64` for $n = 8$) using only nearest-neighbor gates $x_j = I + E_{j,j+1}$ (peak multiplicity `4` on endpoint-1 targets, `16` in general; maximal-distance `CNOT(0 -> 7)` compiles to `92` gates).
   - **Real-Shear Obstruction:** Lifting $S_8 = I_8 + E_{0,1}$ from $\mathbb{F}_2$ to $\mathbb{Z}/\mathbb{Q}/\mathbb{R}$ keeps $\det(S_8) = 1$ but breaks involution and orthogonality: $\operatorname{tr}(S_8^\top S_8) = 9 \ne 8$, nontrivial Gram block $M = \begin{pmatrix}1 & 1\\ 1 & 2\end{pmatrix}$ satisfies $M^2 - 3M + I = 0$, and spectral condition number $\kappa_2(S_8) = \phi^2 = \frac{3+\sqrt{5}}{2} \in [2.61800, 2.61805] > 13/5 > 1$ (contrasted with orthogonal Walsh–Hadamard $\kappa_2 = 1$).

3. **Pillar 3 (`M4`) — Pure-$\mathbb{Q}$ Laurent $\beta$-Pole Control (`Lem N.2`, `Prop N.4`) & BF16 Underflow Floor:**
   - **`CircularEP` Implicit DEQ Gradient & `Lem N.2` Cutoff:** At zero free-phase residual ($e^* = 0$), $-\beta^{-1}(E(x^\beta) - E_0)$ cancels the $\beta^{-1}$ pole identically (`[beta^0] = -7/3`), and cutoff $N = 2^L\Delta = 8$ ($L = 3, \Delta = 1$) strips $\beta^9$ without perturbing $[\beta^{\le 0}]$; at $e^* = 1/100$, an exact $-1/100 \cdot \beta^{-1}$ pole leaks.
   - **`Prop N.4` Scale-Shift Isolation ($\sigma_r: \beta \mapsto \beta^r$):** Against an outer $\beta^{-2}$ pole ($P = 2$), $r = 1$ leaks (`min_exp = -1`), whereas $r = 3 > P$ isolates all perturbation terms (`min_exp = 0`, `[beta^0] = 9/4`).
   - **BF16 Normal Floor Obstruction:** Four composed rounds of $\sigma_3$ at $\beta = 2^{-2}$ reach $2^{-162} < 2^{-126}$ (flushing below IEEE BF16 normal range), separating exact $\mathbb{Q}((\beta))$ algebra from unrescaled low-precision arithmetic.

4. **Pillar 4 (`M5` + `M6`) — Weighted-Cheeger `128`-Expert Zipf MoE Lift & `aletheia` v2.3 Dual-Kernel Trust Gates (`T-13`..`T-15`):**
   - **Weighted-Cheeger MoE Cut Collapse:** Lifting `Prop E.10` ($9s(k-s) \ge 2k^2$, unweighted floor `2/9 = 0.222222`) to a `128`-expert Zipf MoE (`64/64` hot/cold shard) drops the cross-shard traffic fraction from `1/4 = 0.250000` (unweighted) to `0.110768` (`2.0062x` below `2/9`, `Zipf-1`) and `0.004694` (`47.3399x` below `2/9`, `Zipf-2`).
   - **Executable `aletheia` v2.3 Formal Trust Gates (`T-13`..`T-15`):** Standalone prototype enforcing `T-13` (`Statement.lean`/`Challenge.lean` import isolation), `T-14` (dual-kernel `Lean + nanoda`, pinned 40-char SHAs, strict standard axioms, zero `sorry` outside `Challenge.lean`), and `T-15` (1:1 paper-to-Lean declaration parity and explicit gap reasons for unformalized remarks): `1/1` positive bundle passes and `6/6` adversarial controls fail closed.

---

## Live `Lean 4.36.0` Formalization (`13/13` Pure-`Init` Theorems)

All `13` theorems in [`VpVnpPropagationCerts.lean`](VpVnpPropagationCerts.lean) compile directly under `Lean 4.36.0` with zero external imports (`Init` only), zero compiler warnings, and exact-set `#print axioms` verification (`4` zero-axiom `[]`, `9` standard-only axioms):

| # | Theorem (`S82VpVnpPropagationCerts.*`) | Pillar | Kernel Axioms |
| :-: | :--- | :---: | :--- |
| 1 | `strassen_2x2_exact_rerouting` | P1 (`M2`) | `[propext, Quot.sound]` |
| 2 | `strassen_exponent_strictly_subcubic` | P1 (`M2`) | `[]` |
| 3 | `linear_code_rank_metric_non_euclidean` | P1 (`M1`) | `[propext]` |
| 4 | `lem_F2_cnot1d_long_range_E03` | P2 (`M3`) | `[propext, Classical.choice, Quot.sound]` |
| 5 | `cnot1d_involution` | P2 (`M3`) | `[propext, Classical.choice, Quot.sound]` |
| 6 | `real_shear_minimal_poly_and_non_orthogonality` | P2 (`M3`) | `[propext, Classical.choice, Quot.sound]` |
| 7 | `real_shear_kappa_exceeds_26_tenths` | P2 (`M3`) | `[]` |
| 8 | `circularep_zero_residual_cancels_pole` | P3 (`M4`) | `[propext, Quot.sound]` |
| 9 | `m4_laurent_cutoff_valuation_bound` | P3 (`M4`) | `[propext, Quot.sound]` |
| 10 | `prop_N4_sigma_r_isolates_pole` | P3 (`M4`) | `[propext, Quot.sound]` |
| 11 | `prop_E10_unweighted_balanced_cut` | P4 (`M5`) | `[propext, Quot.sound]` |
| 12 | `weighted_moe_zipf_cut_beats_unweighted_floor` | P4 (`M5`) | `[]` |
| 13 | `aletheia_v23_trust_gate_fail_closed` | P4 (`M6`) | `[]` |

---

## Files in This Study (`7` Files)

| File | SHA-256 | Role |
| :--- | :--- | :--- |
| [`README.md`](README.md) | *(this file)* | Public overview, theorem index, and quickstart commands |
| [`REPORT.md`](REPORT.md) | `50dfb890594bc397d79bb1486434f04b9e16a4f1240709ae683ce8e513a4943f` | Full mathematical derivations, propagation matrix, and verification receipts |
| [`s82_vpvnp_propagation_oracle.py`](s82_vpvnp_propagation_oracle.py) | `40141a50a99b68c91929ad9085c17802d3572fb2ea081af4b60c588d33aecef1` | Pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2$ reference oracles for Pillars 1–4 (`M1`–`M6`) |
| [`verify_s82_vpvnp_propagation.py`](verify_s82_vpvnp_propagation.py) | `f5fa4fecc18a240520728f1b7ea513e556c852aefde762570c02e0853851545a` | Fail-closed certificate verifier, standalone replay CLI, and static + live `Lean 4` kernel checker |
| [`VpVnpPropagationCerts.lean`](VpVnpPropagationCerts.lean) | `5c774b978e9eaf918edfd63b4d85d01ce0740b45469c7c48b934f85c380f1dd8` | `13` pure-`Init` `Lean 4.36.0` formal certificates |
| [`s82_vpvnp_propagation_certificate.json`](s82_vpvnp_propagation_certificate.json) | `10c1203cd9c9f80d4082f4cdbbd09f60624aa1d4fd6b49c70ec5d622f0d2f76b` | Zero-float canonical JSON certificate (`payload_sha256 = ecf05db1bb683b19a4047850154f3fc2a6b87ae404536d52634e030cbc213502`) |
| [`test_s82_r5.py`](test_s82_r5.py) | `48b5ffd96bec55112195e8aa8f2e0c6e05775f48b1cf9da37f1e3d153b4638e9` | `12`-test isolated-mode, mutation-killing, and adversarial fail-closed test suite |

---

## Quickstart & Exact Reproduction

From `studies/s82-vpvnp-cross-field-propagation/` (note: `verify_s82_vpvnp_propagation.py` accepts one primary mode flag per invocation):

```bash
# 1. Verify the committed zero-float canonical JSON certificate (full oracle replay)
python3 -I -B verify_s82_vpvnp_propagation.py \
  --check s82_vpvnp_propagation_certificate.json --json

# 2. Run standalone oracle recomputation (reproduces payload_sha256 = ecf05db1... byte-for-byte)
python3 -I -B verify_s82_vpvnp_propagation.py --standalone --json

# 3. Verify all 13 pure-Init Lean 4.36.0 theorems via static anti-bypass + live kernel check
#    (requires `lean` 4.36.0 on PATH)
python3 -I -B verify_s82_vpvnp_propagation.py \
  --verify-lean VpVnpPropagationCerts.lean --json

# 4. Direct Lean 4 compiler check (0 warnings, exit code 0)
lean VpVnpPropagationCerts.lean

# 5. Full 3-mode isolated unit, tamper, and fail-closed test suite (12/12 OK in each mode)
python3 -I -B test_s82_r5.py
python3 -I -O -B test_s82_r5.py
python3 -I -B -W error test_s82_r5.py
```

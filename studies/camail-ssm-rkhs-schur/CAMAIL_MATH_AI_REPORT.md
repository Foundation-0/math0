# Wave 2 Round 5 — Arm R5-3 (`AUDIT-058`): Beyond-Language Exact-Operator Symbiosis & Read-Only Tomography of `camail-official`

- **Arm / Owner:** Arm R5-3 (`fractals-probe`), Round 5 Portal `R5-P03` (`SF-01 #26` RKHS Discrepancy Schur Quadrature + SSM/DeltaNet Schur & Spectral-Inertia Unification)
- **Strictly Read-Only Policy:** `0` external PRs, issues, comments, or mutations across all 7 pinned `camail-official` repositories.
- **Oracle Class & Honest Law-4 Novelty Tag:** `exact+anchor` (100% pure Python 3 stdlib `int`/`Fraction`/`Qi`, **ZERO floats** anywhere in code or JSON, **ZERO external deps**, **ZERO bare `assert`s**) | **`N1`** (clean-room zero-float cross-domain operator unification + independently reproducible upstream bug proofs `CAMAIL-B1..B5` across pinned CAMAIL repositories; all classical theories strictly quarantined as `N0`).
- **Artifacts (`studies/camail-ssm-rkhs-schur/`):**
  - `camail_math_ai_symbiosis.py` — self-contained pure-$\mathbb{Q}/\mathbb{Q}[i]$ exact-operator symbiosis & upstream bug-proof engine
  - `test_camail_math_ai_r5.py` — 4-group R1–R5 verification, invariance, unseen-instance, and mutation-kill suite (`49/49` `100.0%` killed)
  - `camail_math_ai_certificate.json` — zero-float canonical certificate (`canonical_sha256 = 2d3e646fa11628cf12b191b71f15f3fe46f808dae82f46d05d6fdca335716295`)
  - `CAMAIL_MATH_AI_REPORT.md` — this report

---

## 1. Pinned Read-Only `camail-official` Inventory & Verified Upstream Findings (`CAMAIL-B1`–`B5`)

| Repo (`camail-official/...`) | Pinned `main` SHA | Key Verified Code Anchors | Upstream Findings (Zero False Positives) |
|---|---|---|---|
| `compressm` (ICLR 2026) | `2910a88a273004e624351788126736aede7ab81f` | `compressm/reduction/{balanced_truncation.py:42-55, hsv.py:52-157}`, `compressm/models/lru.py:148-235` | **`CAMAIL-B1` (Math Bug):** `balanced_realization_transformation(method="chol")` (`balanced_truncation.py:20,49-50`, default!) uses `.T` instead of `.conj().T` (`Lo.T @ Lc`, `VT.T`), computing HSVs of $(P, \overline{Q})$ instead of $(P, Q)$ and breaking complex LRU balancing (committed exact $\mathbb{Q}[i]$ witness: $\operatorname{Tr}(PQ) = 116$ vs. buggy $\operatorname{Tr}(P\overline{Q}) = 68$). Also `hsv.py:122-148` docstring says *"sum of squared singular values"* while code sums L1 `np.sum(g_sorted)`; `hsv.py:83,139` silently converts `NaN` from tiny negative eigvals to `0.0`; `balanced_truncation.py:103` unseeded `np.random.permutation`. |
| `LinearAttentionPruning` | `919d8667d951c385e08510bc1267c2e7049a4f56` | `scripts/eval/effective_state_rank.py:382-425`, `src/key_reduction/pruners/{grad.py:59-135, rrqr.py:83-230, pca.py:42-130}` | **`CAMAIL-B2` (Dead-Code Bug):** `grad.py:75-76` returns `{}` on iteration 0 inside `for i, layer in enumerate(layers): return importance_scores`, making the entire Taylor importance computation (`L79-134` of `compute_importance`) unreachable! Also `pca.py:107` falsy-zero trap `if matrix_seed:` skips `seed=0`; `rrqr.py:110,214` unseeded RNG. |
| `LoReS` | `1529d48ed974ade54745d4ab22369693d7a8e10b` | `lores/backends/hf/qwen3_5/rotations.py:43-78`, `fake_quant/{quantizers.py:18-190, state.py:16-111}`, `rotations/matrices.py:1-75`, `evaluation/state_quant.py:11-44` | **`CAMAIL-B3` (Hygiene/R4):** Bare `assert`s silenced under `-O` in `quantizers.py:108` and `state_quant.py:14,28,37,42`; unseeded `torch.rand_like` stochastic rounding (`quantizers.py:47,120`). Strong architectural bridge to `siliquant#24` (`R_k^T S`, `S R_v` SpinQuant Hadamard rotations!). |
| `neuro-lds` (ICML 2026) | `9671e84b9dfa18056a670b13d2f3b42c779906de` | `scripts/{utils.py:43-198, main.py:353-401, models.py:1-27}` | **`CAMAIL-B4` (Formula Bug):** `utils.py:189` (`seqL2ctr_weighted`) uses `c0 = prod(1 + (g*g)/12)` while `sum1`/`sum2` (`L190,193`) are linear in `g`, violating $\iint K_\gamma = \prod(1 + \gamma_j/12)$! Produces strictly negative $D^2$ at $\gamma=1/2$ (`-31/1536`, clamped by `sqrt_safe(eps=1e-12)` to `1e-6` with zero gradient!) and spurious `+1/6` floor at $\gamma=2$. **`CAMAIL-B5` (R4/CLI):** `main.py:353-401` omits `--seed` (hardcoded `seed=0`), uses `type=bool` on `--verb` (`L365`), and tracks `scripts/__pycache__/*.pyc` + `.DS_Store` in git. |
| `Quotient_Recurrent_Reasoner_QRR` | `3e3c9ebecad534296482316e1c39f1063f0a6a32` | `models/{gauge_layers.py:1-160, integrator.py:1-105}` | Clean token-local $U(1)$ gauge-equivariant attention & quotient distance; bare `assert`s in `models/integrator.py:23,69,72,73,89,93` silenced under `-O`. |
| `LoopedActor` | `549a4e81ebd2d823112ed1bcf008f837e0f449b5` | `models/fprm.py:48-180` | Clean coupled-residual FPRM core (`alpha_1=0.75, alpha_2=0.25`) + differentiable policy-KL halting scan (bare `assert`s at `models/fprm.py:128,219,242`). |
| `discretax` | `d74281286a3d785c37288fea478eb7d3ea5201f6` | `src/discretax/sequence_mixers/{deltanet.py:20-70, lru.py:1-65}` | Clean JAX Equinox SSMs (`DeltaNet`, `LRU`, `S4D`, `S5`, `LinOSS`); exact WY lower-triangular forward-substitution inversion `(I + tril(K_beta K^T, -1))^{-1}` (`src/discretax/sequence_mixers/deltanet.py:56-60`). |

---

## 2. Strict Law-4 `N0` Prior-Art Quarantine Table (Aligned with `ROUND5_PORTALS.md` `R5-N0-06..20`)

| Quarantine ID | Established Classical / Modern Result | Primary Prior Art | Role in `AUDIT-058` |
|---|---|---|---|
| `R5-N0-06` | Balanced truncation, discrete Lyapunov Gramians, Hankel singular values, Singular Perturbation Approximation (SPA) | Moore (1981); Glover (1984); Liu–Anderson (1989); Antoulas (2005) | Foundation of Pillar 1 (`compressm` audit & DC Schur SPA) |
| `R5-N0-07..08` | In-training SSM compression, DeltaNet rank-based key pruning, LoReS recurrent quantization, QRR, LoopedActor, Discretax | CAMAIL (2026); Yang et al. (2024); Orvieto et al. (2023) | Pinned audited repositories (`7` repos) |
| `R5-N0-09` | Low-discrepancy sequences (Halton, Fibonacci rank-1 lattices), Niederreiter grid formula for $D_\infty^*$, Hickernell weighted $L_2$-discrepancies, optimal RKHS quadrature | van der Corput (1935); Hickernell (1998); Niederreiter (1992); Novak–Woźniakowski (2010) | Foundation of Pillar 3 (`neuro-lds` audit & RKHS Schur `⧄`) |
| `R5-N0-15` | Hadamard rotation incoherence (QuaRot/SpinQuant), lattice second moments $G(E_8) = 929/12960$, $G(\Lambda_{24})$, covering radii | Conway–Sloane (*SPLAG*); Ashkboos et al. (2024); Liu et al. (2024) | Foundation of Pillar 2 (`LoReS` $\leftrightarrow$ `siliquant#24`) |
| `R5-N0-18` | Banach fixed-point contraction & a-posteriori residual bounds | Banach (1922); Bai et al. (2019, DEQ) | Foundation of Pillar 4 (`LoopedActor` contraction) |
| `R5-N0-20` | Exact `R_opt`, `R_{H4}`, Bareiss PSD, `SP-09` dark-drift, and 8-glyph operator calculus (`⧄ ⧅ ⦷ ⟠ ⧇ ⦺ ⩩ ⫩`) | Cave Expedition Waves 1–2 (`AUDIT-002, 014, 027, 028, 031, 035, 051`) | Core exact-operator engine applied to CAMAIL |

---

## 3. Four Verified Exact-Operator Symbiosis Pillars (Zero Floats, Pure $\mathbb{Q}/\mathbb{Q}[i]$)

### Pillar 1 — `compressm` & `LinearAttentionPruning` $\longleftrightarrow$ `Foundation-0/spectral-inertia` (`⧄ ⧅ ⦺ ⩩`)
1. **Pure-$\mathbb{Q}[i]$ Proof of `CAMAIL-B1` (`balanced_truncation.py:49-50`):** For exact lower-triangular complex Cholesky factors $L_c, L_o \in \mathbb{Q}[i]^{2\times 2}$ defining complex Hermitian PD Gramians $P = L_c L_c^H$, $Q = L_o L_o^H$:
   - True squared HSV sum $\operatorname{Tr}(P Q) = \operatorname{Tr}((L_o^H L_c)^H (L_o^H L_c)) = \mathbf{116}$.
   - Upstream `Lo.T @ Lc` computes $\operatorname{Tr}((L_o^\top L_c)^H (L_o^\top L_c)) = \operatorname{Tr}(P \overline{Q}) = \mathbf{68 \neq 116}$ — literally computing the Hankel singular values of the **complex-conjugated observability Gramian $\overline{Q}$**!
2. **Exact Zero-Float Lyapunov + Direct Truncation vs. DC Schur-Complement SPA (`M_DC ⧄ x_2`):** On a coupled 3-state stable LTI system over $\mathbb{Q}$, exact Kronecker Lyapunov Gramians satisfy `⦺(P) = ⦺(Q) = (3, 0, 0)` (strictly PD, zero `eps = 1e-9` jitter, zero `NaN`s). Exact full DC gain is `G(1) = 220/19`: `compressm`-style direct truncation yields `5/1` (DC bias **`-125/19`**), whereas eliminating fast mode $x_2$ via exact DC **Schur complement (`⧄`)** gives **`220/19`** (`0/1` residual!).
3. **Exact Stable-Rank / `R_opt` / `R_{H4}` / Bareiss PSD Hierarchy (`LinearAttentionPruning` `effective_state_rank.py:382-425`):**
   - For PSD state Gram $G = S^\top S \succeq 0$, exact pure-$\mathbb{Q}$ moments obey $1 \le \mathrm{sr}(S) \le R_{\mathrm{opt}}(G) \le R_{H4}(G) \le \operatorname{rank}(S)$ without any SVD: on $\operatorname{diag}(4, 2, 1, 1)$, `sr = 2 < R_opt = 32/11 < R_{H4} = 89/23 < rank = 4`, bracketed by zero-float Bunch–Kaufman `⦺(4I - G) = (3, 1, 0)` and `⦺((15/4)I - G) = (3, 0, 1)`.
   - **Exact `CS-11` Blindness Refutation:** `diag(2, 1, 1, 0)` (rank 3) and `diag(2, 4/3, 1/3, 1/3)` (rank 4) have **identical stable rank `sr = 2/1` AND identical `R_opt = 8/3`**, yet the 2-step Schur moment bound **`R_{H4}` separates them cleanly (`3/1` vs `219/61`)** with zero SVD!
4. **DeltaNet Key-Pruning Schur Residual (`⧄`) & `SP-09` Dark-Mode Shadow (`⧅`):** Conditional Schur pruning `G_K ⧄ K_prune` strictly improves over naive coordinate slicing (`⦺(G_keep - (G_K ⧄ K_prune)) = (1, 1, 0)` PSD), while coupled singular dark fibers expose exact `SP-09` drift (`dim_dark = 1, r_cross = 1`, Krein inertia `(3, 0, 1)`).

### Pillar 2 — `LoReS` Recurrent-State Quantization $\longleftrightarrow$ `Moissanite-Labs/siliquant#24`
1. **Exact Pure-$\mathbb{Q}$ Gated DeltaNet Hadamard Equivariance (`qwen3_5/rotations.py:43-78`):** Using exact rational orthogonal Sylvester Hadamard rotations $R_k = H_4/2$ and signed $R_v = D_v H_4/2$ ($R_k^\top R_k = R_v^\top R_v = I_4$), 3-step exact rational GDN recurrence satisfies $S_t^{\mathrm{rot}} \mathbin{⩩} R_k S_t R_v^\top$ and unrotated readout $o_t^{\mathrm{rot}} \mathbin{⩩} o_t$ with **`0` rational residual**.
2. **Exact Decay-Amplification Separation & `siliquant#24` Lattice Dominance:** For scalar head decay $\alpha \in (0, 1)$:
   - Deterministic RTN worst-case error energy grows as $(1-\alpha)^{-2}$, whereas unbiased stochastic rounding (`LoReS`) MSE grows as $(1-\alpha^2)^{-1}$ — an exact **$\frac{1+\alpha}{1-\alpha}$ quadratic separation** (`3x, 15x, 31x, 127x` at $\alpha = 1/2, 7/8, 15/16, 63/64$), explaining algebraically why slow-decay heads require stochastic rounding and higher precision.
   - Replacing `LoReS`'s scalar $\mathbb{Z}$ block quantizer with `siliquant#24`'s **`E_8` Hadamard lattice** (leveraging `LoReS`'s existing Hadamard rotations for free!) cuts steady-state stochastic-rounding MSE by exact ratio **`929/1080`** (`-13.98%` / **`+0.654 dB`**) at every decay $\alpha$, while **`\Lambda_{24}`** cuts worst-case adversarial error energy by exact factor **`2/6 = 1/3`** (`3x` tighter, vs `1/2` for $E_8^3$)!

### Pillar 3 — `neuro-lds` (ICML 2026) $\longleftrightarrow$ Exact Rational RKHS Schur Discrepancy (`SF-01 #26`) & Fibonacci Lattices (`incentre-lattices#106`)
1. **Zero-Float Krein-Inertia Refutation of `CAMAIL-B4` (`neuro-lds/scripts/utils.py:189`):** Because $\int_0^1\int_0^1 \frac{1}{2}(|x-\frac{1}{2}|+|y-\frac{1}{2}|-|x-y|)\,dx\,dy = \frac{1}{12}$, the linear-weight kernel $K_\gamma(x,y) = \prod(1 + \gamma_j k(x_j, y_j))$ requires $c_0 = \prod(1 + \gamma_j/12)$, NOT `utils.py:189`'s `prod(1 + (g*g)/12)`:
   - At `gamma = 1/2` on 8 uniform midpoints: buggy $D^2 = \mathbf{-31/1536 < 0}$ (clamped to `1e-12` by `sqrt_safe` with **zero gradient**!), buggy augmented RKHS Gram matrix has **negative Krein eigenvalue `⦺(G_buggy) = (8, 0, 1)`** and negative Schur optimal quadrature **`G_buggy ⧄ P = -64483/3194880 < 0`** (vs. fixed `D^2 = +1/1536`, `⦺(G_fixed) = (9, 0, 0)`, `G_fixed ⧄ P = +2077/3194880 > 0`).
   - At `gamma = 1`: `g^2 == g` hides the bug (`1/768 == 1/768`); at `gamma = 2`: buggy `c0` adds an irredeemable spurious floor of **`+1/6`** (`65/384` vs `1/384`).
2. **Exact Pure-$\mathbb{Q}$ 2D $D_\infty^*$ + $D_2^{*2}$ + RKHS Schur-Optimal Quadrature (`G_K ⧄ P`, `SF-01 #26`):**

| 2D Point Set | $N$ | Exact $D_\infty^*$ | Exact Equal-Weight $D_2^{*2}$ | Exact Schur-Optimal `G_K ⧄ P` | `⦺(G_K)` |
|---|---:|---:|---:|---:|---|
| `Fib_8_origin` | 8 | `15/64` (`0.2344`) | `1399/147456` (`0.009488`) | **`43880983/22184460288` (`0.001978`)** | `(9, 0, 0)` |
| `Fib_8_midpoint` | 8 | **`41/256` (`0.1602`)** | **`3695/1179648` (`0.003132`)** | `294224466533/124050198233088` (`0.002372`) | `(9, 0, 0)` |
| `Halton_8` | 8 | `2/9` (`0.2222`) | `1301/331776` (`0.003921`) | `6831718651/2781527703552` (`0.002456`) | `(9, 0, 0)` |
| `Fib_13_origin` | 13 | `28/169` (`0.1657`) | `1093/257049` (`0.004252`) | **`0.000866`** (`4.91x` drop) | `(14, 0, 0)` |
| `Fib_13_midpoint` | 13 | **`79/676` (`0.1169`)** | **`12215/8225568` (`0.001485`)** | `0.000992` | `(14, 0, 0)` |
| `Halton_13` | 13 | `119/468` (`0.2543`) | `361931/63078912` (`0.005738`) | `0.001122` (`5.11x` drop) | `(14, 0, 0)` |

Notice the crisp structural reversal at $N = 8$: unshifted `Fib_8_origin` loses to `Halton_8` under equal-weight QMC (`0.00949 > 0.00392`), yet after exact RKHS Schur-optimal reweighting `G_K ⧄ P` (`4.80x` reduction!) **`Fib_8_origin` (`0.001978`) strictly beats `Halton_8` (`0.002456`)**!

### Pillar 4 — `QRR`, `discretax`, & `LoopedActor` Cross-Links (Bridging to `AUDIT-060`)
1. **`QRR` (`models/gauge_layers.py:26-29, 105-124`):** Exact $\mathbb{Q}[i]$ proof of the dressed-attention identity (`1273/260 == 1273/260`) and exact 6-phase Pythagorean $U(1) \cap \mathbb{Q}[i]$ orbit equalizer (`|<a, e^{i\phi} b>|^2 == 49/1` identically across `{1, i, -1, -i, (3+4i)/5, (5-12i)/13}`).
2. **`discretax` (`src/discretax/sequence_mixers/deltanet.py:56-60`):** Exact pure-$\mathbb{Q}$ 4×4 verification that the forward-substitution WY recurrence computes $T = (I + \operatorname{tril}(K_\beta K^\top, -1))^{-1}$ identically (`(I+L)T = T(I+L) = I_4`).
3. **`LoopedActor` (`models/fprm.py:59-64`):** Exact coupled-residual contraction `q = 3/4 + (1/4)(1/2) = 7/8 < 1` (vs. unscaled `3/2 > 1`) with 4-step a-posteriori factor `2401/512`, directly bridging to Arm R5-5 (`AUDIT-060`).

---

## 4. R1–R5 Verification Receipts & Falsification Criteria

- **Repro Commands (`studies/camail-ssm-rkhs-schur/`):**
  ```bash
  for f in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
    python3 $f camail_math_ai_symbiosis.py --json | sha256sum
    python3 $f test_camail_math_ai_r5.py
  done
  # With Foundation-0/aletheia on PYTHONPATH:
  python3 -B -W error -m aletheia audit-check . \
    --scripts camail_math_ai_symbiosis.py test_camail_math_ai_r5.py --json
  python3 -B -W error -m aletheia mutate camail_math_ai_symbiosis.py \
    --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_camail_math_ai_r5.py" --json
  ```
- **Falsification Criteria:** Fails if any of the 7 pinned SHAs or verbatim upstream bug diagnoses (`CAMAIL-B1..B5`) is inaccurate; if any exact $\mathbb{Q}/\mathbb{Q}[i]$ identity in Pillars 1–4 fails independent SymPy verification (incl. `CAMAIL-B1` `116` vs `68`, `CAMAIL-B4` `-31/1536` & `(8,0,1)` vs `(9,0,0)`, DC SPA `220/19`, `CS-11` `R_H4` `3/1` vs `219/61`, GDN Hadamard equivariance, 2D `D_inf*` / `G_K ⧄ P`, `QRR` `1273/260`, `discretax` WY inverse); if any float appears in JSON; or if any mutant survives (`49/49`) or R4/`audit-check` fails.

# Wave 2 Round 4D — Arm R4D-2 (`AUDIT-053`): Exact Zero-Float Polytope/Farkas & Craik–Criminale / Leray Schur Audit of Alpöge–Buckmaster–Coiculescu (`tristanbuckmaster-cc.pdf`)

**Audit ID:** `AUDIT-053` | **Oracle Class:** `exact+anchor` | **Honest Novelty Grade:** `N1` (clean-room zero-float rational polytope/Farkas sensitivity audit, constructive dual obstruction proofs, exact saddle-point Leray Schur complement `SF-01 #23` & Section 2–6 identity verification, and Wave-1 Sabra structural contrast; zero fabricated `N2` claim)  
**Ethical Posture:** **STRICTLY READ-ONLY** on the local PDF preprint (`0` external writes, `0` external PRs/issues/comments, `0` false alarms on the manuscript).

---

## 1. Pinned Read-Only Source & Strict Law-4 `N0` Prior-Art Quarantine

- **Preprint:** *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, **Levent Alpöge, Tristan Buckmaster, and Matei P. Coiculescu** (`tristanbuckmaster-cc.pdf`, `55` pages, `SHA-256: 414f5af635c78e807d674a1bab49a440c3cf1173bc3bc7cd12f8686f80a077a3`, dated `2026-11-20`).
- **Scope Inspected Full-Text (`pdftotext -layout`):** Sections 1–8 and Appendices A–D, with exact equation/page verification across §1.1, §1.5 (`(1.13)–(1.15)`), §2 (`(2.1)–(2.24)`), §3 (`(3.1)–(3.8)`), §4 (`(4.1)–(4.12)`), §5 (`(5.1)–(5.59)`), §6 (`(6.1)–(6.8)`), §7 (`(7.1)–(7.12)`), §8 (`(8.1)–(8.2)`), and Appendices A–D.
- **Strict Law-4 `N0` Prior-Art Quarantine:** The 3D incompressible Euler equations (Euler 1755), Beale–Kato–Majda criterion (1984), Craik–Criminale inviscid wave solutions (1986), Arnold's geodesic Jacobi equation (1966) & Brenier's action-minimization criterion (1989/1999), Leray Helmholtz projection, Farkas's lemma (1902), and the entire multi-scale localized Craik–Criminale blow-up construction (`Theorem 1.1`, `Theorem 7.1`, `Lemma 1.3`, `Lemmas 2.1–2.8`, `Theorem 5.6`, `Appendices A–D`) belong to their respective authors (`N0`).

---

## 2. Part 1 — Exact 1-Step Rational Exponent Polytope & Constructive Farkas Dual Obstructions (`SF-05`)

Translating every Section 3/5/6 single-step exponent inequality for seed amplitude $|a| \sim \lambda^{-\alpha_a}$, bump width $h = \lambda^{-\beta_h}$ ($\alpha_v = \alpha_a + \beta_h$, fast derivative $\gamma_\partial = 1 + \beta_h$), per-level expansion decay $\lambda^{-\delta_{\mathrm{lvl}}}$, and parent headroom $C_{\mathrm{step}} \le \lambda^{\eta_D}$ into a single authoritative pure-`Fraction` table `STEP_POLYTOPE_CONSTRAINTS` shared directly by both `evaluate_step_polytope_exact` and `certify_farkas_obstructions_exact`:

- **Canonical Paper Point `(alpha_a, beta_h, delta_lvl, eta_d) = (3/4, 1/2, 2/3, 1/12)` (`alpha_v = 5/4`, `gamma_d = 3/2`):**
  **`10/10` inequalities SATISFIED — ZERO algebraic errors or gaps!**

| Constraint | Paper Site | Exact Rational Formula | Exact Slack at `(3/4, 1/2, 2/3, 1/12)` | Status |
|---|---|---|---|---|
| `E1` | §6.1, `(7.3)` | $1 - \alpha_a > 0$ (positive wave strength $\sigma_{\mathrm{lead}} = \lambda^{1-\alpha_a}$) | `1/4` | Strict PASS |
| `E2` | Lem. 5.9 `(5.49)` | $\alpha_a + \beta_h - 1 - \eta_D > 0$ (leading pressure Hessian $D_x^2 P^\backslash \le \mathrm{Id}$) | `1/6` | Strict PASS |
| **`E3`** | Thm. 5.6 (`(C_i\cdot\kappa)\partial_s Y_j`) | $\alpha_a - \delta_{\mathrm{lvl}} - \eta_D \ge 0$ (`beta_h` cancels identically!) | **`0`** | **TIGHT ACTIVE FACET** |
| `E4` | Thm. 5.6 (linear curl) | $1 - \delta_{\mathrm{lvl}} - \eta_D \ge 0$ | `1/4` | PASS |
| `E5` | Thm. 5.6 (label advection) | $\alpha_v - \delta_{\mathrm{lvl}} - \eta_D \ge 0$ | `1/2` | PASS |
| **`E6`** | Thm. 5.6 `(5.40)` | $\alpha_v - \delta_{\mathrm{lvl}} - \eta_D - 1/2 \ge 0$ (`\lambda^{1/2}\|B_p\|` induction shift) | **`0`** | **TIGHT ACTIVE FACET** |
| `E7` | Thm. 5.6 (mean phase adv.) | $\alpha_a - 1/2 - \eta_D > 0$ | `1/6` | Strict PASS |
| `E8` | Lem. 5.9 `(5.52)` | $\alpha_v + \delta_{\mathrm{lvl}} - \gamma_\partial - \eta_D = \alpha_a + \delta_{\mathrm{lvl}} - 1 - \eta_D > 0$ | `1/3` | Strict PASS |
| **`E9`** | Lem. 5.9 `(5.50)` | $\alpha_a + \delta_{\mathrm{lvl}} - 1 - \eta_D - 1/3 \ge 0$ ($|E_c| \le \lambda^{-1/3}$) | **`0`** | **TIGHT ACTIVE FACET** |
| `E10` | Lem. 5.10 `(5.53)` | $\alpha_a - \eta_D > 0$ (scaled flow-map gradient) | `2/3` | Strict PASS |

### Three Constructive Farkas Dual Certificates (Why the Paper's Architecture Is Forced)
1. **`Farkas-1` (Sine-Profile Impossibility, $\beta_h = 0$):** With dual weights `y = (E1: 1, E2: 1)`, summing `E1` ($1 - \alpha_a > 0$) and `E2` at $\beta_h = 0$ ($\alpha_a - 1 - \eta_D > 0$) eliminates $\alpha_a$ identically to $-\eta_D > 0$ — an exact contradiction for every $\eta_D > 0$. This proves algebraically why classical $F(s) = \sin(2\pi s)$ fails and Lemma 3.1's thin-bump profile $F_h$ ($\beta_h > 0$) is mandatory.
2. **`Farkas-2` (Strong-Decay Ceilings $\alpha_a > 1/2 + \eta_D$, $\eta_D < 1/2$, and Exact Sharp Ceiling $\eta_D < 1/3$):** Because $\beta_h$ cancels identically in `E3`, `E8`, and `E9`:
   - Summing `y = (E3: 1, E8: 1)` eliminates $\delta_{\mathrm{lvl}}$ to `[2, 0, 0, -2, -1]` $\implies 2\alpha_a - 2\eta_D - 1 > 0 \iff \mathbf{\alpha_a > 1/2 + \eta_D}$.
   - Adding `2 * E1` gives `[0, 0, 0, -2, 1]` $\implies 1 - 2\eta_D > 0 \iff \mathbf{\eta_D < 1/2}$.
   - Replacing `E8` with `E9` (`|E_c| \le \lambda^{-1/3}`, Lem. 5.9 `(5.50)`) gives `y = (E3: 1, E9: 1, E1: 2)` $\implies$ `[0, 0, 0, -2, 2/3]` $\implies \frac{2}{3} - 2\eta_D > 0 \iff \mathbf{\eta_D < 1/3}$ — which is the **exact sharp ceiling** of `E1..E10` (`eta_d = 1/3` rejected; `(23/24, 1/2, 2/3, 7/24)` with `eta_d = 7/24 < 1/3` satisfies all `10/10` constraints!).
3. **`Farkas-3` (Transverse Pressure-Gradient Trick `(5.16)` Strictly Required at $\alpha_a = 3/4$):** Without `(5.16)`, two Eulerian derivatives on $p_2$ cost $2\gamma_\partial = 3$ against $1 + \alpha_v + \delta_{\mathrm{lvl}} = 35/12$, leaving exact slack **`-1/12 < 0`** (matching Lem. 5.9 p. 37 *"leaving $\lambda^{1/12}$"* verbatim!), whereas `(5.16)` raises the slack to **`+1/3 > 0`**. Moreover, summing `E6` with naive `p_2` decay yields $2\alpha_a - \eta_D > 3/2 \implies \alpha_a > 3/4 + \eta_D/2$, proving `(5.16)` is strictly required for EVERY $(\beta_h, \delta_{\mathrm{lvl}})$ whenever $\alpha_a = 3/4$ (whereas `(7/8, 1/2, 3/4, 1/12)` satisfies `E1..E10` with naive slack `+1/8 > 0`).

---

## 3. Part 2 — Exact Multi-Scale Induction & Appendix C Audit (`§1.5`, `§7`, `§8`, Appendix C)

Across all tested admissible order transitions `(b, q_j, q_{j+1}, q_{j+2}) ∈ {(1,1,1,1), (1,1,2,3), (3,4,5,5)}`, **all `13/13` explicit exponent inequalities (`C1..C13`) hold with exact nonnegative rational slack — ZERO gaps or edge-case breaks** (including $j = 1$ in Appendix C Lemma 1.3 and $j = 2$ in §7.2(2)):

- `C1` ($P + 1 \le 7 K(q_{j+1})$, p. 43): slack `K_{j+1} - 1 >= 639`.
- `C2` (`(7.8)` $10b/K_j \le 1/32$): slack `>= 1/64`.
- `C3` (p. 45 $10b(q_j + 2) \le K_j / 16$): exact margin **`10 b q_j >= 10`**.
- `C4`–`C5` (p. 44 $\lambda_{j-2}^9 \le \mu^{1/32}, \lambda_{j-2}^{18} \le \mu^{1/16}$, requiring $K_{j-1} \ge 288$): cleared by $K(1) = 640b \ge 640$ with slacks `11/640` and `11/320`.
- `C6` (`(7.9)` $\varepsilon_j / \varepsilon_{j-1} = K_{j+2}^{-2} \le 1/32$): $640^{-2} = 1/409600$ (`12,800x` margin; slack `12799/409600`).
- `C7`–`C9` (`(7.12)` Bernstein & Fourier tail): $K_{j+1} - 15 \ge 625 > 0$; $2(P+1) - (3P/2 + 1/4 + (P+2)/32) = \frac{15}{32}P + \frac{27}{16} > 0$.
- `C10`–`C11` (`(7.11)` expansion remainder): $\frac{2}{3}P - 4K_{j+1} \equiv \mathbf{0}$ identically (`P = 6 K_{j+1}` exact!), headroom $K_{j+1}/2 - 33/16 \ge 5087/16 > 0$.
- `C12` (p. 45 finite-time geometric sum): $2 - \sum_{k=0}^\infty 4^{-k} = 2 - 4/3 = \mathbf{2/3 > 0}$ ($T_\infty < S_j$).
- `C13` (**Appendix C Lemma 1.3**): Pure arbitrary-precision integer simulation of the logarithmic tower (`log_B(s) = 4 K(s+1)^3`, saturating `(1.13)` and $N = B(1)$ tightly!) verifies `q_sequence = [1, 1, 2, 3, 4, 5, 6, 7, 8]` ($q_j \uparrow \infty$) and $L_{j+1} \le (\log \lambda_{j-1})^2$ (`(1.15)`) at **every step $j = 1..8$** with zero floating-point logarithms.

---

## 4. Part 3 — Exact Zero-Float Section 2–6 Craik–Criminale & Leray Schur Algebra (`SF-01 #23`) + Wave-1 Sabra Contrast (`AUDIT-010`)

Every core algebraic identity in Sections 2–6 was verified **over exact `Fraction` with `0/1` residual**:
1. **Leray Projection = Exact $4 \times 4$ Saddle-Point Schur Complement (`SF-01 #23`, Thm. 4.2, Lem. A.2):**
   $$\begin{pmatrix} K & k \\ k^\top & 0 \end{pmatrix}\begin{pmatrix} v \\ \phi \end{pmatrix} = \begin{pmatrix} f \\ 0 \end{pmatrix} \implies s_K(k) = -k^\top K^{-1} k < 0, \quad v = \left(K^{-1} - \frac{K^{-1} k k^\top K^{-1}}{k^\top K^{-1} k}\right) f.$$
   Verified exact `0/1` saddle-point residual for BOTH Euclidean $K = I_3$ ($s = -14$, $\phi = 25/7$, $P_k^\perp$ idempotent with $\operatorname{tr} = 2$, Craik–Criminale Householder reflection $R_k = I_3 - 2 P_k$ involutory with $\det = -1$) AND the anisotropic stationary-shear metric $K_0(t) = (I + t B_\rho)^\top(I + t B_\rho)$ ($s = -1286/25$, $\phi = 2196/643$), plus **Gate-2 $SO(3, \mathbb{Q})$ Cayley rotation equivariance** and **§5.4 dual pseudoinverse equivalence** $A_\perp A_\perp^\dagger \equiv P_\kappa^\perp$ (`(5.18)`).
2. **All Section 2–6 Identities (`0/1` Exact Rational Residual):**
   - **Lem. 2.1 `(2.1)`:** Exact transversality $(k \cdot a)' \equiv 0$ and zero self-advection.
   - **Lem. 2.2 `(2.2)`:** Exact moving-frame ODE and Kelvin vorticity-strength law $(k \times a)'/\sigma = B_{13} E_1 + \eta E_2 + B_{33} E_3$ ($\implies (\log\sigma)' = B_{33}$ via $\operatorname{tr} B = 0$).
   - **Lem. 2.4 (p. 14–15):** All `5/5` general trace-free background moving-frame equations (`z1'`, `z2'`, `z3'`, `alpha1'`, `alpha2'` via `F_1, F_2, N_{11}..N_{22}`) match with exact `0/1` residual.
   - **Lem. 2.5 (p. 16 `(2.12)–(2.13)`) & Lem. 2.7 (p. 20 `(2.22)`):** Parametrizing $\phi$ via exact rational Pythagorean triples $(a,b)$ verifies the delicate 6-term Riccati-to-$e'$ ODE $e' = \cos\phi(-2e - e^2 + \frac{1}{2}\varepsilon\sin\phi\cos\phi)$ (`0/1` residual + exact barrier signs at $e=0$ and $e=\varepsilon/8$) AND the $O(\varepsilon\tan\phi)$ large-term cancellation for both $\nu_+/\nu$ and $\eta_+/\nu$ (`0/1` residual).
   - **§3.1 `(3.6)` & §4.2 `(4.7)` & §6.1 `(6.2)`:** Exact vector triple-product curl recovery $k \times (-(k \times V)/|k|^2) \equiv V$; exact Arnold–Brenier Lagrangian–Eulerian coercivity identity $K z_t \cdot z_t + \Omega z_t \cdot z + \partial_t(\xi \cdot M \xi) \equiv |\xi_t|^2 - H^\# \xi \cdot \xi$ (verified on general non-symmetric $H^\#$); exact nilpotency $B_\rho^2 = 0$ and $(I + t B_\rho)(I - t B_\rho) = I$.
3. **Honest Structural Comparison vs. Wave-1 Sabra Helicity Shell Cascades (`AUDIT-010`, `SF-05`):**
   - **Shared (`SF-05`):** Both organize finite-time blow-up via a cascade of geometrically separated frequency shells governed by exact rational polytope/Farkas ratio constraints.
   - **Sharp Divergence (Law-3 Honesty):** (a) Sabra uses fixed dyadic shell ratio `2` (producing log-periodic / period-2 multiplicative-Farkas ripples in `AUDIT-010`), whereas Alpöge–Buckmaster–Coiculescu uses a **super-exponentially accelerating tower** $\lambda_j = \lambda_{j-1}^{K_j}$ ($K_j = 320b(q_j+1) \uparrow \infty$) to absorb $D^b$ losses and achieve $C^\infty$ convergence away from $0$; (b) each single Craik–Criminale wave has **identically zero pointwise helicity** ($a \cdot (k \times a) \equiv 0$, $k \cdot (k \times a) \equiv 0$, contrasting with Sabra's alternating chiral helicity $(-1)^n k_n |u_n|^2$), while **inter-scale cross-projection** $\kappa_j \cdot (\kappa_{j-1} \times a_{j-1}) = \lambda_j \zeta_3 \sigma_{j-1} > 0$ (`(8.1)`) prevents curl cancellation at the origin (`Prop. 8.2`).

---

## 5. Verification Summary & Falsification Criteria

- **Artifacts (`studies/euler-3d-craik-criminale-polytope/`):** `buckmaster_euler_cc_audit.py`, `test_buckmaster_euler_cc_r5.py`, `buckmaster_euler_cc_results.json` (`canonical_sha256: 4c23ad27c94ae03aad41aa257f174ff0b0aca7a795821f15ce159cc79cdeaf36`), `BUCKMASTER_EULER_CC_AUDIT_REPORT.md`.
- **4-Mode Isolated R4 Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`):** **`4/4` bit-identical** on `buckmaster_euler_cc_audit.py --json` (`SHA-256: ad064b1ee13623dc765e1bdaf13231dfff9027d76188e2d1490115f57185262e`, exact match to `buckmaster_euler_cc_results.json`), ZERO floats in JSON; `python3 <flags> test_buckmaster_euler_cc_r5.py` passes directly across all 4 isolated `-I` modes (`5/5` tests OK, including certificate `canonical_sha256` integrity and single-source Farkas row verification).
- **External `Foundation-0/aletheia v2.0.0` (`@ 7227bcc5`) Receipts:** `audit-check --strict-ancestors --safety-scan` **`PASS`** (`4` files, `0` CRLF, `0` `__pycache__`, `0` personal-path leaks, `0` bare `assert`s, `0` unseeded RNG, `0` JSON errors); `mutate --max-mutants 0 --add-cwd` **`17/17` (`100.0%`) KILLED, `0` SURVIVORS** (pinned receipt in [`../ROUND4_MUTATION_RECEIPTS.json`](../ROUND4_MUTATION_RECEIPTS.json)).
- **Falsification Criteria:** Fails if any equation/page citation does not match `tristanbuckmaster-cc.pdf` (`SHA-256: 414f5af635c78e807d674a1bab49a440c3cf1173bc3bc7cd12f8686f80a077a3`), if any exact rational Farkas dual / multi-scale slack / Appendix C integer tower / Leray Schur / Section 2–6 identity or `canonical_sha256` integrity check deviates from exact `0/1` residual, if any float enters JSON, or if any R4/`audit-check`/R5 mutant gate fails.

# Track S21e: Exact-Q Finite-Orthogonal Isotypic Projectors and Schur Obstructions Across Three Symmetry-Breaking Frontiers

- **Track ID:** `TRACK-S21E-ESCHER-METAMORPHOSIS-SYMMETRY-BRIDGE`
- **Certificate Schema:** `aletheia.escher_metamorphosis_symmetry_bridge.certificate.v1`
- **Novelty Tier:** `N1_UNIFIED_CROSS_FRONTIER_EXACT_SYNTHESIS`
- **Law-5 Functor:** `exact_Q_finite_orthogonal_isotypic_projector_and_schur_obstruction`
- **Implementation Discipline:** Pure Python 3 standard library (`int` + `fractions.Fraction`), zero IEEE-754 floating-point values, zero external dependencies, zero bare `assert` statements, zero RNG, fail-closed Zone-B JSON and path validation.

---

## 1. Executive Summary

Track S21e unifies three distinct mathematical-physics and lattice-coding domains under one exact rational operator framework: finite orthogonal group verification ($G \subset O(n, \mathbb{Q})$), character-derived isotypic orthogonal projectors ($P_\rho = \frac{d_\rho}{|G|} \sum_{g \in G} \chi_\rho(g) g$ with $P_\rho^2 = P_\rho = P_\rho^\top$, $\sum_\rho P_\rho = I_n$, $P_\rho P_\sigma = 0$ for $\rho \neq \sigma$), exact Schur equivariance and cross-irrep coupling Frobenius norms ($\|P_\rho A P_\sigma\|_F^2$), and exact rational Sylvester inertia $(n_+, n_-, n_0)$ via Bunch-Kaufman congruence over $\mathbb{Q}$.

Every theorem, group closure check, projector partition, Hessian spectrum, Schur-complement homogenized elasticity tensor, and Voronoi shift invariant is recomputed from scratch in `metamorphosis_symmetry_oracle.py` and bound cryptographically to `metamorphosis_symmetry_certificate.json` (`payload_sha256 = eab0b4b167ec4f0a1cc14cfee2b250380031c82eaee0cddc49c2e8dfcdce457b`, `certificate_sha256 = 72039ed901655749312c83cf80d51155ab104099be285e00accf189096bb81fe`).

---

## 2. Frontier 1 — $E_8$ Basis Metamorphosis ($W(E_8)$ Intertwiner, Steiner Bleed, and Antipodal Breaking)

| Invariant / Witness | Exact $\mathbb{Q}$ / $\mathbb{Z}$ Value | Interpretation |
|---|---|---|
| $E_8$ root count | `240` | Verified in both standard (`BH2`) and Hadamard (`WHT8`) frames |
| Basis intertwiner $A = \frac{1}{2}(H_4 \otimes I_2)$ | $A^\top A = I_8$, $U_{\mathrm{WHT8}} = U_{\mathrm{BH2}} A$, $A \in W(E_8)$ | Exact orthogonal Weyl-group intertwiner preserving $E_8$ |
| Root support weight distribution (`std` -> `had`) | `{2: 112, 8: 128}` -> `{1: 16, 4: 224}` | Axis-aligned 1-sparse roots jump from `0` to `16` |
| 1-sparse axis $d^2_{\max}$ / gain$^2$ (`std` -> `had`) | `1` -> `1/2` / `1` -> `2` | Exact $2\times$ squared-distance sharpening on axis spikes |
| Steiner $3$-$(8, 4, 1)$ quad count in $E_8^{\mathrm{Had}}$ | `14` | Exact Hamming-code parity quads on weight-4 roots |
| Steiner 3-active probe bleed | `min_d2 = 9801/20000`, `unique_nearest = 1`, `forced_coord4_nonzero = true` | Symmetry forces exact non-zero bleed onto the 4th Steiner coordinate |
| Antipodal symmetry $\{-I_8\}$ | `order = 2`, `triv_projector_rank = 0` | Unbroken $\{-I_8\}$ forces mean Voronoi bias $\mu = 0$ |
| Weyl-chamber antipodal breaking (`siliquant_default` & `lexicographic`) | `120` pos roots, `ties = 0`, $\|\mu_\infty\|^2 = 31/45$, $\max(\mu_\infty \cdot r) = 29/30 < 1$ | Strictly interior Voronoi shift; `52/240` shifted roots inside open $\sqrt{2}$-ball, $\min d^2 = 34/45$ |

Chamber-universal invariants agree identically between the two distinct Weyl chambers:
- **`siliquant_default`:** $\rho = (2, 10, 1, -17, 11, 4, -5, 8)$, $\mu_\infty = (1/15, 1/3, 1/30, -17/30, 11/30, 2/15, -1/6, 4/15)$.
- **`lexicographic`:** $\rho = (23, 6, 5, 4, 3, 2, 1, 0)$, $\mu_\infty = (23/30, 1/5, 1/6, 2/15, 1/10, 1/15, 1/30, 0)$.

---

## 3. Frontier 2 — Exact Harmonic Coulomb Hessian Walls ($T_d \to C_{3v}$ and $D_{4h} \to D_{2h}$)

Verified finite orthogonal point groups on $\mathbb{Q}^3$ have exact orders $|T_d| = 24$, $|C_{3v}| = 6$, $|D_{4h}| = 16$, $|D_{2h}| = 8$, with isotypic rank partitions:
- $T_d$: trivial projector rank `0` (3D irreducible representation $T_2$ forbids any nonzero symmetric traceless $T_d$-equivariant Hessian).
- $C_{3v}$: $T_2 \downarrow C_{3v} = A_1(1) \oplus E(2)$.
- $D_{4h}$: $A_{2u}(1) \oplus E_u(2)$.
- $D_{2h}$: $[1, 1, 1]$ (full three-axis splitting).

### 3.1 $n = 4$ Pyramid Family ($T_d \to C_{3v}$)

| Configuration | Parameters | Exact Scaled Hessian $H$ | Eigenvalues | Sylvester Inertia $(n_+, n_-, n_0)$ | Morse Index | Schur / Equivariance |
|---|---|---|---|---|---|---|
| Unbroken $T_d$ wall | $t = 1, q_a = 1$ | $0_{3 \times 3}$ | `0, 0, 0` | `[0, 0, 3]` | `0` (degenerate) | $T_d$-equivariant, $\nabla V = 0$, $\operatorname{tr}(H) = 0$ |
| Compressed $C_{3v}$ | $t = 1/2, q_a = 1/4$ | off-diag `3` | $\lambda_{A_1} = 6$, $\lambda_E = -3$ | `[1, 2, 0]` | `2` | $C_{3v}$-equivariant, $P_{A_1} H P_E = 0$ (`frob_sq = 0`) |
| Extended $C_{3v}$ | $t = 2, q_a = 4$ | off-diag `-3/2` | $\lambda_{A_1} = -3$, $\lambda_E = 3/2$ | `[2, 1, 0]` | `1` | $C_{3v}$-equivariant, $P_{A_1} H P_E = 0$ (`frob_sq = 0`) |

Crossing the unbroken $T_d$ wall flips $(-1)^{\mathrm{ind}(H)}$ between $+1$ (index `2`) and $-1$ (index `1`), producing an exact `2`-unit Poincare-Hopf sign jump (`pyramid_poincare_hopf_sign_jump = 2`).

### 3.2 $D_{4h} \to D_{2h}$ Square Pitchfork & $C_1$ Fold Invariance

| Configuration | Exact Diagonal $H$ | Inertia $(n_+, n_-, n_0)$ | Symmetry Status |
|---|---|---|---|
| Unbroken $D_{4h}$ ($q_x = 1$) | `[2, 2, -4]` | `[2, 1, 0]` (index `1`) | $D_{4h}$-equivariant |
| Degenerate $B_{2u}$ pitchfork wall ($q_x = 2$) | `[6, 0, -6]` | `[1, 1, 1]` | $D_{4h}$ broken, zero mode along $y$ |
| Broken $D_{2h}$ post-pitchfork ($q_x = 3$) | `[10, -2, -8]` | `[1, 2, 0]` (index `2`) | $D_{2h}$-split |

In the generic $C_1$ $n = 4$ fold transition (`n4_c1_fold_poincare_hopf`), total equilibria drop from `11` (`m2 = 7, m1 = 4`) to `9` (`m2 = 6, m1 = 3`) while preserving the exact Euler-index difference $m_2 - m_1 = 3$.

---

## 4. Frontier 3 — Voigt Homogenization ($D_{2h}$ vs $C_3$), $Z_2$ Truss Singularity, and 6-Spoke Prestress

### 4.1 Periodic $F_3$ Truss Homogenization on 6D Voigt Space ($\mathbb{Q}^6 = A_g(3) \oplus B_{1g} \oplus B_{2g} \oplus B_{3g}$)

The faithful action of $D_{2h}$ on symmetric 3D strain tensors has order `4` ($D_2$) and partitions $\mathbb{Q}^6$ into 3D axial $A_g$ and three 1D shear irreps $B_{1g}, B_{2g}, B_{3g}$. Exact rational Schur-complement relaxation (`relaxation_zero_residual = true` across all 4 modes) certifies:

| Tie Mode | Bars / Ties | $C_{11}$ | $C_{12}$ | $C_{44}$ | $C_{14}$ (axial-shear) | Shear / Tie | Inertia | $D_{2h}$ Schur Coupling $\|P_{A_g} C P_{\text{shear}}\|_F^2$ | $C_3$ Equiv. |
|---|---|---|---|---|---|---|---|---|---|
| `none` | `15 / 0` | `2/9` | `1/18` | `0` | `0` | `0` | `[3, 0, 3]` | `0` (equivariant) | `true` |
| `one_per_plane` | `18 / 3` | `97/253` | `79/506` | `34/253` | `-26/253` | `34/759` | `[6, 0, 0]` | `4083/64009` (broken; defect `180/529`) | `true` |
| `half_2_opp` | `21 / 6` | `31/55` | `29/110` | `1/4` | `0` | `1/24` | `[6, 0, 0]` | `0` (equivariant) | `true` |
| `full_4` | `27 / 12` | `1` | `1/2` | `1/2` | `0` | `1/24` | `[6, 0, 0]` | `0` (equivariant) | `true` |

Breaking $D_{2h} \to C_3$ via chiral single-diagonal bracing (`one_per_plane`) opens parasitic axial-shear coupling $C_{14} = -26/253$ and lowers shear efficiency to `34/759` per tie; restoring $D_{2h}$ (`half_2_opp`, `6` ties) annihilates $C_{14} = 0$ identically and achieves the optimal `1/24` shear stiffness per tie (matching `full_4` at half the tie budget).

### 4.2 Exact $Z_2$ 2-Bar Truss ($\mathbb{Q}^2 = A_1 \oplus B_1$) and 6-Spoke Unilateral Prestress

- **`flat_singular_9_10_11_10`:** $x^* = -1/10$, $H = \operatorname{diag}(200/99, 0)$, inertia `[1, 0, 1]`, $Z_2$-equivariant (`cross_coupling_frob_sq = 0`), stabilized by exact positive quartic term `257500/970299` $y^4$.
- **`online_saddle_9_10_11_10`:** $x^* = -109/100$, $H = \operatorname{diag}(200/99, -2000/209)$, inertia `[1, 1, 0]`, $Z_2$-equivariant (`cross_coupling_frob_sq = 0`).
- **`broken_z2_corner_7_10_3_2`:** $x^* = -11/25$, $y^* = 21/50$, exact Pythagorean equilibrium verified, $H = \begin{pmatrix} 6688/4375 & 2216/4375 \\ 2216/4375 & 7436/13125 \end{pmatrix}$, $\det H = 64/105$, $\operatorname{tr} H = 44/21$, inertia `[2, 0, 0]`, $Z_2$ broken (`cross_coupling_frob_sq = 4910656/19140625`).
- **Anchored 6-spoke unilateral cable prestress:** Tension weights `(1, 10, 11)` satisfy zero force residual with strictly positive-definite interior stress matrix inertia `[7, 0, 0]` (full `[12, 0, 1]`), whereas inverted compression weights `(1, -10, -9)` yield strictly negative-definite interior inertia `[0, 7, 0]` (full `[0, 12, 1]`).

---

## 5. Law-2b Honest Obstruction & Non-Claims

- **Protective Symmetry vs. Degeneracy Trap:** Across all three frontiers, exact equivariance acts as a double-edged operator. Enforcing $G$-equivariance provably forbids parasitic couplings and invariant drift ($C_{14} = 0$ under $D_{2h}$, $\mu = 0$ under $\{-I_8\}$, $H_{xy} = 0$ under $Z_2$). Conversely, excessive symmetry forces complete degeneracy walls or structural bleed ($T_d$ forces $H(0) = 0_{3\times 3}$, $Z_2$ flat truss forces $H_{yy} = 0$, $E_8^{\mathrm{Had}}$ forces Steiner `9801/20000` 4th-coordinate bleed), requiring controlled symmetry breaking or graded augmentation to escape.
- **Explicit Scope Limits (Non-Claims):**
  - This track is a finite-dimensional exact-$\mathbb{Q}$ cross-frontier synthesis (`N1`); it does not claim new infinite-family classification theorems for general Lie groups, nonlinear continuum finite-strain elasticity beyond linearized Voigt homogenization, or global Maxwell/Coulomb equilibrium counts for arbitrary $n > 4$.
  - No GPU or empirical neural-network inference claims are made here; Frontier 1 certifies exact $E_8$ lattice and Weyl-chamber invariants only.

---

## 6. Artifact Manifest & Independent Verification Receipts

### 6.1 Companion File SHA-256 Manifest

| File | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `metamorphosis_symmetry_oracle.py` | `1350` | `55794` | `077f9833826cb0dd085f466f64752aa1874e901e59e55a5640ce75610c33a4fa` |
| `metamorphosis_symmetry_audit.py` | `137` | `4784` | `730e09cefdfb663c0e0462a59233132998b70d99cee2f987c61faaacfdcd0807` |
| `metamorphosis_symmetry_certificate.json` | `1` | `7372` | `6db040e4699644f58294a12c03e3ff57a2b7f6a56b33c8fd7004f1b611061a3e` |
| `test_metamorphosis_symmetry_r5.py` | `594` | `33000` | `309b5b1faf3be7305a4b09acb37dff10410af695b05952684b40f0f95ef044e9` |

### 6.2 Reproduction Commands (Verified Live)

```bash
# 1. Zero-skip R5 unit + adversarial Zone-B test suite across all three isolated modes
python3 -I -B test_metamorphosis_symmetry_r5.py
python3 -I -O -B test_metamorphosis_symmetry_r5.py
python3 -I -B -W error test_metamorphosis_symmetry_r5.py
# Expected: Ran 4 tests ... OK (0 skips) in all three modes

# 2. Fail-closed certificate verification across all three isolated modes
python3 -I -B metamorphosis_symmetry_audit.py --check metamorphosis_symmetry_certificate.json
python3 -I -O -B metamorphosis_symmetry_audit.py --check metamorphosis_symmetry_certificate.json
python3 -I -B -W error metamorphosis_symmetry_audit.py --check metamorphosis_symmetry_certificate.json
# Expected: OK TRACK-S21E-ESCHER-METAMORPHOSIS-SYMMETRY-BRIDGE certificate_sha256=72039ed901655749312c83cf80d51155ab104099be285e00accf189096bb81fe

# 3. Standalone oracle replay & byte-for-byte canonical JSON parity
python3 -I -B metamorphosis_symmetry_audit.py --standalone
python3 -I -B metamorphosis_symmetry_audit.py --standalone --json | cmp -s - metamorphosis_symmetry_certificate.json
# Expected: PASS TRACK-S21E-ESCHER-METAMORPHOSIS-SYMMETRY-BRIDGE ... and exit 0 on cmp -s
```

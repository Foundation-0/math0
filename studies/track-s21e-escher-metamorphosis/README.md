# Track S21e: Exact-Q Finite-Orthogonal Isotypic Projectors & Schur Obstructions Across Three Symmetry-Breaking Frontiers

Self-contained pure-$\mathbb{Z}/\mathbb{Q}$ (`int` + `fractions.Fraction`, zero IEEE-754 floats, zero bare `assert`s, zero external dependencies) certifier unifying finite orthogonal group verification, exact isotypic projector decompositions, Schur cross-irrep coupling norms, and Bunch-Kaufman Sylvester inertia across three frontiers:

- **Frontier 1 ($E_8$ Basis Metamorphosis & Weyl-Chamber Antipodal Breaking):** Orthogonal Weyl intertwiner $A = \frac{1}{2}(H_4 \otimes I_2) \in W(E_8)$ satisfies $U_{\mathrm{WHT8}} = U_{\mathrm{BH2}} A$, lifting 1-sparse axis root counts from `0` to `16` (`{2: 112, 8: 128}` -> `{1: 16, 4: 224}`, $d^2_{\max}$ `1 -> 1/2`, gain$^2$ `1 -> 2`) while inducing `14` Steiner $3$-$(8, 4, 1)$ quads with forced 4th-coordinate bleed (`min_d2 = 9801/20000`, `unique_nearest = 1`). Breaking $\{-I_8\}$ (`triv_rank = 0`) across both `siliquant_default` and `lexicographic` chambers (`120` positive roots, `ties = 0`) yields universal $\|\mu_\infty\|^2 = 31/45$, $\max(\mu_\infty \cdot r) = 29/30 < 1$, and `52/240` shifted roots inside the open $\sqrt{2}$-ball ($\min d^2 = 34/45$).
- **Frontier 2 (Harmonic Coulomb Hessian Walls):** Exact $n = 4$ $T_d \to C_{3v}$ pyramid family (`|Td| = 24`, `|C3v| = 6`, $T_2 = A_1(1) \oplus E(2)$) crosses the $T_d$-forced zero Hessian wall $H(0) = 0_{3\times 3}$ (`[0, 0, 3]`) from compressed $C_{3v}$ ($\lambda_{A_1} = 6, \lambda_E = -3$, `[1, 2, 0]`, index `2`) to extended $C_{3v}$ ($\lambda_{A_1} = -3, \lambda_E = 3/2$, `[2, 1, 0]`, index `1`) with an exact `2`-unit Poincare-Hopf sign jump; exact $D_{4h} \to D_{2h}$ square pitchfork transitions `[2, 2, -4]` (`[2, 1, 0]`) -> `[6, 0, -6]` (`[1, 1, 1]`) -> `[10, -2, -8]` (`[1, 2, 0]`); $C_1$ fold preserves $m_2 - m_1 = 3$ (`7 - 4` -> `6 - 3`).
- **Frontier 3 (Voigt Homogenization, $Z_2$ Truss Singularity, & 6-Spoke Prestress):** Under faithful $D_2 \subset O(6, \mathbb{Q})$ from $D_{2h}$ ($\mathbb{Q}^6 = A_g(3) \oplus B_{1g} \oplus B_{2g} \oplus B_{3g}$), symmetric `none`, `half_2_opp` (`C44 = 1/4`, optimal `1/24` shear/tie), and `full_4` (`C44 = 1/2`, `1/24` shear/tie) enforce exact $C_{14} = 0$ (`cross_coupling_frob_sq = 0`), whereas chiral `one_per_plane` breaks $D_{2h} \to C_3$ and opens $C_{14} = -26/253$ (`cross_coupling_frob_sq = 4083/64009`, `34/759` shear/tie). Companion exact $Z_2$ 2-bar truss (`flat_singular` `[1, 0, 1]` with quartic `257500/970299`, `online_saddle` `[1, 1, 0]`, `broken_z2_corner` `[2, 0, 0]` with $\det H = 64/105$) and anchored 6-spoke tension/compression prestress (`[7, 0, 0]` vs `[0, 7, 0]`) complete the synthesis.
- **Honest Scope (`N1`):** Synthesizes exact finite-dimensional symmetry-breaking obstructions without claiming infinite-family classification or empirical GPU claims.

## Quick Verification

```bash
cd studies/track-s21e-escher-metamorphosis

# 1. Zero-skip R5 test suite across all three isolated modes
python3 -I -B test_metamorphosis_symmetry_r5.py
python3 -I -O -B test_metamorphosis_symmetry_r5.py
python3 -I -B -W error test_metamorphosis_symmetry_r5.py

# 2. Fail-closed certificate check & byte-identical standalone replay
python3 -I -B metamorphosis_symmetry_audit.py --check metamorphosis_symmetry_certificate.json
python3 -I -B metamorphosis_symmetry_audit.py --standalone --json | cmp -s - metamorphosis_symmetry_certificate.json
```

See [`REPORT.md`](REPORT.md) for the complete mathematical tables, Law-2b obstruction analysis, and companion file SHA-256 manifest.

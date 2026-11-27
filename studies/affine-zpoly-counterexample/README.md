# Sub-Million Affine Counterexamples to Log-Concavity and Real-Rootedness of Matroid Z-Polynomials

This directory provides a self-contained, zero-dependency Python (`int` / `fractions.Fraction`) and pure-`Init` **Lean 4.36.0** (`0` external packages, `0` `sorry`, `0` `Classical.choice`) verification suite for counterexamples to the log-concavity and real-rootedness conjectures for matroid $Z$-polynomials posed by Proudfoot, Xu, and Young ([arXiv:1706.05575](https://arxiv.org/abs/1706.05575), Conjectures 5.1 and 6.5).

Building on the hyperplane-coalescence framework of Bérczi, Coron, Eur, and Li ([arXiv:2610.17135](https://arxiv.org/abs/2610.17135), Proposition 3.11 and Sections 4.1–4.5) and the first projective counterexample announced by Mingfei Guo ([`guoriyue/z123`](https://github.com/guoriyue/z123), commit `0b23a1c9d4618df8af1f454e917ff4ac0b1e171f`, $|E| = 29,840,942$ in $\mathrm{PG}(5, 27)$), we construct and formally certify two substantially smaller families of rank-$7$ coalesced matroid counterexamples in affine $4$-space $\mathrm{AG}(4, q)$ (for prime powers $q$):

1. **Elementary Affine Gabidulin Family $A_{4,q}$ ($28.04\times$ to $32.33\times$ smaller, zero spread packing):** Partitioning $\mathrm{End}_{\mathbb{F}_q}(\mathbb{F}_{q^2}) = \{\phi_{u,a}(x) = u x + a x^q : u, a \in \mathbb{F}_{q^2}\}$ by its $q^2$ Frobenius parameter cosets $a \in \mathbb{F}_{q^2}$ produces $m \le q^2$ collections of $s = q^2$ linear $2$-subspaces of $\mathbb{F}_q^4$ whose parallel direction spaces at infinity intersect trivially ($\{0\}$) within each coset (so affine $2$-planes from distinct parallel classes of the same coset meet in at most a single point, rank $\le 1$) and intersect in dimension at most $1$ across distinct cosets ($\dim_{\mathbb{F}_q}(\ker(\phi_{u,a} - \phi_{u',a'})) \le 1$, so cross-coset affine $2$-planes meet in at most an affine line of size $\le q$, $\operatorname{rk}(F \cap F') \le 2 = r - 2$, never sharing a rank-$3$ hyperplane). This satisfies Bérczi–Coron–Eur–Li Proposition 3.11 directly from elementary field arithmetic.
   - At $q = 27$, an exhaustive exact sweep confirms $T(A_{4,27}^{(m)} \oplus A_{4,27}^{(m)})$ violates $z_2^2 \ge z_1 z_3$ for all $269/269$ integers $m \in [461, 729]$, achieving $|E| = 1,064,340$ at $m = 729$, deepest violation at $m = 618$ (**$|E| = 1,064,118$**, **$28.04\times$ smaller** than $|E| = 29,840,942$, $z_2^2/(z_1 z_3) \approx 0.897780$), and sharp threshold $|E| = 1,063,804$ at $m = 461$ ($m = 460$ remains log-concave).
   - The asymmetric elementary sum $T(A_{4,27}^{(510)} \oplus A_{4,25}^{(456)})$ breaks the one-million element barrier at **$|E| = 923,032$** (**$32.33\times$ smaller**) without any spread-packing construction.
2. **Explicit $651$-Spread Parallelism Witness in $\mathrm{AG}(4, 25)$ ($38.14\times$ to $38.15\times$ smaller):** Using the closed-form Hall-spread parallelism construction of Pavese and Santonastaso ([arXiv:2506.16271](https://arxiv.org/abs/2506.16271), Definition 3.3 and Theorem 3.4; existence originally due to Denniston, 1972/1973), we explicitly construct over $\mathbb{F}_{625} = \mathbb{F}_5[w]/(w^2 - 2)[z]/(z^2 - w)$ ($w = 5$) all **$651$ pairwise-disjoint spreads** of $\mathrm{PG}(3, 25)$ ($1$ Desarguesian spread + $650$ Hall spreads $= 407,526 = \begin{bmatrix}4\\2\end{bmatrix}_{25}$ distinct Plücker lines, $0$ overlaps, with all **$651/651$** spreads directly verified to partition all $16,276$ points of $\mathrm{PG}(3, 25)$).
   - Eliminating all unabsorbed affine-line extensions ($s = q^2 + 1 = 626$ vs. $s = q^2 = 625$, where the exact $m \in [1, 625]$ sweep stays log-concave with minimum ratio $1.029858$ at $m = 537$) drops the symmetric counterexample threshold from $q = 27$ to $q = 25$: $T(M_{25}^{(m)} \oplus M_{25}^{(m)})$ fails log-concavity for all $56/56$ integers $m \in [510, 565]$, achieving deepest violation at $m = 537$ (**$|E| = 782,324$**, **$38.14\times$ smaller**), symmetric threshold $m = 510$ (**$|E| = 782,270$**), and $2$-connected asymmetric parallel connection $P(M_{25}^{(496)}, M_{25}^{(497)})$ at **$|E| = 782,242$** (**$38.15\times$ smaller**).

---

## Summary of Certified Witnesses (Rank $7$)

For every rank-$7$ matroid $M$, $Z_M(t) = 1 + z_1 t + z_2 t^2 + z_3 t^3 + z_3 t^4 + z_2 t^5 + z_1 t^6 + t^7$ is palindromic of degree $7$; internal log-concavity at index $2$ requires $z_2^2 - z_1 z_3 \ge 0$, and real-rootedness implies log-concavity by Newton's inequalities.

| Witness Family | Ambient Geometry | $(q, m, s)$ | Ground Set $|E|$ | Shrinkage vs. `z123` | Exact Sign of $z_2^2 - z_1 z_3$ | $z_2^2 / (z_1 z_3)$ |
|---|---|---|---:|---:|---|---:|
| `guoriyue/z123` (`T(G ⊕ G)`) | $\mathrm{PG}(5, 27)$ | $(27, 19683, \text{proj})$ | `29,840,942` | $1.00\times$ | `−3.062906… × 10^64` (**FAILS**) | `0.896151` |
| Projective control (`T(G ⊕ G)`) | $\mathrm{PG}(5, 25)$ | $(25, 15625, \text{proj})$ | `20,376,302` | $1.46\times$ | `+1.762969… × 10^62` (holds) | `1.019699` |
| Projective subset (`T(G ⊕ G)`) | $\mathrm{PG}(5, 25)$ | $(25, 13000, \text{proj})$ | `20,371,052` | $1.46\times$ | `−6.255286… × 10^61` (**FAILS**) | `0.984416` |
| Elementary Gabidulin full (`T(A ⊕ A)`) | $\mathrm{AG}(4, 27)$ | $(27, 729, 729)$ | `1,064,340` | $28.04\times$ | `−1.223692… × 10^47` (**FAILS**) | `0.927243` |
| **Elementary Gabidulin min-ratio (`T(A ⊕ A)`)** | $\mathrm{AG}(4, 27)$ | $(27, 618, 729)$ | **`1,064,118`** | **`28.04×`** (`14920471/532059`) | `−8.390772… × 10^46` (**FAILS**) | `0.897780` |
| Elementary Gabidulin threshold (`T(A ⊕ A)`) | $\mathrm{AG}(4, 27)$ | $(27, 461, 729)$ | `1,063,804` | $28.05\times$ | `−1.569217… × 10^44` (**FAILS**) | `0.999340` |
| **Asymmetric Elementary (`T(A_1 ⊕ A_2)`)** | $\mathrm{AG}(4,27) \sqcup \mathrm{AG}(4,25)$ | $(27,510)\oplus(25,456)$ | **`923,032`** | **`32.33×`** (`14920471/461516`) | `−1.494051… × 10^42` (**FAILS**) | `0.999986` |
| **Explicit Spread-Packing (`T(M ⊕ M)`)** | $\mathrm{AG}(4, 25)$ | $(25, 537, 626)$ | **`782,324`** | **`38.14×`** (`14920471/391162`) | `−2.129748… × 10^44` (**FAILS**) | `0.996696` |
| Spread-Packing threshold (`T(M ⊕ M)`) | $\mathrm{AG}(4, 25)$ | $(25, 510, 626)$ | `782,270` | $38.15\times$ | `−5.633915… × 10^42` (**FAILS**) | `0.999891` |
| $2$-Connected Parallel Conn. (`P(M, M)`) | $\mathrm{AG}(4, 25)$ | $(25, 537, 626)$ | `782,323` | $38.14\times$ | `−4.866177… × 10^44` (**FAILS**) | `0.992366` |
| **Asymmetric Parallel Conn. (`P(M_1, M_2)`)** | $\mathrm{AG}(4, 25)$ | $(25, 496/497, 626)$ | **`782,242`** | **`38.15×`** (`14920471/391121`) | `−9.517210… × 10^41` (**FAILS**) | `0.999979` |
| Spread-Packing control (`T(M ⊕ M)`) | $\mathrm{AG}(4, 23)$ | $(23, 461, 530)$ | `560,604` | $53.23\times$ | `+6.302865… × 10^44` (holds) | `1.151786` |

All full arbitrary-precision integers $(z_1, z_2, z_3, z_2^2 - z_1 z_3)$, exact reduced fractions $z_2^2/(z_1 z_3)$, complete range sweeps, and negative controls are recorded in the certificate JSON file in this directory (`s161_z123_zpoly_certificate.json`).

---

## Independent Verification Pillars

1. **Zero-Shared-Code EPW Kazhdan–Lusztig & $Z$-Polynomial Poset Audit:** The pure-$\mathbb{Z}/\mathbb{Q}$ oracle builds flat lattices downward from hyperplanes (verifying Oxley Proposition 2.1.24 upward-cover partitions) and evaluates the defining Elias–Proudfoot–Wakefield recurrence $t^r P_M(t^{-1}) - P_M(t) = \sum_{F \ne \emptyset} \chi_{M|_F}(t) P_{M/F}(t)$ from scratch on non-uniform matroids of ranks $3, 4, 5, 7$ ($K_4$, $A_{4,2}$, $T(K_4 \oplus K_4)$, and $T^7(K_4 \oplus K_4 \oplus U_{2,3})$), confirming the exact flag-$f$-vector formulas for $[t]P_N$ (ranks $3, 4$), $[t^2]P_N$ (rank $5$), and $(z_1, z_2, z_3)$ (rank $7$). It cross-checks the $17$-orbit parallel-connection DAG over an explicit $7$-spread parallelism of $\mathrm{PG}(3, 2)$ across all $41/41$ rank tuples ($k \le 3$) both against rank-$4$ basepoint-typed flat-pairing sums on $L(M_{2,m})$ for all $m \in \{1, 2, 3, 4\}$ ($17/17$ orbits active at $m = 4$, $164/164$ checks, $0$ mismatches) and directly against the explicit un-quotiented rank-$7$ bitmask flat lattices $L(P(M_{2,1}, M_{2,1}))$ ($|E| = 33$, $14,440$ hyperplanes) and asymmetric $L(P(M_{2,1}, M_{2,2}))$ ($|E| = 34$, $14,456$ hyperplanes) verified via Oxley Proposition 2.1.24 upward-cover partitions across all ranks $0..6$ ($82/82$ checks, $0$ mismatches).
2. **Exhaustive Finite Ground-Truth Verification of $A_{4,2}$ and $A_{4,3}$:** Explicitly constructs finite $A_{4,2}$ ($|E| = 20$, $336$ hyperplanes, $1,140/1,140$ unique $3$-element covers, $\alpha_{\{1,2,3\}} = 3,368$) and $A_{4,3}$ ($|E| = 90$, $1,845$ rank-$2$ flats explicitly verified to partition all $\binom{90}{2} = 4,005$ element pairs uniquely with zero overlaps, $5,142$ hyperplanes satisfying all $1,845$ upward-cover partition checks, $\alpha_{\{1,2,3\}} = 81,990$, $Z_{A_{4,3}}(t) = 1 + 5142 t + 21222 t^2 + 5142 t^3 + t^4$), matching the closed-form flag polynomial identically.
3. **Explicit Overlap-Free $651$-Spread Parallelism of $\mathrm{PG}(3, 25)$:** Constructs $\mathbb{F}_{25} = \mathbb{F}_5[w]/(w^2 - 2)$ and $\mathbb{F}_{625} = \mathbb{F}_{25}[z]/(z^2 - w)$ ($w = 5$), verifies the $26$-element norm-$1$ circle good set $\mathcal{P} = \{(w, 1, v) : v^{26} = 1\}$, derives $650$ Hall spreads via opposite reguli and $E$-group shifts alongside the Desarguesian spread, and directly verifies all $651/651$ spreads partition all $16,276$ points of $\mathrm{PG}(3, 25)$ with all $407,526$ Plücker line codes pairwise distinct ($0$ overlaps).
4. **Pure-`Init` Lean 4.36.0 Formalization (`ZPolyCounterexample.lean`, $62$ Theorems):** With zero imports (`lake-manifest.json` `packages = []`) and axioms restricted strictly to `{propext, Quot.sound}`, proves polynomial ring/Horner Taylor-shift homomorphisms, universal flag-polynomial log-concavity failure $z_2^2 < z_1 z_3$ for **every integer $q \ge 27$** (applying to all prime-power geometries $\mathrm{PG}(5, q)$ and $\mathrm{AG}(4, q)$ with $q \ge 27$) via degree-$46$ (`pg5_zpoly_not_log_concave_for_all_q_ge_27`, $47/47$ positive shifted coefficients, minimum $324$) and degree-$34$ (`ag4_elem_zpoly_not_log_concave_for_all_q_ge_27`, $35/35$ positive shifted coefficients, minimum $324$) certificates, universal ground-set dominance (`ag4_ground_set_strictly_smaller_than_pg5`, $2(q^4 + q^2) < 2([6]_q + q^3)$ for all $q \ge 2$), concrete exact-integer witnesses and boundary controls (`pg5_q27_guoriyue_witness`, `pg5_q25_m13000_witness`, `ag4_elem_q27_witnesses`, `ag4_elem_q27_m461_threshold_witness`, `ag4_elem_asym_submillion_witness`, `ag4_spread_q25_submillion_witnesses`, `ag4_spread_q23_m461_control_witness`), and the algebraic $\mathbb{F}_{625}$ good-set non-collision theorem `f625_closed_form_good_set_valid` (the matroid/EPW lattice correspondence, reciprocal-pair partition of `allowedNorms25`, and full geometric spread enumeration are verified in the companion pure-$\mathbb{Z}/\mathbb{Q}$ Python oracle).

---

## Reproducing All Checks

Requirements: Python 3.10+ (standard library only) and optionally `leanprover/lean4:v4.36.0` (`elan` / `lake`) for live Lean kernel replay.

```bash
# 1. Offline pure-Z/Q certificate + static Lean package verification
PYTHONDONTWRITEBYTECODE=1 python3 -I -B verify_s161_z123_zpoly.py --check

# 2. Live Lean 4.36.0 kernel + lake build verification in isolated tempdir
PYTHONDONTWRITEBYTECODE=1 python3 -I -B verify_s161_z123_zpoly.py --live-lean --check

# 3. Standalone pure-Z/Q mathematical oracle
PYTHONDONTWRITEBYTECODE=1 python3 -I -B s161_z123_zpoly_oracle.py --json

# 4. Full refusal, boundary, strict I/O, and Lean audit test suite
PYTHONDONTWRITEBYTECODE=1 python3 -I -B -m unittest discover -s . -p "test_s161_z123_zpoly_r5.py" -v
```

---

## References

- G. Bérczi, B. Coron, C. Eur, and S. Li, *Chow polynomials and chain polynomials of matroids are not log-concave*, Preprint, 2026 ([arXiv:2610.17135](https://arxiv.org/abs/2610.17135)).
- R. Cheng and S. Liu, *Kazhdan–Lusztig polynomials of matroids need not be unimodal*, Preprint, 2026 ([arXiv:2607.24186](https://arxiv.org/abs/2607.24186)).
- R. H. F. Denniston, *Some packings of projective spaces*, Atti della Accademia Nazionale dei Lincei. Rendiconti, (8) **52**, 36–40, 1972.
- R. H. F. Denniston, *Packings of $\mathrm{PG}(3, q)$*, in *Finite Geometric Structures and their Applications* (C.I.M.E. Vol. 60), Edizioni Cremonese, Rome, 193–199, 1973.
- B. Elias, N. Proudfoot, and M. Wakefield, *The Kazhdan–Lusztig polynomial of a matroid*, Advances in Mathematics **299**, 36–70, 2016 ([arXiv:1412.7408](https://arxiv.org/abs/1412.7408)).
- M. Guo (`guoriyue`), *`z123`: Rank-$7$ $Z$-polynomial log-concavity counterexamples from truncated projective Gabidulin matroids*, GitHub repository, commit `0b23a1c9d4618df8af1f454e917ff4ac0b1e171f`, 2026 ([`github.com/guoriyue/z123`](https://github.com/guoriyue/z123)).
- J. Oxley, *Matroid Theory* (2nd ed.), Oxford University Press, 2011.
- F. Pavese and P. Santonastaso, *On line-parallelisms of $\mathrm{PG}(3, q)$*, Preprint, 2025 ([arXiv:2506.16271](https://arxiv.org/abs/2506.16271)).
- N. Proudfoot, Y. Xu, and B. Young, *The $Z$-polynomial of a matroid*, Electronic Journal of Combinatorics **25**(1), `#P1.26`, 2018 ([arXiv:1706.05575](https://arxiv.org/abs/1706.05575), 2017).

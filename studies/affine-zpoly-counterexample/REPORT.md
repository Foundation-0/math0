# Independent Audit of `guoriyue/z123` and Sub-Million Affine `AG(4, q)` Counterexamples to Matroid Z-Polynomial Log-Concavity

- **Certificate Schema:** `s161.q44a.z123_affine_zpoly.v1`
- **Oracle Class:** `exact` (pure arbitrary-precision $\mathbb{Z}/\mathbb{Q}$, zero floating-point operations)
- **Novelty Classification:** `N1` (`n2_claims = 0`; independent verification and $28.04\times$–$38.15\times$ smaller affine geometric instantiations following Proudfoot–Xu–Young `arXiv:1706.05575`, Bérczi–Coron–Eur–Li `arXiv:2610.17135`, Mingfei Guo `guoriyue/z123 @ 0b23a1c9d4618df8af1f454e917ff4ac0b1e171f`, Denniston 1972/1973, and Pavese–Santonastaso `arXiv:2506.16271`)
- **Lean Formalization:** `ZPolyCounterexample.lean` (`leanprover/lean4:v4.36.0`, `1,071` LOC, `62/62` public theorems audited via `#print axioms`, `0` external dependencies, `0` `sorry`, `0` `Classical.choice`; axioms strictly within `{propext, Quot.sound}`)

---

## 1. Pillar 1 — Zero-Shared-Code EPW Kazhdan–Lusztig & Z-Polynomial Flag Audit

Starting solely from the defining Elias–Proudfoot–Wakefield (EPW) antisymmetric recurrence
$$t^r P_M(t^{-1}) - P_M(t) = \sum_{\emptyset \ne F \le E} \chi_{M|_F}(t)\, P_{M/F}(t), \qquad \deg P_M < \frac{r}{2} \quad (r \ge 1), \quad P_{\emptyset}(t) = 1,$$
and $Z_M(t) = \sum_{F \in L(M)} t^{\operatorname{rk}(F)} P_{M/F}(t)$, `s161_z123_zpoly_oracle.py` builds full flat lattices downward from hyperplanes (enforcing Oxley Proposition 2.1.24 upward-cover partitions) and verifies the exact proper-flag $f$-vector identities:
- **Rank $3$ ($K_4$, $|E|=6$):** $[t]P_N = \alpha_{\{2\}} - \alpha_{\{1\}} = 7 - 6 = 1$; $P_{K_4}(t) = 1 + t$, $Z_{K_4}(t) = 1 + 7t + 7t^2 + t^3$.
- **Rank $4$ ($A_{4,2}$, $|E|=20$):** $[t]P_N = \alpha_{\{3\}} - \alpha_{\{1\}} = 336 - 20 = 316$; $P_{A_{4,2}}(t) = 1 + 316t$, $Z_{A_{4,2}}(t) = 1 + 336t + 1022t^2 + 336t^3 + t^4$.
- **Rank $5$ ($T(K_4 \oplus K_4)$, $|E|=12$):** $[t^2]P_N = \alpha_{\{3\}} - \alpha_{\{2\}} + \alpha_{\{2,4\}} - \alpha_{\{2,3\}} - \alpha_{\{1,4\}} + \alpha_{\{1,2\}} = 72$; $P(t) = 1 + 49t + 72t^2$, $Z(t) = 1 + 61t + 350t^2 + 350t^3 + 61t^4 + t^5$.
- **Rank $7$ ($T^7(K_4 \oplus K_4 \oplus U_{2,3})$, $|E|=15$):**
  $$z_1 = \alpha_{\{6\}}, \qquad z_2 = \alpha_{\{5\}} + \alpha_{\{4,6\}} - \alpha_{\{4,5\}},$$
  $$z_3 = \alpha_{\{4\}} + \alpha_{\{3,6\}} - \alpha_{\{3,4\}} + \alpha_{\{2,5\}} - \alpha_{\{2,4\}} + \alpha_{\{2,4,6\}} - \alpha_{\{2,4,5\}} - \alpha_{\{2,3,6\}} + \alpha_{\{2,3,4\}},$$
  yielding $P(t) = 1 + 89t + 709t^2 + 360t^3$ and $Z(t) = 1 + 104t + 1546t^2 + 5429t^3 + 5429t^4 + 1546t^5 + 104t^6 + t^7$.

### Projective Gabidulin Verification (`PG(5, q)`)
- **`guoriyue/z123` (`PG(5, 27)`, $m = 19,683 = 27^3$, $|E| = 29,840,942$):**
  - $z_1 = 8431544402365682340068164569237$
  - $z_2 = 514110463898890370094084334091774$
  - $z_3 = 34980380235456818779149506079944992$
  - $z_2^2 - z_1 z_3 = -30629060076556831072416516750219744007195842510749495518880944028 < 0$ ($-3.062906\ldots \times 10^{64}$, $z_2^2/(z_1 z_3) \approx 0.89615107$).
  - Symbolic Taylor shift $-1296 \cdot D_{\mathrm{pg}}(27 + s)$ has degree $46$ (`47/47` exact integral coefficients verified with `denominator == 1`, strictly positive, $\min = 324$, leading coefficient $324$), certifying $z_2^2 < z_1 z_3$ on the closed-form projective Gabidulin flag formula for every integer $q \ge 27$ (and hence every prime-power geometry $\mathrm{PG}(5, q)$ with $q \ge 27$).
- **`PG(5, 25)` Subset vs. Full Control:** Full $m = 15,625$ ($|E| = 20,376,302$) satisfies $z_2^2 - z_1 z_3 = +176296945479121683328078071976611294901757170031472831429303879 > 0$ ($+1.762969\ldots \times 10^{62}$, $\approx 1.01969852$), whereas taking $m = 13,000$ cosets ($|E| = 20,371,052$) already breaks log-concavity at $q = 25$: $z_2^2 - z_1 z_3 = -62552862318891567771041511842682217527109820025018625017855246 < 0$ ($-6.255286\ldots \times 10^{61}$, $\approx 0.98441603$).

---

## 2. Pillar 2 — Elementary Affine Gabidulin Family $A_{4,q}$ in `AG(4, q)` (`28.04×`–`32.33×` Smaller)

For any prime power $q$, identifying $V = \mathbb{F}_{q^2} \times \mathbb{F}_{q^2} \cong \mathbb{F}_q^4$, the $q^4$ $\mathbb{F}_q$-linear maps $\phi_{u,a}(x) = u x + a x^q$ ($u, a \in \mathbb{F}_{q^2}$) partition by Frobenius parameter $a \in \mathbb{F}_{q^2}$ into $q^2$ cosets of $s = q^2$ $2$-dimensional linear direction subspaces $W_{u,a} = \{(x, \phi_{u,a}(x)) : x \in \mathbb{F}_{q^2}\}$. Within each coset $a$, distinct graphs satisfy $W_{u,a} \cap W_{u',a} = \{0\}$ because $(u - u')x = 0 \implies x = 0$ for $u \ne u'$, so distinct parallel translates of the same $W_{u,a}$ are disjoint while translates of distinct $W_{u,a}, W_{u',a}$ meet in a single point (rank $1 \le 2$). Across distinct cosets $a \ne a'$, $\phi_{u,a} - \phi_{u',a'}$ is a nonzero linearized polynomial of $q$-degree $1$, so $\dim_{\mathbb{F}_q}(\ker(\phi_{u,a} - \phi_{u',a'})) \le 1$; consequently, two affine $2$-planes from distinct cosets can intersect in $0$, $1$, or $q$ points — at most a rank-$2$ affine line ($\operatorname{rk}(F \cap F') \le 2 = r - 2$, never sharing a rank-$3$ hyperplane; for example, in $A_{4,2}$ over $\mathbb{F}_4$, $\phi_{1,0}(x) = x$ and $\phi_{0,1}(x) = x^2$ meet along the $2$-point affine line $\{(0, 0), (1, 1)\}$, and cross-coset intersections realize sizes $\{0, 1, 2\}$). Because every pair of coalesced hyperplanes intersects in a proper flat of rank $\le r - 2 = 2$, the family satisfies Bérczi–Coron–Eur–Li Proposition 3.11 with **zero spread-packing machinery**.

- **Exhaustive Finite Ground-Truth Verification:**
  - **$A_{4,2}$ ($|E| = 20$, $m = 4, s = 4$):** $336$ hyperplanes cover all $\binom{20}{3} = 1,140$ triples with multiplicity exactly $1$; empirical poset flag vector `{(): 1, (1,): 20, (2,): 190, (3,): 336, (1,2): 380, (1,3): 1212, (2,3): 1684, (1,2,3): 3368}` matches `affine_coalesced_alpha(2, 4, 4)` identically.
  - **$A_{4,3}$ ($|E| = 90$, $m = 9, s = 9$):** Explicit pair-set verification confirms all $1,845$ rank-$2$ flats partition all $\binom{90}{2} = 4,005$ element pairs uniquely (`len(seen_pairs) == 4005` and `pair_sum == 4005`, zero overlaps); all $1,845$ rank-$2$ upward-cover checks against the $5,142$ hyperplanes pass; empirical flag vector (`a123 = 81,990`, $Z_{A_{4,3}}(t) = 1 + 5142 t + 21222 t^2 + 5142 t^3 + t^4$) matches `affine_coalesced_alpha(3, 9, 9)` identically.
- **Universal $q \ge 27$ Failure, Exhaustive Sweep, & $28.04\times$ Shrinkage:** Symbolic Taylor shift $-1296 \cdot D_{\mathrm{el}}(27 + s)$ has degree $34$ (`35/35` exact integral coefficients with `denominator == 1`, strictly positive, $\min = 324$, leading coefficient $324$). An exact exhaustive sweep over all $m \in [0, 729]$ (persisted in `range_sweeps.ag4_elem_q27_s729`) confirms $T(A_{4,27}^{(m)} \oplus A_{4,27}^{(m)})$ violates log-concavity for all $269/269$ contiguous integers $m \in [461, 729]$ (with $m \in [0, 460]$ log-concave), including $m = 729$ ($|E| = 1,064,340$, $-1.223692\ldots \times 10^{47}$), deepest violation $m = 618$ (**$|E| = 1,064,118$**, exact shrinkage $14920471/532059 \approx 28.0429\times$, $-8.390772\ldots \times 10^{46}$, ratio $0.897780$), and sharp threshold $m = 461$ ($|E| = 1,063,804$, $-1.569217\ldots \times 10^{44}$, ratio $0.999340$).
- **Sub-Million Elementary Asymmetric Witness (Zero Spread Packing):** $T(A_{4,27}^{(510)} \oplus A_{4,25}^{(456)})$ achieves **$|E| = 923,032 < 1,000,000$** ($14920471/461516 \approx 32.3293\times$ smaller) with $z_2^2 - z_1 z_3 = -1494051551252406887510567535632103074287010 < 0$ ($-1.494051\ldots \times 10^{42}$, ratio $0.999986$).

---

## 3. Pillar 3 — Explicit $651$-Spread Parallelism of `PG(3, 25)` & Sub-Million Lower-Bound Search (`38.14×`–`38.15×` Smaller)

At $q = 25$, partial spreads ($s = q^2 = 625$) leave unabsorbed affine-line extensions ($n_U = m q^3 (q + 1)$), and an exact sweep over all $m \in [1, 625]$ (persisted in `negative_controls.ag4_partial_q25_s625_sweep`) confirms `fail_count = 0` with exact global minimum ratio **`1.029858`** (`1.02985798`, achieved at $m = 537$) and full-sweep endpoint ratio **`1.057819`** (`1.05781878`, persisted as `m625_ratio` at $m = 625$). Full spreads ($s = q^2 + 1 = 626$) eliminate all type-`(U)` hyperplanes ($n_U \equiv 0$), dropping the symmetric failure threshold to $q = 25$.

- **Explicit Algebraic Construction Over $\mathbb{F}_{625}$ (`0` Overlaps & `651/651` Point-Partition Verified):** Setting $\mathbb{F}_{25} = \mathbb{F}_5[w]/(w^2 - 2)$ and $\mathbb{F}_{625} = \mathbb{F}_{25}[z]/(z^2 - w)$ with $w = 5 \in \mathbb{F}_{25}$ ($N(w) = w^{26} = w^2 = 2 \in \mathbb{F}_{25}^\times \setminus \{1\}$, $2^2 = 4 \ne 1$), the $26$-element norm-$1$ circle $\mathcal{U} = \{v \in \mathbb{F}_{625}^\times : v^{26} = 1\}$ yields the closed-form $26$-triple good set $\mathcal{P} = \{(w, 1, v) : v \in \mathcal{U}\}$ satisfying Pavese–Santonastaso (`arXiv:2506.16271`, Definition 3.3 / Theorem 3.4) conditions `(3.2)` ($v_j - v_i \ne 0$) and `(3.3)` ($2(v_j^{25} - v_i^{25}) \ne 0$). Replacing each regulus $\mathcal{R}_i$ in $\mathcal{D}_1$ by its opposite regulus $\mathcal{R}_i^{\mathrm{opp}}$ and applying the $25$-element $E$-group shifts constructs $1 + 26 \times 25 = 651$ spreads covering all $407,526 = \begin{bmatrix}4\\2\end{bmatrix}_{25}$ Plücker lines of $\mathrm{PG}(3, 25)$ with **$0$ pairwise overlaps** (`319,260` lines at $m = 510$; `336,162` lines at $m = 537$), and the oracle directly runs `check_point_partition` on **all `651/651` spreads** (`point_partitions_verified = 651`), confirming every spread partitions all $16,276$ points of $\mathrm{PG}(3, 25)$.
- **Certified Sub-Million Witnesses & Exhaustive Sweeps:**
  - Exact sweep `range_sweeps.ag4_spread_q25_s626` over all $m \in [0, 651]$ confirms $T(M_{25}^{(m)} \oplus M_{25}^{(m)})$ fails log-concavity for all $56/56$ contiguous integers $m \in [510, 565]$ (with $m \in [0, 509]$ and $m \in [566, 651]$ log-concave):
    - Deepest violation $m = 537$: **$|E| = 782,324$** ($14920471/391162 \approx 38.1440\times$ smaller), $z_2^2 - z_1 z_3 = -212974814633787833903301832658405502046453382 < 0$ ($-2.129748\ldots \times 10^{44}$, ratio $0.99669628$).
    - Sharp symmetric threshold $m = 510$: **$|E| = 782,270$** ($38.1466\times$ smaller), $z_2^2 - z_1 z_3 = -5633915117621256661554904625581209355833980 < 0$ ($-5.633915\ldots \times 10^{42}$, ratio $0.99989083$).
  - $2$-Connected Parallel Connections: The $17$-orbit stabilizer DAG `_build_pconn_orbit_dag` is cross-checked over an explicit $7$-spread parallelism of $\mathrm{PG}(3, 2)$ across **all $41/41$ rank tuples** of length $k \le 3$ in two ways (persisted in `pconn_q2_verification`): (a) against rank-$4$ basepoint-typed flat-pairing sums on $L(M_{2,m})$ across **all $m \in \{1, 2, 3, 4\}$** (all $17/17$ orbits active at $m = 4$, `164/164` exact matches, `0` mismatches), and (b) directly against the explicit un-quotiented rank-$7$ bitmask flat lattices $L(P(M_{2,1}, M_{2,1}))$ ($|E| = 33$, `14,440` hyperplanes) and asymmetric $L(P(M_{2,1}, M_{2,2}))$ ($|E| = 34$, `14,456` hyperplanes) built from hyperplanes with Oxley Proposition 2.1.24 cover-partition checks across all ranks `0..6` (`82/82` exact matches, `0` mismatches). At $q = 25$, $P(M_{25}^{(537)}, M_{25}^{(537)})$ reaches $|E| = 782,323$ ($-4.866177\ldots \times 10^{44}$, ratio $0.99236595$, $>2\times$ deeper defect than $T$), and asymmetric $P(M_{25}^{(496)}, M_{25}^{(497)})$ reaches **$|E| = 782,242$** ($14920471/391121 \approx 38.1480\times$ smaller), $z_2^2 - z_1 z_3 = -951721065410900906898773806443907695215600 < 0$ ($-9.517210\ldots \times 10^{41}$, ratio $0.99997906$).
  - **Exact Persisted Negative Controls (`negative_controls`):**
    - `ag4_partial_q25_s625_sweep` ($q = 25, s = 625$, all $m \in [1, 625]$): `0` failures, min ratio **`1.029858`** at $m = 537$.
    - `ag4_spread_q23_T_sweep` ($q = 23, s = 530$, all $m \in [1, 553]$): `0` failures, min ratio **`1.151786`** at $m = 461$ ($|E| = 560,604$, $+6.302865\ldots \times 10^{44}$).
    - `ag4_spread_q23_P_sweep` ($q = 23, s = 530$, all $m \in [1, 553]$): `0` failures, min ratio **`1.146531`** at $m = 462$.
    - `ag4_pconn_mixed_q25_q23`: $P(M_{25}^{(537)}, M_{23}^{(461)})$ ratio **`1.066830`**; $P(M_{25}^{(538)}, M_{23}^{(461)})$ ratio **`1.066826`**.
    - `ag4_3conn_q25_m537` ($3$-connected $T^7(M_{25}^{(537)} \oplus M_{25}^{(537)} \oplus U_{1,1})$, $|E| = 782,325$): ratio **`1.034964`**.
    - `ag4_rk6_q25_sweep` (rank-$6$ $T^6(M_{25}^{(m)} \oplus M_{25}^{(m)})$, all $m \in [1, 651]$): `0` failures, min $z_2^2/(z_1 z_3)$ **`11.639961`** at $m = 651$ (`11.826325` at $m = 626$), min $z_3^2/z_2^2$ **`72.378997`**.

---

## 4. Pillar 4 — Full-Text Prior-Art & Novelty Audit (`N1`, `n2_claims = 0`)

| Source Inspected | Scope Verified | Exact Finding |
|---|---|---|
| Proudfoot–Xu–Young (`arXiv:1706.05575`) | Full HTML/PDF | Poses Conjecture 5.1 (real-rootedness of $Z_M(t)$) and Conjecture 6.5 / Remark 6.6 (log-concavity of $Z_M(t)$). |
| Cheng–Liu (`arXiv:2607.24186v2`) | Abstract & results | Disproves unimodality (and hence log-concavity and real-rootedness) of $P_M(t)$ while proving $Z_M(t)$ of their matroids equals $Z_{\mathrm{PG}(d-1,q)}(t)$ (real-rooted/log-concave). |
| Bérczi–Coron–Eur–Li (`arXiv:2610.17135v1`) | Full HTML (`0` `Z-poly` / `Proudfoot` hits) | Introduces Prop. 3.11 absorption, §4.1 `AG(4,q)` Klein/Denniston families, §4.2 projective Gabidulin, §4.5 rank-$7$ $T(G \oplus G)$ & parallel connection for Chow/chain/$h$-vector conjectures; does **not** evaluate $Z_M(t)$ or cite PXY. |
| `1337isnot1337/solved-conjectures` | All `13` branches, `392` PRs, `908` issues | **`0` matroid $Z$-polynomial entries** (`PR #748` concerns ribbon lattice-path $Z$-polynomials). |
| Mingfei Guo (`guoriyue/z123 @ 0b23a1c9d4...`) | Full `z123.py` & commit history | First public disproof of PXY Conjectures 5.1/6.5 via projective $T(G_{4,27} \oplus G_{4,27})$ in $\mathrm{PG}(5, 27)$ ($|E| = 29,840,942$). |

Honest novelty classification: **`N1`** (`n2_claims = 0`). Full credit for the $T(G \oplus G)$ rank-$7$ $Z$-polynomial disproof mechanism belongs to Mingfei Guo (`guoriyue/z123`) and Bérczi–Coron–Eur–Li (`arXiv:2610.17135`), and for $\mathrm{PG}(3, q)$ spread parallelisms to Denniston (1972/1973) and Pavese–Santonastaso (`arXiv:2506.16271`); our contributions are the independent zero-shared-code audit, the $28.04\times$–$32.33\times$ smaller elementary $A_{4,q}$ family, the explicit overlap-free and `651/651` point-partition-verified $\mathrm{PG}(3, 25)$ witnesses ($38.14\times$–$38.15\times$ smaller, down to $|E| = 782,242$), and the $62$-theorem pure-`Init` Lean 4.36.0 formalization.

---

## 5. Pillar 5 — Pure-`Init` Lean 4.36.0 Formalization (`ZPolyCounterexample.lean`, $62$ Theorems)

`ZPolyCounterexample.lean` uses zero `import` statements (`lake-manifest.json` `packages = []`) and zero `Classical.choice`, formalizing the algebraic flag-polynomial, shifted-certificate, witness, and $\mathbb{F}_{625}$ good-set layers (while the matroid/EPW lattice bridge and full geometric `651`-spread enumeration over prime-power geometries are verified in `s161_z123_zpoly_oracle.py`). Every theorem name below matches `ZPolyCounterexample.lean` verbatim:

- **§1 Polynomial Ring & Horner Taylor Shift (`16` theorems):** `isZeroInt_eq_true`, `evalP_addP`, `evalP_scaleP`, `evalP_negP`, `evalP_subP`, `evalP_mulP`, `evalP_consTrim`, `evalP_trimP`, `evalP_shiftAdd`, `evalP_shiftStep`, `evalP_shiftFast`, `evalP_nonneg_of_coeffs_nonneg`, `evalP_pos_of_coeffs_pos`, `all_pos_of_all_gt_zero`, `neg_of_shiftFast_neg_coeffs_pos`, `pos_of_mul_pos_left`.
- **§2 Exact Divisibility & Gaussian $q$-Binomials (`8` theorems):** `mul_two_three`, `mul_three_two`, `two_mul_choose2`, `six_mul_choose3`, `gaussQ_zero_right`, `gaussQ_one_mul`, `evalP_qPowPoly`, `evalP_gaussPoly`.
- **§3–§5 Multichain Bilinear Forms, Scaling & Polynomial Bridges (`14` theorems):** `z1Pair_eq_bilin`, `z2Pair_eq_bilin`, `z3Pair_eq_bilin`, `z1Bilin_scale6`, `z2Bilin_scale6`, `z3Bilin_scale6`, `evalFlagPoly_trimFlagPoly`, `evalP_z1Poly`, `evalP_z2Poly`, `evalP_z3Poly`, `evalP_sixChoose2Poly`, `evalP_sixChoose3Poly`, `evalFlagPoly_projGabPoly6`, `evalFlagPoly_affElemPoly6` (note: spread-packing witnesses are certified via exact integer `affGabFlag` evaluation in §7 rather than a symbolic spread polynomial).
- **§6 Trimmed Defect Polynomials & Universal $q \ge 27$ Flag-Polynomial Disproofs (`15` theorems):** `pg5FlagTrim_eq`, `pg5Z1Trim_eq`, `pg5Z2Trim_eq`, `pg5Z3Trim_eq`, `pg5Defect_eq`, `ag4FlagTrim_eq`, `ag4Z1Trim_eq`, `ag4Z2Trim_eq`, `ag4Z3Trim_eq`, `ag4Defect_eq`, `trimmed_defect_bridge`, `pg5_defect_eval_neg_for_all_q_ge_27`, `ag4_elem_defect_eval_neg_for_all_q_ge_27`, plus:
  - `pg5_zpoly_not_log_concave_for_all_q_ge_27`: $\forall q \in \mathbb{Z},\ q \ge 27 \implies z_2^2 < z_1 z_3$ for `projGabFlag q (q ^ 3)` (applying to every prime-power geometry $\mathrm{PG}(5, q)$ with $q \ge 27$).
  - `ag4_elem_zpoly_not_log_concave_for_all_q_ge_27`: $\forall q \in \mathbb{Z},\ q \ge 27 \implies z_2^2 < z_1 z_3$ for `affGabFlag q (q ^ 2) (q ^ 2)` (applying to every prime-power geometry $\mathrm{AG}(4, q)$ with $q \ge 27$).
- **§7 Ground-Set Dominance & Concrete Witnesses/Controls (`8` theorems):**
  - `ag4_ground_set_strictly_smaller_than_pg5`: $\forall q \in \mathbb{Z},\ q \ge 2 \implies 2(q^4 + q^2) < 2(\begin{bmatrix}6\\1\end{bmatrix}_q + q^3)$.
  - `pg5_q27_guoriyue_witness` (`|E| = 29,840,942`), `pg5_q25_m13000_witness` (`m = 13,000` fails, `m = 15,625` holds), `ag4_elem_q27_witnesses` (`m = 729` and `m = 618`, `28.04×`), `ag4_elem_q27_m461_threshold_witness` (`m = 461` fails, `m = 460` holds), `ag4_elem_asym_submillion_witness` (`|E| = 923,032`), `ag4_spread_q25_submillion_witnesses` (`m = 537` `|E| = 782,324` `38.14×` and `m = 510` `|E| = 782,270`), and `ag4_spread_q23_m461_control_witness` (`|E| = 560,604`, log-concave control).
- **§8 Algebraic $\mathbb{F}_{625}$ Good-Set Certificate (`1` theorem):** `f625_closed_form_good_set_valid` verifies `goodSetP25.length = 26`, norm membership `norm625 5 = 2 ∈ allowedNorms25`, unit-circle norms `norm625 u = norm625 v = 1`, and all pairwise `(3.2)`–`(3.3)` checks via `allPairsGood goodSetP25 = true` (the $11$-reciprocal-pair partition of $\mathbb{F}_{25}^\times \setminus \{1\}$ including $-1 = 4$ and $2^2 = 4 \ne 1$ for `allowedNorms25` is verified computationally in `s161_z123_zpoly_oracle.py`).

---

## 6. Artifact Manifest & Post-Edit Verification Receipts

| File | Bytes | SHA-256 |
|---|---:|---|
| `ZPolyCounterexample.lean` | `47,882` | `44a0891fa188d392b350006a05c0211e33cd3c301f36b946532023e33508bb26` |
| `lakefile.toml` | `113` | `6e26024feb14dba53e43bc1303258b134809855e80e3973270bc0355c9248446` |
| `lean-toolchain` | `25` | `582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a` |
| `lake-manifest.json` | `133` | `50e534cfda6b85b96c09dd488e7178d1fbabc2bf9c56307e697a9c8012f0457c` |
| `s161_z123_zpoly_certificate.json` | `12,759` | `f6996e69afbf071aa99c1879a00be9b0c039d77d67c185ecff43e682b4dd8382` |
| `s161_z123_zpoly_oracle.py` | `77,341` | `4a3e8ab70ec37448b200130ebbd55165da2c478daedd3ee4d1df2b72227a60d9` |
| `verify_s161_z123_zpoly.py` | `22,339` | `39151e4533cc8e02d310ef9671f474d739745b7084a473ef72d6859e9e26135d` |
| `test_s161_z123_zpoly_r5.py` | `36,171` | `4308803cdca169dd96ed86fe5ca8ca41f554f5279895d68b251b53eac4db78f2` |
| `README.md` | `13,395` | `5a79b56dc96a147aca4411f4583040135c4c0c591cd23563d70ac8a2ba181b65` |

### Verified Post-Edit Deterministic, Live-Lean, Hardened I/O, Mutation, & Audit Gates
- **Pinned Certificate & Payload Digests:** `s161_z123_zpoly_certificate.json` SHA-256 `f6996e69afbf071aa99c1879a00be9b0c039d77d67c185ecff43e682b4dd8382` (`payload_sha256 = b04f0a40765bd0b1644ac823888f42f122a84b084223ca924e318f53b337cc91`).
- **Hardened Zone-B I/O & Type-Exact Certificate Checks:**
  - `write_cert` enforces ancestor symlink checks, `O_NOFOLLOW` parent-directory walk, regular-file & `st_nlink == 1` target verification via `lstat(..., dir_fd=dfd)`, CSPRNG `secrets.token_hex(8)` unique `O_CREAT | O_EXCL | O_NOFOLLOW` temp file inside verified parent directory (assigning cleanup target only after `os.open` succeeds to prevent pre-unlink collision races), and `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`: `--write <symlink>/../victim.json`, symlink leaf, hardlink target, directory target, and `..` leaf all fail closed (`RC=2`) leaving existing files untouched.
  - `read_strict_bytes` enforces `st_nlink == 1`; `verify_lean_package` reads, audits, and SHA-verifies the `4` Lean files once, and `default_live_lean_runner` stages those exact already-hashed in-memory byte buffers directly into explicit `0o755`/`0o644` temporary directories (zero disk re-read TOCTOU window). `validate_axiom_lines` binds every `#print axioms` output prefix to the `62` audited Lean theorem identifiers.
  - `strict_json_equal` enforces recursive `type(a) is type(b)` equality so `bool`/`int` spoofs (`lean_files: true`, `1 -> true`, `0 -> false`) fail closed (`RC=2`, `CERT_MISMATCH`).
  - Fail-closed CLI parsers (`allow_abbrev=False`) convert abbreviated or malformed flag-value syntax (e.g., `--chec`, `--jso`, `--json=1`) to single-line JSON on stderr (`RC=2`), and `oracle.main` catches `OSError`/`RecursionError` uniformly (`RC=2`); Lean static audit regexes additionally guard against `#check_failure`, `run_cmd`, `run_meta`, `run_elab`, `run_tac`, `by_elab`, `debug.skipKernelTC`, extra `lakefile.toml` directives (`precompileModules`, `[[extern_lib]]`, etc.), and `@[...]` theorem attributes.
- **`3x -I` Isolated Parity (`-I -B`, `-I -O -B`, `-I -B -W error`):**
  - `s161_z123_zpoly_oracle.py --json`: bit-identical stdout SHA-256 `9ec0f5a38ed196a138f53a974ac1a5884c0e9ea97204ac18675e7e75cda7634d` (`×3`).
  - `verify_s161_z123_zpoly.py --check --json`: bit-identical stdout SHA-256 `f6996e69afbf071aa99c1879a00be9b0c039d77d67c185ecff43e682b4dd8382` (`×3`).
  - `test_s161_z123_zpoly_r5.py`: **`8/8 OK` ×3** (`0` skips, `0` bare asserts, `0` float literals/calls in `oracle.py`, `verify_s161_z123_zpoly.py`, and `test_s161_z123_zpoly_r5.py`, `0` local path literals).
- **Read-Only & Live Lean 4.36.0 Kernel Replay:** `verify_s161_z123_zpoly.py --live-lean --check --json` on both RW and `chmod -R a-w` read-only snapshot -> **`PASS`** (`62/62` theorems audited with theorem-name binding, `0` warnings, `0` `.lake/` residue, stdout bit-identical `f6996e69afbf071aa99c1879a00be9b0c039d77d67c185ecff43e682b4dd8382`).
- **Dual Uncapped Refusal & Boundary Mutation (`aletheia mutate --max-mutants 0`, `null_mutant = passed`, `truncated = false`):**
  - `verify_s161_z123_zpoly.py`: **`93/93 = 100.0%`** (`default`) & **`93/93 = 100.0%`** (`--guards require_ok`), `0` survived.
  - `s161_z123_zpoly_oracle.py`: **`74/74 = 100.0%`** (`default`) & **`74/74 = 100.0%`** (`--guards require_ok`), `0` survived.
  - Combined: **`167/167 = 100.0%` ×2** (`334/334`, `0` survived).
- **Whole-File AST `BoolOp` Mutation (`5` `ast.BoolOp` nodes: `3` in oracle + `2` in verifier):** **`5/5` `OP_SWAP` + `10/10` `SUBCOND_DEL` = `15/15 = 100.0%`** killed (`0` survived).
- **Directory Hygiene & Lean Static Audit (`python3 -m aletheia audit-check . --lean-audit --strict-ancestors --safety-scan --strict-unseeded --scripts s161_z123_zpoly_oracle.py verify_s161_z123_zpoly.py`):** **`PASS`** (`10` files, `0` findings, `0` notices, `0` `.lake/` or `__pycache__/` residue).

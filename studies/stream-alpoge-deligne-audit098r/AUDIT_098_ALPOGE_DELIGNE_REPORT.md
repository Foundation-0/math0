# AUDIT-098: Line-by-Line Adversarial Audit & Pure-Q Certification of `hexagonmath.org/2611.00789v1` (*A short proof of Deligne's bound for Frobenius eigenvalues, after Alpöge*)

- **Audit ID:** `AUDIT-098` (Track S2, Continuous-Flow Intake `intake-2026-11-22`)
- **Author Seat:** `spectral-prover` (independent pre-verification audit; pending `verifier` seat)
- **Governance:** Aletheia v2.0.0 Laws 1–5 + `OWN_TERMS_FIRST` + **Law 2b (`LAW2B_TRANSFORM_BEFORE_DISMISSAL`)** + **Strict Law-4 `N0` Prior-Art Quarantine**
- **Overall Verdict:**
  - **Main Proof of Theorem 1 (`deligne_sign_only_v5.tex`, Sections 3–7, `HS-01..03`, `SG-08..11`):** **MATHEMATICALLY SOUND** — no fatal gap and no circular weight/purity/Fourier-Deligne dependency; three minor precision slips (`AD-01`, `AD-02`, `AD-04`) have exact one-sentence Law-2b repairs, and we identify a **perverse-sheaf elimination simplification** in Section 5 (`AD-02b`).
  - **Hexagon v1 Deposit Background Diff (`L89-91`):** **CONTAINS A REAL MATHEMATICAL ERROR (`AD-03`)** introduced by the diff between the GitHub archive (`77414a8d...`) and the Hexagon deposit (`52d5e171...`): attributing to Lafforgue `Corollaire VII.8` that *every lisse sheaf on a normal scheme of finite type over $\mathbf{F}_q$ is a unique direct sum $\bigoplus_\chi \sigma_\chi \otimes \chi$* is **FALSE** for non-semisimple lisse sheaves (explicit counterexample: the indecomposable rank-2 Kummer extension $0 \to \overline{\mathbf{Q}}_\ell(1) \to \mathcal{K}_t \to \overline{\mathbf{Q}}_\ell \to 0$ on $\mathbf{G}_m / \mathbf{F}_q$). This sits in Section 1's contextual remark and does **not** affect the proof of Theorem 1.
- **Honest Novelty Classification (Law 4):** **`N0`** (Deligne 1974/1980 theorem; Alpöge 20 Nov 2026 footnote 3 idea; `hexagon:2611.00789v1` exposition; our deliverable is an adversarial audit, exact pure-$\mathbb{Q}$/cyclotomic computational certifier, expository erratum `AD-01..AD-04`, and `mcproof`/Lean 4 mechanization blueprint).

---

## 1. Staged Primary Sources & Provenance Diff

| Artifact | Origin | SHA-256 (first 16 hex) | Role |
|---|---|---|---|
| `deligne_sign_only_v5.tex` (Hexagon deposit) | `hexagonmath.org/src/2611.00789v1` (21 Nov 2026, CC0, 554 lines) | `52d5e171cf7ec01d` | Primary audited text (*"Primarily AI-generated text / Human understanding: no parts"*) |
| `deligne_sign_only_v5.tex` (GitHub archive) | `KokunoYumeto/grothendieck-montpellier-archive @ 3ca09e90` (552 lines) | `77414a8df400f0ad` | Upstream archive copy (differs at L84–94 & L515–520) |
| `alpoge_remark.pdf` | `alpo.ge/remark.pdf` (20 Nov 2026, 4 pp.) | `3fc97784b71ddd44` | Primary idea source (p. 2 & footnote 3: `qN = M^k + R` path-quadric sketch) |
| `CHECK_a3ccbc11_20261121.md` | Upstream archive (`Claude Fable 5.2`) | `d6d2c25625d61e34` | Prior AI check (caught Cor. 3.4.1 -> App. A.5 fix; missed `AD-01..AD-04`) |

### Exact Hexagon vs. GitHub Archive Diff (`L84-94` & `L515-520`)
1. **GitHub (`77414a8d...`, L87–89):** *"this is not a gain in generality, since by a theorem of L. Lafforgue [Théorème VII.6 and Corollaire VII.8] every constructible $\overline{\mathbf{Q}}_\ell$-sheaf on $X$ is $\iota$-mixed."* (True as a summary.)
2. **Hexagon (`52d5e171...`, L87–91):** Replaced that sentence with: *"By results of L. Lafforgue, an irreducible lisse sheaf on a smooth curve over $\mathbf{F}_q$ whose determinant has finite order is pure of weight zero for every embedding [Théorème VII.6 (ii)], and on a normal scheme of finite type over $\mathbf{F}_q$ every lisse sheaf is, in a unique way, a direct sum $\bigoplus_\chi \sigma_\chi \otimes \chi$ of twists by characters $\chi$ [Corollaire VII.8]."* (Introduced **`AD-03`** — see Section 3 below!)
3. **Provenance lines (`L515-520`):** Updated to state that the two statements of Lafforgue were read at source by Claude Opus 5.5 rather than recalled from memory.

---

## 2. Line-by-Line Proof Audit & High-Risk Site Verdicts

| Unit | Lines in `v5.tex` | Claimed Inputs | Adversarial Audit Verdict |
|---|---|---|---|
| **Lemma 2 (`HS-01` / `HS-02`)** | L193–219 | Finite-dim $\overline{\mathbf{Q}}_\ell$-spaces, rational generating function $\sum m_j \mu_j z / (1 - \mu_j z)$ | **SOUND** (minor slip `AD-01`: invertibility of geometric Frobenius $F$ on $H^d_c(U,\mathcal{F})$ and $K$ is used without being cited; easily fixed or avoided by summing over nonzero eigenvalues). |
| **Lemma 3 (`HS-03`)** | L226–250 | Nondegenerate bilinear forms $b_i$, finite-field orthogonality, Cauchy–Schwarz | **SOUND** (`100%` exact exponent $T^k Q^{d(k+1)/2}$; works in **all** characteristics including **$p = 2$** because path couplings $b(x_i, x_{i+1})$ have no diagonal $x_i^2$ terms). |
| **Prop. 4 (`SG-08`)** | L269–307 | SGA 4 XIV 3.1 (Artin vanishing), XVII 5.4.3 (Künneth), XVIII §3 (Poincaré duality), SGA 4½ Trace Formula | **SOUND** (`100%` exact signs, Tate twist $(-1)$ on Gysin source, boundary surjection kernel $K$, Künneth collapse to $H^d_c(U,\mathcal{F})^{\otimes k}$, and $Y = \emptyset$ edge case). |
| **Thm 7 & Lemma 8 (Site A)** | L328–384 | Katz ACT App. A.3–A.5 (Deligne: SGA 4½ generic base change + duality + Artin vanishing) + Bertini count | **SOUND & WEIGHT-FREE** (minor slip `AD-02a`: Bertini formula $M - D - 1$ needs empty-incidence branch when $M = D$; simplification `AD-02b`: BBD perverse sheaves can be eliminated completely for closed immersions $\Gamma$ and lisse $\mathcal{G}$!). |
| **Thm 9 (`SG-09`)** | L388–455 | Stacks Tag `00OY` (Nagata Noether normalization over finite $\mathbf{F}_q$), Lemmas 2, 3, 8, Prop. 4 | **SOUND** (confirmed fibre count $\le B$ via $\dim_E(R \otimes_A E) \le B$ holds even for non-reduced/inseparable fibres; $(h,i)$-dependent weights $t_{i,h}(x)$ invoke Lemma 3 inside the $h \in E^\times$ triangle sum with zero hidden factor leaks). |
| **Section 7 (`SG-10`, `SG-11`)** | L457–506 | Induction on $\dim X$, open/closed LES, Poincaré duality on smooth proper $X$ | **SOUND** (minor slip `AD-04`: L471 writes *"with $C$ the rank of $\mathcal{F}$"*, implicitly assuming $U$ connected and $\operatorname{rank}\mathcal{F} > 0$; fix by $C = \max(1, \max_\alpha \operatorname{rank}(\mathcal{F}|_{U_\alpha}))$). |

### Detailed Audit of the Three High-Risk Sites

1. **Site A — Katz ACT Appendix A.5, Characteristic-$p$ Bertini, and Perverse-Sheaf Elimination:**
   - Deligne's Appendix A.3–A.5 uses generic base change (`SGA 4½`, *Th. finitude* 1.9), Verdier biduality (*Th. finitude* 4.3), Künneth, proper base change, and Artin vanishing (`SGA 4`, XIV 3.1). **No weights, purity, Weil I/II, or $\ell$-adic Fourier transform enter.**
   - **Perverse-Sheaf Elimination (`AD-02b`):** Because `v5.tex` only ever applies Theorem 7 to a closed immersion $\Gamma: V \hookrightarrow \mathbf{A}^M \subset \mathbf{P}^M$ and a lisse sheaf $\mathcal{G}$ on smooth $V$ of pure dimension $D$, the base-changed map $g: V \setminus Y \to W := \mathbf{P}^M \setminus H \cong \mathbf{A}^M$ is **quasi-finite** (and affine). Thus $R g_!(\alpha^*\mathcal{G}^\vee) = g_!(\alpha^*\mathcal{G}^\vee)$ sits in degree $0$ supported on a closed subset of dimension $\le D$ inside affine $W$. By Verdier duality on $W$, $H^i_c(W, R g_* \alpha^*\mathcal{G})^\vee \cong H^{2D-i}(W, g_! \alpha^*\mathcal{G}^\vee)(D)$, which vanishes for $2D - i > D$ (i.e. $i < D$) by **ordinary Artin vanishing** — completely removing BBD perverse sheaves from the dependency footprint!
   - **Characteristic-$p$ Bertini (`lem:good`, L373–380):** Because $\Gamma: V \hookrightarrow \mathbf{A}^M$ is a closed immersion, $d\Gamma$ is injective on every tangent space $T_v V$ in **every characteristic $p \ge 0$** (no inseparability failure!). Every hyperplane outside the closure of the $\le (M-1)$-dimensional tangency locus cuts $V$ transversely; by the Jacobian criterion over $\overline{\mathbf{F}}_q$, $\Gamma^{-1}H$ is smooth of pure dimension $D-1$ (or empty on missed components). Note `AD-02a`: when $M = D$, the tangency locus is empty (not a projective space of dimension $-1$).

2. **Site B — Effective Gysin Remainder (`prop:remainder`, `SG-08`):**
   - Geometric Frobenius $F$ acts on $\overline{\mathbf{Q}}_\ell(1)$ by $r^{-1}$ and on $\overline{\mathbf{Q}}_\ell(-1)$ by $r$.
   - Dualizing $H^a(X, \mathcal{F}_k^\vee) \to H^a(Y, \mathcal{F}_k^\vee)$ via Poincaré duality $H^a(X, \mathcal{F}_k^\vee)^\vee \cong H^{2D-a}_c(X, \mathcal{F}_k)(D)$ and $H^a(Y, \mathcal{F}_k^\vee)^\vee \cong H^{2D-2-a}_c(Y, \mathcal{F}_k)(D-1)$, and twisting by $(-D)$, gives the $F$-equivariant Gysin map $H^j_c(Y, \mathcal{F}_k)(-1) \to H^{j+2}_c(X, \mathcal{F}_k)$ ($j = 2D - 2 - a$), bijective for $j > D-1$ and surjective for $j = D-1$.
   - In $(-1)^{D-1}(r^n N_n - M_n^k)$, $W_a(-1) = H^{D-1+a}_c(Y)(-1)$ enters with sign $(-1)^a$ and $T_b = H^{D+b}_c(X)$ enters with sign $(-1)^b$. For $a \ge 1$, $W_a(-1) \xrightarrow{\sim} T_{a+1}$ cancels pairwise; the surviving terms are $+\operatorname{Tr}(T_0) + (\operatorname{Tr}(W_0(-1)) - \operatorname{Tr}(T_1)) = \operatorname{Tr}(H^d_c(U,\mathcal{F})^{\otimes k}) + \operatorname{Tr}(K)$, an **actual** (non-virtual) module trace with no alternating-sign cancellation. Empty $Y$ forces $T_b = 0$ for $b \ge 1$ and preserves the identity verbatim.

3. **Site C — Iterated Parseval with $(h,i)$-Dependent Weights (`lem:parseval`, `HS-03` + `thm:middle`):**
   - Noether normalization $\pi: U \to \mathbf{A}^d$ exists over **finite** $\mathbf{F}_q$ via Nagata's nonlinear substitution (`Stacks Tag 00OY`). For any field $E/\mathbf{F}_q$ and $x \in E^d$, $\dim_E(\mathcal{O}(U) \otimes_{\mathcal{O}(\mathbf{A}^d)} E) \le B$, so $|\{u \in U(E) : \pi(u) = x\}| \le B$ even for non-reduced or wildly ramified fibres.
   - For each fixed $h \in E^\times$, the linear perturbations $g_i(u_i) = \sum_j a_{ij} z_j(u_i)$ stay local to factor $i$, yielding fibre weights $t_{i,h}(x)$ bounded uniformly by $T = B C Q^{w/2}$. Applying Lemma 3 per fixed $h \in E^\times$ gives $|S_h| \le (BC)^k Q^{kw/2} Q^{d(k+1)/2}$; summing via the triangle inequality over the $Q - 1$ elements $h \in E^\times$ gives $|R_n| \le (Q-1)(BC)^k Q^{k(w+d)/2 + d/2} \le (BC)^k Q^{k(w+d)/2 + d/2 + 1}$ with **zero hidden leaks**.

---

## 3. Concrete Audit Findings & Law 2b Transformational Steelman Repairs

| ID | Severity | Location | Exact Finding | Law 2b Steelman / Exact Repair |
|---|---|---|---|---|
| **`AD-03`** | **MED (Real Erratum in Hexagon v1 Diff)** | `v5.tex` L89–91 (Hexagon `52d5e171`) | Claims Lafforgue `Corollaire VII.8` states that on a normal scheme $X/\mathbf{F}_q$, *"every lisse sheaf is, in a unique way, a direct sum $\bigoplus_\chi \sigma_\chi \otimes \chi$ of twists by characters $\chi$"*. Unconstrained $\sigma_\chi$ makes this vacuous/non-unique; with pure weight-0 / finite-determinant $\sigma_\chi$, it is **FALSE** for non-semisimple lisse sheaves. **Counterexample (certified in `W6`):** the Kummer extension $0 \to \overline{\mathbf{Q}}_\ell(1) \to \mathcal{K}_t \to \overline{\mathbf{Q}}_\ell \to 0$ on smooth normal $X = \mathbf{G}_m / \mathbf{F}_q$ has nontrivial unipotent geometric monodromy $T = \bigl(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\bigr)$ with $F T F^{-1} = T^{1/q}$, a **unique** 1D invariant subspace $\operatorname{span}(e_1)$ (indecomposable!), and two distinct Frobenius weights ($-2$ and $0$). | Restrict L89–91 to **semisimple** (or irreducible) lisse sheaves—or state the decomposition for the **semisimplification** $\mathcal{F}^{\mathrm{ss}}$ (which implies every constructible sheaf is $\iota$-mixed via Jordan–Hölder filtration, matching the GitHub copy `77414a8d` L87–89). Does **not** affect Theorem 1's proof. |
| **`AD-01`** | LOW-MED | `v5.tex` L194, L452 | Lemma 2 requires $F$ and $\Phi_k$ to be **automorphisms** ($\mu_j \neq 0$), but Theorem 9 never states why geometric Frobenius $F$ acts invertibly on $H^d_c(U,\mathcal{F})$ and $K$. | Add one sentence citing topological invariance of the étale site ($F^*\mathcal{F} \xrightarrow{\sim} \mathcal{F}$ for genuine constructible $\overline{\mathbf{Q}}_\ell$-sheaves), OR simply sum over nonzero eigenvalues in Lemma 2 (eigenvalue $0$ satisfies $|0| \le q^a$ trivially). |
| **`AD-02`** | LOW-MED | `v5.tex` L328–384, L473 | (a) Bertini dimension count $M - D - 1$ breaks syntactically when $M = D$ (e.g. $\mathrm{id}: \mathbf{A}^d \hookrightarrow \mathbf{A}^d$ in §7). (b) Perverse-sheaf language in Thm 7 is heavier than needed for closed immersions & lisse sheaves. | (a) Note tangency locus is empty when $M = D$ (or pad with a zero coordinate so $M > D$). (b) Optionally note direct Artin vanishing on $g_!\alpha^*\mathcal{G}^\vee$ removes BBD perverse sheaves. |
| **`AD-04`** | LOW | `v5.tex` L463, L471 | §7 writes *"with $C$ the rank of $\mathcal{F}$"* on smooth affine $U$ without assuming $U$ connected or $\operatorname{rank}\mathcal{F} > 0$ (whereas Thm 9 assumes $C > 0$). | Reduce to connected components of $U$ first and set $C = \max(1, \operatorname{rank}(\mathcal{F}|_{U_\alpha}))$. |

---

## 4. Exact Pure-$\mathbb{Q}$ / $\mathbb{Z}[\zeta_p]$ Computational Witnesses (`alpoge_deligne_certifier.py`)

All 6 witness families are independently certified in [`alpoge_deligne_certifier.py`](alpoge_deligne_certifier.py) (pure Python stdlib, **zero floats**, exact $\mathbb{Z}[\zeta_p]$ cyclotomic arithmetic, exact JSON certificate [`alpoge_deligne_certificate.json`](alpoge_deligne_certificate.json), inner SHA-256 `71d3454c29188a2a3aa3547889d61a333fada65b2181db78da888b48e6a53def`):

| Witness | Setting | Key Exact Verified Outputs | Negative / Genericity Control |
|---|---|---|---|
| **`W1`** | Paper Ex. 5: $U = \mathbf{A}^1, k=2$, $xy+x+y=0$ over $\mathbf{F}_p$, $p \in \{2,3,5,7,11\}$ | $K_1 K_1^* = p I_p$; $R = -p = \sum_{h\neq 0} S_h$; $(-1)^1 R = +p = \operatorname{Tr}(K_2)$; $R^2 \le (p-1)^2 p^3$ | Singular reducible conic $(x+1)(y+1)=0$ over $\mathbf{F}_7$: $N=13$, $R = +42 = p^2 - p$ (violates smooth $-p$) |
| **`W2`** | $U = \mathbf{G}_m$ ($H^1_c(\mathbf{G}_m) = \overline{\mathbf{Q}}_\ell \neq 0$), $k=2$ ($p \in \{3,5,7\}$) & $k=3$ ($p \in \{5,7\}$) | $k=2$: $(-1)^1 R = 1 + p$ ($4, 6, 8$); $k=3$ generic $(1,1,2,3)$: $N = p^2 - 3p + 5$, $(-1)^2 R = 1 + 2p$ ($11, 15$) — exact positive effective trace! | **Smooth non-generic** $(1,2,1,1)$ over $\mathbf{F}_5$ (parallel lines $L_1 \parallel L_2$): smooth yet Weak Lefschetz FAILS ($\dim H^1(\mathbf{G}_m^3)=3 \neq 4=\dim H^1(Y)$), producing **non-effective** $R = -p^2+2p+1 = -14$! |
| **`W3`** | Elliptic curves $E^\circ: y^2 = x^3 + Ax + B$ over $\mathbf{F}_5, \mathbf{F}_7, \mathbf{F}_{11}$, Noether $\pi(x,y)=x$ ($B=2$) | $a_p = (-3, -1, -1)$ ($a_p^2 \le 4p$); $\max|\pi^{-1}(x)| = 2$; Jacobian smooth at all $\mathbf{F}_p$-points; $R_{\text{direct}} = R_{\text{chars}} = (-4, -29, -1)$; $R^2 \le 16(p-1)^2 p^3$ | Jacobian smoothness checker catches singular parameter tuples ($c=0$ on $E/\mathbf{F}_5$, $c=1$ on $E/\mathbf{F}_{11}$) |
| **`W4`** | Higher dim $d=2$ & **char $p = 2$**: $U = \mathbf{A}^2, k=2$, $x_1 y_1 + x_2 y_2 + 1 = 0$ over $\mathbf{F}_2, \mathbf{F}_3, \mathbf{F}_4$ | $K_1 K_1^* = Q^2 I_{Q^2}$ (including over $\mathbf{F}_4$!); $N = Q^3 - Q$; $R = -Q^2 = (-4, -9, -16)$; $(-1)^3 R = +Q^2$ | Confirms proof works unmodified in characteristic $2$ (dot product nondegenerate, no diagonal $x_i^2$) |
| **`W5`** | Lisse rank-1 quadratic sheaf $\mathcal{L}_\chi$ on $\mathbf{G}_m$ over $\mathbf{F}_5, \mathbf{F}_7, \mathbf{F}_{11}$ | $M = 0$; generic $x_1 x_2 + x_1 + x_2 + 2 = 0$ gives $R_{\text{generic}} = R_{\text{chars}} = (10, 0, 0) \ll (p-1)p^{3/2}$ | **Smooth non-generic** $x_1 x_2 + 1 = 0$: $\mathcal{L}_\chi \boxtimes \mathcal{L}_\chi$ trivializes on $Y$, inflating $|R| = p(p-1) = (20, 42, 110)$! Demonstrates sheaf-specific genericity in `lem:good` |
| **`W6`** | `HS-01` rational pole non-cancellation & **`AD-03`** Kummer extension over $\mathbf{F}_5$ | Positive multiplicities: $0$ cancelled poles; Kummer $F T F^{-1} = T^{1/5}$, $(T-I)^2 = 0 \neq T-I$ (unique 1D invariant line), distinct weights $1/5 \neq 1$ | Virtual signed trace $(+1, -1)$ at $\mu = 10$ cancels pole identically ($0$ surviving poles despite $|\mu| = 10$) |

---

## 5. `Proven-Commons/mcproof` & Lean 4 / Mathlib Mechanization Map

Separating elementary algebraic cores (immediately mechanizable in Lean 4 + Mathlib / `mcproof` Family A & B) from currently absent étale-cohomology infrastructure:

| Component | Lean 4 / Mathlib Readiness | Concrete `mcproof` Target |
|---|---|---|
| **`HS-01` & `HS-02` (Lemma 2):** Rational generating function pole radius & $k$-th root tensor amplification | **READY NOW** (Mathlib has `PowerSeries`, `Complex.CauchyIntegral` / `hasSum_geometric_of_norm_lt_one`, `Matrix.charpoly`, `TensorProduct`) | `mcproof` Family A Lean 4 theorem module + exact $\mathbb{Q}(z)$ pole-residue checker |
| **`HS-03` (Lemma 3):** Finite-field path character sum & unitary kernel bound $K_i K_i^* = Q^d I$ | **READY NOW** (Mathlib has `ZMod`, `FiniteField`, `AddChar`, `Matrix.conjTranspose`, `EuclideanSpace`, Cauchy–Schwarz) | High-value standalone Lean 4 lemma (`path_parseval_bound`) — completely self-contained, zero étale cohomology! |
| **Noether fibre cardinality ($\le B$) & `W1..W5` point-count witnesses** | **READY NOW** (`Module.finrank` + CRT for finite-dim $E$-algebras; decidable `Fintype` checks for small $\mathbb{F}_q$) | `mcproof` Family B exact pure-$\mathbb{Q}$ / $\mathbb{Z}[\zeta_p]$ witness checkers |
| **`AD-03` Kummer 2×2 indecomposability lemma** | **READY NOW** (`Matrix (Fin 2) (Fin 2) ℚ` nilpotency + unique 1D invariant subspace) | Crisp negative-control theorem in Lean 4 |
| **Étale cohomology stack (`SG-08..11`, Katz App. A.5):** Grothendieck–Lefschetz trace formula, Künneth, Poincaré duality, Artin vanishing, Deligne generic base change | **NOT YET IN MATHLIB** (multi-year formalization frontier; requires derived étale $\ell$-adic sheaves $D^b_c(X, \overline{\mathbf{Q}}_\ell)$ and six-functor formalism) | Axiomatize cleanly as a minimal 5-axiom interface (no weights, no BBD perversity per `AD-02b`!) to formally verify the *combinatorial/sign assembly* of `SG-08..11` in Lean 4 right now |

---

## 6. Reproducibility & R5 Verification Receipts

- **Standalone 3-mode isolated R4 execution:**
  `python3 -I -O -B -W error alpoge_deligne_certifier.py --json` reproduces [`alpoge_deligne_certificate.json`](alpoge_deligne_certificate.json) byte-for-byte with zero external dependencies and zero floats.
- **R5 test suite:** `python3 -I -O -B -W error test_alpoge_deligne_r5.py` (`5/5` groups OK, including positive controls, singular/non-generic negative controls, and full certificate tamper tests).
- **Aletheia v2.0.0 gates:** Checked via `aletheia audit-check . --strict-ancestors --scripts alpoge_deligne_certifier.py test_alpoge_deligne_r5.py`, `aletheia safety-scan .`, and `aletheia mutate alpoge_deligne_certifier.py --max-mutants 0 --add-cwd`.

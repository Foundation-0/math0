# Mathematical Engine Tomography, Barrier Audit, Executable Oracle & Lean 4.36.0 Companion for `VP ≠ VNP` Over Every Field

**Target:** `anthropics/formal-math/vp-vnp` (commit `11b6c7e3`, Lean `4.33.1` + Mathlib `0df444a3` + `comparator`/`nanoda`, `paper.pdf`, `324` `.lean` files / `72,932` lines).
**Companion Forensics Verification:** Independent trust-boundary scan (R9 11-class static scan, CI `nanoda` receipt `#45272623486`, `1,012/1,012` token match, `87/87` Table 3 symbols).
**Scope & Method:** Pure CPU-only, clean-room, zero-shared-code mathematical tomography, barrier dissection, exact pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_p$ finite-instance verification (`7` independent oracles, `0` floating-point ops), and live kernel-checked **`Lean 4.36.0`** companion certificates (`15` theorems, `0` external imports, `0` warnings, `0` `sorryAx`, strictly standard-only / `[]` axioms).

---

## 1. Executive Summary & 10-Minute Mathematical Roadmap

The `anthropics/formal-math/vp-vnp` repository presents an AI-discovered, Lean-formalized proof of **Valiant's conjecture $\mathrm{VP} \ne \mathrm{VNP}$ and its border strengthening $\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}$ over every field $\mathbb{k}$**, establishing a uniform superpolynomial lower bound:

$$L(\mathrm{HC}_m) > m^{c (\log_2 m)^{1/3}} \quad (\forall\, \mathrm{char}(\mathbb{k})),\qquad L(\mathrm{PERM}_m) > m^{c (\log_2 m)^{1/3}} \quad (\mathrm{char}(\mathbb{k}) \ne 2)$$

for an explicit universal constant $c = 1 / 1600^2$ and a characteristic-dependent, non-effective threshold $m \ge m_0(p)$ (both for exact division-free arithmetic circuits and for approximating circuits over formal Laurent series $\mathbb{k}((\varepsilon))$).

### 1.1 Modular Codebase Decomposition (`324` `.lean` Files / `72,932` Lines)

| Directory | Files | Lines | Exact Mathematical Role |
| :--- | ---: | ---: | :--- |
| `Ov/` | `11` | `1,855` | Multiparty $\mathbb{k}$-tensors, party restrictions, covers, **spectral points** $\varphi$ (`Def A.1`), wire exponents $d_\varphi(u,v)$ & **prices**, hub routing (`Lem A.3`), and **Strassen duality** (`Thm A.6` via Zorn's Lemma). |
| `Nc/` | `236` | `46,094` | Core engine: `Cross/` (Meixner polynomials & crossing-wires identity `Prop B.2`), `Price/` (2-sheet fan ultrafilter averaging, Bruhat–Tits CAT(0) CN inequality `Thm C.1`, $\mathrm{Mat}_\mu(\mathbb{F}_2)$ flat-vs-contracting dichotomy `Thm D.2`), `Rate/` (flat-case circuit lower bound `Prop E.10` / `Thm E.11`), `Hc/` (`Prop E.1` permanent grid & `Prop M.2` characteristic-2 Hamiltonian-cycle XOR-gadget), `Tower/` & `Tow/` ($U_h(\mathbb{F}_2)$ Poincaré inequality `Thm F.6`, Strassen rerouting laws `App. G`, $\mathrm{SL}_h(\mathbb{F}_2[s]/(s^{n+1}))$ coset-tower tree decomposition `Thm H.2`), `Tape/`/`Sort/`/`Uni/` (universal tape automaton & computation cutting `Thm J.4`), `Vp/` (Valiant classes). |
| `NS1/` | `29` | `7,308` | Contracting-case diagonalization engine: low-degree parse-tree unfolding (`Lem K.2`), accelerators (`Lem K.3`), constant postponement (`Lem K.4`), multi-scale transfer (`Prop K.5`), Nullstellensatz finite-field reduction & self-application $V = 1 + V$ (`Thm K.6`), plus Laurent approximate accelerators (`Approx*`, `Prop N.4`). |
| `Paper/` | `43` | `17,448` | One-to-one formal statement interface matching Appendix Q Table 3 (`87/87` paper theorems). |
| Root & `scripts/` | `5` | `227` | `Statement.lean` (public self-contained definitions & 4 headline props + `permanent_over_real`), `Challenge.lean` (5 `sorry` stubs for `comparator`), `Solution.lean` (zero-`sorry` bridges), `scripts/PrintAxioms.lean`. |

### 1.2 The Architecture: Non-Constructive Geometric Dichotomy (`Thm D.2`)

The proof does **not** attack circuits directly with one fixed polynomial invariant. Instead, it equips the tensor category over $\mathbb{k}$ with an intrinsic **CAT(0) metric geometry on party labels** and splits on a non-constructive law of excluded middle (`Thm D.2` / `thm_alt`):

1. **Spectral Points & Prices (`Ov/`, App. A):** A *spectral point* $\varphi$ is a nonnegative, multiplicative, restriction-monotone, subadditive functional on multiparty $\mathbb{k}$-tensors with $\varphi(1) = 1$. On a wire tensor $\langle q \rangle_{uv}$ of dimension $q$ between parties $u, v$, multiplicativity forces $\varphi(\langle q \rangle_{uv}) = q^{d_\varphi(u,v)}$ with $d_\varphi(u,v) \in [0, 1]$. Pointwise limits of rescaled metrics $c \cdot d_\varphi$ ($c \ge 0$) are called **prices**.
2. **Meixner Crossing-Wires Identity (`Prop B.2`, App. B):** To force metric curvature bounds on *every* spectral point simultaneously over *every* field $\mathbb{k}$, the proof introduces a purely **integral** 4-party matrix determinant $\Psi(X) = \det M \in \mathbb{Z}[X]$ built from Meixner orthogonal polynomials $B(r,n) = [t^n](1+t)^r/(1+yt)^{r+1}$ and $C(r,n) = [t^n](1+yt)^r/(1+t)^{r+1}$ ($y = X^2$), indexed by Frobenius symbols $(I, J)$ of fixed size and energy.
   - At $X = 1$, every $(y-1)$-block vanishes and $\Psi(1) = \epsilon \cdot \langle |\Sigma_1| \rangle_{ac} \langle |\Sigma_2| \rangle_{bd}$ (exact **crossing wires**).
   - Near $X = 0$, truncated Meixner orthogonality `(B.1)` $(1-y)\sum_{r<R} y^r B(r,i)B(r,j) \equiv [i=j] y^i \pmod{y^R}$ yields a Schur-complement factorization whose degree-$N$ coefficient has rank $\le (N+1)P(N)$ across $ad \mid bc$.
   - Reciprocity $X^\Theta \Psi(1/X; s_a, s_b, s_c, s_d) = \Psi(X; s_a, s_d, s_c, s_b)$ ($\Theta = 2(e_1 + e_2)$) gives rank $\le (\Theta - N + 1)P(\Theta - N)$ across $ab \mid cd$.
3. **Nonpositive Curvature (`Thm C.1`, App. C):** Applying $\varphi$ to `Prop B.2` produces a 4-point crossing inequality `(B.2)`. Averaging over 2-sheet fans on $\mathbb{Z}^2$ with a free ultrafilter (`hyperfilter`) upgrades this to the **parallelogram law** (`Lem C.2`) and hence the **Bruhat–Tits CAT(0) CN inequality** $|zm|^2 \le \frac{1}{2}|zx|^2 + \frac{1}{2}|zv|^2 - \frac{1}{4}|xv|^2$ (`Thm C.1`). Every price embeds in a complete CAT(0) price space (`Prop C.3`).
4. **The Dichotomy on $\mathrm{Mat}_\mu(\mathbb{F}_2)$ (`Thm D.2`, App. D):** Note carefully that $\mathbb{F}_2$ here is **only an index-label group**, completely independent of the scalar field $\mathbb{k}$! Over random transversal pairs $(W, W')$ in $\mathrm{Mat}_\mu(\mathbb{F}_2)$, the CAT(0) quadrilateral inequality gives $D(\mu)^2 \le \mu D(1)^2$. Thus either:
   - **Contracting Case:** $\exists\, \mu \ge 2,\, 1 \le s < \sqrt{\mu}$ such that $D(\mu) \le s D(1)$ for *every* price on $\mathrm{Mat}_\mu(\mathbb{F}_2)$; **OR**
   - **Flat Case:** Contraction fails for every $\mu \ge 3$. Compactness yields a limit price attaining equality $D(r)^2 = r$ for all $r \le \mu$. Step-by-step bilinearization (`Steps 3–7`) forces $|a, a'|^2 = \mathrm{rk}(a - a')$ on all of $\mathrm{Mat}_\mu(\mathbb{F}_2)$. Its diagonal subcube $\{0,1\}^\mu$ forms Euclidean unit-cube vertices, filled isometrically via the CAT(0) Flat Rectangle theorem (`Lem C.4(f)`), proving that **every finite Euclidean metric is a price**.

---

## 2. Exact Source of the $(\log_2 m)^{1/3}$ Exponent vs. the Contracting Bound

The headline exponent $m^{c(\log_2 m)^{1/3}}$ comes **strictly from the Flat Case (`App. E`)**; the Contracting Case (`App. F–K`) actually yields the asymptotically stronger bound $2^{c(\log_2 m)^2 / \log\log m}$ (so the minimum of the two cases is governed by the flat branch).

### 2.1 Flat Case Mechanism (`App. E` -> $m^{c(\log_2 m)^{1/3}}$)

1. **Complete-Graph Wire Network Polynomial (`E.2`):** On $k$ nodes with $\ell$ bits per edge, $f_{k,\ell} = \sum_\sigma \prod_{a=1}^k x_{a, \sigma_a}$ corresponds to the wire tensor $T_{k,\ell} = \prod_{a<b} \langle 2^\ell \rangle_{(a,b)(b,a)}$ on $k(k-1)$ half-edge parties. For $k=3, \ell=1$, $f_{3,1}$ is literally the `8`-monomial $2\times 2$ matrix-multiplication trilinear form.
2. **Grid-Sum Reduction (`Prop E.1` / `Lem E.3`):** $f_{k,\ell}$ reduces to $\mathrm{PERM}_m$ ($\mathrm{char}\ne 2$, factor $3$) or $\mathrm{HC}_m$ (all $\mathrm{char}$, factor $40$) for $m \approx \theta k^3 \ell 2^{k\ell} \le 2^{2k\ell}$.
3. **Balanced Decomposition & Hub Routing (`Lem E.4` + `Lem A.3`):** VSBR/Hyafil balanced decomposition writes a size-$L$ circuit for $f_{k,\ell}$ as a sum over at most $2^k$ balanced cuts $S \subset [k]$ ($k/3 \le |S| \le 2k/3$), each routed through two hub parties $\pm o_S$ connected by a wire of rank $\le L$.
4. **Euclidean Cube Facet-Center Geometry (`Prop E.10`):** Place half-edge $(a,b)$ ($a < b$) at $+\frac{1}{2} e_a \in \mathbb{R}^k$ and $(b,a)$ at $-\frac{1}{2} e_a$. Every edge has Euclidean length $1$. For any balanced cut $S$, define $w_S = 2 \sum_{a \in S, b \ne a} \mathrm{pos}(a,b) = \sum_a \pm c_a e_a$, where $\sum_a c_a = |S|(k - |S|)$. By the exact integer identity

   $$9|S|(k - |S|) - 2k^2 = (3|S| - k)(2k - 3|S|) \ge 0 \quad (k \le 3|S| \le 2k)$$

   and Cauchy–Schwarz ($k \|w_S\|^2 \ge (\sum_a c_a)^2$), we get $\|w_S\|^2 \ge \frac{4}{81} k^3$, i.e. $\|w_S\| \ge \frac{2}{9} k^{3/2}$. Setting hubs at $\pm o_S = \pm \eta w_S / \|w_S\|$ with $\eta = \frac{2}{9\sqrt{k}}$ yields an exact per-bit distance saving of $2\eta\|w_S\| - k^2 \eta^2 \ge \frac{4}{81} k$.
5. **Sum Overhead & Exact Cubic-to-Quartic Scaling (`Prop E.9` + `Thm E.11`):** Using `Lem E.7` (`lem_few`) and `Prop E.9` ($c g_\varphi(\mathcal{E}) \le \sqrt{k} + \delta$), the $2^k$-term sum overhead costs only $k^{3/2}$ instead of $k^2$, yielding $\log_2(5L) \ge \frac{\ell k^{3/2}}{16}$ whenever $\ell \ge 100\sqrt{k}$. Choosing the minimal threshold **$k = r^2$, $\ell = 100 r$** forces:
   - $\log_2 m \asymp 200 r^3$ (cubic in $r$), while
   - $\log_2 L \ge \Omega(\ell k^{3/2}) = \Omega(r^4)$ (quartic in $r$)!
   - Eliminating $r \asymp (\log_2 m)^{1/3}$ gives $\log_2 L = \Omega((\log_2 m)^{4/3}) = \Omega((\log_2 m)(\log_2 m)^{1/3})$, i.e. **$L > m^{c(\log_2 m)^{1/3}}$**!

### 2.2 Contracting Case Mechanism (`App. F–K` -> $2^{c(\log_2 m)^2 / \log\log m}$)

When prices on $\mathrm{Mat}_\mu(\mathbb{F}_2)$ contract by $s < \sqrt{\mu}$, the proof switches completely from geometric lower bounds to **indirect complexity-theoretic diagonalization**:

1. **Uniform Poincaré Inequality on $U_h(\mathbb{F}_2)$ (`App. F`):** `Lem F.2` factors every upper-right rank-1 block $I + \xi \omega^T \in U_n(\mathbb{F}_2)$ into elementary generators $x_j = I + E_{j,j+1}$ with $\le 4$ occurrences per generator for endpoint-1 vectors ($A B^{-1} x_{k-1} B A^{-1}$) and $\le 16$ in general. Combining `Lem F.1`–`F.3` with almost-orthogonal projections of overlapping windows $[p, p+2u)$ onto CAT(0) fixed-point sets yields a **uniform Poincaré constant $C_0$ independent of $h$** (`Thm F.6`).
2. **Strassen Duality Rerouting Laws (`App. G`) & Coset-Tower Tree Decomposition (`App. H–J`):** `Thm A.6` turns the Poincaré inequality into finitely many algebraic *rerouting laws* over a finitely generated subring $A \subset \mathbb{k}$. Iterating these along the nilpotent coset tower $G_n = \mathrm{SL}_h(\mathbb{F}_2[s]/(s^{n+1}))$ (`Prop H.1`, commutator $[e_{jk}(r), e_{kl}(r')] = e_{jl}(rr')$) rewrites any tensor network as a sum of bounded-depth tree networks (`Thm H.2`), cutting any $\tau$-step universal tape-automaton computation into $v^H$-step pieces listed in $\tau / v^{24}$ steps (`Thm J.4`).
3. **Low-Degree Parse-Tree Accelerators & Diagonalization (`App. K` / `NS1/`):** A small circuit for `PERM`/`HC` computes the clause-sum polynomial $\Phi = \sum_w U_t(w) y^w$ of degree $d \le n \ll t$. `Lem K.2` unfolds homogeneous parts $g^{(i)} = \sum_{g',g''} b_{g,g',g''} \sum_{0<j<i} g'^{(j)} g''^{(i-j)}$ via nondeterministic parse trees recording only constant names (`a_{g,l}`, `b_{g,g',g''}`), giving a $v^H \to v^{H-16}$ **accelerator** (`Lem K.3`). Constant postponement (`Lem K.4`) + scale iteration (`Prop K.5`) + Nullstellensatz reduction mod a maximal ideal (`[Eis95, Thm 4.19]`) reduces to a **finite field $E$** where squaring powers $c^{2^j}$ are eventually periodic. Self-application $P(P)$ of a program that guesses $1$ or runs the accelerator on $x(x)$ forces **$V = 1 + V$ in $E$** (`Thm K.6`), contradicting $1 \ne 0$.

---

## 3. Comprehensive Barrier Audit

| Barrier / Edge Case | Exact Verdict | Load-Bearing Structural Mechanism |
| :--- | :--- | :--- |
| **Rank-Method Barriers** (`[EGOW18]`, `[GMOW19]`) | **Evaded by BOTH branches** | Flat case replaces matrix flattening ranks with **non-explicit Zorn's-lemma Strassen spectral points** $\varphi$ (`prop_gauge`) evaluated on multiparty wire networks; contracting case uses no tensor rank bound on the target polynomial at all. |
| **Algebraic Natural Proofs** (`[FSV18]`, `[GKSS17]`) | **Evaded by BOTH branches** | Flat case relies on non-explicit spectral points (failing constructivity/explicitness); contracting case uses **no polynomial property beyond low degree** and terminates in indirect diagonalization $V = 1 + V$. *(Note: authors explicitly leave relativization `[BGS75]` / algebrization `[AW09]` unanalyzed.)* |
| **Characteristic-2 `perm = det` Collapse vs. `HC` Survival** | **Exact algebraic split (`Prop E.1` vs `Prop M.2`)** | In `Prop E.1`, Row 1 $\times$ Row 2 without $\frac{1}{2}$ equals $2(A_n B_n + A_{\sigma n} C_n) + (A_n^2 + B_n^2 - A_{\sigma n}^2 - C_n^2)$; in $\mathrm{char}=2$ the factor $2$ annihilates the squarefree selector completely (and $\mathrm{perm} = \det \in \mathrm{VP}$). `Prop M.2` replaces permanents by a directed cyclic segment graph with 3-vertex bidirectional XOR gadgets ($a - b - c$), using **only entries in $\{0, 1, W_n(x,r)\}$** with $|V| + |K| + 37|I| \le 39|I| \le 40|I|$ vertices and **zero divisions**. |
| **Border Complexity / $\overline{\mathrm{VP}}$ (`App. N`)** | **Closed over every field (`F((ε))`)** | `Lem N.2` cuts every Laurent constant above $\varepsilon^N$ ($N = 2^L \Delta$) without altering any $\varepsilon^{\le 0}$ output coefficient. Flat case `Lem N.3` absorbs the $(2n\Delta + 1)^{|V|}$ polynomial-in-$n$ cover overhead in the $n$-th root as $n \to \infty$. Contracting case `Prop N.4` applies $\sigma_r: \varepsilon \mapsto \varepsilon^r$ ($r > \max|\exp(\lambda_e)|$) per round to keep error in $\varepsilon E[\varepsilon]$, then extracts $[\varepsilon^0]$ via an exact exponent counter modulo $2^W$. |
| **Pólya Permanent-Sign Obstruction** | **Strictly orthogonal, complementary obstructions** | Exact enumeration certifies that **`0 / 512`** $3\times 3$ sign matrices $S \in \{\pm 1\}^{3\times 3}$ satisfy $\det(S \odot A) = \mathrm{perm}(A)$ over $\mathbb{Z}$ — obstructing *exact-dimension sign-flip reductions* $\mathrm{perm}_3 \to \det_3$. The `vp-vnp` proof establishes superpolynomial lower bounds against *arbitrary* division-free arithmetic and border circuits (allowing arbitrary blowup $m^k$ and arbitrary constants) for `HC_m` (all fields) and `PERM_m` ($\mathrm{char}\ne 2$). Conversely, the border determinantal corollary (`Remark N.6`, Mulmuley–Sohoni) is **not** formalized in Lean. |
| **Determinant (`det`) Failure Point (`Sec. 2.5`)** | **Fails cleanly ONLY at arrows `P`** | `det` has polynomial-size circuits (`[Ber84]`). Every tensor/CAT(0)/circuit step (`C`) applies to arbitrary circuits; the proof fails **solely** because clause sums (`f_{k,\ell}` and $\Phi$) admit no comparable Valiant-style reduction to `det`. |
| **Boolean Circuits Failure Point (`Sec. 2.5`)** | **Fails cleanly ONLY at arrows `C`** | Over $\mathbb{F}_2$, the `Prop M.2` substitutions (`P`) map $\{0,1\}$ to $\{0,1\}$, so `P` is *not* the obstruction. A Boolean circuit for `HC_m` need only compute $g = \mathrm{HC}_m + \sum_i (x_i^2 - x_i) h_i$. Adding Boolean-zero garbage $(x_1^2 - x_1) x_2 x_3$ agrees identically on all $2^3 = 8$ points of $\{0,1\}^3$ yet **completely annihilates** the degree-$\le 3$ formal homogeneous part of $x_1 x_2 x_3$ over $\mathbb{F}_2$, breaking both `lem_balanced` and `lem_lowdeg` (`C`). |

---

## 4. Independent Discovery & Clean-Room Executable Tomography Receipts

All seven core finite mechanisms were re-implemented from scratch in `s75_vp_vnp_mechanism_probe.py` using pure $\mathbb{Z}$, $\mathbb{Q}$ (`fractions.Fraction`), $\mathbb{F}_p$, and exact Laurent polynomial arithmetic (`0` floats, `0` shared code), audited by `verify_s75_vp_vnp.py`, and paired with `15` live kernel-checked theorems in `VpVnpMechanismCerts.lean` (`Lean 4.36.0`, pure `Init`).

### 4.1 Independent Finding: Explicit 5-Point Non-Euclidean Witness for Remark D.3 Already at $\mu = 2$

Remark D.3 notes that outside the contracting case, the price $d(A, B) = \sqrt{\mathrm{rk}(A - B)}$ constructed for $\mu \ge 3$ in `Thm D.2` is not Euclidean. Our exact rational Gram-matrix oracle (`Oracle 2`) located a minimal **5-point witness inside $\mathrm{Mat}_2(\mathbb{F}_2)$** (and hence embedded in $\mathrm{Mat}_\mu(\mathbb{F}_2)$ for every $\mu \ge 2$):

$$\{0,\; E_{00},\; E_{01},\; E_{11},\; E_{00} + E_{11}\}.$$

Under $G_{ij} = \frac{1}{2}(\mathrm{rk}(A_i) + \mathrm{rk}(A_j) - \mathrm{rk}(A_i - A_j))$:

$$2G = \begin{pmatrix} 2 & 1 & 0 & 2 \\ 1 & 2 & 1 & 1 \\ 0 & 1 & 2 & 2 \\ 2 & 1 & 2 & 4 \end{pmatrix},\qquad \det(G) = -\frac{1}{4} < 0.$$

Geometrically, $E_{00}$ and $E_{11}$ are orthogonal unit vectors whose orthogonal sum $E_{00} + E_{11}$ would force $\langle E_{01}, E_{00}+E_{11}\rangle = \frac{1}{2} + \frac{1}{2} = 1$ in any Hilbert space, yet $\mathrm{rk}(E_{01} - (E_{00}+E_{11})) = 2$ forces $G_{24} = \frac{1}{2}$. For $u = (2, -1, 2, -2)^T$, $u^T (2G) u = -2$, i.e. **$u^T G u = -1 < 0$** (certified both in `Oracle 2` and in Lean theorem `S75VpVnpMechanismCerts.remark_D3_rank_metric_non_euclidean`). Remark D.3 restricts to $\mu \ge 3$ only because Step 5 of `Thm D.2` needs $\mu \ge 3$ to establish that $\sqrt{\mathrm{rk}(A-B)}$ is a *price*.

### 4.2 Summary of All 7 Executable Oracles (`s75_vp_vnp_certificate.json`)

Canonical payload SHA-256: `8391bbc2bad5063761ba9eaede41c236a8ce048c70ebb6524bc854d776cb3979` (`7/7` PASS, runtime `~0.055s`).

| # | Oracle | Paper Anchor | Exact Verified Finite Witnesses |
| :-: | :--- | :--- | :--- |
| 1 | `probe_meixner_crossing_identity` | `App. B`, `Prop B.2`, `(B.1)` | `36/36` reciprocal checks ($0 \le r,n \le 5$); `216/216` exact truncated orthogonality checks ($1 \le R \le 6, 0 \le i,j \le 5$); full 4-party $4\times 4$ $\mathbb{Z}[X]$-matrix determinant $\Psi(X)$ on $\Sigma_1 = \Sigma_2 = \{(\{0\},\{1\}),(\{1\},\{0\})\}$ ($\Theta = 16$): exact $X=1$ crossing wires (`4/16` matched tuples, uniform $\epsilon = +1$), `16/16` exact reflection identities $X^{16}\Psi(1/X; s_a,s_b,s_c,s_d) = \Psi(X; s_a,s_d,s_c,s_b)$, and exact $ad \mid bc$ rank profile `[1, 0, 3, 0, 4, ..., 4]` (interpolating live from rank `1` at $X=0$ through rank `4` crossing wires at $X=1$ to $ab \mid cd$ rank `1` at $X=\infty$)! |
| 2 | `probe_cat0_mat_f2_dichotomy` | `App. C–D`, `Thm C.1`, `Thm D.2`, `Rem D.3` | Exact rank histograms $\mathrm{Mat}_2(\mathbb{F}_2) = [1, 9, 6]$ (`16`) and $\mathrm{Mat}_3(\mathbb{F}_2) = [1, 49, 294, 168]$ (`512`); `64/64` diagonal subcube $\{0,1\}^3$ pairs match Euclidean squared distance; Bruhat–Tits CN equality on $\mathbb{R}^2$ vs strict tree gap `2`; Remark D.3 non-Euclidean witness $\det(G) = -1/4$, $u^T G u = -1$. |
| 3 | `probe_flat_case_perm_and_hub_bounds` | `App. E`, `Prop E.1`, `f_{3,1}`, `Prop E.10`, `Thm E.11` | Exact $9\times 9$ `Prop E.1` permanent equals direct grid sum `31075` over $\mathbb{Q}$, `1` over $\mathbb{F}_3$, `0` over $\mathbb{F}_5$, while 2-cleared matrix collapses to `0 mod 2` against true odd sum `1 mod 2`; `f_{3,1}` has `8` trilinear monomials; `334/334` balanced cuts ($k=3..8$) satisfy $81\|w_S\|^2 / k^3 \ge 21/4 > 4$; `5/5` exact $r$-invariant cubic-to-quartic scaling checks ($125/819200000$). |
| 4 | `probe_char2_perm_vs_hc_gadgets` | `App. M`, `Prop M.2` & Pólya Sign Map | Exact $\mathbb{F}_2$ separation on $3\times 3$ and $4\times 4$ matrices: `det = perm = 0`, `HC = 1`; Pólya obstruction independently re-verified (`0/512` $3\times 3$ sign maps); full verbatim `39`-vertex directed `Prop M.2` XOR-gadget graph (`|I|=1, |V|=1, |K|=1`) has entries strictly in $\{0, 1, W_0(x,r)\}$ and exact `HC = 27 == 27` over $\mathbb{Z}$ (`1` in $\mathbb{F}_2$, `0` in $\mathbb{F}_3$, `2` in $\mathbb{F}_5$, zero division by 2!). |
| 5 | `probe_contracting_unitriangular` | `App. F & H`, `Lem F.2`, `Prop H.1` | Exhaustive verification of `Lem F.2` generator words across all `95` nonzero rank-1 upper-right blocks in $U_4(\mathbb{F}_2)$ & $U_5(\mathbb{F}_2)$ (`44` endpoint-1 pairs achieving tight max multiplicity `4`; all `95` achieving tight max multiplicity `16`); `54/54` exact commutators $[e_{jk}(r), e_{kl}(r')] = e_{jl}(rr')$ in $\mathrm{SL}_3(\mathbb{F}_2[s]/(s^3))$. |
| 6 | `probe_lowdeg_parse_tree_and_diag` | `App. K`, `Lem K.2`, `Sec. 2.5`, `Thm K.6` | Exact `Lem K.2` chain-sum & parse-tree recursion on a 9-gate nonlinear circuit with squaring gate matches all homogeneous parts `deg 0..5` across all four rings $\mathbb{Z}, \mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5$; Section 2.5 Boolean garbage agrees on `8/8` bits while annihilating `deg <= 3` (`1 -> 0` terms); finite-field squaring periods verified (`F_3: 1, F_5: 1, F_7: 2`). |
| 7 | `probe_border_laurent_closure` | `App. N`, `Lem N.2`, `Lem N.3`, `Prop N.4` | Genuine $1/\varepsilon$-pole border circuit verified under `Lem N.2` cutoff $N = 2^L \Delta = 16$ over both $\mathbb{Z}$ and $\mathbb{F}_2$ (exact $\varepsilon^{\le 0}$ preservation); `Lem N.3` cover inequality $129^4 = 276{,}922{,}881 < 2^{32} = 4{,}294{,}967{,}296$; `Prop N.4` $\sigma_3$ error isolation (`min_exp = 0`, $[\varepsilon^0] = 7$) and mod-$2^4$ exponent counter extracting exact $[\varepsilon^0] = 17$. |

### 4.3 Live Kernel-Checked `Lean 4.36.0` Companion Certificates (`VpVnpMechanismCerts.lean`)

Verified live via `verify_s75_vp_vnp.py --verify-lean --json` (`static_clean: true`, `rc = 0`, `stderr = ""`, `0` warnings, `0` `sorryAx`, `0` custom axioms, `0` external imports):

- **Zero-Axiom Constructive Theorems (`[]`):** `prop_E1_char2_collapse`, `sec25_boolean_garbage_vanishes_on_bits`, `sec25_boolean_garbage_corrupts_formal_deg3`.
- **`[propext]` Only:** `remark_D3_rank_metric_non_euclidean`, `char2_hc3_separates_from_perm3_and_det3`, `char0_perm3_separates_from_det3`, `thm_E11_exponent_scaling`.
- **`[propext, Quot.sound]`:** `prop_E1_squarefree_factor2`, `prop_E10_balanced_cut_bound`, `lem_N2_cutoff_preserves_nonpositive_exponents`, `thm_K6_diagonalization_int`, `thm_K6_diagonalization_mod`.
- **`[propext, Classical.choice, Quot.sound]`:** `meixner_reciprocal_verified_5x5`, `meixner_orthogonality_verified_R5`, `lem_F2_U4_rank1_word`.
- **Total:** **`15 / 15`** theorems live-verified by Lean `4.36.0` kernel.

---

## 5. Honest Epistemic Status & Human-Verification Obligations

Combining our mechanism tomography with independent trust-boundary forensics, the honest epistemic status of `anthropics/formal-math/vp-vnp` is:

1. **Kernel & Mechanism Soundness:** Both the formal trust boundary (`0` R9 soundness findings across `323/323` non-`Challenge` files, corroborated by live CI `nanoda` run `#45272623486`) and every core finite algebraic identity across Appendices B–N pass independent clean-room verification without defect.
2. **Remaining Human-Verification & Mathematical Obligations:**
   - **Zero Human Mathematical Review:** Per `paper.pdf` Section 3 / Appendix Q, no human mathematician has yet checked `Statement.lean` or `paper.pdf` line-by-line against every nuance of textbook Valiant theory.
   - **Non-Constructive Dichotomy (`Thm D.2`):** The proof does not determine whether $\mathbb{R}$ or $\mathbb{C}$ satisfies the flat hypothesis, the contracting hypothesis, or both — resolving this dichotomy is itself an open mathematical problem.
   - **Non-Effective Threshold $m_0(p)$:** Due to `Classical.choice` / compactness / `hyperfilter`, $m_0(p)$ is non-effective in the contracting case (though uniform across fields of equal characteristic $p$).
   - **Four Lean-Only Program-Correctness Proofs:** `Prop I.1`, `Thm H.2(d,e)`, `Thm J.3`, and `Prop N.4` rely on machine-checked Lean program semantics that are only sketched to exponent level in `paper.pdf`.
   - **Unformalized Corollaries:** `Remark N.6` (border determinantal complexity / Mulmuley–Sohoni conjecture) is explicitly **not** formalized in Lean (relying externally on Berkowitz `[Ber84]` and Alder/Bürgisser Zariski closure); likewise Strassen division elimination is external to the division-free `Computes` definition.
   - **Local Full-Repo Rebuild:** Our local workstation is pinned to Lean `4.36.0`; an optional future isolated `v4.33.1` + `Mathlib 0df444a3` + `nanoda` local rebuild would remove reliance on GitHub Actions CI receipt `#45272623486`.

---

## 6. Verification Suite Receipts & Frozen Manifest

All gates below executed post-last-edit with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1` (`0` GPU touch, `0` GitHub writes):

- **Three-Mode `-I` Parity (`-I -B`, `-I -O -B`, `-I -B -W error`) + `PYTHONHASHSEED=42 -B` + `umask 077` + Simulated CI (`chmod 644 s75_vp_vnp_certificate.json`):** **`5 / 5` environments × `13 / 13 OK` (`65 / 65 PASS`)** plus bit-identical `--check`, `--standalone`, and `--verify-lean` receipts.
- **Genuine 4-Surface Adversarial Fuzzer (`CLI` 25 + `FR1` 19 + `FR0` 19 + `SEC` 19):** **`82 / 82 PASS` (`bypasses = 0, crashes = 0`)** covering `verify_s75_vp_vnp.py --check`, `verify_certificate_dict(..., full_replay=True)`, `verify_certificate_dict(..., full_replay=False)`, and `secondary_audit(...)`.
- **Live Guard/Boundary Mutation (`aletheia mutate`, `verify_s75_vp_vnp.py`, `--workers 4 --timeout 180 --max-mutants 0`):** **`PASS 137 / 137 (100.0%)`, `truncated = False, survived = 0, timeout = 0, null_mutant = passed`**.
- **Null-Mutant-Verified Whole-File DFS AST `BoolOp` (`OP_SWAP + SUBCOND_DEL`, both `.py` production files):** **`null_controls = 2 / 2, killed = 248 / 248 (100.00%), survivors = 0, timeouts = 0`** (`s75_vp_vnp_mechanism_probe.py: 57/57`, `verify_s75_vp_vnp.py: 191/191`).
- **Live `Lean 4.36.0` Kernel, Multi-Line `#print axioms` & R9+ Static Scanner (`--verify-lean --json`):** **`15 / 15` theorems `PASS`, `0` warnings, `0` `sorryAx`**, with live E2E exploit regression suite rejecting `import Lean` + `elab`, `debug.skipKernelTC`, `decide (native := !false/(true))`, `initialize`, `dbg_trace` native splices, `'...'` char-literal quote-parity spoofing, `r#"""#` raw-string axiom smuggling, and extra/duplicate `#print axioms` lines.

### Frozen 6-File Artifact Manifest

| File | Lines | Bytes | Mode | SHA-256 |
| :--- | ---: | ---: | :---: | :--- |
| `VpVnpMechanismCerts.lean` | `374` | `15663` | `0o644` | `b33414b53d4cb82c4c2d47513871d9f4cf74d724e44cdd1b1e4f4edbe296fa67` |
| `s75_vp_vnp_certificate.json` | `1` | `1982` | `0o600` | `7e383c1cfe04937277be7f8f4ff4305984d51ecd81858eebdd67e45238823224` |
| `s75_vp_vnp_mechanism_probe.py` | `1513` | `60946` | `0o644` | `0eff96a5b74ec7d6c8ae649313c1e00bbf05871798807bcd556ec820dab8f67a` |
| `test_s75_vp_vnp_r5.py` | `1200` | `66110` | `0o644` | `5ebcf64f9808dc029ff6d77996e222d024f30705e67fa3651a761bf6395dfba7` |
| `verify_s75_vp_vnp.py` | `1366` | `55190` | `0o644` | `3d8f219ab26b03f8776b8c242156583fb5e2dea65dd0f9416d5d801eb953a261` |
| `VP_VNP_MECHANISM_REPORT.md` | — | — | `0o644` | *(self; SHA-256 recorded externally upon freeze)* |

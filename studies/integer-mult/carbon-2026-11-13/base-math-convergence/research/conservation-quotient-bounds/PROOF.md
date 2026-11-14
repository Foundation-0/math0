# The Anchored Conservation Quotient: Base-Mathematics Unification of Transport Cuts, Orthogonal Frames, Null-Space Decoders, and Recursive Power-Sum Bounds

**Scoped Mathematical & Algorithmic Convergence Package for [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds)**  
**Pinned Base**: `main` at `e545235` (Priority Revision 8; Selected Frontier [`#7000`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/selected-result.json), $\kappa = \frac{363005817}{100000000000} = 0.00363005817$)  
**Certificate SHA-256**: `c31c51ac130d853dcaad64abce3bd13f9b9c3ffb282410637552c293ebfd492e`  
**License**: Apache-2.0

## 1. Thesis & Scope Boundary

Four independent algorithmic campaigns—discrete token-routing lower bounds in [`ahrazzle/soko`](https://github.com/ahrazzle/soko), certified neural morphogenesis in [`Moissanite-Labs/weft`](https://github.com/Moissanite-Labs/weft), multi-probe compartment identifiability in [`Foundation-0/project-asma`](https://github.com/Foundation-0/project-asma), and sub-$n \log n$ reversible circuit compilation in [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) ([`fdn0.org/research/integer-multiplication/`](https://fdn0.org/research/integer-multiplication/))—turn out to instantiate **one exact algebraic object over $(\mathbb{Z}, \mathbb{Q})$**: the **Anchored Conservation Quotient**.

Per [`AGENTS.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/AGENTS.md) and [`CONTRIBUTING.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/CONTRIBUTING.md), we state the exact scope boundary up front:
- **What this package proves and certifies**: Four self-contained theorems in base mathematics ($\mathbb{Z}, \mathbb{Q}$), backed by a solver-free `fractions.Fraction` checker (`check_certificate.py`), an independent C11 `__int128` verifier (`c11_base_verifier.c`), 18 re-hashed semantic tamper controls (`verify.py`), and a zero-`sorry` Core Lean 4 algebraic module (`formal/BaseMathConvergence.lean`).
- **What this package does NOT claim**: It does not claim a new selected global $\kappa$ above Frontier `#7000`, does not materialize the all-size Turing multiplier, and notes explicitly that `BaseMathConvergence.lean` was verified via token-stream surface audit in this container (`lake env lean` remains an explicit downstream check).

| Invariant Layer | [`ahrazzle/soko`](https://github.com/ahrazzle/soko) | [`Moissanite-Labs/weft`](https://github.com/Moissanite-Labs/weft) | [`Foundation-0/project-asma`](https://github.com/Foundation-0/project-asma) | [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) | Base-Mathematics Law ($\mathbb{Z}, \mathbb{Q}$) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **I. Bottleneck Capacity** | 9-Flow + Picard–Queyranne min-cut | Unit-capacity Dinic routing + mitosis trigger | Compartment flux conservation | Staged helper/wire cut-rank floor ([Discussion `#5470`](https://github.com/CrocSwap/integer-mult-bounds/discussions/5470)) | $\operatorname{rank}_{\mathbb{F}}(M) \le \min_{(U, \bar{U})} c(U, \bar{U})$ |
| **II-A. Protected Subspace** | Prefix nogood invariance | Anchor null-space $\Delta W \in \ker(X_{\text{anchor}})$ | Orthogonal LH channel isolation (`P03`) | Reverse-frame $H$-complement $U_z^{\perp_H}$ ([`cross-point-sharing.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/docs/research/cross-point-sharing.md)) | $\mathbb{Q}^r = U_z \oplus U_z^{\perp_H} \iff \det(B_z^T H B_z) \neq 0$ |
| **II-B. Kernel Closure** | Non-stuttering CNF clauses | `[X_dom; X_tail; Q_Haar]` MPDI gate | Multi-probe identifiability matrix | Persistent 8-field kernel + cache decoder ([Discussion `#5470`](https://github.com/CrocSwap/integer-mult-bounds/discussions/5470)) | $L \begin{bmatrix} P \\ C \end{bmatrix} = I_N \implies \ker(P) \cap \ker(C) = \{0\}$ |
| **III. Contraction Receipt** | Cost-partitioned LP lower bound | Fixed-radix $10^{-6}$ Farkas receipt | Exact Farkas noise margin $\varepsilon^* = 0.2156$ | Rational power-sum bill + Karamata–Farkas ceiling ([`autoresearch.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/autoresearch.md)) | $A^T y \le L(a^*),\; b^T y \ge W(1-\varepsilon) \implies \operatorname{bill}(a^*) \ge 1$ |

## 2. Theorem I — Universal Factorized Cut-Rank & Picard–Queyranne Lattice

**Theorem 1 (Search-Free Cut-Rank Impossibility & Canonical Bottleneck Interval).**  
Let $G = (V, E)$ be a finite acyclic linear circuit over an arbitrary field $\mathbb{F}$ with input terminals $S_{\text{in}}$ ($|S_{\text{in}}| = d_{\text{in}}$), output terminals $T_{\text{out}}$ ($|T_{\text{out}}| = d_{\text{out}}$), and induced input-to-output linear map $M \in \mathbb{F}^{d_{\text{out}} \times d_{\text{in}}}$.
1. *Factorization Bound*: For any vertex cut $(U, \bar{U})$ with $S_{\text{in}} \subseteq U$ and $T_{\text{out}} \subseteq \bar{U}$, let $E(U, \bar{U}) = \{(u, v) \in E : u \in U, v \in \bar{U}\}$ have cardinality $c$. Because $G$ is acyclic and every directed path from $S_{\text{in}}$ to $T_{\text{out}}$ crosses $E(U, \bar{U})$, the wire values on $E(U, \bar{U})$ are linear forms $B_U x \in \mathbb{F}^c$ and the terminal outputs depend linearly on $E(U, \bar{U})$ via $y = A_{\bar{U}}(B_U x)$. Thus $M = A_{\bar{U}} B_U$ and $\operatorname{rank}_{\mathbb{F}}(M) \le c$.
2. *Submodular Lattice Interval*: Cut capacity $c(U) = |E(U, \bar{U})|$ is submodular: $c(U) + c(W) \ge c(U \cap W) + c(U \cup W)$. Hence minimum $S_{\text{in}}$-$T_{\text{out}}$ cuts form a finite distributive lattice $[U_{\min}, U_{\max}]$ under inclusion, uniquely bracketed by the source-minimal cut $U_{\min}$ (earliest mandatory helper-climb frame) and sink-minimal cut $U_{\max}$ (latest mandatory helper-climb frame).
3. *Zero-Solver Verification*: Deleting $E(U, \bar{U})$ and verifying $T_{\text{out}} \cap \operatorname{Reach}_{G \setminus E(U, \bar{U})}(S_{\text{in}}) = \emptyset$ with $|E(U, \bar{U})| < r_{\text{target}}$ proves $\operatorname{rank}_{\mathbb{F}}(M) < r_{\text{target}}$ in $O(|V| + |E|)$ integer steps without trusting any max-flow implementation.

## 3. Theorem II — Indefinite Reverse-Frame Duality & Closed-Form `Helper300` Decoder

### 3.1 Indefinite Bilinear Nondegeneracy ([`docs/research/cross-point-sharing.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/docs/research/cross-point-sharing.md))

**Theorem 2A (Indefinite Reverse-Frame Galois Duality).**  
Let $H \in \mathbb{Q}^{r \times r}$ be symmetric with $\det H \neq 0$ (possibly indefinite on mixed cross-point spans). For full-column-rank $B_z \in \mathbb{Q}^{r \times k}$ spanning $U_z$:
1. $\mathbb{Q}^r = U_z \oplus U_z^{\perp_H} \iff \det(B_z^T H B_z) \neq 0$.
2. When $\det(B_z^T H B_z) \neq 0$ and $\det(B_w^T H B_w) \neq 0$, the exact rational $H$-orthogonal projectors $P_z = B_z (B_z^T H B_z)^{-1} B_z^T H$ and $P_w = B_w (B_w^T H B_w)^{-1} B_w^T H$ satisfy $P^2 = P$, $H P = P^T H$, and:
   $$U_z \subseteq U_w \iff P_w B_z = B_z \iff (I_r - P_z)(I_r - P_w) = I_r - P_w \iff U_w^{\perp_H} \subseteq U_z^{\perp_H}.$$
3. *Certified Isotropic Obstruction*: On $H = \operatorname{diag}(1, 1, 1, -1, -1)$, $B_{\text{iso}} = (1, 0, 0, 1, 0)^T \neq 0$ has $B_{\text{iso}}^T H B_{\text{iso}} = 0$, so $B_{\text{iso}} \in U_{\text{iso}} \cap U_{\text{iso}}^{\perp_H}$, constructively proving why scalar sum interning across groups requires explicit Gram determinant certification.

### 3.2 Closed-Form Ring Decoder for the Persistent+Cache Endpoint ([Discussion `#5470`](https://github.com/CrocSwap/integer-mult-bounds/discussions/5470))

In Discussion `#5470`, the normalized persistent endpoint and retained cache map take the block form:
$$P_{\text{persist}}(x, y, h) = \begin{bmatrix} x - y + \frac{1}{4} M E h \\ y \\ (I_m - B^T E) h \end{bmatrix}, \qquad C_{\text{cache}}(x, y, h) = E h - M^T y, \qquad E B^T = I_k \; (k = 8).$$

**Theorem 2B (Persistent Null-Space & Unconditional $\mathbb{Z}[\frac{1}{4}]$ Left-Inverse Theorem).**
1. *Exact $k$-Field Persistent Kernel*: For $K_{\text{null}}(z) = \begin{bmatrix} -\frac{1}{4} M z & 0 & (B^T z)^T \end{bmatrix}^T$ ($z \in \mathbb{Q}^k$), $E B^T = I_k$ implies $P_{\text{persist}}(K_{\text{null}}(z)) = 0$ and $C_{\text{cache}}(K_{\text{null}}(z)) = z$. Thus $\dim \ker(P_{\text{persist}}) \ge k = 8$ (identical in structure to masked null-space updates $\Delta W \in \ker(X_{\text{dom}})$ in [`Moissanite-Labs/weft`](https://github.com/Moissanite-Labs/weft)).
2. *Explicit Matrix-Inversion-Free Post-Decoder*: Define the polynomial block operator $L \in \mathbb{Z}[\frac{1}{4}]^{(2n_x + m) \times (2n_x + m + k)}$:
   $$L = \begin{bmatrix} I_{n_x} & I_{n_x} - \frac{1}{4} M M^T & 0 & -\frac{1}{4} M \\ 0 & I_{n_x} & 0 & 0 \\ 0 & B^T M^T & I_m & B^T \end{bmatrix}.$$
   Then for **arbitrary** dimensions $(n_x, m, k)$ and **arbitrary** matrices $(M, B, E)$ over any ring containing $\frac{1}{4}$ (or over $\mathbb{Z}$ after scaling by $4$, proved in `BaseMathConvergence.lean`):
   $$L \begin{bmatrix} P_{\text{persist}} \\ C_{\text{cache}} \end{bmatrix} = I_{2n_x + m}.$$
   *Proof*: Substituting $Y = y$ and $C + M^T Y = E h$ gives $H_{\text{out}} + B^T(C + M^T Y) = (h - B^T E h) + B^T E h = h$ and $X + Y - \frac{1}{4} M(C + M^T Y) = (x - y + \frac{1}{4} M E h) + y - \frac{1}{4} M E h = x$. $\square$

## 4. Theorem III — Rational Power-Sum Enclosures, the Two-Geometry Law in Aska PR `#469`, and Farkas Histogram Ceilings

### 4.1 Zero-Float Directed Rational Enclosure of $(r/m)^{1-a}$

For integers $1 \le r < m$ and rational saving $a \in (0, \frac{1}{2}) \cap \mathbb{Q}$, choose $k \in \mathbb{Z}_{\ge 0}$ so $u = \frac{m}{r \cdot 2^k} \in [\frac{2}{3}, \frac{4}{3}]$ and $z = \frac{u-1}{u+1} \in [-\frac{1}{5}, \frac{1}{7}]$. Using elementary geometric-series remainder bounds:
$$\left| \ln\!\left(\frac{1+z}{1-z}\right) - 2 \sum_{j=0}^{K-1} \frac{z^{2j+1}}{2j+1} \right| \le \frac{2 |z|^{2K+1}}{(2K+1)(1 - z^2)}, \qquad 0 \le e^x - \sum_{j=0}^{J-1} \frac{x^j}{j!} \le \frac{x^J}{J!} \frac{J+1}{J+1 - x} \quad (0 \le x \le 1),$$
we obtain pure `fractions.Fraction` brackets $[L_r(a), U_r(a)] \subset \mathbb{Q}$ of width $< 10^{-32}$ at $K = 26, J = 26$, locking all 18 published digits of DreamingOfClouds `PR #450` ($\kappa = 0.001347744547714835$), `Aska PR #464` ($\kappa = 0.001347744550711765$), and `Aska PR #469` ($\kappa = 0.001350580884553120$) from [`fdn0.org/research/integer-multiplication/`](https://fdn0.org/research/integer-multiplication/).

### 4.2 The Dual Subadditivity–Concavity Law Inside Aska PR `#469`

**Theorem 3A (Opposite Signs of Coalescing vs. Mean-Preserving Contraction).**  
For $a \in (0, 1)$, let $f_a(r) = r^{1-a}$ on $r > 0$. Because $f_a(0) = 0$, $f_a'(r) = (1-a)r^{-a} > 0$, and $f_a''(r) = -a(1-a)r^{-1-a} < 0$:
1. *Coalescing ($\Delta N < 0, \sum r \Delta n_r = 0$) Strictly Saves*: Merging smaller child jobs $r_1, r_2 > 0$ into $r_1 + r_2$ changes the raw sum by $(r_1 + r_2)^{1-a} - r_1^{1-a} - r_2^{1-a} < 0$ by strict subadditivity of concave $f_a$.
2. *Mean-Preserving Contraction ($\Delta N = 0, \sum r \Delta n_r = 0$) Strictly Costs*: Replacing $(r - \delta, r + \delta)$ by $(r, r)$ ($0 < \delta < r$) changes the raw sum by $2 r^{1-a} - (r-\delta)^{1-a} - (r+\delta)^{1-a} > 0$ by strict Jensen concavity!

**Exact Decomposition of Aska PR `#469` ($m = 78, W = 1200$)**:  
The 113-move gate-frame retiming $\Delta n = n_{\#469} - n_{\#450}$ splits into two exact work-conserving moves ($\sum r \Delta n_r = 0$):
- **Sub-move A on $\{1, 2, 3\}$**: $\Delta n_{1,2,3} = (-649, +77, +165)$ ($\Delta N = -407$ jobs, $-649 + 154 + 495 = 0$), a pure coalescing move reducing $\operatorname{bill}(a)$ by $\approx 1.1584 \times 10^{-5}$.
- **Sub-move B on $\{5, 6, 7\}$**: $\Delta n_{5,6,7} = (-99, +198, -99)$ ($\Delta N = 0$ jobs, $-495 + 1188 - 693 = 0$), a **pure mean-preserving contraction** that *paid a concavity penalty* of $+2.8013e-8$ on $\operatorname{bill}(a)$—witnessed at $a \to 0^+$ by the exact integer inequality $6^{12} = 2,176,782,336 < 2,573,571,875 = 5^5 \cdot 7^7$! Pruning Sub-move B lifts $\kappa$ to `$0.001350654975655192` (`+6.89e-9` higher) with fewer retimed moves.

### 4.3 Analytic Farkas Dual Ceiling on Constrained Child Histograms

**Theorem 3B (Exact Rational Farkas Histogram Ceiling).**  
Given linear cut-rank and leaf-interface constraints $A n \ge b$ on $n \in \mathbb{Q}_{\ge 0}^{|R|}$ and rational lower enclosures $L_r(a^*) \le (r/m)^{1-a^*}$, any dual vector $y \in \mathbb{Q}_{\ge 0}^k$ satisfying $A^T y \le L(a^*)$ and $b^T y \ge W(1 - \varepsilon_{\text{fee}})$ certifies in two rational dot products that **every** legal circuit in $\\{n \ge 0 : A n \ge b\}$ obeys $\operatorname{bill}(a^*) \ge 1$, bounding $\kappa < \frac{a^*}{1 + a^*}$ (certified at $\kappa_{\text{ceil}} = 0.001467442448$ for the $(93192, 25000, 58432, 82874)$ cut-rank interface polytope).

# General $\mathrm{SL}_2(\mathbb{Z})$ Cubic-Repair Frames, Quadratic-Norm Leapfrog, and Unconditional 2-Adic Monic Obstructions (no $\kappa$)

## Summary of Contributions

Building on [PR #6653](https://github.com/CrocSwap/integer-mult-bounds/pull/6653), [PR #7475](https://github.com/CrocSwap/integer-mult-bounds/pull/7475), [PR #7478](https://github.com/CrocSwap/integer-mult-bounds/pull/7478), and [PR #7479](https://github.com/CrocSwap/integer-mult-bounds/pull/7479) in [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds), this package establishes three exact algebraic/number-theoretic theorems and 20 strictly new constructive 3-query dyadic cubic repair certificates for the deferred cubic-reader defect:

$$D_r(A, B) = \sum_{i=0}^{r-1} (A + i B)^3 - r A^3 = 3 S A^2 B + S (2r - 1) A B^2 + S^2 B^3, \qquad S = \frac{r(r-1)}{2}.$$

1. **Theorem 1 (Dyadic-to-$\mathrm{SL}_2(\mathbb{Z})$ Equivalence — resolves the dyadic-direction part of [#6653](https://github.com/CrocSwap/integer-mult-bounds/pull/6653) Open Question 1):** Any 3-query dyadic representation $D_r(A,B) = \sum_{j=0}^2 \tilde{q}_j (\tilde{u}_j A + \tilde{v}_j B)^3$ with arbitrary dyadic coefficients $(\tilde{u}_j, \tilde{v}_j) \in \mathbb{Z}[1/2]^2 \setminus \{(0,0)\}$ and $\tilde{q}_j \in \mathbb{Z}[1/2]$ reduces immediately to primitive integer source rows $(u_j, v_j) \in \mathbb{Z}^2$ ($\gcd(u_j, v_j) = 1$, completable to $\mathrm{SL}_2(\mathbb{Z})$ shear words) with dyadic weights $q_j \in \mathbb{Z}[1/2]$.
2. **Theorem 2 (Quadratic-Field Norm-Square Law over $\mathbb{Q}(\sqrt{K})$):** In shifted coordinates $w_j = 6 v_j - (2r - 1) u_j$ with $K = 3(2r^2 - 2r - 1)$, apolarity of three distinct projective directions $[u_j : v_j]$ to $D_r$ is equivalent to $u_0 w_1 w_2 + u_1 w_0 w_2 + u_2 w_0 w_1 + K u_0 u_1 u_2 = 0$, i.e. $z_0 z_1 z_2 \in \mathbb{Z}$ for $z_j = w_j + u_j \sqrt{K} \in \mathbb{Z}[\sqrt{K}]$. Hence $(w_0^2 - K u_0^2)(w_1^2 - K u_1^2)(w_2^2 - K u_2^2) = M_{\mathrm{re}}^2$ is identically an integer square, and for every permutation $(i, j, k)$ of $(0, 1, 2)$,
   $$144\, q_j q_k\, \Delta_{ij} \Delta_{ik} \Delta_{jk}^2 = r^2 (r-1)^2 (K u_i^2 - w_i^2), \qquad \Delta_{ab} = u_a v_b - u_b v_a.$$
   Every odd prime dividing $\Delta_{jk}$ must divide $3 r(r-1)(K u_j^2 - w_j^2)$.
3. **Theorem 3 (2-Adic Odd-$u$ Collision Obstruction & Unconditional Monic 4-Query Lower Bound — directly answers [#7479](https://github.com/CrocSwap/integer-mult-bounds/pull/7479) Open Question 1):** Whenever $S = r(r-1)/2$ is odd ($r \equiv 2, 3 \pmod 4$), no three odd-$u$ primitive frames can collide modulo $2$ (otherwise $e_2(w/u) \equiv 3 \not\equiv -K \equiv 7 \pmod 8$). Under the monic shear contract $u_0 = u_1 = u_2 = 1$ ($L_j = A + c_j B$ of [#6653](https://github.com/CrocSwap/integer-mult-bounds/pull/6653)), ordering $c_0 \not\equiv c_1 \equiv c_2 \pmod 2$ forces $x = c_1 - c_0$ and $y = c_2 - c_0$ to be odd, $q_0 \in \mathbb{Z} \setminus \{0\}$ to be a non-zero integer, $\min(|x|, |y|) < 2S = r(r-1)$, and $(w_0 + 3x)(w_0 + x + 4y) = 3x^2 - M$ ($M = 2r^2 - 2r - 1$), so $y \mid \mathrm{odd}(S(3x^2 - M))$ when $3x^2 \neq M$ and $y \mid \mathrm{odd}(Sx)$ when $3x^2 = M$. Exhausting these exact finite divisor sets across all 99 odd-$S$ arities in $3 \le r \le 200$ proves unconditionally over all of $\mathbb{Z}^3$ that **82 of the 99 odd-$S$ arities — including $r \in \{15, 22, 30, 31, 34, 39, 43, 58\}$ — admit zero monic 3-query dyadic repairs**, establishing a sharp 4-query lower bound under the monic shear contract despite [#7479](https://github.com/CrocSwap/integer-mult-bounds/pull/7479)'s solvability modulo every odd $m > 1$.
4. **20 Strictly New Constructive 3-Query Dyadic Certificates ($r \le 192$):** Using Theorem 2 as an $O(1)$-per-step Euclidean leapfrog filter, we certify 20 strictly new non-pure-$B$ arities outside [#6653](https://github.com/CrocSwap/integer-mult-bounds/pull/6653) and [#7475](https://github.com/CrocSwap/integer-mult-bounds/pull/7475), including **5 first-ever multi-non-unit general-frame witnesses** ($r \in \{84, 105, 121, 132, 148\}$ where two source rows have $u_j > 1$).

## Certified New 3-Query Dyadic Witnesses ($r \le 192$)

| Arity $r$ | Non-unit $u_j$ | Primitive rows $(u_0,v_0), (u_1,v_1), (u_2,v_2)$ | Dyadic weights $(q_0, q_1, q_2)$ | Total $\mathrm{SL}_2(\mathbb{Z})$ shears |
| :---: | :---: | :--- | :--- | :---: |
| 48 | 1 | `(13, 184), (1, -40), (1, 24)` | `-47/1024, -1081/512, 105421/1024` | 9 |
| 49 | 1 | `(5, -1217), (1, -141), (1, 115)` | `245/16384, -118139/16384, 43757/8192` | 13 |
| 57 | 1 | `(5, -4), (1, 12), (1, 44)` | `-209/512, 11039/512, 7543/256` | 7 |
| 60 | 1 | `(5, 242), (1, -6), (1, 74)` | `295/1024, -4307/128, -2419/1024` | 9 |
| 69 | 1 | `(31, 963), (1, -35), (1, 29)` | `1955/65536, -523549/65536, -1803683/2048` | 9 |
| 84 | 2 | `(11, -1235), (1, 295), (7, 2193)` | `-17513/2097152, 557345/8192, -348019/2097152` | 13 |
| 88 | 1 | `(5, 272), (1, -16), (1, 36)` | `29/32, -1073/32, -319/4` | 9 |
| 96 | 1 | `(5, -208), (1, -48), (1, 80)` | `-95/64, 36005/256, 11495/256` | 15 |
| 105 | 2 | `(13, 1396), (1, 68), (7, -36)` | `1001/262144, 4046315/65536, -53599/262144` | 13 |
| 112 | 1 | `(19, -120), (1, 56), (1, 88)` | `-11/1024, 2933/128, 51985/1024` | 9 |
| 120 | 1 | `(5, 2781), (1, -263), (1, 761)` | `149345/1048576, -11044985/1048576, -1905785/262144` | 10 |
| 121 | 2 | `(37, 5067), (1, 47), (7, 73)` | `605/2097152, 2424235/16384, -994015/2097152` | 10 |
| 124 | 0 | `(1, 259), (1, -765), (1, -253)` | `4195571/262144, 291059/262144, -2243315/131072` | 11 |
| 132 | 2 | `(19, -20806), (1, 670), (7, -9390)` | `-9229/4194304, 201427/32768, 109385/4194304` | 15 |
| 133 | 1 | `(11, 1106), (1, -10), (1, 102)` | `77/512, -41459/512, -15257/128` | 12 |
| 148 | 2 | `(19, -635), (1, -249), (11, 1357)` | `-705257/67108864, 9538193/8388608, 3577049/67108864` | 20 |
| 169 | 0 | `(1, 340), (1, -52), (1, 204)` | `-169/16, -31265/512, 36673/512` | 7 |
| 177 | 0 | `(1, -2765), (1, -2253), (1, 1331)` | `2024231/262144, -431585/32768, 1428449/262144` | 11 |
| 184 | 0 | `(1, 84), (1, -160), (1, 64)` | `3013/4, -253/32, -23851/32` | 7 |
| 192 | 1 | `(7, 160), (1, 96), (1, 608)` | `-47177/65536, 2018297/8192, 35335/65536` | 5 |

## Open Next Questions

1. **Global Thue--Mahler / $S$-unit bound for non-monic frames at $r = 15$:** Relevance: settles whether general frames with even $u_j$ (`[0:1] mod 2` collision) or two odd determinants $\Delta_{01}, \Delta_{02}$ can ever solve $r = 15$. First execution step: solve the norm-form $S$-unit equation $u_0 \Delta_{12} - u_1 \Delta_{02} + u_2 \Delta_{01} = 0$ over $\mathbb{Q}(\sqrt{1257})$ for $r=15$ ($K = 1257 = 3 \times 419$). Blockers: bounding odd prime cancellation between $\Delta_{01}, \Delta_{02}$ and $K u_i^2 - w_i^2$ without bounding $|u_j|$ a priori.
2. **Backend physical cost pricing of low-shear general-frame repairs ($r = 192$ at 5 shears, $r = 57, 169, 184$ at 7 shears, $r = 48$ at 9 shears):** Relevance: determines whether general-frame 3-query repairs beat $r$ eager restorations under a pinned backend. First execution step: price temporary $b$-register shear widths and dyadic query scaling against the PR #6250 / [#7475](https://github.com/CrocSwap/integer-mult-bounds/pull/7475) comparator. Blockers: full caller routing and precision-tape accounting.
3. **Even-$S$ unresolved quartet $r \in \{40, 61, 141, 165, 168\}$ in $r \le 200$:** Relevance: completes the even-$S$ classification up to $r = 200$. First execution step: run `cubic_leapfrog_prover --search` with two free non-unit coordinates $u_1, u_2 > 1$ up to $|v_1| \le 50,000$ or check local Hilbert symbols on the genus-1 curve cut out by squareness of $(K u_0^2 - w_0^2)(K u_1^2 - w_1^2)$.

# O'Sullivan's Gaussian-polynomial / Chebyshev representation conjecture (A267486), proved

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A267486  
**Date:** 2026-10-29

## Result

Fix m, n ≥ 0 and put N = n + ⌊m/2⌋, so that 2n + m + 1 - (m mod 2) = 2N + 1. Let g = g(m;n) be mn for odd m and (2n+1)m/2 for even m. Let G(m;n,x) be the coefficient of t^m in (1+t) ∏_{k=1}^{N} (1 + t² + 2t T_k(x/2)), where T_k is the Chebyshev polynomial of the first kind. Write a(m;n,k) = [x^k] G(m;n,x). The claim is that deg_x G(m;n,x) ≤ g, and that the Gaussian polynomial satisfies [2N+1, m]_q = Σ_{k=0}^{g} a(m;n,k) (1+q²)^k q^{g-k}. The Gaussian polynomial is the one defined by the q-Pascal rule [M+1,m+1] = [M,m] + q^{m+1}[M,m+1].

## Assessment

Put x = q + 1/q. Then 2T_k(x/2) = q^k + q^{-k}, so each factor 1 + t^2 + 2tT_k(x/2) splits as (1+tq^k)(1+tq^{-k}), and (1+t) times the product equals prod_{j=-N}^{N}(1+tq^j). The classical finite q-binomial theorem then gives the coefficient of t^m as q^{-g}[2N+1,m]_q, which is exactly the claimed expansion. The degree bound follows because [2N+1,m]_q has q-span 2g. This is the full proof, well under a page, built from two textbook facts. It settles the general conjecture as the author intended it, not only some degenerate reading.

*Follows from:* The Cauchy/Rothe finite q-binomial theorem, prod_{j=0}^{M-1}(1+q^j t) = sum_m q^{C(m,2)} [M,m]_q t^m, combined with the standard Chebyshev identity 2T_k((q+1/q)/2) = q^k + q^{-k}.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A267486](https://oeis.org/A267486) as [`Math0.Statements.A267486.statement`](../../lean/Math0/Statements/OEIS/A267486.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A267486.lean`](../../lean/Math0/Frontier/OEIS/A267486.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A267486 Conjecture: More generally, the Gaussian polynomial [2*n+m+1-(m mod 2),m]_q = Sum_{k=0..g(m;n)} a(m;n,k)*(1+q^2)^k*q^(g(m;n)-k), for m >= 0, n >= 0, where g(m;n) = m*n if m is odd and (2*n+1)*m/2 if m is even, and ... a(m;n,k) = [x^k]G(m;n,x), G(m;n,x) = (d^m/dt^m)G(m;n,t,x)/m!|_{t=0}, G(m;n,t,x) = (1+t)*Product_{k=1..n+(m - m mod 2)/2}(1 + t^2 + 2*t*T(k,x/2)). (Stephen O'Sullivan, entry author, 2016)

Referees: - OEIS A267486 (local mirror, revision #23, May 30 2026) and its siblings A267120, A267482, A267483, A267484, A267485 all state the same general conjecture with no recorded proof.
- A267482: W. Lang (Oct 19 2019) proves the m=1 case only, settling T. Baruchel's 2018 conjecture R(n,x) = S(n,x) + S(n-1,x) via [2n+1]_q = q^n S(2n, q^(1/2)+q^(-1/2)).
- S. O'Sullivan, 'A class of high-order Runge-Kutta-Chebyshev stability polynomials', J. Comput. Phys. 300 (2015) 665-678, arXiv:1507.08631, Eqs. (19)-(20): the representation [P,k]_q = Sum r_g q^(G_k/2-g)(1+q^2)^g, with generating function (1-t)·Prod_{k=1..N}(1+t^2-2tC_k), is stated without proof (P = 2N+1).
- O'Sullivan's follow-ups arXiv:1702.03818 and arXiv:1712.03971 do not treat it.
- The classical Cauchy/Rothe finite q-binomial theorem, Prod_{j=0..M-1}(1+q^j t) = Sum_m q^(C(m,2))[M,m]_q t^m, makes the general identity a direct corollary, though I found no source that writes out this deduction for the conjecture.
- Not related to this conjecture: J.-C. Liu, arXiv:2509.06357 (Chebyshev expansions of MacMahon-type q-series).

## Citation

```bibtex
@misc{math0:oeis-a267486,
  author       = {{math0}},
  title        = {{O'Sullivan's Gaussian-polynomial / Chebyshev representation conjecture (A267486), proved}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a267486}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

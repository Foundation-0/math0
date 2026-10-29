# Barker's order-20 recurrence for the lines through an 8 x n grid holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A160848  
**Date:** 2026-10-24

## Result

Let a(n) be the number of lines in the plane through at least 2 points of the 8 x n grid {0..n-1} x {0..7} (OEIS A160848). Then for every n > 21: a(n) = -a(n-2) + a(n-5) + a(n-6) + 2a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2a(n-13) - a(n-14) - a(n-15) + a(n-18) + a(n-20) (Colin Barker's 2017 conjecture).

## Assessment

The conjecture follows readily from the slope-sum formula already in the entry. With 8 rows, y ranges over a bounded set, and for each fixed y the second difference in n of Sum_x (n-|kx|)[gcd(x,y)=1] is a gcd indicator that is periodic with period at most 7 (at most 6 for the k=2 term). So the second difference of a(n) is eventually a combination of sequences with periods 1..7. That means a(n) is annihilated by (1-x)^2 times lcm(1-x^q : q<=7), which is exactly Barker's denominator (1-x)^3 Phi_2...Phi_7. The manuscript re-derives the counting formula via "first pairs" and checks the period-420 identity by kernel computation, but the underlying idea is a standard half-page quasi-polynomial argument.

*Follows from:* The entry's own formula a(n) = (1/2)(f(8,n,1) - f(8,n,2)), with f(m,n,k) = Sum (n-|kx|)(m-|ky|) over coprime (x,y), proved by Mustonen (PointsInGrid.pdf, Section 3) and repeated in the parent array A295707. Taking the second difference in n gives a periodic residual, which is Mustonen's eq. (38) for m=8.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A160848](https://oeis.org/A160848) as [`Math0.Statements.A160848.statement`](../../lean/Math0/Statements/OEIS/A160848.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A160848.lean`](../../lean/Math0/Frontier/OEIS/A160848.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjectures from _Colin Barker_, Dec 25 2017: "a(n) = -a(n-2) + a(n-5) + a(n-6) + 2*a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2*a(n-13) - a(n-14) - a(n-15) + a(n-18) + a(n-20) for n>21", with g.f. denominator (1-x)^3(1+x)(1-x+x^2)(1+x^2)(1+x+x^2)(1+...+x^4)(1+...+x^6).

Referees: - OEIS A160848 (local mirror, revision #13 of Dec 25 2017): Barker's g.f. and order-20 recurrence are labelled "Conjectures from Colin Barker, Dec 25 2017", with no later %E. Siblings A160845, A160846, A160847, A160849 and A160850 are likewise still conjectural or empirical; A295707 is the parent array.
- S. Mustonen, "On lines and their intersection points in a rectangular grid of points", http://www.survo.fi/papers/PointsInGrid.pdf (2009). Section 3 proves L(m,n) = ½[f(m,n,1) - f(m,n,2)]. Appendix 2, eq. (38), gives the second-difference recursion L(m,n) = 2L(m,n-1) - L(m,n-2) + 2ψ1 + 2ψ4 with periodic residuals, supported by a heuristic "bearing points" argument and numerical checks; that recursion is the basis of the Mathematica code in the OEIS entry.
- P. Haukkanen and J. K. Merikoski, arXiv:1108.1041 (2011), Remark 2: for n1 ≠ n2, "Mustonen [5] conjectured a recursive formula", and the question is "more difficult".
- A.-M. Ernvall-Hytönen, K. Matomäki, P. Haukkanen and J. K. Merikoski, "Formulas for the number of gridlines", Monatsh. Math. 164 (2011) 157-170: proves Mustonen's recursions only for n×n and (n-1)×n grids.
- S. Mustonen, "On lines through a given number of points in a rectangular grid of points", LinesInGrid2.pdf: covers square grids only.

No prior proof or counterexample of Barker's A160848 recurrence was found.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a160848,
  author       = {{math0}},
  title        = {{Barker's order-20 recurrence for the lines through an 8 x n grid holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a160848}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Barker's order-20 recurrence for the lines through an 8 x n grid holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A160848  
**Date:** 2026-10-24

## Result

Let a(n) be the number of lines in the plane through at least 2 points of the 8 x n grid {0..n-1} x {0..7} (OEIS A160848). Then for every n > 21: a(n) = -a(n-2) + a(n-5) + a(n-6) + 2a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2a(n-13) - a(n-14) - a(n-15) + a(n-18) + a(n-20) (Colin Barker's 2017 conjecture).

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

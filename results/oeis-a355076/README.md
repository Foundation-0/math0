# Integer partial sums of the Calkin-Wilf ratios fusc(k)/fusc(k+1) at n = 2*4^k-1 and 2*4^k-2 (A355076)

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** OEIS A355076  
**Date:** 2026-10-18

## Result

Let fusc be Stern's diatomic sequence (fusc 0 = 0, fusc 1 = 1, fusc(2n) = fusc n, fusc(2n+1) = fusc n + fusc(n+1)), and let a(n) be the denominator of s(n) = sum_{k=0}^{n} fusc(k)/fusc(k+1). Then for every k >= 0, a(n) = 1 when n = 2*4^k - 1 or n = 2*4^k - 2. In other words, s(n) is an integer for those n.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A355076](https://oeis.org/A355076) as [`Math0.Statements.A355076.statement`](../../lean/Math0/Statements/OEIS/A355076.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A355076.lean`](../../lean/Math0/Frontier/OEIS/A355076.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(n) = 1 for n of the form 2*4^k - 1 or 2*4^k - 2 for some k >= 0. (entry by _Rémy Sigrist_, Jun 18 2022)

Referees: - **Row-sum theorem (the key ingredient):** K. Siddharth Choudary and A. Satyanarayana Reddy, "Calkin-Wilf tree", arXiv:2003.13466 [math.CO], Mar 2020, accepted in Resonance. Theorem 1.1, Part 11: the sum of all elements in level n (root at level 1) is 3·2^{n−2} − 1/2, proved by induction.
- **Earlier statement of the same fact:** OEIS A052940, comment by Carl Najafi (Jul 10 2011): 3·2^n − 1 is the numerator of the sum of terms at the n-th level of the Calkin-Wilf tree.
- **Classical facts:** OEIS A002487 records a(2^k) = 1 and a(2^k − 1) = k (Adamchuk comment), and that a(n)/a(n+1) enumerates the rationals (Stern; N. Calkin and H. Wilf, "Recounting the rationals", Amer. Math. Monthly 107 (2000)).
- **The conjecture itself:** OEIS A355076 (R. Sigrist, Jun 18 2022, rev. #11) is still listed as a conjecture with no %E edits. A355075 is the matching numerators entry. I found no explicit resolution anywhere; the result follows immediately from the Choudary–Reddy row sum plus the classical facts above.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a355076,
  author       = {{math0}},
  title        = {{Integer partial sums of the Calkin-Wilf ratios fusc(k)/fusc(k+1) at n = 2*4^k-1 and 2*4^k-2 (A355076)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a355076}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

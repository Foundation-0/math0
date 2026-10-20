# 3 × 3 lower triangles with neighbours differing by at most two: a(n) = 1047 n - 1459 for n > 2 (A195249)

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A195249  
**Date:** 2026-10-20

## Result

Let a(n) be the number of fillings (x0,...,x5) of the six cells of the lower triangle of a 3 × 3 array (rows of lengths 1, 2, 3) with entries in {0,...,n}, such that any two king-adjacent cells (horizontal, vertical or diagonal neighbours) have entries differing by at most 2. The adjacent pairs are 0-1, 0-2, 1-2, 1-3, 2-3, 1-4, 2-4, 3-4, 2-5, 4-5. Then a(n) = 1047 n - 1459 for every n > 2. This is Hardin's empirical formula from OEIS A195249.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A195249](https://oeis.org/A195249) as [`Math0.Statements.A195249.statement`](../../lean/Math0/Statements/OEIS/A195249.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A195249.lean`](../../lean/Math0/Frontier/OEIS/A195249.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F Empirical: a(n) = 1047*n - 1459 for n>2. (R. H. Hardin, Sep 13 2011); %F Conjectures from Colin Barker, May 06 2018: G.f.: x*(64 + 601*x + 288*x^2 + 94*x^3) / (1 - x)^2. a(n) = 2*a(n-1) - a(n-2) for n>4.

Referees: I found no prior proof of A195249 or of row 3 of A195248. The local OEIS mirror entries for A195249, A195248 and A195214 have no %E lines and still mark the formulas 'Empirical'. The closest prior work is Robert Israel's comment (Nov 21 2017) on the sibling sequence OEIS A195232 ('one or less' variant), which proves the analogous linearity in k with the same span argument; this is a direct template for the current proof. Israel's Ehrhart-polynomial comment on A195220 (Oct 06 2019) is related. Hardin's own 'Generalizing' note on A195248 gives no proof. Searches I checked that turned up nothing relevant: Dougherty-Bliss & Kauers, 'Hardinian Arrays', Electron. J. Combin. 31(2) P9 (arXiv:2309.00487), which treats a different Hardin family; Ekhad-Yang-Zeilberger arXiv:1707.04654, which treats Mathar's conjectures; and web, arXiv and MathOverflow searches for the formula, the A-numbers and the entry's name text.

## Citation

```bibtex
@misc{math0:oeis-a195249,
  author       = {{math0}},
  title        = {{3 × 3 lower triangles with neighbours differing by at most two: a(n) = 1047 n - 1459 for n > 2 (A195249)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a195249}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

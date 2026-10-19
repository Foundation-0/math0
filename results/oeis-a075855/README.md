# The longest path on the black squares of an even chessboard has (n^2-n+2)/2 squares (A075855)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A075855  
**Date:** 2026-10-19

## Result

Let n = 2m be even, with m >= 1. Use the n x n board with rows and columns numbered 0..n-1, and call square (i,j) black when i+j is even. Two black squares are adjacent when they are diagonal neighbours, that is |di| = |dj| = 1. A path is a sequence of distinct black squares in which each square is adjacent to the next. Claim: the largest number of squares on such a path is a(n) = (n^2 - n + 2)/2 = 2m^2 - m + 1. In the frozen statement, a n is computed by exhaustive search, and the file's lemma a_spec shows it is the greatest path length.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A075855](https://oeis.org/A075855) as [`Math0.Statements.A075855.statement`](../../lean/Math0/Statements/OEIS/A075855.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A075855.lean`](../../lean/Math0/Frontier/OEIS/A075855.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A075855: "For n odd, a(n)=(n-1)^2/2+1. For n even, it is conjectured that a(n)=(n^2-n+2)/2 (it is easy to show this is a lower bound)." (entry by Jon Perry, Oct 15 2002; edited by Dean Hickerson, Oct 25 2002). Barker's 'Empirical g.f.' (Apr 12 2012) is equivalent.

Referees: - USAMO 2008 Problem 3 (proposed by Gabriel Carroll): S_n = {(x,y) in Z^2 : |x|+|y+1/2| < n} cannot be partitioned into fewer than n unit-step paths. Under the isomorphism (i,j) -> ((i-j)/2, (i+j)/2 - m), S_m is the graph of black squares of the 2m x 2m board with diagonal adjacency. Adding the uncovered squares as one-point paths then gives the A075855 upper bound 2m^2 - m + 1 directly. See the AoPS wiki page 2008_USAMO_Problems/Problem_3 and Evan Chen's USAMO 2008 solution notes.
- Evan Chen, "Iberoamerican 2019/5" (Twitch Solves ISL Ep. 109), https://web.evanchen.cc/twitch/Ep109-Iberoamerican-2019-5-Solution.pdf. It uses USAMO 2008/3 as the claim that the "blue zigzags" (the diagonal-move graph on one colour class of a (2m)x(2m) vertex grid) need at least m paths.
- Lean formalization of USAMO 2008/3: compfiles, https://github.com/dwrensha/compfiles/blob/main/Compfiles/Usa2008P3.lean (problem usa2008_p3; no sorry).
- OEIS A075855 (Jon Perry, 2002; edited by Dean Hickerson) still states the even case as a conjecture. OEIS A249333 (Richard Stanley) cross-references it as "conjecturally the same as b(n+1) for A075855", which this result also settles.
- I found no explicit statement anywhere of the A075855 to USAMO 2008/3 link. The classification rests on this one-line reduction to a known theorem, not on a direct citation.

## Citation

```bibtex
@misc{math0:oeis-a075855,
  author       = {{math0}},
  title        = {{The longest path on the black squares of an even chessboard has (n^2-n+2)/2 squares (A075855)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a075855}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

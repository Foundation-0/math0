# A338885: the smallest number in row 655 is 104, not A228286(655) = 115

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A338885  
**Date:** 2026-10-18

## Result

Kagey's conjecture in OEIS A338885 says that for every n ≥ 2, the smallest k for which a diagonal lattice rectangle (integer vertices, no side parallel to the x-axis) lies in the n X k box [0,n]×[0,k] and touches all four of its sides is A228286(n) = min{x + y*z : x, y, z ≥ 1, x*y + z = n}. This is false. For n = 655, the value k = 104 is in the row, but A228286(655) = 115 ≥ 105. So A228286(655) is not the least element of row 655.

## Assessment

The conjecture is refuted by one counterexample, n = 655, found by a direct search. The row minimum there is 104, from an explicit lattice rectangle, while A228286(655) = 115; the lower bound is a finite check over about 2400 pairs (x, y). The only setup is the observation that the side vectors' coordinates satisfy a+b = n, c+d = k and ab = cd, which takes a few lines, and after that the search is mechanical (I reproduced it independently: counterexamples at n = 655, 845, 909 and 1019 below 1100). The counterexample is an ordinary row of the triangle and falls within the conjecture's intended meaning, so the result is not literal-only, but no new mathematical idea was needed.

*Follows from:* Finite computer search, using the elementary parametrization that k is in row n iff n = a+b, k = c+d and ab = cd for positive a, b, c, d (the explicit rectangle with vertices (4,0),(655,42),(651,104),(0,62); 4*651 = 42*62 = 2604)

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A338885](https://oeis.org/A338885) as [`Math0.Statements.A338885.statement`](../../lean/Math0/Statements/OEIS/A338885.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A338885.lean`](../../lean/Math0/Frontier/OEIS/A338885.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: The smallest number in the n-th row is A228286(n)." (entry by _Peter Kagey_, Nov 14 2020; a second conjecture in the same entry, "The largest number in the n-th row is A033638(n)", is true; see approach)

Referees: I found no prior resolution.
- OEIS A338885 (Kagey, Nov 14 2020): I checked both the local mirror and the latest raw oeisdata version (rev #22, Sep 11 2021). The conjecture is still listed, with no counterexample noted, and the b-file covers only rows 2..101.
- Cross-references (local mirror): A228286, A228287, A228288, A338886, A338887, A033638, A085582, A113751. None of them mentions a resolution.
- Code Golf SE question 213754 "Rectangles in rectangles", read via the Stack Exchange API: neither the answers nor the comments mention the conjecture.
- Web searches (OEIS/A338885, Kagey, SeqFan, the min x+yz / ab+cd formulations, ARML 2013) turned up nothing relevant.
- Independent computation: n = 655 is the smallest counterexample (row min 104 vs A228286 = 115). Further counterexamples are at n = 845, 909 and 1019 for n <= 1200.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a338885,
  author       = {{math0}},
  title        = {{A338885: the smallest number in row 655 is 104, not A228286(655) = 115}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a338885}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

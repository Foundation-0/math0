# Edges of the all-chords graph of a triangle with n general-position points per side (A367119)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A367119  
**Date:** 2026-10-20

## Result

Take the equilateral triangle with corners 0, 1 and 1/2 + (√3/2)i. Let B be the three corners together with exactly n points in the relative interior of each side, and no other points. Draw the segment between every pair of distinct points of B; pairs on a common side give pieces of that side. Assume general position: no interior point of the triangle lies on three pairwise distinct drawn segments. Form the planar graph whose vertices are the points of B together with every point where two drawn segments meet in a single point. Two distinct vertices are adjacent when they lie on a common drawn segment and no vertex lies strictly between them. Then for every n ≥ 0 this graph has (3/2)(3n^4 + 4n^3 + 3n^2 + 4n + 2) edges. This was conjectured by Shannon and Sloane for OEIS A367119.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A367119](https://oeis.org/A367119) as [`Math0.Statements.A367119.statement`](../../lean/Math0/Statements/OEIS/A367119.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A367119.lean`](../../lean/Math0/Frontier/OEIS/A367119.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F Conjecture: a(n) = (3/2)*(3*n^4 + 4*n^3 + 3*n^2 + 4*n + 2). (Scott R. Shannon and N. J. A. Sloane, Nov 05 2023)

Referees: OEIS sources (read from the local mirror and checked against GitHub oeisdata main):
- A367119 (Shannon and Sloane, Nov 05 2023): the edge formula is still marked "Conjecture"; last edited Nov 09 2023.
- A367117: "Theorem: a(n) = (3/4)*(n+1)*(3*n^3+n^2+4)" for the vertex count of the same configuration. This is the key prior result, since the edge formula follows from it by degree counting: E = 2V + 3(n^2−1).
- A213827: "a(n) = (A367177 [sic, i.e. A367117](n) − 3*(n+1))/3 – Shannon & Sloane, Nov 09 2023". This is the interior-crossing count n^2(n+1)(3n+1)/4 per side-orbit.
- A367183 (Nov 13 2023): T(3,k) = A367117(k) appears apart from its "Conjectured" rows.
- A365929: Sloane's proof (Nov 07 2023) of the crossing count for the corner-free triangle variant.
- A366932 and A367015: the analogous edge and region conjectures, marked "now a theorem" by Sloane on Dec 31 2025.
- A392261, A392282, A392228 (Shannon and Sloane, Jan 2026): Shannon's attached proof (a392261.txt) of the general vertex, edge and region formulas for k general points per side of a regular n-gon without corners. The local mirror holds only a git-lfs pointer and the file could not be fetched; oeis.org was not queried, as instructed.
- A367190 and A366253: the triangle row (n=3) with corners is listed as a conjecture.

Web searches (arXiv, Math StackExchange, general) found no paper or post that explicitly proves the A367119 or A367118 conjecture. The general method is the classical Euler-formula and crossing-count argument for chord arrangements (Moser's circle problem; Poonen–Rubinstein, arXiv math/9508209).

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a367119,
  author       = {{math0}},
  title        = {{Edges of the all-chords graph of a triangle with n general-position points per side (A367119)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a367119}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

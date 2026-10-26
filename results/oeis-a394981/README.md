# Bar tilings of the smallest-perimeter rectangle: a(n+1) = 4 a(n) for odd n >= 3 (A394981)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A394981  
**Date:** 2026-10-20

## Result

Let a(n) be the number of tilings, counted up to the symmetries of the rectangle, of the rows(n) x cols(n) rectangle by the n bars 1x1, 1x2, ..., 1xn, each used exactly once. Here rows(n) = floor((n+1)/2) and cols(n) = (n(n+1)/2)/rows(n). For n = 2m+1 the rectangle is (m+1) x (2m+1), and for n = 2m+2 it is (m+1) x (2m+3). In Lean, a(n) is the frozen bitmask-search definition: it sums the stabilizer sizes of all tilings found by the search and divides by the order of the symmetry group (Burnside). Claim (A394981 conjecture, read for odd n >= 3): for every odd n >= 3, a(n+1) = 4 a(n). The literal case n = 1 fails, a(2) = 1 != 4 = 4 a(1), and the statement excludes it.

## Assessment

The proof is short and elementary, about a page of informal argument. Because all bar lengths differ, no tiling has a nontrivial symmetry, so a(n) is a quarter of the raw tiling count. Every bar longer than half the width must lie horizontally, and these bars take one row each, so they all cover the middle column. A case split on where bar m+1 sits divides the larger rectangle's tilings into four classes. Deleting one or two middle or edge columns gives a bijection from each class to the tilings of the smaller rectangle. This pigeonhole and column-deletion argument would come quickly to a competent combinatorialist. The 2400-line Lean file reflects the work of formalizing it, not the difficulty of the mathematics. The proof needs the hypothesis n >= 3 because the identity fails at n = 1. That case is a degenerate exception, and the intended conjecture is fully settled.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A394981](https://oeis.org/A394981) as [`def statement`](../../lean/Math0/Statements/OEIS/A394981.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A394981.lean`](../../lean/Math0/Frontier/OEIS/A394981.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A394981 Conjecture: If n is odd, then a(n+1) = 4*a(n).  (Unattributed formula line. Entry by _Gary Yane_, Apr 08 2026; a(1)-a(2) corrected by _Pontus von Brömssen_, May 13 2026.)

Referees: The OEIS A394981 entry (Gary Yane, Apr 08 2026; a(1)-a(2) corrected by Pontus von Brömssen, May 13 2026; revision #42, May 16 2026, the same in the local mirror and upstream oeisdata) still states the identity as a conjecture, with keyword "more" and no proof reference. No other OEIS entry cites it. Cross-references A254414/A254458/A254607/A329279 are unrelated counts. Searches found no proof or counterexample on arXiv, MathOverflow, Math StackExchange, SeqFan or the general web. Nearest work, all on a different problem: arXiv:2606.05439, Blanco, Dougherty-Bliss, Ter-Saakov and Zeilberger, "In How Many Ways can a Rectangle be Rectangled?" (tilings by bars of any length); arXiv:2607.29369, Martinez (L-tetromino tilings).

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a394981,
  author       = {{math0}},
  title        = {{Bar tilings of the smallest-perimeter rectangle: a(n+1) = 4 a(n) for odd n >= 3 (A394981)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a394981}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

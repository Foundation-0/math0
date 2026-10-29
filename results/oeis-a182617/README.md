# The toothpick spiral around n hexagonal cells (A182617): a(n) = 2n + ceil(sqrt(12n - 3))

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A182617  
**Date:** 2026-10-29

## Result

For the toothpick spiral on the hexagonal net, encoded as in Math0.Statements.A182617, let a(n) be the least number t of toothpicks at which at least n cells are ON. Then for every n > 0, a(n) = 2n + ceil(sqrt(12n - 3)). This is Librandi's conjecture from 2017.

## Assessment

The walk is an explicit spiral. Ring m of vertices is visited during times 6m^2+2m to 6m^2+14m+7. Cell s of cell ring j becomes ON at time 6j^2 - 1 + 2s + c, where c (1 to 6) is one more than the number of ring corners passed so far. With n = 3j(j-1)+1+s we have 12n-3 = (6j-3)^2 + 12s, and checking which pair of consecutive squares this lies between gives ceil(sqrt(12n-3)) = 6j-3+c. Equivalently, the result is Harborth's known spiral-polyhex edge count combined with Euler's formula. That is about a page of standard counting. The long Lean proof (coordinates, case analysis over the six sides) is formalization effort, not a new idea.

*Follows from:* Harborth's formula 3n + ceil(sqrt(12n-3)) for the minimal edge count of an n-cell polyhex (A135708), which spiral polyhexes attain (Harary-Harborth 1976). Together with Euler's formula this gives |V| = 2n + ceil(sqrt(12n-3)) + 1 for the n-cell spiral. The toothpick path at stage n covers exactly the spiral's vertices, so a(n) = |V| - 1. The ring-by-ring increments listed in A182618 lead to the same result.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A182617](https://oeis.org/A182617) as [`Math0.Statements.A182617.statement`](../../lean/Math0/Statements/OEIS/A182617.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A182617.lean`](../../lean/Math0/Frontier/OEIS/A182617.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A182617 Conjecture: a(n) = 2*n + ceiling(sqrt(12*n - 3)), for n > 0. - _Vincenzo Librandi_, Sep 20 2017

Referees: OEIS A182617 (rev #35, Sep 23 2025): the formula is still marked "Conjecture", with no %E lines recording a resolution. No other OEIS entry in the local mirror references A182617. Related known results:
- A135708, minimal edge count of an n-cell polyhex, 3n + ceil(sqrt(12n-3)), attributed to H. Harborth; Kupitz 1991.
- A135711, minimal polyhex perimeter, 2*ceil(sqrt(12n-3)).
- F. Harary and H. Harborth, "Extremal animals", J. Combin. Inform. System Sci. 1 (1976): spiral animals attain the minimum.
- G. Malen, É. Roldán and R. Toalá-Enríquez, "Extremal {p,q}-Animals", Ann. Comb. (2023), arXiv:2109.05331, Cor. 1.9.
- É. Roldán and R. Toalá-Enríquez, "Isoperimetric Formulas for Hyperbolic Animals", arXiv:2206.14910.
- A036496 (W. C. Yang): ceil(sqrt(12n-3)) for a triangular-lattice spiral.
- Applegate, Pol and Sloane, "The Toothpick Sequence and Other Sequences from Cellular Automata", Congr. Numer. 206 (2010), arXiv:1004.3036: background only, no formula for A182617.
None of these states or proves the A182617 formula. They imply it only together with the extra fact that the toothpick walk's vertex set at time a(n) equals the vertex set of the extremal n-cell spiral, which I found nowhere in print.

## Citation

```bibtex
@misc{math0:oeis-a182617,
  author       = {{math0}},
  title        = {{The toothpick spiral around n hexagonal cells (A182617): a(n) = 2n + ceil(sqrt(12n - 3))}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a182617}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

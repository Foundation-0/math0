# The toothpick spiral around n hexagonal cells (A182617): a(n) = 2n + ceil(sqrt(12n - 3))

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A182617  
**Date:** 2026-10-29

## Result

For the toothpick spiral on the hexagonal net, encoded as in Math0.Statements.A182617, let a(n) be the least number t of toothpicks at which at least n cells are ON. Then for every n > 0, a(n) = 2n + ceil(sqrt(12n - 3)). This is Librandi's conjecture from 2017.

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

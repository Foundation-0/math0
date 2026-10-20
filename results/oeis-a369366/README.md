# The least number of inequivalent cells of a (6k+5)-iamond is 3(k+1)

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A369366  
**Date:** 2026-10-20

## Result

For every k >= 0, the least number of inequivalent cells over all polyiamonds with n = 6k+5 cells is 3(k+1). Two cells of P are equivalent when a symmetry of the triangular grid maps P onto itself and one cell to the other. This is Exley's conjecture in OEIS A369366, a(6k+5) = 3(k+1).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A369366](https://oeis.org/A369366) as [`def statement`](../../lean/Math0/Statements/OEIS/A369366.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A369366.lean`](../../lean/Math0/Frontier/OEIS/A369366.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A369366 Conjecture: a(6k+5) = 3(k+1) for all k >= 0. Observed for k = 0, 1, 2 (n = 5, 11, 17). The next test case is a(23), predicted to be 12.  (From _Peter Exley_, Apr 07 2026)

Referees: OEIS A369366 (local mirror revision #14, Apr 14 2026, identical to oeisdata main): Exley's comment of Apr 07 2026 states the conjecture and already proves the lower bound a(6k+5) >= 3(k+1) (no rotations are possible when n = 6k+5, so |G_max| = 2). No upper-bound construction or full proof appears in the entry or its %E history. Cross-references checked: A369365, A369367, A369363, A369364, A367758, A367759, A373637, A376798, A376799. The only related proof is Mason and von Brömssen's formula proof for the polyomino analog A367758 (square lattice, a different problem). Exley's linked GitHub repo github.com/pexley-math/oeis-A369366 and the account page return 404 and could not be inspected. Web searches (arXiv, general web) found no prior resolution.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a369366,
  author       = {{math0}},
  title        = {{The least number of inequivalent cells of a (6k+5)-iamond is 3(k+1)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a369366}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

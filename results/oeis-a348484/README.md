# A348484: no two squares two steps apart; the conjectured formula holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A348484  
**Date:** 2026-10-18

## Result

For every n >= 1, let a(n) be the largest number of squares you can choose on an n x n board so that no two chosen squares are exactly two steps apart in the same row or in the same column. Then a(n) = n^2/2 if n ≡ 0 (mod 4), a(n) = (n^2+1)/2 if n is odd, and a(n) = n^2/2 + 2 if n ≡ 2 (mod 4). (This is Yang Hong's conjecture in OEIS A348484.)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A348484](https://oeis.org/A348484) as [`Math0.Statements.A348484.statement`](../../lean/Math0/Statements/OEIS/A348484.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A348484.lean`](../../lean/Math0/Frontier/OEIS/A348484.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A348484 Conjectures: a(n) = n^2/2 for n == 0 (mod 4). a(n) = (n^2 + 1)/2 for n == 1 or 3 (mod 4). a(n) = n^2/2 + 2 for n == 2 (mod 4).  (Entry by _Yang Hong_, Oct 20 2021; last edit #33, Dec 06 2022.)

Referees: OEIS A348484 (Yang Hong, Oct 20 2021; latest revision #33, Dec 06 2022) still marks the formulas as "Conjectures". R. J. Mathar's Dec 2022 comment gives a 2×2-block checkerboard construction. Its g.f. -x(1+2x-2x^2+2x^3+x^4)/((1+x)(1+x^2)(x-1)^3) matches the conjectured values, but he states it only as a lower bound. Cross-reference: A048716 (the 1-D row condition, k AND 4k = 0). I found no published or online proof of the upper bound on arXiv, Math StackExchange, MathOverflow, SeqFan or general web search. The result does follow directly from the standard fact that a grid graph P_a□P_b has independence number ⌈ab/2⌉, because the "two apart" graph is a disjoint union of four such grids.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a348484,
  author       = {{math0}},
  title        = {{A348484: no two squares two steps apart; the conjectured formula holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a348484}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

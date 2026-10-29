# Diagonal sums of A368846 equal A229580 (Luschny's conjecture)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A368846  
**Date:** 2026-10-29

## Result

Let T(n,k) = (-1)^(n+k)·2·C(2k-1,n)·C(2n+1,2k) for k > 0 and T(n,0) = 0^n. Let A229580(n) be the number of colorings of the n X 2 array with colors 0..2 that have exactly one mistake and introduce colors in row-major 0..2 order. Here the array is connected horizontally and antidiagonally, and a mistake is an edge whose two ends have the same color. Then for every k ≥ 0, |Σ_{j=0}^{k} T(k+j,k)| = A229580(k+1). Both sides equal 1 for k = 0 and (2k+1)·2^(2k-1) for k ≥ 1.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A368846](https://oeis.org/A368846) as [`Math0.Statements.A368846.statement`](../../lean/Math0/Statements/OEIS/A368846.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A368846.lean`](../../lean/Math0/Frontier/OEIS/A368846.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A368846 Conjecture: |Sum_{j=0..k} T(k + j, k)| = A229580(k + 1) for k >= 0. (_Peter Luschny_, Jan 07 2024)

Referees: No prior proof or counterexample found. Checked: the A368846 entry (local mirror and the current oeisdata GitHub raw file, both rev #26, Feb 17 2025, still "Conjecture", no %E). A229580: closed form (2n-1)*2^(2n-3) credited to Gerson W. Barbosa/Gerald Hillier, 2018, given without proof; the recurrence and g.f. are marked "Empirical". OEIS entries citing A229580 (A383608, A385601, A386227 by Navarrete, 2025) and A368846 (A368847, A368848, A369134, A369135, A369120). T. Curtright, arXiv:2401.00586 and arXiv:2502.09633; T. Curtright and C. Vignat, arXiv:2504.18998 (they discuss diagonals of the inverse matrix, not column sums of M, and call combinatorial interpretations an open question). Blair–Flórez–Mukherjee, arXiv:2203.13205, is linked from A229580; I read only its link, not the paper. Web searches on arXiv, MSE, MathOverflow and SeqFan topics found nothing.

## Citation

```bibtex
@misc{math0:oeis-a368846,
  author       = {{math0}},
  title        = {{Diagonal sums of A368846 equal A229580 (Luschny's conjecture)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a368846}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

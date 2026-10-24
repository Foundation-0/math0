# Collinear 5-point sets in the grid {0,…,4}^n number (7^n − 5^n)/2 (Hardin's conjecture, A081200)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A081200  
**Date:** 2026-10-24

## Result

For every n ≥ 0, the number of 5-element subsets of the grid {0,1,2,3,4}^n ⊂ ℝ^n that lie on one real line equals a(n) = Σ_{k=0}^{n} C(n,k)·6^{n−k}·(k mod 2), the 6th binomial transform of 0,1,0,1,…. Equivalently the count is (7^n − 5^n)/2.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A081200](https://oeis.org/A081200) as [`Math0.Statements.A081200.statement`](../../lean/Math0/Statements/OEIS/A081200.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A081200.lean`](../../lean/Math0/Frontier/OEIS/A081200.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A081200 Conjecture (verified up to a(9)): Number of collinear 5-tuples of points in a 5 X 5 X 5 X ... n-dimensional cubic grid. - Ron Hardin, May 24 2010

Referees: P. Erdős and J. L. Selfridge, "On a combinatorial game", J. Combin. Theory Ser. A 14 (1973) 298-301 (states that the n-dimensional hypercube of side k has ((k+2)^n - k^n)/2 winning lines; k=5 gives (7^n-5^n)/2 = A081200); S. W. Golomb and A. W. Hales, "Hypercube Tic-Tac-Toe", More Games of No Chance, MSRI Publ. 42 (2002), 167-182, Theorem 1 (same count, same word encoding and 2-to-1 reversal proof; work dates to before 1972); the border-shell proof is credited to Leo Moser in R. Honsberger, Mathematical Morsels (cut-the-knot.org/proofs/tictactoe.shtml); O. Patashnik, "Qubic: 4x4x4 Tic-Tac-Toe", Math. Mag. 53 (1980) (k^n game has ((k+2)^n - k^n)/2 lines); OEIS A005059 (k=3 analogue stated without a conjecture label, D. W. Wilson c. 1999). Related open Hardin comments that the same argument settles: A081199 (k=4) and A081201 (k=6).

## Citation

```bibtex
@misc{math0:oeis-a081200,
  author       = {{math0}},
  title        = {{Collinear 5-point sets in the grid {0,…,4}^n number (7^n − 5^n)/2 (Hardin's conjecture, A081200)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a081200}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

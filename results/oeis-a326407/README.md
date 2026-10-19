# Prime-Minesweeper on the A060734 array: a(n) < 6, and a(n) = 5 only at n = 6

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A326407  
**Date:** 2026-10-18

## Result

Write the positive integers into the square array A060734. The cell in row r, column c (both counted from 0) holds val(r,c) = (c+1)^2 - r if r <= c, and r^2 + 1 + c if r > c. Every positive integer appears in exactly one cell. Set a(n) = -1 if n is prime. Otherwise a(n) is the number of primes in the king-move neighbouring cells of n's cell. There are up to 8 such cells, 5 on row 0 or column 0, and 3 at the corner (0,0). Claim: for every n >= 1 we have a(n) < 6, and a(n) = 5 holds exactly when n = 6.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A326407](https://oeis.org/A326407) as [`Math0.Statements.A326407.statement`](../../lean/Math0/Statements/OEIS/A326407.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A326407.lean`](../../lean/Math0/Frontier/OEIS/A326407.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C a(n) < 6 (conjectured). %C a(n) = 5 for n={6} (conjectured). %C Set of n such that a(n) = 4 is unbounded (conjectured). (Witold Tatkiewicz, Oct 02 2019)

Referees: OEIS A326407 (Tatkiewicz, Oct 2019; last edit #27, Mar 20 2020) still lists "a(n) < 6" and "a(n) = 5 for n={6}" as conjectured, with no %E edits or proof links. OEIS A327893 (hexagonal spiral, De Vlieger 2019) records Tatkiewicz's parity argument bounding its terms by 4. That is the same technique applied to a different grid, not a proof for A326407. OEIS A326408 and A326409 state "a(n) < 5" without "(conjectured)" but give no proof. A326405, A326406, A326410, A060734, A136626 and A136627 contain nothing relevant. Web searches (arXiv, MathOverflow/Math StackExchange, SeqFan, general) found no prior proof or counterexample for A326407.

## Citation

```bibtex
@misc{math0:oeis-a326407,
  author       = {{math0}},
  title        = {{Prime-Minesweeper on the A060734 array: a(n) < 6, and a(n) = 5 only at n = 6}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a326407}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

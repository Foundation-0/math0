# A338885: the smallest number in row 655 is 104, not A228286(655) = 115

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A338885  
**Date:** 2026-10-18

## Result

Kagey's conjecture in OEIS A338885 says that for every n ≥ 2, the smallest k for which a diagonal lattice rectangle (integer vertices, no side parallel to the x-axis) lies in the n X k box [0,n]×[0,k] and touches all four of its sides is A228286(n) = min{x + y*z : x, y, z ≥ 1, x*y + z = n}. This is false. For n = 655, the value k = 104 is in the row, but A228286(655) = 115 ≥ 105. So A228286(655) is not the least element of row 655.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A338885](https://oeis.org/A338885) as [`Math0.Statements.A338885.statement`](../../lean/Math0/Statements/OEIS/A338885.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A338885.lean`](../../lean/Math0/Frontier/OEIS/A338885.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: The smallest number in the n-th row is A228286(n)." (entry by _Peter Kagey_, Nov 14 2020; a second conjecture in the same entry, "The largest number in the n-th row is A033638(n)", is true; see approach)

Referees: I found no prior resolution.
- OEIS A338885 (Kagey, Nov 14 2020): I checked both the local mirror and the latest raw oeisdata version (rev #22, Sep 11 2021). The conjecture is still listed, with no counterexample noted, and the b-file covers only rows 2..101.
- Cross-references (local mirror): A228286, A228287, A228288, A338886, A338887, A033638, A085582, A113751. None of them mentions a resolution.
- Code Golf SE question 213754 "Rectangles in rectangles", read via the Stack Exchange API: neither the answers nor the comments mention the conjecture.
- Web searches (OEIS/A338885, Kagey, SeqFan, the min x+yz / ab+cd formulations, ARML 2013) turned up nothing relevant.
- Independent computation: n = 655 is the smallest counterexample (row min 104 vs A228286 = 115). Further counterexamples are at n = 845, 909 and 1019 for n <= 1200.

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

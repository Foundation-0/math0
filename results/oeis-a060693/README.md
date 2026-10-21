# Schulte's alternating quadratic sum over the Schröder-peaks triangle (A060693)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Discrete geometry  
**Source problem:** OEIS A060693  
**Date:** 2026-10-21

## Result

Let T(n,k) be the number of Schröder paths from (0,0) to (2n,0) (steps U=(1,1), D=(1,-1), H=(2,0), never going below the x-axis) that have exactly k peaks (a peak is a U step immediately followed by a D step). Then for every n ≥ 0,
  Σ_{k=0}^{n} (-1)^k · T(n,k) · (n+1-k)^2 = 1 + n + n^2.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A060693](https://oeis.org/A060693) as [`def statement`](../../lean/Math0/Statements/OEIS/A060693.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A060693.lean`](../../lean/Math0/Frontier/OEIS/A060693.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: Sum_{k=0..n} (-1)^k*T(n,k)*(n+1-k)^2 = 1+n+n^2. - _Werner Schulte_, Jan 11 2017"

Referees: Prior Lean proof: the-omega-institute/trureturing, PR #7436 by ElonSG, "prove: OEIS A060693 Schröder-path peak identity (Schulte 2017)", merged into dev on 2026-09-13 (https://github.com/the-omega-institute/trureturing/pull/7436). It supersedes PR #7402 (https://github.com/the-omega-institute/trureturing/pull/7402), with pre-registration issue #7384 (https://github.com/the-omega-institute/trureturing/issues/7384). The file is D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.lean and the theorem is schulte_a060693. The result also follows directly from the OEIS A060693 formula T_n(x) = C_n(x+1) with C_n the Narayana row polynomial (Mitch Harris, Jan 2007), plus the Narayana values N(n,1)=1 and N(n,2)=n(n-1)/2 (A001263). The OEIS entry (local mirror, %I #147, Oct 04 2026) still says "Conjecture". The identity is not in the OEIS Open benchmark (arXiv:2608.11941; tadamcz.com/oeis-open results.json). LANTERN (arXiv:2609.32264), cited in the entry, is about cross-reference relations and does not address this conjecture.

## Citation

```bibtex
@misc{math0:oeis-a060693,
  author       = {{math0}},
  title        = {{Schulte's alternating quadratic sum over the Schröder-peaks triangle (A060693)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a060693}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

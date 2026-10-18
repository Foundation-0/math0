# The set of Mahler Z-numbers is countable, so its Hausdorff dimension is 0, which is less than 1

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Books / BugeaudDistributionModuloOne / Problem10_9  
**Date:** 2026-10-17

## Result

A Z-number is a real ξ > 0 such that the fractional part {ξ (3/2)^n} lies in [0, 1/2) for every integer n ≥ 1. The set Z of all Z-numbers has Hausdorff dimension < 1, i.e. dimH {ξ : ℝ | IsZNumber ξ} < 1 in ℝ≥0∞. Flatto, Lagarias and Pollington (1995) proved this result, recorded in Bugeaud, Problem 10.9. We prove something stronger, going back to Mahler (1968): Z is countable, so dimH Z = 0.

## Verification

The Lean file [`lean/Math0/Books/Bugeaud09_problem_10_9_variants_dimH_lt_one.lean`](../../lean/Math0/Books/Bugeaud09_problem_10_9_variants_dimH_lt_one.lean) proves the upstream statement [`Bugeaud09.problem_10_9.variants.dimH_lt_one`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_9.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Mahler, K. "An unsolved problem on the powers of 3/2", J. Austral. Math. Soc. 8 (1968) 313-321: shows each interval [k, k+1) contains at most one Z-number, so the set of Z-numbers is countable (hence of Lebesgue measure 0 and Hausdorff dimension 0). Flatto, Lagarias and Pollington, "On the range of fractional parts {ξ(p/q)^n}", Acta Arith. 70 (1995) 125-147, credited by the upstream docstring; for this particular set their result is weaker than Mahler's countability. Bugeaud, "Distribution modulo one and Diophantine approximation" (CUP 2012), Ch. 10, Problem 10.9. I know of no prior Lean formalization: the upstream formal_conjectures statement is `sorry` with no formal_proof link, and Mathlib has no Z-number results.

## Citation

```bibtex
@misc{math0:bugeaud09-problem-10-9-variants-dimh-lt-one,
  author       = {{math0}},
  title        = {{The set of Mahler Z-numbers is countable, so its Hausdorff dimension is 0, which is less than 1}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/bugeaud09-problem-10-9-variants-dimh-lt-one}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# The p-adic Littlewood conjecture for real quadratic irrationals

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Books / BugeaudDistributionModuloOne / Problem10_8  
**Date:** 2026-10-17

## Result

Let p be a prime and ξ a real number whose minimal polynomial over ℚ has degree 2. Then inf over integers q ≥ 1 of q · |q|_p · ‖qξ‖ is 0. Here ‖·‖ is the distance to the nearest integer, |·|_p is the p-adic absolute value, and the infimum is the real sInf of the set {q · padicNorm p q · distToNearestInt(qξ) : q ∈ ℕ, q ≥ 1}.

## Verification

The Lean file [`lean/Math0/Books/Bugeaud08_problem_10_8_variants_quadratic.lean`](../../lean/Math0/Books/Bugeaud08_problem_10_8_variants_quadratic.lean) proves the upstream statement [`Bugeaud08.problem_10_8.variants.quadratic`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_8.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

de Mathan, B. and Teulié, O., "Problèmes diophantiens simultanés", Monatshefte für Mathematik 143 (2004), 229–245. They proved the p-adic Littlewood conjecture for quadratic irrationals, in a stronger form with a log factor. The problem is stated as Problem 10.8 in Bugeaud, "Distribution modulo one and Diophantine approximation" (CUP, 2012), Chapter 10. The elementary Pell/units argument used here is the standard proof of the quadratic case. I found no prior Lean formalization: there is no formal_proof attribute on Bugeaud08.problem_10_8.variants.quadratic, nothing in Mathlib, and the related formal_conjectures statement LittlewoodConjecture.padic_littlewood_conjecture is open and sorried.

## Citation

```bibtex
@misc{math0:bugeaud08-problem-10-8-variants-quadratic,
  author       = {{math0}},
  title        = {{The p-adic Littlewood conjecture for real quadratic irrationals}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/bugeaud08-problem-10-8-variants-quadratic}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Mahler's Z-numbers form a Lebesgue-null set

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Books / BugeaudDistributionModuloOne / Problem10_9  
**Date:** 2026-10-17

## Result

A Z-number is a real number ξ > 0 such that the fractional part {ξ (3/2)^n} lies in [0, 1/2) for every integer n ≥ 1. The set of Z-numbers has Lebesgue measure zero (Mahler 1968; Bugeaud, Distribution modulo one and Diophantine approximation, Problem 10.9, measure-zero variant). Formally: MeasureTheory.volume {ξ : ℝ | IsZNumber ξ} = 0.

## Verification

The Lean file [`lean/Math0/Books/Bugeaud09_problem_10_9_variants_measure_zero.lean`](../../lean/Math0/Books/Bugeaud09_problem_10_9_variants_measure_zero.lean) proves the upstream statement [`Bugeaud09.problem_10_9.variants.measure_zero`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_9.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

K. Mahler, "An unsolved problem on the powers of 3/2", J. Austral. Math. Soc. 8 (1968) 313-321: at most one Z-number in each interval [k, k+1) (n ≥ 0 normalization), so Z-numbers are countable, with counting function O(x^0.7). This gives measure zero. Y. Bugeaud, Distribution Modulo One and Diophantine Approximation (CUP 2012), Ch. 10, Problem 10.9. Flatto–Lagarias–Pollington, Acta Arith. 70 (1995), is the source of the related dimH variant. I know of no earlier Lean formalization: the upstream formal-conjectures item is a `sorry` with no formal_proof link. I could not search GitHub because session access is limited to configured repositories.

## Citation

```bibtex
@misc{math0:bugeaud09-problem-10-9-variants-measure-zero,
  author       = {{math0}},
  title        = {{Mahler's Z-numbers form a Lebesgue-null set}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/bugeaud09-problem-10-9-variants-measure-zero}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

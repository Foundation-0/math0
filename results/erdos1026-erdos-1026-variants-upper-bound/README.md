# Erdős 1026: no constant c > 1 is admissible (Cambie's construction)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #1026  
**Date:** 2026-10-17

## Result

Call c admissible if for every ε > 0, for all sufficiently large n, every sequence x_1,...,x_n of distinct positive reals has a monotone (non-decreasing or non-increasing) subsequence whose sum is at least (c − ε)/√n · Σ_i x_i. Then every admissible constant satisfies c ≤ 1, i.e. 1 is an upper bound of the set of admissible constants.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1026_erdos_1026_variants_upper_bound.lean`](../../lean/Math0/ErdosProblems/Erdos1026_erdos_1026_variants_upper_bound.lean) proves the upstream statement [`Erdos1026.erdos_1026.variants.upper_bound`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1026.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

- Erdős, "Some unsolved problems in graph theory and combinatorial analysis" (1971) [Er71]: the original problem.
- erdosproblems.com/1026 forum: van Doorn's precise formulation, and Cambie's construction showing c ≤ 1.
- Tidor, Wang and Yang, arXiv:1608.04153 [TWY16], and Wagner, J. Graph Theory 2017 [Wa17]: the weighted Erdős–Szekeres theorem, which gives c ≥ 1 and hence c = 1.
- Hanani 1957 [Ha57]: c ≥ 1/√2.
- Steele 1995 [St95].
- Existing Lean formalization by Aristotle and Boris Alexeev: https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1026.lean. Its theorem `c_opt_eq_k_div_sq_add_a` gives the exact c_opt(n) for all n, which implies the upper bound. erdosproblems problems.yaml lists the status as "solved (Lean)", last updated 2025-12-12.
- Background: Tao's blog post https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/.

## Citation

```bibtex
@misc{math0:erdos1026-erdos-1026-variants-upper-bound,
  author       = {{math0}},
  title        = {{Erdős 1026: no constant c > 1 is admissible (Cambie's construction)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1026-erdos-1026-variants-upper-bound}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Goodman–Goodman covering theorem for balls in ℝ^d (Erdős 1121, higher-dimensional variant)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** Erdős Problem #1121  
**Date:** 2026-10-17

## Result

Let d, n be natural numbers, c_1,…,c_n points of ℝ^d and r_1,…,r_n > 0. Suppose that for every nonzero v ∈ ℝ^d and every t ∈ ℝ, if the hyperplane {p : ⟨v,p⟩ = t} meets none of the closed balls B_i = B̄(c_i, r_i), then either ⟨v,c_i⟩ < t for all i or ⟨v,c_i⟩ > t for all i. Then there is z ∈ ℝ^d with ⋃_i B_i ⊆ B̄(z, R), where R = Σ_i r_i.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1121_erdos_1121_variants_higher_dimension.lean`](../../lean/Math0/ErdosProblems/Erdos1121_erdos_1121_variants_higher_dimension.lean) proves the upstream statement [`Erdos1121.erdos_1121.variants.higher_dimension`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1121.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The result is Goodman, A. W. and Goodman, R. E., "A circle covering theorem", Amer. Math. Monthly 52 (1945), 494–498. The upstream docstring notes that their proof generalises to higher dimensions. Hadwiger, "Nonseparable convex systems", Amer. Math. Monthly 54 (1947), 583–585, extends it to convex bodies. Bezdek and Litvak, "Packing convex bodies by cylinders", Discrete Comput. Geom. (2016), 725–738, give an alternative proof. erdosproblems.com/1121 lists the problem as "proved (Lean)". That refers to the 2D statement, whose existing Lean proof (https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1121.lean, by Aristotle and Amogh Parab) is restricted to EuclideanSpace ℝ (Fin 2). The higher-dimensional variant has no formal_proof link in the pinned upstream or the current upstream main branch.

## Citation

```bibtex
@misc{math0:erdos1121-erdos-1121-variants-higher-dimension,
  author       = {{math0}},
  title        = {{Goodman–Goodman covering theorem for balls in ℝ^d (Erdős 1121, higher-dimensional variant)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1121-erdos-1121-variants-higher-dimension}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

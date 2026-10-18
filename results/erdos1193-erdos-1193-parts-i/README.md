# Erdős Problem 1193 (i): the lower density of {n : 1_A*1_A(n) = g(n)} need not be 0

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics, Number theory  
**Source problem:** Erdős Problem #1193  
**Date:** 2026-10-17

## Result

It is not true that for every A ⊆ ℕ and every non-decreasing g : ℕ → ℕ with g(n) > 0 for all n, the set {n ∈ ℕ : 1_A ∗ 1_A(n) = g(n)} has lower natural density 0. Here 1_A ∗ 1_A(n) = #{(a,b) ∈ ℕ² : a + b = n, a ∈ A, b ∈ A} counts ordered representations (with 0 ∈ ℕ). The lower density of S is liminf_{N→∞} #(S ∩ [0,N)) / N.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1193_erdos_1193_parts_i.lean`](../../lean/Math0/ErdosProblems/Erdos1193_erdos_1193_parts_i.lean) proves the upstream statement [`Erdos1193.erdos_1193.parts.i`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1193.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The problem is Erdős Problem #1193 (erdosproblems.com/1193), from P. Erdős, "A survey of problems in combinatorial number theory", Ann. Discrete Math. (1980), 89–115. The site marks it "solved (Lean)": the literal question is trivially false via A = ℕ, which gives 1_A∗1_A(n) = n+1. The existing Lean formalization is plby/lean-proofs src/v4.29.1/ErdosProblems/Erdos1193.lean (Aristotle / Pietro Monticone; forum thread erdosproblems.com/forum/thread/1193#post-5360). It is linked from the upstream variant erdos_1193.variants.sumRep_univ and proves the key identity conv_ind univ n = n+1, but not the density step.

## Citation

```bibtex
@misc{math0:erdos1193-erdos-1193-parts-i,
  author       = {{math0}},
  title        = {{Erdős Problem 1193 (i): the lower density of {n : 1_A*1_A(n) = g(n)} need not be 0}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1193-erdos-1193-parts-i}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

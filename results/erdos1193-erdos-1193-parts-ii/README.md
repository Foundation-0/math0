# Erdős Problem 1193 (ii): the upper density of {n : 1_A*1_A(n) = g(n)} need not be bounded away from 1

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics, Number theory  
**Source problem:** Erdős Problem #1193  
**Date:** 2026-10-17

## Result

There is no real constant c < 1 such that for every A ⊆ ℕ and every monotone g : ℕ → ℕ with g(n) > 0 for all n, the set {n ∈ ℕ : sumRep A n = g n} has upper density < c. Here sumRep A n is the number of ordered pairs (a, b) ∈ A × A with a + b = n (i.e. 1_A * 1_A(n)), and the upper density of S ⊆ ℕ is limsup_{N→∞} |S ∩ [0, N)| / N.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1193_erdos_1193_parts_ii.lean`](../../lean/Math0/ErdosProblems/Erdos1193_erdos_1193_parts_ii.lean) proves the upstream statement [`Erdos1193.erdos_1193.parts.ii`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1193.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős, P., "A survey of problems in combinatorial number theory", Ann. Discrete Math. (1980), 89-115 [Er80]. erdosproblems.com/1193 says the question as stated is trivially "no" because of A = ℕ (1_A*1_A(n) = n+1), and its data file gives the status as "solved (Lean)" (2026-04-13). An existing Lean formalization is linked from the upstream formal_conjectures file: https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1193.lean.

## Citation

```bibtex
@misc{math0:erdos1193-erdos-1193-parts-ii,
  author       = {{math0}},
  title        = {{Erdős Problem 1193 (ii): the upper density of {n : 1_A*1_A(n) = g(n)} need not be bounded away from 1}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1193-erdos-1193-parts-ii}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

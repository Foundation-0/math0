# Sets avoiding sums equal to powers of two have lower density at most 1/2 (Müller)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** Erdős Problem #1136  
**Date:** 2026-10-17

## Result

Let A ⊆ ℕ be such that a + b ≠ 2^k for all a, b ∈ A (not necessarily distinct) and all k ≥ 0. Then the lower natural density of A, liminf_{N→∞} |A ∩ [0, N)| / N, is at most 1/2.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_upper_bound.lean`](../../lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_upper_bound.lean) proves the upstream statement [`Erdos1136.erdos_1136.variants.upper_bound`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1136.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Müller, Helmut, "Über ein additiv-zahlentheoretisches Problem von P. Erdős", Mitt. Math. Ges. Hamburg (2011), 75-78. Müller proves the existence of a set with density 1/2 and that every such set has density at most 1/2. erdosproblems.com/1136 has status "proved (Lean)" in problems.yaml (formal_status Lean, 2026-04-19). The existing Lean proof is linked from the upstream formal_proof attribute: https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1136.lean (Aristotle, Lorenzo Luccioli, Wouter van Doorn). It contains `sumfree_upperDensity_le_half`, an upper density ≤ 1/2 bound for any power-of-two-sum-free S ⊆ ℕ, and `main_result`. Related formalizations are Luccioli's gist (mathlib v4.28.0) and https://github.com/Woett/Lean-files/blob/main/ErdosProblem1136.lean.

## Citation

```bibtex
@misc{math0:erdos1136-erdos-1136-variants-upper-bound,
  author       = {{math0}},
  title        = {{Sets avoiding sums equal to powers of two have lower density at most 1/2 (Müller)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1136-erdos-1136-variants-upper-bound}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

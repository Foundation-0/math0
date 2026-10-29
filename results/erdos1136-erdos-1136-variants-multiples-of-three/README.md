# The multiples of 3 avoid sums equal to powers of two and have density 1/3

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Erdős Problem #1136  
**Date:** 2026-10-17

## Result

Let A = {n ∈ ℕ : 3 ∣ n}. (i) For all a, b ∈ A (not necessarily distinct) and all k ≥ 0, a + b ≠ 2^k. (ii) A has natural density 1/3: the quantity #(A ∩ [0, b)) / #[0, b) tends to 1/3 as b → ∞. This is the trivial benchmark in Erdős Problem 1136, which asks for a set with lower density greater than 1/3 and the same avoidance property.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_multiples_of_three.lean`](../../lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_multiples_of_three.lean) proves the upstream statement [`Erdos1136.erdos_1136.variants.multiples_of_three`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1136.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 1136 (erdosproblems.com/1136; problems.yaml gives status "proved (Lean)", last updated 2026-04-19). H. Müller, "Über ein additiv-zahlentheoretisches Problem von P. Erdős", Mitt. Math. Ges. Hamburg (2011), 75-78: Müller's set has density 1/2, and density 1/2 is optimal. The density-1/3 example using multiples of 3 is a folklore fact noted as trivial in the upstream docstring. The existing Lean proof at plby/lean-proofs (src/v4.29.1/ErdosProblems/Erdos1136.lean) formalizes the main problem, Müller's set and the upper bound, but not the multiples-of-3 variant.

## Citation

```bibtex
@misc{math0:erdos1136-erdos-1136-variants-multiples-of-three,
  author       = {{math0}},
  title        = {{The multiples of 3 avoid sums equal to powers of two and have density 1/3}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1136-erdos-1136-variants-multiples-of-three}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

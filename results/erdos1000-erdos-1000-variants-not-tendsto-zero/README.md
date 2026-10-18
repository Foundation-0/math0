# Erdős Problem 1000: φ_A(k)/n_k does not tend to 0

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** Erdős Problem #1000  
**Date:** 2026-10-17

## Result

Let n_0 < n_1 < n_2 < ... be a strictly increasing sequence of positive integers. Let φ_A(k) be the number of integers 1 ≤ m ≤ n_k such that n_k / gcd(m, n_k) divides none of the earlier terms n_j with j < k. Then φ_A(k)/n_k does not tend to 0 as k → ∞. (Erdős [Er64b], erdosproblems.com/1000.)

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1000_erdos_1000_variants_not_tendsto_zero.lean`](../../lean/Math0/ErdosProblems/Erdos1000_erdos_1000_variants_not_tendsto_zero.lean) proves the upstream statement [`Erdos1000.erdos_1000.variants.not_tendsto_zero`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1000.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős, Problems and results on diophantine approximations, Compositio Math. 1964 [Er64b], where Erdős proves that lim φ_A(k)/n_k ≠ 0 and that liminf = 0 forces limsup = 1. Cassels [Ca50b] introduced φ_A. Haight solved the main question. erdosproblems.com/1000 lists the problem as "proved (Lean)"; that formal proof (plby/lean-proofs src/v4.29.1/ErdosProblems/Erdos1000.lean) covers only Haight's main theorem. math0 had already committed a proof of upstream erdos_1000.variants.limsup_eq_one (lean/Math0/ErdosProblems/Erdos1000_erdos_1000_variants_limsup_eq_one.lean), and this result follows from it directly. Verified in /tmp/claude-0/-home-user-math0/e48cfc7c-53b7-512a-aa13-db31d47b5e5e/scratchpad/referee1000/Corollary.lean.

## Citation

```bibtex
@misc{math0:erdos1000-erdos-1000-variants-not-tendsto-zero,
  author       = {{math0}},
  title        = {{Erdős Problem 1000: φ_A(k)/n_k does not tend to 0}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1000-erdos-1000-variants-not-tendsto-zero}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

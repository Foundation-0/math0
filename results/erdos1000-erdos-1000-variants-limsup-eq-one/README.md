# Erdős Problem 1000: liminf φ_A(k)/n_k = 0 forces limsup φ_A(k)/n_k = 1

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Erdős Problem #1000  
**Date:** 2026-10-17

## Result

Let n_0 < n_1 < n_2 < ... be a strictly increasing sequence of positive integers. Let φ_A(k) be the number of integers 1 ≤ m ≤ n_k such that n_k / gcd(m, n_k) divides no n_j with j < k. Put r_k = φ_A(k)/n_k. If liminf_{k→∞} r_k = 0, then limsup_{k→∞} r_k = 1. (Erdős [Er64b], recorded as erdosproblems.com/1000.)

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1000_erdos_1000_variants_limsup_eq_one.lean`](../../lean/Math0/ErdosProblems/Erdos1000_erdos_1000_variants_limsup_eq_one.lean) proves the upstream statement [`Erdos1000.erdos_1000.variants.limsup_eq_one`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1000.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The result is Erdős, P., "Problems and results on diophantine approximations", Compositio Math. 16 (1964), 52-65 [Er64b]: if liminf φ_A(k)/n_k = 0 then limsup φ_A(k)/n_k = 1. The function φ_A was introduced by Cassels, "Some metrical theorems in Diophantine approximation. I", Proc. Cambridge Philos. Soc. (1950) [Ca50b]. Cassels's existence result (liminf of the Cesàro averages equal to 0) shows the hypothesis can hold. Haight's PhD thesis [Ha] settled the main problem: the averages can tend to 0. The problem is erdosproblems.com/1000, listed as "proved (Lean)". That status refers to the main problem, whose existing formalization is https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1000.lean. That file covers only the main existence theorem, not the limsup_eq_one variant.

## Citation

```bibtex
@misc{math0:erdos1000-erdos-1000-variants-limsup-eq-one,
  author       = {{math0}},
  title        = {{Erdős Problem 1000: liminf φ_A(k)/n_k = 0 forces limsup φ_A(k)/n_k = 1}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1000-erdos-1000-variants-limsup-eq-one}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

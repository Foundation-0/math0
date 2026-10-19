# Erdős 142 (Θ variant): no k-independent order of magnitude for r_k(N)

**Classification:** Misformalization found (upstream statement does not match the problem)  
**Area:** Number theory  
**Source problem:** Erdős Problem #142  
**Date:** 2026-10-17

## Result

Let r_k(N) = Set.IsAPOfLengthFree.maxCard k N be the largest size of a subset of {1,...,N} that contains no non-trivial k-term arithmetic progression. The upstream statement asks for one function answer : ℕ → ℝ such that for every k ∈ ℕ, (N ↦ r_k(N)) =Θ[atTop] answer. We prove the negation for every possible value of the unknown: for all a : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (r k N : ℝ)) =Θ[atTop] a.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos142_erdos_142_variants_isTheta.lean`](../../lean/Math0/ErdosProblems/Erdos142_erdos_142_variants_isTheta.lean) refutes, for every possible value of its unknown, the upstream statement [`Erdos142.erdos_142.variants.isTheta`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/142.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes_every_answer` checks that our theorem's type is syntactically identical to the upstream statement negated and universally quantified over the unknown and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 142 (erdosproblems.com/142, $10000 prize, listed open, OEIS A003002–A003005) asks for the order of magnitude, or an asymptotic formula, of r_k(N), the largest subset of {1,...,N} with no k-term AP.

Known results:
- Szemerédi: r_k(N) = o(N).
- Behrend (k = 3) and Rankin (general k): lower bounds of the form N·exp(−c(log N)^{1/ℓ}).
- Gowers: upper bounds for general k.
- Kelley–Meka (2023), improved by Bloom–Sisask: r_3(N) ≤ N·exp(−c(log N)^{1/12}), later exponent 1/9.
- Green–Tao: bounds for r_4.
- Leng–Sah–Sawhney (2024): r_k(N) ≤ N·exp(−(log log N)^{c_k}).

The order of magnitude of r_k is open for every k ≥ 3.

The facts the refutation uses are trivial and belong to the formal library: r_1(N) = N (`Set.IsAPOfLengthFree.maxCard_one`), and r_2(N) ≤ 1 because any two points form a 2-term AP. I know of no previous Lean artifact reporting that `erdos_142.variants.isTheta` (or the sibling `erdos_142`) is false because its answer does not depend on k. - erdosproblems.com/142: open, $10000; it gives order of magnitude as the "more reasonable" goal and cites [Er80], [Va99]. Best known bounds: Kelley–Meka 2023 (k=3), Green–Tao 2017 (k=4), Leng–Sah–Sawhney 2024 (k≥5). Lower bounds: Behrend 1946 and Rankin 1961.
- erdosproblems.com/forum/thread/142: a single comment by jleng01 (2026-08-09), unrelated to formalization.
- google-deepmind/formal-conjectures PR #5446 (open, 2026-09-10): flags 142.lean:37,56 as answer slots that cannot depend on the required binder k.

(Abridged; the manuscript discusses the literature in full.)

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:erdos142-erdos-142-variants-istheta,
  author       = {{math0}},
  title        = {{Erdős 142 (Θ variant): no k-independent order of magnitude for r_k(N)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos142-erdos-142-variants-istheta}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

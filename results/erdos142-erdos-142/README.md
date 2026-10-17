# Erdős 142: no single k-independent asymptotic formula for r_k(N)

**Classification:** Misformalization found (upstream statement does not match the problem)  
**Area:** Number theory  
**Source problem:** Erdős Problem #142  
**Date:** 2026-10-17

## Result

Let r_k(N) = Set.IsAPOfLengthFree.maxCard k N be the largest size of a subset of {1,...,N} that contains no non-trivial k-term arithmetic progression. The upstream statement says that for every k ∈ ℕ, the sequence N ↦ r_k(N) is asymptotically equivalent (as N → ∞) to erdos_142.answer : ℕ → ℝ, which is one fixed function that does not depend on k. We prove that this fails for every possible choice of that function: ∀ a : ℕ → ℝ, ¬ ∀ k, (fun N => (r k N : ℝ)) ~[atTop] a.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos142_erdos_142.lean`](../../lean/Math0/ErdosProblems/Erdos142_erdos_142.lean) refutes, for every possible value of its unknown, the upstream statement [`Erdos142.erdos_142`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/142.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes_every_answer` checks that our theorem's type is syntactically identical to the upstream statement negated and universally quantified over the unknown and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 142 ($10000 prize) is open. In erdosproblems problems.yaml, entry "142" has status "open" and formal_status "unformalized". The OEIS sequences A003002–A003005 give r_3 through r_6. Known bounds include:
- Szemerédi: r_k(N) = o(N).
- Behrend and Rankin: lower bounds of the form N·exp(-c(log N)^{1/ℓ}).
- Kelley–Meka (2023) and Bloom–Sisask: r_3(N) ≤ N·exp(-c(log N)^{1/9}).
- Green–Tao: k = 4.
- Leng–Sah–Sawhney (2024): k ≥ 5.

No asymptotic formula r_k(N) ~ f_k(N) is known for any k ≥ 3. The Lean result does not touch this question. It only shows that the upstream statement, with one answer for every k ∈ ℕ including k = 1 and k = 2, is false, which is a trivial consequence of r_1(N) = N and r_2(N) ≤ 1. Sources:
- erdosproblems.com/142: the problem is open, $10000 prize; the page says an asymptotic formula is "still far out of reach, even for k=3", lists bounds by Kelley–Meka (k=3), Green–Tao (k=4) and Leng–Sah–Sawhney (k≥5), and notes Erdős's [Er80] remark that it is not known whether r_k/r_{k+1} → 0.
- erdosproblems.com/forum/thread/142: only one unrelated comment, and nothing about the formal statement.

Upstream formal-conjectures history (google-deepmind/formal-conjectures):
- Commit 2c24ebe7 (#7327, 2026-10-14, M. Firsching): introduced the k-independent top-level `def erdos_142.answer : ℕ → ℝ := sorry`.
- Commit 7f64240c (#5810, 2026-09-12, S. Mercuri): changed Θ to ~ (fixes #5628 and #4922).
- Commit bf0ea56f (#1187, 2025-11-11): noted maxCard 0/1 N = N and

## Citation

```bibtex
@misc{math0:erdos142-erdos-142,
  author       = {{math0}},
  title        = {{Erdős 142: no single k-independent asymptotic formula for r_k(N)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos142-erdos-142}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

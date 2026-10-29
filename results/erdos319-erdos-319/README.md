# Erdős 319: no constant answer works for every N (formalization defect)

**Classification:** Misformalization found (upstream statement does not match the problem)  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #319  
**Date:** 2026-10-17

## Result

For N ∈ ℕ, let S_N be the set of sizes |A| of finite sets A ⊆ {1,…,N} for which there is δ : ℕ → {±1} with ∑_{n∈A} δ(n)/n = 0 and ∑_{n∈A'} δ(n)/n ≠ 0 for every nonempty proper subset A' ⊊ A. The upstream statement claims that a single natural number erdos_319.answer is the greatest element of S_N for every N. We prove the negation for every possible value: for every c ∈ ℕ, it is not true that c = max S_N for all N.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos319_erdos_319.lean`](../../lean/Math0/ErdosProblems/Erdos319_erdos_319.lean) refutes, for every possible value of its unknown, the upstream statement [`Erdos319.erdos_319`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/319.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes_every_answer` checks that our theorem's type is syntactically identical to the upstream statement negated and universally quantified over the unknown and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 319 (erdosproblems.com/319). problems.yaml lists it as status open, last updated 2025-08-31, with formal_status "unformalized" and formalized "yes"; no Lean proof is recorded. By the upstream file's comments, c(N) = Θ(N): trivially c(N) ≤ N, and a lower bound c(N) ≥ (1 − 1/e + o(1))N, observed by Adenwalla, follows from Croot, "On unit fractions with denominators in short intervals", Acta Arith. 2001. The refutation here concerns only the defective constant-answer formalization and says nothing about the open problem. - Erdős Problem #319: https://www.erdosproblems.com/319. Status open. It cites [ErGr80], Erdős–Graham, Old and New Problems and Results in Combinatorial Number Theory (1980). Its only result is Adenwalla's lower bound c(N) ≥ (1−1/e+o(1))N, derived from E. S. Croot III, "On unit fractions with denominators in short intervals", Acta Arith. 99 (2001) 99–114.
- Forum thread: https://www.erdosproblems.com/forum/thread/319. It has 0 comments and nothing about an upper bound or an exact value.

(Abridged; the manuscript discusses the literature in full.)

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:erdos319-erdos-319,
  author       = {{math0}},
  title        = {{Erdős 319: no constant answer works for every N (formalization defect)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos319-erdos-319}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

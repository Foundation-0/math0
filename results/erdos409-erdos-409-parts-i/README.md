# Erdős 409(i): no constant iteration count works for every starting value (formalization defect)

**Classification:** Misformalization found (upstream statement does not match the problem)  
**Area:** Number theory  
**Source problem:** Erdős Problem #409  
**Date:** 2026-10-17

## Result

The upstream statement says: for every n > 0, the least i ≥ 0 such that the i-th iterate of f(m) = φ(m) + 1, started at n, is prime equals one fixed natural number `erdos_409.parts.i.answer` (a constant that does not depend on n). We prove the negation for every possible value of that constant: for all a ∈ ℕ, it is not the case that for every n > 0, a is the least element of {i : f^[i](n) is prime}.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos409_erdos_409_parts_i.lean`](../../lean/Math0/ErdosProblems/Erdos409_erdos_409_parts_i.lean) refutes, for every possible value of its unknown, the upstream statement [`Erdos409.erdos_409.parts.i`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/409.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes_every_answer` checks that our theorem's type is syntactically identical to the upstream statement negated and universally quantified over the unknown and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

erdosproblems.com/409 (problems.yaml: status open, last_update 2025-08-31; OEIS A039651, A229487) asks how many iterations of n ↦ φ(n)+1 are needed to reach a prime. The answer is a function c(n), as in OEIS A039651, whose values include c(2)=0 and c(4)=1. The solver did not settle the actual asymptotic question, which the upstream erdos_409.parts.i.isTheta/isBigO/isLittleO variants state. The refutation uses only the fact that c(n) is not constant. erdosproblems.com/409 (open; attributed to Finucane, [ErGr80, p.81], Guy B41; it reads the question as bounding F(n), notes F(n)=o(n) is trivial and F(n)=1 infinitely often, per comments by S. Cambie). OEIS A039651 (number of iterations of n -> phi(n)+1 to reach a prime: a(1)=1, a(2)=0, a(3)=0, a(4)=1, so the value is not constant) and A229487. Local problems.yaml entry for 409: status open (2025-08-31), formalized yes. Upstream google-deepmind/formal-conjectures FormalConjectures/ErdosProblems/409.lean on main still declares `def erdos_409.parts.i.answer : ℕ := sorry` with the per-n IsLeast claim. The file has isTheta/isBigO/isLittleO variants with c : ℕ → ℕ that state the intended problem correctly. Formal Conjectures paper (arXiv 2605.13171) gives the misformalization taxonomy (translation-level error). I found no prior public report of this specific defect.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:erdos409-erdos-409-parts-i,
  author       = {{math0}},
  title        = {{Erdős 409(i): no constant iteration count works for every starting value (formalization defect)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos409-erdos-409-parts-i}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

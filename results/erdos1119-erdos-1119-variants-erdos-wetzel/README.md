# Erdős–Wetzel theorem: if ℵ₁ < 𝔠, families of entire functions with countably many values at each point are countable

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Logic, Complex analysis  
**Source problem:** Erdős Problem #1119  
**Date:** 2026-10-17

## Result

Assume ℵ₁ < 𝔠. Let F be a set of entire functions ℂ → ℂ such that for every z₀ ∈ ℂ the set of values {f(z₀) : f ∈ F} is countable. Then F is countable. (Formally, the hypothesis ℵ_1 < 𝔠 is stated in an arbitrary universe `Cardinal.{u_1}`.)

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1119_erdos_1119_variants_erdos_wetzel.lean`](../../lean/Math0/ErdosProblems/Erdos1119_erdos_1119_variants_erdos_wetzel.lean) proves the upstream statement [`Erdos1119.erdos_1119.variants.erdos_wetzel`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1119.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

- Erdős, P., "An interpolation problem associated with the continuum hypothesis", Michigan Math. J. 11 (1964), 9–10. This is the original theorem: ¬CH implies the family is countable, and CH gives an uncountable counterexample.
- Hayman, W. K., Research problems in function theory (1974), Problem 2.46.
- Kumar–Shelah, Fund. Math. 2017, and Schilhan–Weinert, J. London Math. Soc. 2024. These give the independence of the general-cardinal problem.
- Earlier formalizations:
  - plby/lean-proofs (Boris Alexeev; Codex/GPT), src/latest/ErdosProblems/Erdos1119.lean at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. It proves easy_case and `erdos_1119` (ℵ_1 < 𝔠 → pointwise-countable entire family is countable), and aliases it to `erdos_1119.variants.erdos_wetzel`.
  - Collin Yuanjie Ren, Lean proof of the full Wetzel/CH biconditional (github.com/CollinYuanjieRen/awards, jsp-000930-cyr). It is credited in the erdosproblems.com formal_status note, and the formalized state there is "yes".
  - L. C. Paulson, "Wetzel's Problem and the Continuum Hypothesis", Isabelle AFP (2022).

## Citation

```bibtex
@misc{math0:erdos1119-erdos-1119-variants-erdos-wetzel,
  author       = {{math0}},
  title        = {{Erdős–Wetzel theorem: if ℵ₁ < 𝔠, families of entire functions with countably many values at each point are countable}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1119-erdos-1119-variants-erdos-wetzel}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

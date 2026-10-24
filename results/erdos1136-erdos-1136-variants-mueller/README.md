# Müller's set avoids sums equal to powers of two and has density 1/2 (Erdős 1136)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** Erdős Problem #1136  
**Date:** 2026-10-17

## Result

Let M be the set of natural numbers n such that n ≡ 3·2^i (mod 2^{i+2}) for some i ≥ 0. Then (1) no a, b ∈ M (not necessarily distinct) satisfy a + b = 2^k for any k ≥ 0, and (2) M has natural density 1/2: #(M ∩ [0,b)) / b → 1/2 as b → ∞.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_mueller.lean`](../../lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_mueller.lean) proves the upstream statement [`Erdos1136.erdos_1136.variants.mueller`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1136.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The result is H. Müller, "Über ein additiv-zahlentheoretisches Problem von P. Erdős", Mitt. Math. Ges. Hamburg (2011), 75-78. erdosproblems.com/1136 lists the status "proved (Lean)" (2026-04-19). Earlier Lean proofs exist:
- plby/lean-proofs src/v4.29.1/ErdosProblems/Erdos1136.lean (by Aristotle, L. Luccioli and W. van Doorn), which proves the same set is sum-free (`A_sumfree`) and has density 1/2 (`A_density_half`).
- Luccioli's gist on live.lean-lang.org.
- Woett/Lean-files ErdosProblem1136.lean.

## Citation

```bibtex
@misc{math0:erdos1136-erdos-1136-variants-mueller,
  author       = {{math0}},
  title        = {{Müller's set avoids sums equal to powers of two and has density 1/2 (Erdős 1136)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1136-erdos-1136-variants-mueller}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

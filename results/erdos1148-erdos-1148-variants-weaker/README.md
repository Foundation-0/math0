# Every n is x² + y² − z² with max(x², y², z²) ≤ n + 2√n

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Erdős Problem #1148  
**Date:** 2026-10-17

## Result

For every natural number n there exist natural numbers x, y, z with n = x² + y² − z² (the subtraction is truncated subtraction on ℕ) and x², y², z² ≤ n + 2√n, where √n is the real square root. This is the relaxed form of Erdős Problem 1148, which [Va99] calls "obvious".

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1148_erdos_1148_variants_weaker.lean`](../../lean/Math0/ErdosProblems/Erdos1148_erdos_1148_variants_weaker.lean) proves the upstream statement [`Erdos1148.erdos_1148.variants.weaker`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1148.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

[Va99] "Some of Paul's favorite problems", the booklet for the conference "Paul Erdős and his mathematics" (Budapest, 1999), calls the n + 2√n relaxation "obvious". The main Erdős 1148 problem (bound ≤ n, for large n) was proved by Chojecki [Ch26], "Bounded Representations by x²+y²−z²" (2026). Its Lean proof is plby/lean-proofs src/latest/ErdosProblems/Erdos1148.lean at commit 8822f7d, and it covers only the main theorem for large n, not the weaker variant for every n. In erdosproblems.com's problems.yaml, problem 1148 has status "proved (Lean)" and OEIS entries A390380 and A393168. The upstream formal-conjectures file FormalConjectures/ErdosProblems/1148.lean has a formal_proof link on erdos_1148 only.

## Citation

```bibtex
@misc{math0:erdos1148-erdos-1148-variants-weaker,
  author       = {{math0}},
  title        = {{Every n is x² + y² − z² with max(x², y², z²) ≤ n + 2√n}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1148-erdos-1148-variants-weaker}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

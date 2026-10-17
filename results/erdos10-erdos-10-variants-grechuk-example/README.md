# Grechuk's example: 1117175146 is not a prime plus at most three powers of two

**Classification:** First formal proof of a known result  
**Area:** Combinatorics, Number theory  
**Source problem:** Erdős Problem #10  
**Date:** 2026-10-17

## Result

Let N = 1117175146. There is no prime p and no multiset of at most three natural numbers e_1, ..., e_k (k ≤ 3, repetitions allowed) with N = p + 2^{e_1} + ... + 2^{e_k}. Formally: 1117175146 ∉ sumPrimeAndTwoPows 3, where sumPrimeAndTwoPows k = { p + Σ_{e ∈ pows} 2^e : p prime, pows a multiset of naturals with card pows ≤ k }.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos10_erdos_10_variants_grechuk_example.lean`](../../lean/Math0/ErdosProblems/Erdos10_erdos_10_variants_grechuk_example.lean) proves the upstream statement [`Erdos10.erdos_10.variants.grechuk_example`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/10.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Sources:
- erdosproblems.com/10: the problem is open; it records Bogdan Grechuk's observation that 1117175146 is not a prime plus at most 3 powers of 2, without showing how it was verified. The local problems.yaml lists problem 10 with status open and formalized "yes", with no Lean proof noted for this example.
- Related references: Granville and Soundararajan (1998), the conjecture this example bears on for even integers; Crocker (1971), the infinitude construction.
- The upstream formal_proof link for the infinite variant `erdos_10.variants.grechuk` (DaryxXx gist e112c74c…, Main.lean) does not contain 1117175146. The `two_pows` link is to anatoliiohorodnyk/lean-fc-proofs, whose (truncated) listing has no grechuk_example file.
- A web search for "1117175146" with Lean found nothing.
- Conclusion: the statement is known (a computational fact due to Grechuk), and this appears to be its first Lean formalization.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:erdos10-erdos-10-variants-grechuk-example,
  author       = {{math0}},
  title        = {{Grechuk's example: 1117175146 is not a prime plus at most three powers of two}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos10-erdos-10-variants-grechuk-example}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

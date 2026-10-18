# Erdős–Hajnal: infinite chromatic number with independent sets of size m/2 − cm for every c > 1/4

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #750  
**Date:** 2026-10-17

## Result

For every real c > 1/4 (formally c ∈ ℝ≥0) there is a graph G, on a vertex type in any prescribed universe, with chromatic number ∞, such that every set S of m ≥ 1 vertices contains an independent set I with m/2 − c·m ≤ |I|. The subtraction is truncated subtraction in ℝ≥0.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos750_erdos_750_variants_c_gt_quarter.lean`](../../lean/Math0/ErdosProblems/Erdos750_erdos_750_variants_c_gt_quarter.lean) proves the upstream statement [`Erdos750.erdos_750.variants.c_gt_quarter`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/750.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The problem and its variants:
- Erdős and Hajnal [ErHa67b], "On chromatic graphs", Mat. Lapok (1967), 1–4: graphs of infinite chromatic number in which every m-vertex subgraph has an independent set of size at least m/2 − cm, for any c > 1/4. The classical example is the shift graph with the random-cut argument used here.
- Erdős, Hajnal and Szemerédi [EHS82]: the f(m) = εm case, via a comment by Sellke on erdosproblems.
- Chojecki with GPT-5.5 Pro (ulam.ai/research/erdos750.pdf): the general f → ∞ case.
- Stiebitz [St85], Sachs and Stiebitz [SaSt89], Müller and Stehlík [MuSt19]: the generalised Mycielskian chromatic bound used in that proof.

Existing Lean proofs:
- plby/lean-proofs src/latest/ErdosProblems/Erdos750.lean, commit 8822f7dd: an unconditional `theorem erdos_750` in formal-conjectures form. It implies variants.c_gt_quarter directly by taking f(m) = c·m.
- Jayyhk/erdos-lean problems/750/Erdos750.lean.
- Shashi456/erdos-formalizations: the conditional version.
- erdosproblems.com lists #750 as "proved (Lean)", last updated 2025-08-31.

## Citation

```bibtex
@misc{math0:erdos750-erdos-750-variants-c-gt-quarter,
  author       = {{math0}},
  title        = {{Erdős–Hajnal: infinite chromatic number with independent sets of size m/2 − cm for every c > 1/4}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos750-erdos-750-variants-c-gt-quarter}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

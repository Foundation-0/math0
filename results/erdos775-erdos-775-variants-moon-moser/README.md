# Moon–Moser: a graph on n vertices has at most n − log₂ n + 1 maximal-clique sizes

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #775  
**Date:** 2026-10-17

## Result

There is a real constant C such that for every n ∈ ℕ and every simple graph G on Fin n, the number of distinct sizes of maximal cliques of G (the ncard of SimpleGraph.cliqueSizes G = {k | ∃ S : Finset, S is a maximal clique, |S| = k}) is at most n − log₂ n + C. Here Real.logb 2 0 = 0. We prove it with C = 1, for every n including n = 0.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos775_erdos_775_variants_moon_moser.lean`](../../lean/Math0/ErdosProblems/Erdos775_erdos_775_variants_moon_moser.lean) proves the upstream statement [`Erdos775.erdos_775.variants.moon_moser`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/775.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

J. W. Moon and L. Moser, "On cliques in graphs", Israel J. Math. 3 (1965), 23-28. Proves that the number of distinct maximal-clique sizes on n vertices is at most n − ⌊log₂ n⌋, which is the n − log₂ n + O(1) upper bound. J. H. Spencer, "On cliques in graphs", Israel J. Math. 9 (1971), 419-421. Gives the matching lower-bound construction. J. Gao, "On cliques in hypergraphs", arXiv:2510.14804 (2025). Settles the main 3-uniform hypergraph question. erdosproblems.com/775 has status "disproved (Lean)". The existing Lean proof (github.com/plby/lean-proofs src/v4.29.1/ErdosProblems/Erdos775.lean, by Aristotle and L. Luccioli) covers only Gao's hypergraph theorem, not the graph Moon–Moser variant.

## Citation

```bibtex
@misc{math0:erdos775-erdos-775-variants-moon-moser,
  author       = {{math0}},
  title        = {{Moon–Moser: a graph on n vertices has at most n − log₂ n + 1 maximal-clique sizes}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos775-erdos-775-variants-moon-moser}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

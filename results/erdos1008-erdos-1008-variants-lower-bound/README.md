# Erdős Problem 1008: every graph with m edges has a C4-free subgraph with at least √m/2 edges

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #1008  
**Date:** 2026-10-17

## Result

There is a constant c > 0 such that for every finite type V and every simple graph G on V, some subgraph H ≤ G contains no copy of the 4-cycle C4 and satisfies c · m^{1/2} ≤ |E(H)|, where m = |E(G)|. (Erdős, [Er71], called this bound "trivial" and asked for m^{2/3}.) We prove it with c = 1/2.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1008_erdos_1008_variants_lower_bound.lean`](../../lean/Math0/ErdosProblems/Erdos1008_erdos_1008_variants_lower_bound.lean) proves the upstream statement [`Erdos1008.erdos_1008.variants.lower_bound`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1008.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The source is Erdős [Er71], "Some unsolved problems in graph theory and combinatorial analysis" (1971), which notes that ≫ m^{1/2} is trivial and asks for m^{2/3}. The m^{2/3} bound was proved by Conlon, Fox and Sudakov [CFS14b], "Large subgraphs without complete bipartite graphs" (arXiv:1401.6711), and Hunter gave a simpler proof in the erdosproblems forum. The main statement is formalized in Lean at https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1008.lean (Aristotle / Boris Alexeev), with constant 1/2 and exponent 2/3, and erdosproblems.com lists 1008 as "proved (Lean)". The exponent-1/2 variant follows immediately from that formalized result. The folklore argument used here (max degree versus maximum matching, m ≤ 2Δν) is standard.

## Citation

```bibtex
@misc{math0:erdos1008-erdos-1008-variants-lower-bound,
  author       = {{math0}},
  title        = {{Erdős Problem 1008: every graph with m edges has a C4-free subgraph with at least √m/2 edges}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1008-erdos-1008-variants-lower-bound}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

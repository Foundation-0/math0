# Cliques in the non-commuting graph have at most [G : Z(G)] vertices

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics, Group theory  
**Source problem:** Erdős Problem #1098  
**Date:** 2026-10-17

## Result

Let G be a group and let Γ(G) be its non-commuting graph: the vertices are the elements of G, and g and h are adjacent iff gh ≠ hg. If the centre Z(G) has finite index n = [G : Z(G)], then Γ(G) contains no complete subgraph on n + 1 vertices (Lean: `(nonCommutingGraph G).CliqueFree ((Subgroup.center G).index + 1)` under `[(Subgroup.center G).FiniteIndex]`). This is the remark Neumann (1976) made in answering Erdős Problem 1098.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1098_erdos_1098_variants_upper_bound.lean`](../../lean/Math0/ErdosProblems/Erdos1098_erdos_1098_variants_upper_bound.lean) proves the upstream statement [`Erdos1098.erdos_1098.variants.upper_bound`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1098.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

B. H. Neumann, "A problem of Paul Erdős on groups", J. Austral. Math. Soc. Ser. A 21 (1976), 467–472. It proves that Γ(G) has no infinite clique iff [G:Z(G)] < ∞, and remarks that a clique has at most [G:Z(G)] vertices. erdosproblems.com/1098 lists the problem as "proved (Lean)" (problems.yaml, 2026-05-02). The existing Lean formalization is plby/lean-proofs, src/v4.29.1/ErdosProblems/Erdos1098.lean, which is linked as formal_proof on upstream erdos_1098. Its theorem `erdos1098` contains the same coset-injection bound S.card ≤ Nat.card (G ⧸ center G) for pairwise non-commuting finsets under finite index, and `IsFIZGroup.isPEGroup` uses the same argument.

## Citation

```bibtex
@misc{math0:erdos1098-erdos-1098-variants-upper-bound,
  author       = {{math0}},
  title        = {{Cliques in the non-commuting graph have at most [G : Z(G)] vertices}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1098-erdos-1098-variants-upper-bound}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# A 7-regular 3-critical 3-uniform hypergraph on 9 vertices (Erdős Problem 834, chromatic version)

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #834  
**Date:** 2026-10-17

## Result

There exist n and a 3-uniform hypergraph H on the vertex set {0,…,n−1} such that: (1) H has weak chromatic number exactly 3, meaning it has a vertex 3-coloring with no monochromatic edge but no such coloring with 0, 1 or 2 colors; (2) for every edge e of H, the hypergraph H − e is 2-colorable; (3) for every vertex v, the hypergraph made of the edges of H that avoid v is 2-colorable; and (4) every vertex of {0,…,n−1} lies in at least 7 edges. This is the question of Erdős and Lovász, Erdős Problem 834, part (ii), answered positively by Li [Li25] with a 22-edge example.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos834_erdos_834_parts_ii.lean`](../../lean/Math0/ErdosProblems/Erdos834_erdos_834_parts_ii.lean) proves the upstream statement [`Erdos834.erdos_834.parts.ii`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/834.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 834 (erdosproblems.com/834, from [Er74d, p.282], a problem of Erdős and Lovász). It was solved by R. Li, "On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7", arXiv:2512.24850 (Dec 2025). For the transversal reading, Li shows there are at most 10 edges, so some vertex has degree at most 6, and K_5^(3) shows this is sharp. For the chromatic reading, Li gives an explicit 9-vertex 3-graph with minimum degree 7 (22 edges per the solver) and backs it with witness 2-colorings and a verification script, not a Lean proof. The erdosproblems database (problems.yaml) lists status "solved" (not "(Lean)") and formal_status "unformalized". The formal-conjectures statement Erdos834.erdos_834.parts.ii is still sorry. The solver's witness is a different, 21-edge 7-regular hypergraph on 9 vertices.

## Citation

```bibtex
@misc{math0:erdos834-erdos-834-parts-ii,
  author       = {{math0}},
  title        = {{A 7-regular 3-critical 3-uniform hypergraph on 9 vertices (Erdős Problem 834, chromatic version)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos834-erdos-834-parts-ii}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

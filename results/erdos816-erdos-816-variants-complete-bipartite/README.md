# K_{n,n+1} is extremal for Erdős Problem 816

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #816  
**Date:** 2026-10-17

## Result

For every natural number n, the complete bipartite graph K_{n,n+1} (vertex set Fin n ⊕ Fin (n+1), so 2n+1 vertices) has exactly n^2 + n edges, and it does not contain two distinct vertices u ≠ v with deg u = deg v that are joined by a path of length 3.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos816_erdos_816_variants_complete_bipartite.lean`](../../lean/Math0/ErdosProblems/Erdos816_erdos_816_variants_complete_bipartite.lean) proves the upstream statement [`Erdos816.erdos_816.variants.complete_bipartite`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/816.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 816 (Erdős–Hajnal), erdosproblems.com/816 (status: proved, not marked as Lean). [Er91] Erdős, Problems and results in combinatorial analysis and combinatorial number theory (1991), where K_{n,n+1} is the standard example showing that n^2+n edges do not suffice. [ChMa25] K. Chen and J. Ma, arXiv:2503.19569 (2025), proved the main conjecture and showed that for n ≥ 600, K_{n,n+1} is the unique exception with n^2+n edges. The main theorem has an existing Lean proof at plby/lean-proofs (commit 8822f7d, src/latest/ErdosProblems/Erdos816.lean, L939), but that file contains no K_{n,n+1} or complete_bipartite lemma. So this variant appears to be formalized here for the first time.

## Citation

```bibtex
@misc{math0:erdos816-erdos-816-variants-complete-bipartite,
  author       = {{math0}},
  title        = {{K_{n,n+1} is extremal for Erdős Problem 816}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos816-erdos-816-variants-complete-bipartite}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

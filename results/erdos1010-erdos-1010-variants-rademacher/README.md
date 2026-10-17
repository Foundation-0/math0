# Rademacher's theorem: ⌊n²/4⌋+1 edges force ⌊n/2⌋ triangles

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #1010  
**Date:** 2026-10-17

## Result

For every n ∈ ℕ and every simple graph G on the vertex set Fin n with exactly ⌊n²/4⌋ + 1 edges, G contains at least ⌊n/2⌋ triangles (3-cliques).

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1010_erdos_1010_variants_rademacher.lean`](../../lean/Math0/ErdosProblems/Erdos1010_erdos_1010_variants_rademacher.lean) proves the upstream statement [`Erdos1010.erdos_1010.variants.rademacher`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1010.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Rademacher (1941, unpublished, reported by Erdős): a graph with ⌊n²/4⌋+1 edges has at least ⌊n/2⌋ triangles. Erdős, "On a theorem of Rademacher-Turán", Illinois J. Math. 6 (1962) 122-127, proves t⌊n/2⌋ for t < cn. Lovász–Simonovits (1976) and Nikiforov–Khadzhiivanov, C. R. Acad. Bulgare Sci. (1981), settle the case t < ⌊n/2⌋ (erdosproblems #1010, status: proved). An existing Lean 4 formalization of the general statement, which implies this variant at t = 1, is plby/lean-proofs src/latest/ErdosProblems/Erdos1010.lean (commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, theorem erdos_1010 at L612). It is linked through the formal_proof attribute on Erdos1010.erdos_1010 in /home/user/math0/lean/.lake/packages/formal_conjectures/FormalConjectures/ErdosProblems/1010.lean.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:erdos1010-erdos-1010-variants-rademacher,
  author       = {{math0}},
  title        = {{Rademacher's theorem: ⌊n²/4⌋+1 edges force ⌊n/2⌋ triangles}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1010-erdos-1010-variants-rademacher}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

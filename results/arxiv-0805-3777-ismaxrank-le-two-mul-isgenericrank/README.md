# Maximal tensor rank is at most twice the generic rank (Blekherman–Teitler)

**Classification:** First formal proof of a known result  
**Area:** Algebraic geometry, Linear algebra  
**Source problem:** arXiv:0805.3777  
**Date:** 2026-10-17

## Result

Let ds be any list of dimensions, and consider complex tensors (Holor ℂ ds) with the product topology on HolorIndex ds → ℂ. Suppose r is a generic rank: there is an open dense set U of tensors, all of CP rank exactly r. Suppose R is the maximal rank: R is the largest CP rank of any tensor of format ds. Then R ≤ 2r. This is [BT15, Theorem 1] (Blekherman–Teitler), as formalized in formal-conjectures (FormalConjectures/Arxiv/0805.3777/TensorRank.lean).

## Verification

The Lean file [`lean/Math0/Arxiv/Arxiv_0805_3777_isMaxRank_le_two_mul_isGenericRank.lean`](../../lean/Math0/Arxiv/Arxiv_0805_3777_isMaxRank_le_two_mul_isGenericRank.lean) proves the upstream statement [`Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/0805.3777/TensorRank.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The source is G. Blekherman and Z. Teitler, "On maximum, typical and generic ranks", Math. Ann. 362 (2015), 1021–1031, doi:10.1007/s00208-014-1150-3, arXiv:1402.2371, Theorem 1. It states that the maximum rank is at most twice the generic rank for any nondegenerate irreducible variety. The case here is the Segre variety, i.e. tensors. The upstream file is FormalConjectures/Arxiv/0805.3777/TensorRank.lean, which builds on Friedland, LAA 436 (2012), arXiv:0805.3777. It has no formal_proof link for this item, and I know of no earlier Lean proof.

## Citation

```bibtex
@misc{math0:arxiv-0805-3777-ismaxrank-le-two-mul-isgenericrank,
  author       = {{math0}},
  title        = {{Maximal tensor rank is at most twice the generic rank (Blekherman–Teitler)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/arxiv-0805-3777-ismaxrank-le-two-mul-isgenericrank}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

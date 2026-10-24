# The Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n

**Classification:** First formal proof of a known result  
**Area:** Algebraic geometry, Nonassociative algebra  
**Source problem:** arXiv:math.0608009  
**Date:** 2026-10-17

## Result

Let K be a field of characteristic zero and n a natural number. Suppose the Jacobian conjecture holds in 2n variables over K: every polynomial map F : K^{2n} -> K^{2n} whose Jacobian determinant is a unit of K[x_1,...,x_{2n}] has a polynomial two-sided compositional inverse. Then every K-algebra endomorphism phi of K[x_1..x_n, y_1..y_n] that preserves the canonical Poisson bracket {f,g} = sum_i (d_{x_i} f d_{y_i} g - d_{y_i} f d_{x_i} g) on the generators, i.e. {phi(X_v), phi(X_w)} = {X_v, X_w} for all v, w, is bijective. (Adjamagbo and van den Essen, arXiv math/0608009, Theorems 1 and 7.)

## Verification

The Lean file [`lean/Math0/Arxiv/Arxiv_math_0608009_poisson_conjecture_variants_jacobian_implication.lean`](../../lean/Math0/Arxiv/Arxiv_math_0608009_poisson_conjecture_variants_jacobian_implication.lean) proves the upstream statement [`Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

K. Adjamagbo and A. van den Essen, "On the equivalence of the Jacobian, Dixmier and Poisson conjectures in any characteristic", arXiv math/0608009, published as "A proof of the equivalence of the Dixmier, Jacobian and Poisson conjectures", Acta Math. Vietnam. 32 (2007) 205-214. Theorem 1 / Theorem 7 there state JC_{2n} ⇒ PC_n ⇒ DC_n ⇒ JC_n; JC_{2n} ⇒ PC_n is the step proved here. Related: Bass-Connell-Wright 1982 (DC_n ⇒ JC_n); Tsuchimoto and Belov-Kanel-Kontsevich (JC_{2n} ⇒ DC_n). Upstream records JC as false in dimension 3 (Alpöge 2026) and PC_2 as false (Long 2026), so the hypothesis here is false for n ≥ 2 and the case that still matters, JC_2 ⇒ PC_1, is nontrivial. Upstream has no formal_proof link for this item.

## Citation

```bibtex
@misc{math0:arxiv-math-0608009-poisson-conjecture-variants-jacobian-implication,
  author       = {{math0}},
  title        = {{The Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/arxiv-math-0608009-poisson-conjecture-variants-jacobian-implication}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

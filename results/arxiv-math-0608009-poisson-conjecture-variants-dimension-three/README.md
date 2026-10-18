# The Poisson conjecture fails in dimension three

**Classification:** First formal proof of a known result  
**Area:** Algebraic geometry, Nonassociative algebra  
**Source problem:** arXiv:math.0608009  
**Date:** 2026-10-17

## Result

Let K be a field of characteristic zero and P_3(K) = K[x_1,x_2,x_3,y_1,y_2,y_3] with the canonical Poisson bracket {f,g} = sum_i (d_{x_i} f d_{y_i} g - d_{y_i} f d_{x_i} g). Then some K-algebra endomorphism phi of P_3(K) is not bijective even though it preserves the bracket on generators ({phi(v), phi(w)} = {v, w} for all variables v, w). So PC_3 (every Poisson endomorphism of P_3(K) is an automorphism) is false. Formally: for every field K with CharZero K, ¬ PoissonConjectureFor K 3.

## Verification

The Lean file [`lean/Math0/Arxiv/Arxiv_math_0608009_poisson_conjecture_variants_dimension_three.lean`](../../lean/Math0/Arxiv/Arxiv_math_0608009_poisson_conjecture_variants_dimension_three.lean) proves the upstream statement [`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

[AvdE07] K. Adjamagbo and A. van den Essen, arXiv:math/0608009, Acta Math. Vietnam. 32 (2007): defines PC_n (Notations 5), Lemma 2 (preserving brackets on generators suffices), and Theorem 7 (JC_{2n} ⇒ PC_n ⇒ DC_n ⇒ JC_n). [Alp26] L. Alpöge (2026): counterexample to the Jacobian conjecture in dimension 3. The upstream formal-conjectures file FormalConjectures/Wikipedia/JacobianConjecture.lean formalizes a variant G with Jacobian determinant 1 that is not injective (det_jacobian_G, aeval_G_eq). Upstream FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean marks dimension_three as "research solved" with a sorry proof, no formal_proof link, and a docstring describing exactly this cotangent-lift argument. [Lon26] C. D. Long, arXiv:2608.23777, settles PC_2 and is not relevant to n=3.

## Citation

```bibtex
@misc{math0:arxiv-math-0608009-poisson-conjecture-variants-dimension-three,
  author       = {{math0}},
  title        = {{The Poisson conjecture fails in dimension three}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/arxiv-math-0608009-poisson-conjecture-variants-dimension-three}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

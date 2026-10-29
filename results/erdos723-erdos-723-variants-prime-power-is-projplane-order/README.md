# Projective planes exist for every prime-power order (Erdős 723, existence variant)

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #723  
**Date:** 2026-10-17

## Result

For every natural number n that is a prime power, there exist types P, L (in Type), a membership (incidence) relation between P and L, Fintype structures on P and L, and a projective plane structure pp on (P, L) whose order is exactly n.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos723_erdos_723_variants_prime_power_is_projplane_order.lean`](../../lean/Math0/ErdosProblems/Erdos723_erdos_723_variants_prime_power_is_projplane_order.lean) proves the upstream statement [`Erdos723.erdos_723.variants.prime_power_is_projplane_order`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/723.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The construction of the Desarguesian projective plane PG(2, q) for every prime power q goes back to O. Veblen and W. H. Bussey, "Finite projective geometries", Trans. AMS 7 (1906), 241–259. Standard textbook sources are M. Hall, "Combinatorial Theory", and P. Dembowski, "Finite Geometries" (1968). The open converse is the prime power conjecture (Erdős Problem 723). Related results are Bruck–Ryser (1949), and Lam–Thiel–Swiercz (1989), who showed there is no plane of order 10. In Lean, Mathlib's Combinatorics/Configuration.lean has `Configuration.ofField` (the ProjectivePlane instance on ℙ(K³)) and `ProjectivePlane.card_points`, and LinearAlgebra/Projectivization/Cardinality.lean has `Projectivization.card_of_finrank`. Mathlib does not state the order of ofField or the existence of a plane of every prime-power order, and erdosproblems.com lists 723 as formal_status "unformalized".

## Citation

```bibtex
@misc{math0:erdos723-erdos-723-variants-prime-power-is-projplane-order,
  author       = {{math0}},
  title        = {{Projective planes exist for every prime-power order (Erdős 723, existence variant)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos723-erdos-723-variants-prime-power-is-projplane-order}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

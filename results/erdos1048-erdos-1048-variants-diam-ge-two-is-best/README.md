# Erdős 1048: the component of {|zⁿ| ≤ 1} containing 0 has diameter exactly 2

**Classification:** First formal proof of a known result  
**Area:** Complex analysis  
**Source problem:** Erdős Problem #1048  
**Date:** 2026-10-17

## Result

For every natural number n ≥ 1, the connected component containing 0 of the level set {z ∈ ℂ : |zⁿ| ≤ 1} has (extended) diameter exactly 2. So the Erdős–Herzog–Piranian bound, which says the component containing 0 has diameter ≥ 2 when all roots lie in |z| ≤ r ≤ 1/2, is attained by f(z) = zⁿ.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1048_erdos_1048_variants_diam_ge_two_is_best.lean`](../../lean/Math0/ErdosProblems/Erdos1048_erdos_1048_variants_diam_ge_two_is_best.lean) proves the upstream statement [`Erdos1048.erdos_1048.variants.diam_ge_two_is_best`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1048.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

- Erdős, P., Herzog, F. and Piranian, G., "Metric properties of polynomials", J. Analyse Math. 6 (1958), 125–148. This is the source of the diam ≥ 2 bound for 0 ≤ r ≤ 1/2 and of the remark that zⁿ shows it is sharp.
- Pommerenke, Ch., "On metric properties of complex polynomials", Michigan Math. J. (1961), 97–115.
- erdosproblems.com/1048: status "disproved (Lean)" as of 2026-01-27.
- The existing Lean proof at https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1048.lean (Aristotle / Boris Alexeev) covers only the main disproof, `not_erdos_1048`, through Pommerenke's zⁿ − rⁿ example with r > 1. It does not prove `erdos_1048.variants.diam_ge_two_is_best`.

## Citation

```bibtex
@misc{math0:erdos1048-erdos-1048-variants-diam-ge-two-is-best,
  author       = {{math0}},
  title        = {{Erdős 1048: the component of {|zⁿ| ≤ 1} containing 0 has diameter exactly 2}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1048-erdos-1048-variants-diam-ge-two-is-best}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

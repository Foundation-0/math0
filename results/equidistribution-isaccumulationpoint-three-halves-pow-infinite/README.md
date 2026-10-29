# The fractional parts of (3/2)^n have infinitely many accumulation points

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Books / UniformDistributionOfSequences / Equidistribution  
**Date:** 2026-10-17

## Result

Let r_n = {(3/2)^n} be the fractional part of (3/2)^n for n = 0, 1, 2, .... Call x an accumulation point of (r_n) if x lies in the closure of {r_n : n ∈ ℕ} \ {x}. Then the set of accumulation points of (r_n) is infinite. (Vijayaraghavan's theorem, cited in Kuipers–Niederreiter, Uniform Distribution of Sequences, Ch. 1.)

## Verification

The Lean file [`lean/Math0/Books/Equidistribution_isAccumulationPoint_three_halves_pow_infinite.lean`](../../lean/Math0/Books/Equidistribution_isAccumulationPoint_three_halves_pow_infinite.lean) proves the upstream statement [`Equidistribution.isAccumulationPoint_three_halves_pow_infinite`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Books/UniformDistributionOfSequences/Equidistribution.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

T. Vijayaraghavan, "On the fractional parts of the powers of a number", J. London Math. Soc. 15 (1940), 159–160, proves that {(p/q)^n}, and in particular {(3/2)^n}, has infinitely many limit points. Kuipers & Niederreiter, Uniform Distribution of Sequences (1974), Ch. 1 notes cite it in the source referenced by the upstream file. Upstream google-deepmind/formal-conjectures (main, checked 2026-10-17) still has `sorry` for this theorem, and I know of no previous Lean proof.

## Citation

```bibtex
@misc{math0:equidistribution-isaccumulationpoint-three-halves-pow-infinite,
  author       = {{math0}},
  title        = {{The fractional parts of (3/2)^n have infinitely many accumulation points}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/equidistribution-isaccumulationpoint-three-halves-pow-infinite}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

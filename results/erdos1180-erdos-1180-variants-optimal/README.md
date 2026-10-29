# Erdős 1180, "optimal" variant: false as stated (C_ε grows exponentially in 1/ε, because the constant must cover all primes)

**Classification:** Misformalization found (upstream statement does not match the problem)  
**Area:** Number theory  
**Source problem:** Erdős Problem #1180  
**Date:** 2026-10-17

## Result

For ε > 0 let C(ε) be the least natural number C such that for every prime p and every residue a mod p there is a multiset s of integers n with 1 ≤ n ≤ p^ε and gcd(n,p)=1, |s| ≤ C, and Σ_{n∈s} n^{-1} ≡ a (mod p). If no such C exists, C(ε) = 0 (Lean's sInf ∅ = 0). The upstream statement says: for every δ > 0, C(ε) ≤ ε^{-(1+δ)} for all sufficiently small ε > 0. We prove the negation: there is a δ > 0 (δ = 1 works) such that C(ε) > ε^{-2} for arbitrarily small ε > 0, namely ε = 1/(m+1) for every large m.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos1180_erdos_1180_variants_optimal.lean`](../../lean/Math0/ErdosProblems/Erdos1180_erdos_1180_variants_optimal.lean) refutes (proves the negation of) the upstream statement [`Erdos1180.erdos_1180.variants.optimal`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1180.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes` checks that our theorem's type is syntactically identical to the upstream statement (negated) and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős and Graham, Old and new problems and results in combinatorial number theory (1980), the source of the question. Shparlinski, Arch. Math. (Basel) 2002, pp. 445–448: at most ε⁻³ summands for all p ≥ P(ε). Glibichuk, Mat. Zametki 2006, pp. 384–395: at most ε⁻² summands for all p ≥ P(ε); his covering lemma is the 8XY = F_p result for antisymmetric Y with |X||Y| > p. erdosproblems.com/1180 is marked proved, and its remark that "it may be that C_ε ≤ ε^{-1-o(1)}" is meant for large primes. The upstream formal-conjectures file 1180.lean already notes, in the docstring of variants.shparlinski, that no polynomial bound can hold for all primes. Upstream also links Lean proofs of the main statement and the shparlinski, glibichuk and lower_bound variants (plby/lean-proofs and linrock/math-proofs). The Glibichuk part of this file is adapted from plby/lean-proofs. The "optimal" variant has no prior formal resolution I know of. Its falsity as formalized follows from the small-prime obstruction that the upstream file itself states. - erdosproblems.com/1180. The ε^{-1-o(1)} question is listed there as still open. The page credits Shparlinski with ≪ε^{-3}, Glibichuk with ≪ε^{-2}, and Croot with (log p)^{3+o(1)}.
- [Sh02] I. E. Shparlinski, "On a question of Erdős and Graham", Arch. Math. (Basel) 78 (2002), 445–448.
- [Gl06] A. A. Glibichuk, Mat. Zametki 79 (2006), 384–395 (mathnet.ru mzm2708): N = 8([1/ε+1/2]+1)^2 summands for sufficiently large p.

(Abridged; the manuscript discusses the literature in full.)

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:erdos1180-erdos-1180-variants-optimal,
  author       = {{math0}},
  title        = {{Erdős 1180, "optimal" variant: false as stated (C_ε grows exponentially in 1/ε, because the constant must cover all primes)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos1180-erdos-1180-variants-optimal}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

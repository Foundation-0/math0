# Finite free Stam inequality in degree 2 (First Proof, Problem 4, n = 2): it holds with equality

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Real analysis  
**Source problem:** arXiv:2602.05192  
**Date:** 2026-10-17

## Result

Let p and q be monic real polynomials of degree 2, each having 2 real roots counted with multiplicity. Let p ⊞_2 q be their finite additive convolution, Σ_{k=0}^{2} c_k x^{2-k} with c_k = Σ_{i+j=k} (2-i)!(2-j)!/(2!(2-k)!) a_i b_j, where a_i and b_j are the coefficients of x^{2-i} in p and x^{2-j} in q. For a monic polynomial with simple roots λ_1,…,λ_n, set Φ_n(p) = Σ_i (Σ_{j≠i} 1/(λ_i-λ_j))^2, and set Φ_n(p) = ∞ when p has a repeated root. Then, in [0,∞], 1/Φ_2(p) + 1/Φ_2(q) ≤ 1/Φ_2(p ⊞_2 q). In fact equality always holds.

## Verification

The Lean file [`lean/Math0/Arxiv/Arxiv_2602_05192_four_2.lean`](../../lean/Math0/Arxiv/Arxiv_2602_05192_four_2.lean) proves the upstream statement [`Arxiv.«2602.05192».four_2`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/2602.05192/FirstProof4.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The problem is First Proof (Abouzaid, Blumberg, Hairer, Kileel, Kolda, Nelson, Spielman, Srivastava, Ward, Weinberger, Williams), arXiv:2602.05192v2, Problem 4: the finite free Stam / harmonic-mean inequality for ⊞_n. ⊞_n is the finite free additive convolution of Marcus–Spielman–Srivastava ("Finite free convolutions of polynomials"; "Interlacing families II"). The general statement was answered affirmatively by the First Proof solutions. It was formalized in Lean 4 by FrenzyMath's Archon in the repository frenzymath/Archon-FirstProof-Results, file FirstProof/FirstProof4/Problem4.lean, theorem harmonic_mean_inequality_full, for all n ≥ 2 with zero sorrys according to its README. Upstream links that file as `formal_proof` on `four`. The n = 2 case is an elementary identity: ⊞_2 adds discriminants (second cumulants), so equality holds.

## Citation

```bibtex
@misc{math0:arxiv-2602-05192-four-2,
  author       = {{math0}},
  title        = {{Finite free Stam inequality in degree 2 (First Proof, Problem 4, n = 2): it holds with equality}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/arxiv-2602-05192-four-2}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

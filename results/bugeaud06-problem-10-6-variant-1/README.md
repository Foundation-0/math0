# A sequence with ratio floor 1 + c/log n that is dense mod 1 for every irrational (Bugeaud 10.6, ratio reading)

**Classification:** Misformalization found (upstream statement does not match the problem)  
**Area:** Number theory  
**Source problem:** Books / BugeaudDistributionModuloOne / Problem10_6  
**Date:** 2026-10-17

## Result

There is a strictly increasing sequence m : ℕ → ℕ with two properties. First, it is "genuinely sublacunary": for some c > 0, m(n+1)/m(n) ≥ 1 + c/log n for all sufficiently large n. Second, for every irrational ξ, the points ξ·m(n) mod 1 are dense in ℝ/ℤ.

## Verification

The Lean file [`lean/Math0/Books/Bugeaud06_problem_10_6_variant_1.lean`](../../lean/Math0/Books/Bugeaud06_problem_10_6_variant_1.lean) proves the upstream statement [`Bugeaud06.problem_10_6_variant_1`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

- **Ajtai, Havas, Komlós (1983):** M. Ajtai, I. Havas and J. Komlós, "Every group admits a bad topology", in Studies in Pure Mathematics (to the memory of P. Turán), Birkhäuser, Basel, 1983, pp. 21–34. For any ε_n → 0+ there are integers m_n with m_{n+1}/m_n > 1 + ε_n such that (ξ m_n) is uniformly distributed mod 1 for every irrational ξ. This implies `problem_10_6_variant_1`.
- **Bugeaud (2012):** Y. Bugeaud, Distribution Modulo One and Diophantine Approximation, Cambridge Tracts in Mathematics 193.
  - The Chapter 2 notes (p. 45) cite the AHK result above.
  - Problem 10.6 is on p. 215; it was checked against the text of the book.
- **Boshernitzan (1983):** M. D. Boshernitzan, Monatsh. Math. 96 (1983), 173–181. Bugeaud cites it as "see also [121]" for the AHK result.
- **Formal Lean proofs:** none found, either in formal_conjectures or as a formal_proof link. Upstream has `formal_proof` links only for the growth and sparsity variants (rwst fork, commit 63c3e72). - Y. Bugeaud, Distribution Modulo One and Diophantine Approximation, Cambridge Tracts in Math. 193 (2012):
  - Problem 10.6 is on p. 215, after the remarks on Furstenberg's 2^n 3^m and on Pollington and de Mathan.
  - §2.8 Notes, p. 45, states the Ajtai–Havas–Komlós theorem: for any ε_n → 0 there is an integer sequence with m_{n+1}/m_n > 1 + ε_n that is u.d. mod 1 for every irrational ξ ("see also [121]").
  - PDF used: https://staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf
- M. Ajtai, I. Havas, J. Komlós, "Every group 

## Citation

```bibtex
@misc{math0:bugeaud06-problem-10-6-variant-1,
  author       = {{math0}},
  title        = {{A sequence with ratio floor 1 + c/log n that is dense mod 1 for every irrational (Bugeaud 10.6, ratio reading)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/bugeaud06-problem-10-6-variant-1}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

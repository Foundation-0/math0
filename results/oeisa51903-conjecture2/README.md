# No odd n with a(n) > 1 has b^n ≡ b^{a(n)} (mod n) for all b (OEIS A051903)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** OEIS 51903  
**Date:** 2026-10-17

## Result

Let a(n) be the largest exponent in the prime factorization of n (OEIS A051903; a(1) = 0). Thomas Ordowski (Dec 2019) asked: are there odd numbers n with a(n) > 1 and b^n ≡ b^{a(n)} (mod n) for every natural number b? The upstream formal statement says such an n exists. We prove its negation: there is no odd n with a(n) > 1 such that b^n ≡ b^{a(n)} (mod n) for all b ∈ ℕ.

## Verification

The Lean file [`lean/Math0/OEIS/OeisA51903_conjecture2.lean`](../../lean/Math0/OEIS/OeisA51903_conjecture2.lean) refutes (proves the negation of) the upstream statement [`OeisA51903.conjecture2`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/OEIS/51903.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes` checks that our theorem's type is syntactically identical to the upstream statement (negated) and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

OEIS A051903 comments: Thomas Ordowski, Dec 02 2019, posed questions (*), (**) and (***). Ansh Mishra, Sep 30 2026, added "Answer to (**): No. Answer to (***): Yes. See Mishra and Senthilkumar (2026)". Ansh Mishra and Aryan Senthilkumar, "On Two Questions of Ordowski about the Largest Exponent in a Prime Factorization", Zenodo preprint, 2026-09-30, https://zenodo.org/records/23064142 (doi:10.5281/zenodo.23064142). It includes Lean 4 / Mathlib proofs, `A051903Core.not_conj2` and `OeisA51903.conjecture2_solved`, of the negation of OeisA51903.conjecture2 using only the standard axioms. That paper credits T. Adamczewski, fc-review-results (https://github.com/tadamcz/fc-review-results, runs of 11, 21 and 23 Sep 2026, entry OEIS/51903), with answering (**) negatively by the same p^(e-1) | e argument and with a Lean proof. The upstream formal_conjectures docstring of OeisA51903.conjecture1 also gives the same divisibility argument, with φ in place of λ. - OEIS A051903, comments by T. Ordowski (Dec 02 2019) stating problems (*), (**) and (***). Comment "Answer to (**): No. Answer to (***): Yes. See Mishra and Senthilkumar (2026)" by Ansh Mishra (Sep 30 2026), approved as revision #152 on Oct 11 2026. https://oeis.org/A051903 and https://oeis.org/history?seq=A051903

(Abridged.)

## Citation

```bibtex
@misc{math0:oeisa51903-conjecture2,
  author       = {{math0}},
  title        = {{No odd n with a(n) > 1 has b^n ≡ b^{a(n)} (mod n) for all b (OEIS A051903)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeisa51903-conjecture2}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

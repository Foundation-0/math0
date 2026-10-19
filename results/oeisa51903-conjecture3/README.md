# An odd n with a(n) > 1 and 2^n ≡ 2^{a(n)} (mod n), where a(n) is the largest prime exponent of n (OEIS A051903, Ordowski)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** OEIS 51903  
**Date:** 2026-10-17

## Result

Let a(n) be the largest exponent in the prime factorization of n (OEIS A051903). Ordowski (Dec 2019) asked whether some odd n has a(n) > 1 and 2^n ≡ 2^{a(n)} (mod n). The answer is yes. The formal statement is ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n], with a n defined as the foldr max of the multiplicities over n.primeFactorsList. The witness is n = 9687963167864344937 = 7 · 631 · 881 · 3511² · 201961.

## Verification

The Lean file [`lean/Math0/OEIS/OeisA51903_conjecture3.lean`](../../lean/Math0/OEIS/OeisA51903_conjecture3.lean) proves the upstream statement [`OeisA51903.conjecture3`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/OEIS/51903.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

- OEIS A051903, https://oeis.org/A051903:
  - Thomas Ordowski's comment of Dec 02 2019 poses questions (*), (**) and (***).
  - Ansh Mishra's comment of Sep 30 2026 reads "Answer to (**): No. Answer to (***): Yes. See Mishra and Senthilkumar (2026)."
- A. Mishra and A. Senthilkumar, "On Two Questions of Ordowski about the Largest Exponent in a Prime Factorization", Zenodo preprint, 2026-09-30, doi:10.5281/zenodo.23064142, https://zenodo.org/records/23064142.
  - It gives the same witness n0 = 9687963167864344937 = 7·631·881·3511²·201961, proves that n0 is minimal, and includes Lean 4 proofs of OeisA51903.conjecture2 (negative) and conjecture3 (positive) against the unmodified formal-conjectures file. The relevant files are lean/DMSolutions/OEIS_A051903/{Core,Solution,CheckAnswer}.lean and logs/lean_check.log.
- F. G. Dorais and D. Klyve, "A Wieferich prime search up to 6.7×10^15", J. Integer Seq. 14 (2011). The minimality argument relies on this search.
- T. Adamczewski, tadamcz/fc-review-results (entry OEIS/51903). The Zenodo README cites it as prior work: an earlier negative answer to (**), with (***) still regarded as open as of 2026-09-23.

(Abridged.)

## Citation

```bibtex
@misc{math0:oeisa51903-conjecture3,
  author       = {{math0}},
  title        = {{An odd n with a(n) > 1 and 2^n ≡ 2^{a(n)} (mod n), where a(n) is the largest prime exponent of n (OEIS A051903, Ordowski)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeisa51903-conjecture3}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

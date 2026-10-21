# Every n not divisible by 5 has a multiple with only prime digits (A342992)

**Classification:** New result (open problem settled)  
**Area:** Sequences and series  
**Source problem:** OEIS A342992  
**Date:** 2026-10-20

## Result

For every integer n >= 1 with 5 not dividing n, there is some k such that k*n is positive and every decimal digit of k*n is prime (in {2,3,5,7}). Equivalently, a(n) > 0 for A342992 (Sariyar's conjecture).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A342992](https://oeis.org/A342992) as [`def statement`](../../lean/Math0/Statements/OEIS/A342992.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A342992.lean`](../../lean/Math0/Frontier/OEIS/A342992.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: a(n) > 0 for all n that are not divisible by 5." (A342992, entry by _Metin Sariyar_, Apr 13 2021. Corneth added that a(625k) = 0.)

Referees: No prior explicit proof of the A342992 conjecture was found. The entry still lists it as a conjecture (#60, Apr 22 2021) with no later %E edits.

Closest prior material:
(1) OEIS A078239 (Murthy 2002; Robert Israel, Feb 2018). Comment: "Besides multiples of 10, 625 and its odd multiples have a(n)=0". Its Maple program implicitly assumes a prime-digit multiple exists for every n with 10∤n and 625∤n. This is an unproved assertion. A078250 (Howroyd, 2024) repeats the comment.
(2) OEIS A053316 (Henry Bottomley, Mar 2000; formula corrected by Israel, 2019): an n-digit number with digits 2 and 3 that is divisible by 2^n. This is exactly the proof's block lemma. The digits-{1,2} version is A053312, the 1971 All-Union olympiad problem (cut-the-knot.org/arithmetic/DivisibilityFromSovietMO.shtml).
(3) IMO Shortlist 1994 N7, "wobbly numbers" (prase.cz/kalva/short/soln/sh94n7.html): the same technique of combining a 2-power block with the coprime-to-10 part by repetition.
(4) Galperin & Reid, "Multiples Without Large Digits", Amer. Math. Monthly 126 (2019), as cited by John D. Cook (johndcook.com/blog/2025/12/16/multiples-with-no-large-digits/), with the citation's page numbers disputed by a reader comment. It covers digits 1–5 and does not imply this result.
(5) C. W. Wu, "Pigeonholes and repunits", Amer. Math. Monthly 121 (2014): the related {0,1} case.

The result is elementary and folklore-adjacent, but no source states or proves it for prime digits or for digits {2,3}.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a342992,
  author       = {{math0}},
  title        = {{Every n not divisible by 5 has a multiple with only prime digits (A342992)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a342992}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

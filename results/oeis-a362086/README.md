# OEIS A362086: every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-3)))) except 9 is 1 or a prime

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Number theory  
**Source problem:** OEIS A362086  
**Date:** 2026-10-18

## Result

For n >= 3 let a(n) be the reduced denominator of 1/(2 - 3/(3 - 4/(4 - ... ((n-1) - n/(-3))))), evaluated in Q from the inside out. Then for every n >= 3 with a(n) != 9, a(n) is 1 or a prime. (Mohammed Bouras's conjecture; the value 9 occurs at n = 5.)

## Assessment

The closed form for the unreduced fraction is essentially the gcd formula already listed in the entry. It reduces the denominator to N/gcd(N, 3(n-1)(n-3)!) with N = n^2+n-3, which is roughly n^2. The rest is the standard template from the solved sibling sequences: a prime p up to n-3 that survives in the denominator must divide N to a higher power than it divides (n-3)!, and this is impossible because of size, apart from a small N = 3p^2 case. Prime factors above n must be at least n+1, so at most one fits, and the cases n < 36 are a finite check. The argument is about a page and a direct adaptation of known proofs, with no new idea, so it is routine.

*Follows from:* The entry's own formula a(n) = (n^2+n-3)/gcd(n^2+n-3, 3*A051403(n-3) + n*A051403(n-4)), with A051403 written in left factorials (its %F), combined with the factorial-valuation and size argument already used for the sibling conjectures A363102 (Adamczewski, arXiv:2608.11941, Appendix A), A356247 (Cloitre) and A363482.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A362086](https://oeis.org/A362086) as [`Math0.Statements.A362086.statement`](../../lean/Math0/Statements/OEIS/A362086.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A362086.lean`](../../lean/Math0/Frontier/OEIS/A362086.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Except for 9, every term of this sequence is either a prime or 1. (Mohammed Bouras, May 28 2023)

Referees: OEIS A362086 (local mirror, revision #35, May 09 2024): "Conjecture: Except for 9, every term of this sequence is either a prime or 1." No proof is recorded. Related prior work, none of which settles A362086:
- M. Bouras, "A New Primes-Generating Sequence", arXiv:2509.09745 (2025). Lists A362086 in its Table 1 family; the primality property is stated only as a conjecture.
- B. Cloitre, "On the sequence A356247" (2025), OEIS attachment a356247_1.pdf. Proves Conjectures 1-3 for the innermost -1 analogue, A356247.
- T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941 (2026), together with the AlphaProof Nexus Lean files oeis_363347_conjecture_2.lean and oeis_a363102_conjecture_1.lean. Proves the analogues for innermost -2 (A363102) and -4 (A363347).
A362086 appears in neither the alphaproof-nexus-results repository nor the epoch-research LeanOpenProblems and LeanOpenProblems-results repositories. Searches of arXiv, MathOverflow and Math StackExchange found no proof or counterexample.

Reading note (fidelity pass, 29 Oct 2026): the statement exempts every term equal to 9. Read strictly, the conjecture exempts only the single term a(5) = 9, which also needs the value 9 to occur only once. That holds for n < 1200 by exact computation but is not part of the Lean result.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a362086,
  author       = {{math0}},
  title        = {{OEIS A362086: every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-3)))) except 9 is 1 or a prime}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a362086}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# OEIS A362086: every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-3)))) except 9 is 1 or a prime

**Classification:** New result (open problem settled)  
**Area:** Number theory  
**Source problem:** OEIS A362086  
**Date:** 2026-10-18

## Result

For n >= 3 let a(n) be the reduced denominator of 1/(2 - 3/(3 - 4/(4 - ... ((n-1) - n/(-3))))), evaluated in Q from the inside out. Then for every n >= 3 with a(n) != 9, a(n) is 1 or a prime. (Mohammed Bouras's conjecture; the value 9 occurs at n = 5.)

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A362086](https://oeis.org/A362086) as [`Math0.Statements.A362086.statement`](../../lean/Math0/Statements/OEIS/A362086.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A362086.lean`](../../lean/Math0/Frontier/OEIS/A362086.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Except for 9, every term of this sequence is either a prime or 1. (Mohammed Bouras, May 28 2023)

Referees: OEIS A362086 (local mirror, revision #35, May 09 2024): "Conjecture: Except for 9, every term of this sequence is either a prime or 1." No proof is recorded. Related prior work, none of which settles A362086:
- M. Bouras, "A New Primes-Generating Sequence", arXiv:2509.09745 (2025). Lists A362086 in its Table 1 family; the primality property is stated only as a conjecture.
- B. Cloitre, "On the sequence A356247" (2025), OEIS attachment a356247_1.pdf. Proves Conjectures 1-3 for the innermost -1 analogue, A356247.
- T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941 (2026), together with the AlphaProof Nexus Lean files oeis_363347_conjecture_2.lean and oeis_a363102_conjecture_1.lean. Proves the analogues for innermost -2 (A363102) and -4 (A363347).
A362086 appears in neither the alphaproof-nexus-results repository nor the epoch-research LeanOpenProblems and LeanOpenProblems-results repositories. Searches of arXiv, MathOverflow and Math StackExchange found no proof or counterexample.

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

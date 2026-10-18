# A375522: S2(n) - S1(n) = 1 fails at n = 42 (the difference is 5)

**Classification:** New result (open problem settled)  
**Area:** Number theory  
**Source problem:** OEIS A375522  
**Date:** 2026-10-18

## Result

Let p_k be the k-th prime. Define s(0) = 0 and s(k) = s(k-1) + 1/(p_k b(k)), where b(k) = 1 + floor(1/((1 - s(k-1)) p_k)) (this is A375781). Write s(n) = S1(n)/S2(n) in lowest terms (S2 = A375522, S1 = A375521). Sigrist and Sloane conjectured that S2(n) - S1(n) = 1 for every n >= 1 except n = 4 and n = 6. This is false: S2(42) - S1(42) = 5. Lean: theorem result : ¬ statement.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A375522](https://oeis.org/A375522) as [`Math0.Statements.A375522.statement`](../../lean/Math0/Statements/OEIS/A375522.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A375522.lean`](../../lean/Math0/Frontier/OEIS/A375522.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: The differences S2(n) - S1(n) are surprisingly small: for n = 1,2,...,34 the values S2(n) - S1(n) are: 1, 1, 1, 2, 1, 2, 1, 1, ..., 1 suggesting the conjecture that they are always 1 except for n = 4 and 6 (compare the Theorem in A374983). (Rémy Sigrist and N. J. A. Sloane, Aug 30 2024)

Referees: The conjecture is in OEIS A375522 (R. Sigrist and N. J. A. Sloane, Aug 30 2024; comment added Aug 31 2024; current revision #25, Apr 22 2025). It is restated as still open ("it seems") in A375528 (Sloane, Sep/Oct 2024). Related: A375521, A375781, A374983/A375516 (harmonic analogue, proved by Sigrist), and Sloane, "A Nasty Surprise in a Sequence and Other OEIS Stories", Rutgers Experimental Math Seminar, Oct 10 2024 (slides list these sequences and a general Conjecture 4, with no counterexample). Sigrist and Sloane, "Dampening Down a Divergent Series", is still cited on OEIS as a manuscript in preparation. No prior counterexample or proof turned up in the OEIS histories, arXiv (e.g. Fried arXiv:2607.24832 does not cover it), web searches, or google-deepmind/formal-conjectures. The SeqFan archive could not be reached.

## Citation

```bibtex
@misc{math0:oeis-a375522,
  author       = {{math0}},
  title        = {{A375522: S2(n) - S1(n) = 1 fails at n = 42 (the difference is 5)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a375522}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

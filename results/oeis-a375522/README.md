# A375522: S2(n) - S1(n) = 1 fails at n = 42 (the difference is 5)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Number theory  
**Source problem:** OEIS A375522  
**Date:** 2026-10-18

## Result

Let p_k be the k-th prime. Define s(0) = 0 and s(k) = s(k-1) + 1/(p_k b(k)), where b(k) = 1 + floor(1/((1 - s(k-1)) p_k)) (this is A375781). Write s(n) = S1(n)/S2(n) in lowest terms (S2 = A375522, S1 = A375521). Sigrist and Sloane conjectured that S2(n) - S1(n) = 1 for every n >= 1 except n = 4 and n = 6. This is false: S2(42) - S1(42) = 5. Lean: theorem result : ¬ statement.

## Assessment

The conjecture is refuted by one computed value: S2(42) - S1(42) = 5. Note that S2(42) has about 4*10^11 digits, so it cannot be computed directly. The only idea needed is a standard one. The difference S2(n) - S1(n) is the small numerator of the remainder 1 - s(n), and it depends only on the huge denominator modulo small numbers, so you track that denominator modulo a large smooth modulus and account for the precision lost when you cancel the gcd at each step. That bookkeeping lemma takes about a page and is elementary. Once it is set up, the result is a finite computation, so the work is routine, although the counterexample is real and was out of reach of the authors' direct computation up to n = 34.

*Follows from:* The entry's own recursion (its Maple/Mathematica programs), run as a finite computation modulo a smooth modulus such as (190!)^2. If 1 - s(n-1) = 1/D, then 1 - s(n) = m/(D(D+m)) with m = p_n - (D mod p_n).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A375522](https://oeis.org/A375522) as [`Math0.Statements.A375522.statement`](../../lean/Math0/Statements/OEIS/A375522.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A375522.lean`](../../lean/Math0/Frontier/OEIS/A375522.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: The differences S2(n) - S1(n) are surprisingly small: for n = 1,2,...,34 the values S2(n) - S1(n) are: 1, 1, 1, 2, 1, 2, 1, 1, ..., 1 suggesting the conjecture that they are always 1 except for n = 4 and 6 (compare the Theorem in A374983). (Rémy Sigrist and N. J. A. Sloane, Aug 30 2024)

Referees: The conjecture is in OEIS A375522 (R. Sigrist and N. J. A. Sloane, Aug 30 2024; comment added Aug 31 2024; current revision #25, Apr 22 2025). It is restated as still open ("it seems") in A375528 (Sloane, Sep/Oct 2024). Related: A375521, A375781, A374983/A375516 (harmonic analogue, proved by Sigrist), and Sloane, "A Nasty Surprise in a Sequence and Other OEIS Stories", Rutgers Experimental Math Seminar, Oct 10 2024 (slides list these sequences and a general Conjecture 4, with no counterexample). Sigrist and Sloane, "Dampening Down a Divergent Series", is still cited on OEIS as a manuscript in preparation. No prior counterexample or proof turned up in the OEIS histories, arXiv (e.g. Fried arXiv:2607.24832 does not cover it), web searches, or google-deepmind/formal-conjectures. The SeqFan archive could not be reached.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

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

# Odd terms of A323695 occur only at n = k(k+2)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A323695  
**Date:** 2026-10-18

## Result

Let a(N) be the coefficient of x^N in Sum_{m>=0} x^m (1 - x^(m+1))^m / (1 + x^(m+1))^(m+1) (OEIS A323695, offset 0). If a(n) is odd, then n = k(k+2) for some natural number k. Equivalently, if a(n) is odd then n + 1 is a perfect square.

## Assessment

The proof reduces the generating function modulo 2. There the numerator and denominator of each summand have the same base, so the m-th summand cancels down to x^m/(1+x^(m+1)). The sum is then the classical Lambert series for the divisor function, so a(n) is congruent mod 2 to d(n+1), and d(n+1) is odd exactly when n+1 is a square, by pairing each divisor d with N/d. This is a few lines of standard reasoning that a competent mathematician would find almost at once; the manuscript itself calls the result elementary. Unlike the sibling entries A323557 and A325046, nothing fails to cancel here, and the conjecture is the intended statement, not a degenerate reading of it.

*Follows from:* Reduce the entry's own g.f. modulo 2. Since 1 - x^(m+1) = 1 + x^(m+1) mod 2, each summand becomes x^m/(1+x^(m+1)), and the series becomes the standard Lambert series Sum_m x^m/(1-x^(m+1)) = Sum_n d(n+1) x^n. The classical fact that d(N) is odd iff N is a perfect square finishes the proof.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A323695](https://oeis.org/A323695) as [`Math0.Statements.A323695.statement`](../../lean/Math0/Statements/OEIS/A323695.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A323695.lean`](../../lean/Math0/Frontier/OEIS/A323695.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A323695 (G.f.: Sum_{n>=0} x^n (1 - x^(n+1))^n/(1 + x^(n+1))^(n+1)): "Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture);" (_Paul D. Hanna_, Feb 23 2019). A324300 (G.f.: Sum_{n>=0} x^n (x^(n+1)+i)^n/(1 + i x^(n+1))^(n+1)): "Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture);" (Hanna, Feb 21 2019).

Referees: OEIS A323695 (Hanna, Feb 23 2019; still labeled "(conjecture)" at rev #24, Dec 15 2024; history checked) and its cross-references A323696, A324300 (same conjecture for an i-variant, also unproved), A323675 and A323680. Sibling results proved by others, which do not cover A323695: A325046, odd terms iff N = m(m+1), in S. Fried, "Further proofs of conjectures from the OEIS", arXiv:2607.24832 (Thm 50), also in google-deepmind/alphaproof-nexus-results; A323557, odd terms at r(r+1), in T. Adamczewski, "OEIS Open", arXiv:2608.11941 and AlphaProof Nexus (Tsoukalas et al.). A323695 is in neither google-deepmind/formal-conjectures nor epoch-research/LeanOpenProblems. It is not mentioned in Fried's arXiv:2410.07237 (JIS 25.4.3), JIS 26.1.8 or arXiv:2606.09913. MathOverflow, Math StackExchange and SeqFan searches found nothing.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a323695,
  author       = {{math0}},
  title        = {{Odd terms of A323695 occur only at n = k(k+2)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a323695}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

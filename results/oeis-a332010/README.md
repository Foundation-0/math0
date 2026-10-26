# A332010: the average first letter of one-descent derangements has denominator 2^(n-2)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A332010  
**Date:** 2026-10-19

## Result

For every n ≥ 2, take the derangements of {1, ..., n} (in one-line notation) that have exactly one descent. The average of their first letters, written in lowest terms, has denominator 2^(n-2). This is Kagey's conjecture T(n,1) = 2^(n-2) in OEIS A332010.

## Assessment

A permutation with exactly one descent is sorted(A) followed by sorted(complement of A). Checking fixed points run by run shows it is a derangement exactly when 1 is not in A and n is in A. That gives 2^(n-2) such derangements, and their first letter is min A. Summing min A over these sets gives 3*2^(n-2) - 1, which is odd, so the reduced denominator is 2^(n-2). This is a half-page counting argument built on a textbook description of one-descent permutations, and the count itself already follows from A219836. It needs no new idea.

*Follows from:* Standard fact that a permutation with one descent is an increasing word on a set A followed by an increasing word on its complement (a Grassmannian permutation). A219836 already implies the count 2^(n-2).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A332010](https://oeis.org/A332010) as [`Math0.Statements.A332010.statement`](../../lean/Math0/Statements/OEIS/A332010.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A332010.lean`](../../lean/Math0/Frontier/OEIS/A332010.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: T(n, 1) = 2^(n-2)." (A332010, entry by Peter Kagey, Feb 04 2020)

Referees: No prior resolution found.
- OEIS A332010 and A332009 (Peter Kagey, Feb 04 2020; last edits Mar 30 2024) still state "Conjecture: T(n,1) = 2^(n-2)" and "Conjecture: T(n,1) = A083329(n-1)", with no proof recorded in comments or %E lines. I checked both the local mirror and raw.githubusercontent oeisdata.
- Related known facts:
  - A219836 (Callan 2012; links to Fu–Lin–Zeng arXiv:1507.05184 and Alexandersson arXiv:2609.07325) gives a recurrence implying there are 2^(n-2) derangements with one descent. That is only the unreduced denominator.
  - M. Conger, arXiv math/0508112, proves E[π(1) | des = k] = k+1 over all permutations; this is the analogue for all permutations that the A332010 comment cites.
  - Kagey, arXiv:2112.05281, treats expected π(1) given k-cycles and does not address derangements by descents.
  - Eriksen–Freij–Wästlund, arXiv:0811.1925 / EJC 16 (2009) R32, and Han–Xin (2007) cover derangements with prescribed descent sets, with no first-letter averages.
- Searches of Math StackExchange, arXiv and SeqFan found nothing. MathOverflow was not reachable through the search tool.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a332010,
  author       = {{math0}},
  title        = {{A332010: the average first letter of one-descent derangements has denominator 2^(n-2)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a332010}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

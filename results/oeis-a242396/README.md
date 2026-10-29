# Stephan's conjectured g.f. for A242396 is false (first failure at n = 97)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A242396  
**Date:** 2026-10-21

## Result

Let a(n) be the number of rows (closed horizontal strips j*sqrt(3)/2 <= y <= (j+1)*sqrt(3)/2) of the unit equilateral-triangle tiling that meet the circle of radius n. Stephan's conjecture says that sum_{n>=1} a(n) x^n * (x^14 - x^13 - x + 1) = -2x^14 + 4x^13 + 2x^12 + 2x^11 + 2x^10 + 2x^9 + 2x^8 + 4x^7 + 2x^6 + 2x^5 + 2x^4 + 2x^3 + 2x^2 + 4x in Z[[x]]. We prove that this identity is false.

## Assessment

A row meets the circle exactly when its vertical extent overlaps [-n, n]. That gives a(n) = 2*floor(2n/sqrt(3)) + 2, which is also what the entry's own program computes for n up to 100. A rational g.f. with denominator (1-x)(1-x^13) would force a(n+13) - a(n) = 30 for every n. Because the slope 4/sqrt(3) is irrational, this cannot hold for all n, and a direct computation of four values gives the first failure at n = 97 (226 instead of 224). The refutation needs only this short argument and a finite check: Stephan's g.f. was a fit to the 61 listed terms, and no new idea was required. The counterexample is a real failure of the g.f. for the sequence as defined, not a degenerate or excluded case.

*Follows from:* Elementary closed form a(n) = 2*floor(2n/sqrt(3)) + 2, which is what the entry's own Small Basic program computes, together with direct evaluation of a(83), a(84), a(96), a(97) and comparison of the x^97 coefficient after clearing the denominator (1-x)(1-x^13).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A242396](https://oeis.org/A242396) as [`Math0.Statements.A242396.statement`](../../lean/Math0/Statements/OEIS/A242396.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A242396.lean`](../../lean/Math0/Frontier/OEIS/A242396.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: G.f., conjectured: (-2*x^14 + 4*x^13 + 2*x^12 + 2*x^11 + 2*x^10 + 2*x^9 + 2*x^8 + 4*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 4*x)/(x^14 - x^13 - x + 1). - _Ralf Stephan_, May 18 2014  (also: Asymptotics from g.f.: a(n) ~ 30/13 * n. - _Ralf Stephan_, May 18 2014)

Referees: Sources checked:
- The OEIS A242396 entry, from the local mirror and https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A242/A242396.seq. Both show revision #18 (May 31, 2014), and the g.f. is still marked "conjectured" with no correction.
- The cross-referenced entries A242394 and A242395.
- A mirror search for the sequences ⌊2n/√3⌋ and 2⌊2n/√3⌋+2. The only match was A242396 itself.
- Ralf Stephan's conjecture list at ark.in-berlin.de/conj.txt, which covers only the 2004–2005 list.
- Four papers on proving OEIS conjectures, none of which mention A242396:
  - arXiv:2607.24832, "Further proofs of conjectures from the OEIS"
  - arXiv:2410.07237
  - S. Fried, JIS vol. 28 (fried15)
  - S. Fried, JIS vol. 29 (fried21)
- General web searches (arXiv, MathOverflow/Math StackExchange, SeqFan). These found no counterexample or refutation of Stephan's g.f. for A242396.

No prior resolution was found.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a242396,
  author       = {{math0}},
  title        = {{Stephan's conjectured g.f. for A242396 is false (first failure at n = 97)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a242396}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

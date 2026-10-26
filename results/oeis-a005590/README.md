# Zeros of a(3n) for the signed Stern sequence A005590 are exactly the fibbinary numbers

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Number theory  
**Source problem:** OEIS A005590  
**Date:** 2026-10-18

## Result

Let a : N -> Z be given by a(0)=0, a(1)=1, a(2n)=a(n), a(2n+1)=a(n+1)-a(n) (OEIS A005590). Then for every n >= 0, a(3n)=0 if and only if n is fibbinary (OEIS A003714), i.e. the binary representation of n has no two adjacent 1 bits. This is Ralf Stephan's 2003 conjecture.

## Assessment

The proof follows the pair (a(m), a(m+1)) along the binary digits of m. The pair stays at (0,1) or (1,1) while the digits form blocks 0 and 11. As soon as a 0 is read in state (1,1), the pair lands on (1,0), and from then on a one-line sign invariant (x>0 and y<x, or x<0 and x<y) is preserved and forces a(m) to be nonzero. A short induction on n mod 4 then shows that 3n reaches state 0 exactly when n is fibbinary. This is a standard automaton-plus-invariant argument for a 2-regular sequence, about a page long with elementary case checks, so a competent mathematician would find it quickly. The conjecture stood for a long time only because nobody seems to have tried, not because it needed a new idea.

*Follows from:* The defining recursion read as a 2-regular linear representation: (a(2m),a(2m+1)) and (a(2m+1),a(2m+2)) are fixed linear images of (a(m),a(m+1)). This is the standard way to handle zero sets of 2-regular sequences (Allouche-Shallit), and the entry already notes that the sequence is 2-regular.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A005590](https://oeis.org/A005590) as [`Math0.Statements.A005590.statement`](../../lean/Math0/Statements/OEIS/A005590.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A005590.lean`](../../lean/Math0/Frontier/OEIS/A005590.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(3n)=0 iff n in A003714. - _Ralf Stephan_, May 02 2003

Referees: I found no prior resolution.
- OEIS A005590 (local mirror, rev #97, Nov 2025) still marks Stephan's 2003 claim as a conjecture.
- Related OEIS entries: A003714, A277335 (= 3·A003714, the zero set of A005590, not cross-linked to it), A290258.
- R. Stephan, arXiv:math/0409509: the conjecture is not listed. R. Stephan, arXiv:math/0307027: lists A005590 only in a table.
- J.-P. Allouche and J. Shallit, 'The ring of k-regular sequences', TCS 98 (1992): Example 7 shows 2-regularity only.
- J.-P. Allouche and M. Mendès France, arXiv:1202.0211: links A005590 to Thue–Morse, nothing on zeros.
- No hits in S. Northshield, arXiv:1503.03433; C. Defant, arXiv:1506.07824; B. Reznick, arXiv:math/0610601; or S. Fried, arXiv:2607.24832 (abstract only).
- Not in the OEIS Open / Tsoukalas et al. 492-conjecture set (arXiv:2608.11941, 2605.22763) and not in google-deepmind/formal-conjectures.
- Not checked: B. Reznick, 'A new sequence with many properties', Abstracts AMS 5 (1984) 16. Its scan is on oeis.org, which is rate-limited here.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a005590,
  author       = {{math0}},
  title        = {{Zeros of a(3n) for the signed Stern sequence A005590 are exactly the fibbinary numbers}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a005590}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

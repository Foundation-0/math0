# The only fixed points of reverse(x) - maxdigit(x) are 0 and 89

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A097154  
**Date:** 2026-10-19

## Result

For a natural number x, let rev(x) be its decimal reversal (rev 0 = 0, trailing zeros are dropped) and maxdig(x) its largest decimal digit (maxdig 0 = 0). Let f(x) = rev(x) - maxdig(x). Then f(x) = x if and only if x = 0 or x = 89.

## Assessment

A fixed point satisfies rev(x) = x + maxdig(x). Reversal keeps the digit sum, so maxdig(x) must be divisible by 9, which leaves only rev(x) = x + 9. Comparing the leading and units digits mod 10 and bounding the middle block then gives x = 10a + (a+1), and the largest-digit condition picks out 89. That is under a page of textbook digit arithmetic that a competent mathematician would find quickly. The entry itself carries the keyword 'easy', and the length of the Lean proof reflects formalization effort, not mathematical depth.

*Follows from:* The standard fact that a number is congruent to its digit sum mod 9, so rev(x) ≡ x (mod 9). This forces maxdig(x) = 9 at a nonzero fixed point. A units-digit comparison mod 10 and a size bound then finish it.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A097154](https://oeis.org/A097154) as [`Math0.Statements.A097154.statement`](../../lean/Math0/Statements/OEIS/A097154.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A097154.lean`](../../lean/Math0/Frontier/OEIS/A097154.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "a(89)=-1 because 89 is the first number that will not reach zero: 98-9=89. It is conjectured that 0 and 89 are the only fixed points of f." (A097154, entry by _Jason Earls_, Aug 01 2004. The same sentence appears in A097155 and A097157.)

Referees: **OEIS (local mirror, cross-checked against the current raw GitHub oeisdata files).**
- A097154 (#4, Dec 15 2017), A097155 (#11, last edited Aug 29 2025) and A097157 (#3) all still say "It is conjectured that 0 and 89 are the only fixed points of f".
- None has an %E line, comment, formula or link recording a proof or counterexample. A097155's only %E is a 2011 data correction by Harvey P. Dale.
- The cross-referenced entries A097153, A097156 and A097158 (Earls, Aug 2004; extensions by Robert G. Wilson v and Klaus Brockhaus) are purely computational.
- A grep of the whole local oeisdata mirror finds no other entry that references A097153 through A097158.

**Web searches.** Queries covered the exact map text, "reversal minus largest digit", SeqFan 2004, Math StackExchange/MathOverflow-style phrasing, and an extended search. None found a proof.
- Hits were only the OEIS pages themselves.
- Unrelated digit-reversal work also came up: arXiv 2410.11784 (1089 attractor), arXiv 2404.06656 (reverse divisors), arXiv math/0511366, and OEIS A393794 (fixed points of the 1089-trick map, Havenaar 2026, a different map).
- A GMAT forum problem covers only the two-digit equation reverse(n) = n + 9, which has eight solutions (12, ..., 89). That is a different condition and does not address this conjecture.

No prior resolution was found, so this appears to be the first written proof, and it is Lean-verified.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a097154,
  author       = {{math0}},
  title        = {{The only fixed points of reverse(x) - maxdigit(x) are 0 and 89}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a097154}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Odd descending-by-2 multiples exist exactly when 125 does not divide 2n+1 (A062887)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A062887  
**Date:** 2026-10-19

## Result

Call a positive integer N admissible if all of its decimal digits are odd and, reading from left to right, each digit is 2 less (mod 10) than the one before it. Examples are 975, 75, 319 and 9753197. Let a(n) be the smallest admissible multiple of 2n+1, or 0 if there is none. Then for every n ≥ 0, a(n) = 0 if and only if 125 divides 2n+1.

## Assessment

One direction is a finite check. Every admissible number either has at most two digits or ends in 975, 753, 531, 319 or 197, and none of these is divisible by 125. The other direction repeats the admissible block 31975 (which is divisible by 25) q times with q = phi(99999 m'). This is the textbook argument that a number coprime to 10 divides a suitable repunit. The whole proof takes under a page and uses only standard elementary number theory, so it is routine, even though the Lean formalization took real work.

*Follows from:* Standard facts: an integer is congruent mod 125 to its last three digits, and Euler's theorem (every number coprime to 10 divides some number made of a repeated decimal block, the usual repunit argument). The sibling entry A062886 already uses the same last-digits argument with modulus 25.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A062887](https://oeis.org/A062887) as [`Math0.Statements.A062887.statement`](../../lean/Math0/Statements/OEIS/A062887.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A062887.lean`](../../lean/Math0/Frontier/OEIS/A062887.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: The only numbers n for which a(n)=0 are those for which 2*n+1 is divisible by 125. - _Sean A. Irvine_, Apr 14 2023"

Referees: OEIS A062887 (Amarnath Murthy, 2001; conjecture added by Sean A. Irvine, Apr 14 2023; entry unchanged as of revision #12, checked in the local mirror dated 2026-10-17 and upstream oeisdata). Related: OEIS A062886 (Nathaniel Johnston, May 2011: zeros match 25 | 2n+1 for n ≤ 500, observed but not proved); OEIS A062885 (even-digit analogue: John W. Layman's argument for a(25) = −1, plus a Don Reble analysis file a062885.txt that I could not retrieve). Web searches (OEIS, MSE/MO-style queries, phrases about repeated 31975/97531 blocks and divisibility by 125) found no prior proof or counterexample.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a062887,
  author       = {{math0}},
  title        = {{Odd descending-by-2 multiples exist exactly when 125 does not divide 2n+1 (A062887)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a062887}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

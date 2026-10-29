# Internal n-gons in a regular n-gon: triple points occur only for n = 3, 4, 6, and otherwise there are n k^2 + 1 regions (Shannon's A357216 conjecture)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A357216  
**Date:** 2026-10-18

## Result

Take the regular n-gon with vertices V_j = exp(2πij/n). Divide each side into k+1 equal parts. For m = 1..k, the m-th internal n-gon joins the m-th division points of consecutive sides. Its side (j, m-1) is the segment from the m-th division point of side j to the m-th division point of side j+1. The statement has two parts.
(1) For n >= 3, some k gives a point lying on three distinct drawn sides if and only if n is 3, 4 or 6.
(2) For n = 5 and for every n >= 7 and every k >= 0, the open polygon minus all n*k drawn sides has exactly n*k^2 + 1 connected components.

## Assessment

The proof first notes that two chords can only cross if they cut off the same corner or adjacent corners. So any triple point involves just four consecutive vertices, and in an affine frame these depend only on u = 2cos(2*pi/n). With every chord parameter rational, the condition for three chords to meet is linear in u with a nonzero rational coefficient, so u would be rational, which Niven's theorem rules out for n = 5 and n >= 7. Explicit rational triple points for n = 3, 4, 6, and the standard count (a chord crossed at p distinct interior points adds p + 1 regions) giving n*k^2 + 1, complete the proof. The whole argument is about a page of elementary coordinate geometry plus a classical theorem. The long Lean file reflects the effort of formalizing the topology, not a hard mathematical idea.

*Follows from:* Niven's theorem (cos(2*pi/n) is rational only for n = 1, 2, 3, 4, 6), combined with the Euler-formula count of regions already cited in the entry's %F line (T = edges - vertices + 1).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A357216](https://oeis.org/A357216) as [`Math0.Statements.A357216.statement`](../../lean/Math0/Statements/OEIS/A357216.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A357216.lean`](../../lean/Math0/Frontier/OEIS/A357216.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C Conjecture: the only n-gons that contain non-simple intersections are the 3-gon (triangle), 4-gon (square), and 6-gon (hexagon). %F Conjectured formula for all columns for n >= 7: T(n,k) = n*k^2 + 1. %F Conjectured formula for all rows except for n = 3, 4, 6: T(n,k) = n*k^2 + 1. (Scott R. Shannon, Sep 18 2022; the same conjecture appears in A357235 (vertices n*k^2+n) and A357254 (edges 2n*k^2+n))

Referees: I found no prior resolution. The OEIS entries A357216, A357235 and A357254 (Scott R. Shannon, Sep 2022, last revised Sep 21 2022, no %E lines) still list both claims as conjectures, in the local mirror and the current GitHub oeisdata. The related entries for the triangle (A356984, with Talmon Silver's classification for n = 3 only), the square (A357058) and the hexagon (A357196) give no general proof. arXiv API searches for "A357216" and "internal n-gons" returned nothing. Web searches covering MathOverflow, Math StackExchange, SeqFan and Google-Scholar-style queries found only the OEIS entries themselves. Sela Fried, "Proofs of some Conjectures from the OEIS" (arXiv:2410.07237) is unrelated. The key tool, Niven's theorem (cos(2*pi/n) is rational only for n = 1, 2, 3, 4, 6), is classical.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a357216,
  author       = {{math0}},
  title        = {{Internal n-gons in a regular n-gon: triple points occur only for n = 3, 4, 6, and otherwise there are n k^2 + 1 regions (Shannon's A357216 conjecture)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a357216}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

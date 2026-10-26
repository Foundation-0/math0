# The generating function of A022445 (closed self-avoiding walks in the strip {0,1,2} x Z)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A022445  
**Date:** 2026-10-26

## Result

Let a(n) be the number of closed walks of length 2n in the square lattice that start and end at the origin (a vertex of the boundary column 0), stay in the strip {0,1,2} x Z, and visit no vertex twice except that the endpoint equals the start (a(0) = 1; length-2 walks that retrace their edge are excluded, so a(1) = 0). Then
sum_{n>=0} a(n) x^n = (1 - 4x + 10x^2 - 14x^3 + 27x^4 - 18x^5 + 10x^6 - 6x^7) / ((1 + x^2)^2 (1 - 2x)^2).
In Lean this is stated in Z[[X]] with the denominator cleared.

## Assessment

The proof rests on one observation: a self-avoiding polygon in the strip {0,1,2} x Z crosses each horizontal cut in an even number of distinct columns, at most three, so in 0 or 2 of them. The polygon is therefore two strands, with three possible states per row, and its perimeter series comes from a 3-state transfer matrix (in Lean, a linear recursion for half-strip excursions), with rooting handled by marking column-0 vertices; clearing denominators is then algebra. This is the textbook transfer-matrix method for polygons in narrow strips; it fits in about a page and is the same calculation that gave the area version (A038579) attributed to Labelle. The Lean formalization is long, but the mathematical idea is standard.

*Follows from:* Standard transfer-matrix / row-by-row decomposition of self-avoiding polygons in a strip of fixed width (e.g. Stanley, EC1 Sec. 4.7). In a 3-column strip every horizontal cut meets the polygon in 0 or 2 vertical edges, so the polygons are row-convex with three row states. The same method gives the area generating function of the same objects, A038579, credited to Labelle (Bull. ICA 23, 1998) and cited in the entry.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A022445](https://oeis.org/A022445) as [`Math0.Statements.A022445.statement`](../../lean/Math0/Statements/OEIS/A022445.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A022445.lean`](../../lean/Math0/Frontier/OEIS/A022445.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A022445 G.f.: (-6*x^7+10*x^6-18*x^5+27*x^4-14*x^3+10*x^2-4*x+1) / ((1+x^2)^2*(1-2*x)^2) (conjectured). - _Ralf Stephan_, Apr 28 2004

Referees: OEIS A022445 (local mirror and current github.com/oeis/oeisdata, %I #10 May 16 2019): GF marked "(conjectured). - Ralf Stephan, Apr 28 2004". Sister entry A022444: GF also still conjectured. Related entries A038578 and A038579 have rooted area GFs credited to Labelle by E. Deutsch (Apr 29 2004). Other related entries: A007825, A038577, A302408. J. Labelle, "Self-avoiding walks and polyominoes in strips", Bull. ICA 23 (1998) 88-98; full text not accessible, so I cannot rule out that it has the perimeter GF, but the OEIS has kept it "conjectured" since 2004. M. von Thaden, "Self-avoiding polygons on a three-row square-lattice strip", arXiv:2607.27397 (Jul 2026): unrooted polygon counts on Z×{0,1,2}, does not mention A022445. M. Bousquet-Mélou & R. Brak, "Exactly solved models", and A. J. Guttmann & I. Jensen, "Polygons in strips", both in Polygons, Polyominoes and Polycubes, LNP 775 (2009): unrooted polygon GFs only. Not relevant to this GF: Batchelor–Yung 1994 (transfer-matrix SAWs across strips); Dyhr–Gilbert–Kennedy arXiv:1008.4321; Zeilberger arXiv:math/9506214 and Benjamin, Fib. Quart. 44 (2006) (two-row strip). jOEIS programs for A022444/A022445 use brute-force enumeration. I found no prior proof of the A022445 GF in any of these sources.

## Citation

```bibtex
@misc{math0:oeis-a022445,
  author       = {{math0}},
  title        = {{The generating function of A022445 (closed self-avoiding walks in the strip {0,1,2} x Z)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a022445}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

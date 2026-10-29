# A386538: moving the circle's center off the grid enlarges the max lattice polygon (counterexample at n = 7)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A386538  
**Date:** 2026-10-18

## Result

Conjecture (OEIS A386538, Felix Huber): for every n ≥ 0, the largest area of a polygon with vertices on Z^2 inside the closed disk of radius n is the same whether the disk's center is a grid point or any point of the plane. In the frozen encoding: for all n : ℕ, ⨆_{c ∈ ℝ²} vol(conv(Z² ∩ B(c, n))) = vol(conv(Z² ∩ B(0, n))). We prove the negation. At n = 7 with center c0 = (5/12, 5/24), the convex hull of the lattice points in B(c0, 7) has area at least 277/2 = 138.5. The convex hull for the center 0 has area at most 3457/25 = 138.28; its true value is 138 = a(7).

## Assessment

The conjecture is refuted by one explicit counterexample. With radius 7 and centre (5/12, 5/24), the lattice points in the disk have a convex hull of area 281/2, which beats a(7) = 138. Finding it took only a search over rational centres with exact hull areas, and checking it means comparing the areas of two explicit lattice polygons, a 12-gon and a 15-gon. No new idea was needed, and the extra work in Lean (trapezoid decompositions and measure-theory bookkeeping) does not change that. This is the conjecture as the author meant it, not a degenerate case, so it is genuinely settled, but the mathematics is routine.

*Follows from:* Direct finite search: exact convex-hull area computation of the lattice points in disks of radius n around rational centres, compared with a(7)=138 from the entry's own data.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A386538](https://oeis.org/A386538) as [`Math0.Statements.A386538.statement`](../../lean/Math0/Statements/OEIS/A386538.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A386538.lean`](../../lean/Math0/Frontier/OEIS/A386538.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: The maximum possible area of a polygon within the circle would be the same if only the vertices but not the center were fixed on grid points." (entry by _Felix Huber_, Aug 05 2025). The same conjecture appears for ellipses in A386539, which has T(n,n) = A386538(n).

Referees: Sources checked:
- Local OEIS mirror and raw.githubusercontent.com/oeis/oeisdata, A386538: #23, Aug 19 2025, no %E lines. A386539: #19, Aug 19 2025.
- Entries that cite A386538/A386539: A398490, A396223, A391113. None addresses the conjecture.
- Cross-references read: A066643, A123690, A125228, A288247, A322106, A322107, A357577, A108126. None resolves it. A123690 and A295344 concern lattice-point counts with an off-grid center, not polygon areas.
- Web searches for the A386538 number, the entry's wording, Felix Huber plus counterexample, SeqFan, and MathOverflow/Math.SE on convex hulls of lattice points in a shifted disk.

Related but not resolving:
- J. Zhao, "The Largest Circle Enclosing n Lattice Points", https://arxiv.org/abs/2505.06234, and its sequel https://arxiv.org/pdf/2609.16081
- Bárány–Larman and Balog–Deshouillers on the integer convex hull of a disk (vertex counts, origin-centered only), e.g. https://www.renyi.hu/~barany/cikkek/73.pdf

No prior proof or counterexample found.

OEIS data (found in the fidelity pass of 29 Oct 2026 and recomputed exactly): with the centre on a grid point, the largest polygon is the convex hull of the grid points in the disk. Its area differs from the listed terms at n = 13, 17, 18, 22, 23 (516, 888, 990, 1498, 1628, against the listed 512, 880, 986, 1490, 1624). The entry's Maple and Mathematica programs use a shortcut that does not compute this area. The counterexample at n = 7, where the listed a(7) = 138 is correct, is unaffected.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a386538,
  author       = {{math0}},
  title        = {{A386538: moving the circle's center off the grid enlarges the max lattice polygon (counterexample at n = 7)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a386538}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

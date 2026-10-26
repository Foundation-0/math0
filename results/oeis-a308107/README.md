# A308107: Barker's rational generating function and order-15 recurrence for the sum of smallest sides of scalene integer triangles

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A308107  
**Date:** 2026-10-24

## Result

Let a(n) be the sum of the smallest side k over all integer triples k < i < j with j < k + i and k + i + j = n, i.e. over all scalene integer triangles of perimeter n. Then (1) sum_{n>=0} a(n) x^n = x^9 (2 + 2x + 2x^2 + x^3) / ((1-x)^4 (1+x)^3 (1+x^2)^2 (1+x+x^2)^2) as formal power series over Q, and (2) for every n > 15, a(n) = -a(n-1) + 2a(n-3) + 4a(n-4) + 2a(n-5) - a(n-6) - 5a(n-7) - 5a(n-8) - a(n-9) + 2a(n-10) + 4a(n-11) + 2a(n-12) - a(n-14) - a(n-15).

## Assessment

The proof writes each scalene integer triangle with three positive parameters in one linear relation, 2u+4v+3w=n, with smallest side v+w. Summing this linear weight over the parameters gives the rational generating function in a few lines by a standard MacMahon-type calculation. The order-15 recurrence then follows directly from the denominator. The paper itself calls the argument elementary and a routine computation. The Lean proof's chain of shift bijections is only formalization effort, not a new idea.

*Follows from:* Standard parametrization of integer triangles (as in Alcuin's sequence A005044 / Andrews-Paule-Riese k-gon partitions): scalene triangles of perimeter n are (k,i,j)=(v+w, v+w+u, 2v+w+u) with u,v,w>=1 and 2u+4v+3w=n, so the g.f. is sum (v+w) x^(2u+4v+3w) = x^9(2-x^3-x^4)/((1-x^2)(1-x^3)^2(1-x^4)^2). Alternatively, Cuculiere's bijection in A005044 reduces it to A307686.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A308107](https://oeis.org/A308107) as [`Math0.Statements.A308107.statement`](../../lean/Math0/Statements/OEIS/A308107.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A308107.lean`](../../lean/Math0/Frontier/OEIS/A308107.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A308107 Conjectures from Colin Barker, May 13 2019: (Start) G.f.: x^9*(2 + 2*x + 2*x^2 + x^3) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2). a(n) = -a(n-1) + 2*a(n-3) + ... - a(n-15) for n>15. (End)

Referees: The OEIS entry A308107 (local mirror and current GitHub oeisdata, version #14 of Sep 12 2021) still marks Barker's May 13 2019 g.f. and recurrence as conjectures, with no proof note or %E edit. Its cross-reference A307686 and the related entries A308108, A308109 and A308158 also leave their Barker conjectures unproved. A005044 has Roger Cuculière's comment that scalene triangles of perimeter n+6 correspond to all triangles of perimeter n; this gives a reduction, not a proof. Sela Fried's proofs of OEIS conjectures (arXiv:2410.07237; JIS 28, 2025, Art. 25.4.3; JIS 29, 2026, Art. 26.1.8; arXiv:2607.24832) do not cover A308107 or any triangle sequence near it. Andrews–Paule–Riese (MacMahon's Partition Analysis IX, k-gon partitions), Hirschhorn on k-gon partitions, and arXiv:2308.01912 on Alcuin's sequence treat only the unweighted triangle count. I found no prior proof or counterexample.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a308107,
  author       = {{math0}},
  title        = {{A308107: Barker's rational generating function and order-15 recurrence for the sum of smallest sides of scalene integer triangles}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a308107}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

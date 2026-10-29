# Irwin's nested sums give column 0 of the triangle A132615 (A132616)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A132616  
**Date:** 2026-10-29

## Result

Let T be the infinite lower-triangular matrix with T(0,0) = 1 in which, for every n ≥ 0, row n+1 is row n of T^(2n-1) followed by a 1. For n = 0 the formal exponent is 0, which gives the same row [1, 1]. Let a(n) = T(n,0) (OEIS A132616). Define nest 0 c = 1 and nest (m+1) c = Sum_{i=1..c+2m} nest m i. Then nest(n-1, 1) is Irwin's nested sum Sum_{i_1=1..1+2(n-2)} Sum_{i_2=1..i_1+2(n-3)} ... Sum_{i_(n-1)=1..i_(n-2)} 1. Claim: for every n ≥ 2, a(n) = nest(n-1, 1).

## Assessment

The proof strengthens the claim to every power of the triangle: the (n,k) entry of T^p is Irwin's nested sum with outer bound p. Somos's two-argument program a(n,k) in the entry and Hanna's partial-sums "alternate generating method" in A132615 already point to this generalization. The proof then checks the semigroup law M_p M_q = M_{p+q} by a short double induction: when p goes up by one, row n+1 changes by row n of M at a shifted exponent, and the induction hypothesis matches the two sides. It ends with uniqueness of T, so M_1 = T. This is a standard strengthen-the-induction argument of about half a page, which a competent combinatorialist would find quickly once looking at the powers, a natural move for a triangle defined by its own powers. So it is routine, even though no proof had been published before.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A132616](https://oeis.org/A132616) as [`Math0.Statements.A132616.statement`](../../lean/Math0/Statements/OEIS/A132616.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A132616.lean`](../../lean/Math0/Frontier/OEIS/A132616.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A132616 From Benedict W. J. Irwin, Nov 29 2016: Conjecture: a(n) is described by a series of nested sums, a(2) = Sum_{i=1..1} 1, a(3) = Sum_{i=1..1+2} Sum_{j=1..i} 1, a(4) = Sum_{i=1..1+4} Sum_{j=1..i+2} Sum_{k=1..j} 1, a(5) = Sum_{i=1..1+6} Sum_{j=1..i+4} Sum_{k=1..j+2} Sum_{l=1..k} 1, and so on.

Referees: I found no prior proof or counterexample. Checked: the OEIS entries A132616 and A132615 (Hanna 2007, which includes the unproved "alternate generating method", an equivalent partial-sums form of Irwin's sums), A132617, A132618, A132619, A132610, A101479, A101481 (Kirchner 2017 recurrence, different triangle), and A304190, A304191, A304193 (Hanna 2018, conjectural g.f. links). Local mirror versions match current GitHub oeisdata, with no %E line recording a proof. Also checked S. Fried, "Proofs of several conjectures from the OEIS", JIS 28 (2025) Art. 25.4.3 (https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.html); S. Fried, "Proofs of ten conjectures from the OEIS", JIS 29 (2026) Art. 26.1.8 (https://cs.uwaterloo.ca/journals/JIS/VOL29/Fried/fried21.html); arXiv:2410.07237; arXiv:2606.09913, which proves Irwin's A007405 conjecture but not this one; and arXiv:2607.24832. None mentions A132616 or A132615. Unrelated constructions: P. Barry, arXiv:1804.06801, and arXiv:1203.4419 (Hanna's triangle A096651). Web searches of MathOverflow, Math StackExchange and SeqFan returned only the OEIS pages.

## Citation

```bibtex
@misc{math0:oeis-a132616,
  author       = {{math0}},
  title        = {{Irwin's nested sums give column 0 of the triangle A132615 (A132616)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a132616}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Kurkov's recursion for the row polynomials of convolution triangles holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A357583  
**Date:** 2026-10-29

## Result

For an integer sequence s(1), s(2), ..., let T_s(n,k) = [z^n] A(z)^k with A(z) = sum_{j>=1} s(j) z^j be its convolution triangle. Define polynomials R(n,k) in Z[x] by R(1,k) = s(k) and R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1. Then for every n > 0 the row polynomial sum_{k=0}^{n} T_s(n,k) x^k equals x*R(n,1). In particular (s = Bell numbers) the row polynomials of A357583 are x*R(n,1) with R(1,k) = Bell(k). Both parts of the frozen statement (the Bell case and the case of an arbitrary integer sequence) are proved.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A357583](https://oeis.org/A357583) as [`Math0.Statements.A357583.statement`](../../lean/Math0/Statements/OEIS/A357583.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A357583.lean`](../../lean/Math0/Frontier/OEIS/A357583.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: row polynomials are x*R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1, k > 0 with R(1,k) = Bell(k) for k > 0. The same recursion seems to work for self-convolution of any other sequence. - _Mikhail Kurkov_, Apr 05 2025

Referees: I found no prior resolution.
- The OEIS entries A357583 and A340991 are unchanged upstream since Apr 06 2025 (#10 and #24) and still say "Conjecture" (Mikhail Kurkov, Apr 05 2025).
- A357368, by P. Luschny, defines the convolution-triangle (PMatrix) terminology and gives the row-polynomial recursion P(n,x)=x Σ a(n-k) P(k,x), but not Kurkov's R recursion.
- Kurkov's sibling conjectures of the same shape are still open on OEIS: A350499, A263634, A356145, A055356.
- Neither entry is in google-deepmind/formal-conjectures, which is the corpus behind the Tsoukalas et al. dataset and Epoch's OEIS Open benchmark (arXiv 2608.11941).
- Sela Fried's arXiv 2607.24832 and 2410.07237 do not mention either entry.
- Searches of arXiv, MathOverflow and GitHub (including the-omega-institute/trureturing) found nothing on this recursion.

Relevant background: D. E. Knuth, "Convolution polynomials" (arXiv:math/9207221), on the convolution-triangle framework.

## Citation

```bibtex
@misc{math0:oeis-a357583,
  author       = {{math0}},
  title        = {{Kurkov's recursion for the row polynomials of convolution triangles holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a357583}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# A123710: the rows of inv(floor(n/k)) with four nonzero entries are 6 and the proper prime powers

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A123710  
**Date:** 2026-10-29

## Result

Let A be the lower-triangular matrix with A(n,k) = floor(n/k) (A010766), and let T = A^{-1} (A123706). Let R(n) be the number of nonzero entries in row n of T (A123709), and let a(n) be the n-th smallest n with R(n) = 4 (A123710, offset 1). Let A025475(n) be the n-th term of 1, 4, 8, 9, 16, 25, ... (1 and the prime powers p^m with m >= 2). Hasler's conjecture: a(n) = A025475(n) for all n > 2. Equivalently, R(n) = 4 exactly when n = 6 or n is a proper prime power.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A123710](https://oeis.org/A123710) as [`Math0.Statements.A123710.statement`](../../lean/Math0/Statements/OEIS/A123710.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A123710.lean`](../../lean/Math0/Frontier/OEIS/A123710.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A123710 a(n) = A025475(n) for n>2 (conjectured). - _M. F. Hasler_, Feb 12 2012

Referees: OEIS sequences, all read from the local mirror and checked against https://raw.githubusercontent.com/oeis/oeisdata/main/seq/:
- A123710 (#27, Sep 05 2025): formula still marked "(conjectured)" (Hasler, Feb 12 2012).
- A123709: Hasler's 2^k / omega formula with the n = 6 exception, given without proof. Links Luschny's seqcomp message http://groups.google.com/group/seqcomp/msg/2aabf27ef9b698ef (Feb 2012). The visible part of that thread has the closed form and asks for a proof of A123712 = A178212, but nothing on A123710.
- A123706: Perez Herrero closed form T(n,k) = mu(n/k) - mu(n/(k+1)) (Feb 21 2012), without proof.
- A123711 and A200511, A123712 and A178212: related conjectures, still open.
- A206706: Luschny's variant triangle.

Other sources:
- OEIS wiki, "Sequences determined by prime signature": lists A123711 and A123712 under "Examples which need to be checked".
- S. Fried, JIS 28 (2025) Art. 25.4.3; JIS 29 (2026) Art. 26.1.8; arXiv:2607.24832 (Jul 2026). None treat A123710.

Searches of arXiv, MathOverflow and MSE found no proof of A123710. The SeqFan Feb 2012 archive was unreachable.

## Citation

```bibtex
@misc{math0:oeis-a123710,
  author       = {{math0}},
  title        = {{A123710: the rows of inv(floor(n/k)) with four nonzero entries are 6 and the proper prime powers}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a123710}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

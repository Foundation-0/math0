# Signed A350557 is the matrix inverse of A350512, proved

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A350557  
**Date:** 2026-10-26

## Result

Let T be the A350557 triangle: T(n,0) = (2n)!/(2^n n!) = (2n-1)!!, and for 1 ≤ k ≤ n, T(n,k) = (2n-1)!! · Σ_{i=k}^{n} C(i-1,k-1)/(2i-1)!!. Set T(n,k) = 0 for k > n. Let L be the A350512 triangle: L(n,0) = 1, and for 1 ≤ k ≤ n, L(n,k) = C(n-1,k-1)(2k(n-k)+n)/k. Set L(n,k) = 0 for k > n. Define M(n,k) = (-1)^(n-k) T(n,k). Then M and L are inverse lower-triangular matrices: for all n, j ≥ 0, Σ_{k=0}^{n} L(n,k) M(k,j) = [n=j] and Σ_{k=0}^{n} M(n,k) L(k,j) = [n=j]. This is Werner Schulte's 2022 conjecture.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A350557](https://oeis.org/A350557) as [`Math0.Statements.A350557.statement`](../../lean/Math0/Statements/OEIS/A350557.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A350557.lean`](../../lean/Math0/Frontier/OEIS/A350557.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A350557 Conjecture: M(n,k) = (-1)^(n-k) * T(n,k) is matrix inverse of A350512. (Werner Schulte, entry author, Jan 2022)

Referees: No prior resolution found. Sources checked:
(1) OEIS A350557 and A350512, in both the local mirror and the current raw.githubusercontent oeisdata. The conjecture is still marked open, there are no %E lines, and neither entry has been edited since Jan 18 2022. Across the full mirror, no other entry cross-references A350557 or A350512. I also read A286286, A249349 and A103450.
(2) google-deepmind/formal-conjectures (local checkout from Oct 2026): neither sequence is formalized.
(3) google-deepmind/alphaproof-nexus-results (Tsoukalas et al., arXiv:2605.22763): A350557 is not among the APNOutputs/OEIS files, and the paper does not mention it.
(4) Adamczewski, "OEIS Open" (arXiv:2608.11941): its appendix of resolved conjectures does not include A350557.
(5) "Further proofs of conjectures from the OEIS" (arXiv:2607.24832) and S. Fried, "Proofs of some conjectures from the OEIS" (arXiv:2410.07237): A350557 is not mentioned in either.
(6) Web searches for the A-numbers, the defining formulas, the column g.f. (1+2kx)x^k/(1-x)^(k+1), and Schulte together with the inverse: the only hit is the OEIS page, which still states the claim as a conjecture.
The result is mathematically elementary (a recurrence plus binomial inversion), but there is no published or recorded proof, so I classify it as a new result.

## Citation

```bibtex
@misc{math0:oeis-a350557,
  author       = {{math0}},
  title        = {{Signed A350557 is the matrix inverse of A350512, proved}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a350557}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

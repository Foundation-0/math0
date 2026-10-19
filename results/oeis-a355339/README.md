# A355339: the central even run of the knight-move triangle has length 1 iff n = 2^m - 2

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A355339  
**Date:** 2026-10-19

## Result

Let T(n,k) be the knight-move triangle A355320. It is defined by T(0,0)=1, with zero entries outside |k| <= 2n, and T(n,k) = T(n-1,k-2) + T(n-1,k+2) + T(n-2,k-1) + T(n-2,k+1). Let a(n) be the length of the maximal block of consecutive even entries of row n that contains the centre k=0. It is 0 if T(n,0) is odd, and a(0)=0. Then for every n >= 0, a(n) = 1 if and only if n > 0 and n = 2^m - 2 for some m >= 0 (equivalently, n+2 = 2^{t+2} for some t >= 0).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A355339](https://oeis.org/A355339) as [`Math0.Statements.A355339.statement`](../../lean/Math0/Statements/OEIS/A355339.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A355339.lean`](../../lean/Math0/Frontier/OEIS/A355339.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F Conjecture: a(n) = 1 iff n > 0 and n belongs to A000918. (Rémy Sigrist, Jun 29 2022)

Referees: - OEIS A355339 (Rémy Sigrist, Jun 29 2022): the conjecture is in %F and is still unresolved at revision #10, with no %E extensions (checked in the local mirror and upstream oeisdata on GitHub).
- OEIS A355320 (the triangle; its %F gives T(n,0)=A096609(n) and T(n,1)=A096610(n), but nothing on parity).
- OEIS A096608–A096612 (Kimberling 2004, Catalan knight paths in the right half-plane), A096587, A361292, A000918, A002605: no parity results.
- J.-L. Baril, N. Hassler, S. Kirgizov, J. L. Ramírez, "Grand zigzag knight's paths", arXiv:2402.04851 (ECA 2024): its only parity remark (Remark 3.2) concerns zigzag path counts being even when n ≡ k (mod 2), not this conjecture.
- J.-L. Baril, J. L. Ramírez, "Knight's paths towards Catalan numbers", arXiv:2206.12087: nothing on parity.
- Web searches of arXiv, MathOverflow/MSE, SeqFan and general sources found no prior proof or counterexample.
- No formalization in google-deepmind formal-conjectures.

## Citation

```bibtex
@misc{math0:oeis-a355339,
  author       = {{math0}},
  title        = {{A355339: the central even run of the knight-move triangle has length 1 iff n = 2^m - 2}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a355339}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Column sums of strictly superdiagonal reversed partitions by maximum are A000245

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A388724  
**Date:** 2026-10-25

## Result

Let T(n,k) be the number of reversed integer partitions y = (y_1 <= ... <= y_m) of n (positive parts, weakly increasing, sum n) that are strictly superdiagonal (y_i > i for all i) and have maximum part k. Then for every k >= 1, sum_n T(n,k) = A000245(k-1), where A000245(0) = 0 and A000245(K) = 3(2K)!/((K+2)!(K-1)!) for K >= 1.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A388724](https://oeis.org/A388724) as [`Math0.Statements.A388724.statement`](../../lean/Math0/Statements/OEIS/A388724.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A388724.lean`](../../lean/Math0/Frontier/OEIS/A388724.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Column sums are A000245. - _Gus Wiseman_, Sep 24 2025

Referees: OEIS A388724 (rev #12, Oct 06 2025; the conjecture is still listed and no %E resolution is recorded). M. Archibald, A. Blecher, S. Elizalde, A. Knopfmacher, "Subdiagonal and superdiagonal partitions", Afrika Matematika 36:77 (2025), doi:10.1007/s13370-025-01282-0. Theorem 2.3 and its proof give a bijection from superdiagonal weakly increasing partitions with largest part m to pairs (P in D_m, 0 ≤ h < final E-run length of P), plus the generating function for fixed largest part. Theorem 2.2's proof gives a bijection from partitions with k parts and largest part s to the ballot paths B_{k-1,s}. Combined with the shift y_i -> y_i - 1 and the classical identity sum over D_m of final descent length = A000245(m) (E. Deutsch, "Dyck path enumeration", Discrete Math. 204 (1999); the A000245 comment by Homberger on total returns), or with Catalan-triangle row sums (A009766, which has A000245 as a diagonal), this yields the conjecture immediately. No explicit prior statement or proof of the column-sum identity was found on OEIS, arXiv, MathOverflow, Math StackExchange or the web.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a388724,
  author       = {{math0}},
  title        = {{Column sums of strictly superdiagonal reversed partitions by maximum are A000245}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a388724}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# Fixed polyominoes with n cells and width n-2: T(n,n-2) = 8n^2 - 51n + 86 (A308359)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A308359  
**Date:** 2026-10-19

## Result

For every n >= 5, the number T(n, n-2) of fixed polyominoes with n cells whose convex hull has width n-2 equals 8n^2 - 51n + 86. A fixed polyomino is a finite edge-connected set of grid cells, taken up to translation. The statement file encodes it as the normalized set S in N x N that has min x = 0 and min y = 0. The height is unrestricted.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A308359](https://oeis.org/A308359) as [`Math0.Statements.A308359.statement`](../../lean/Math0/Statements/OEIS/A308359.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A308359.lean`](../../lean/Math0/Frontier/OEIS/A308359.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A308359 Conjecture: T(n,n-2) = 8*n^2 - 51*n + 86 for n >= 5.  (Entry by _R. J. Mathar_, May 22 2019; last edit Oct 10 2022.)

Referees: A. Goupil, H. Cloutier, F. Nouboud, "Enumeration of inscribed polyominos", FPSAC 2010, DMTCS proc. AN (2010) 737-748 (https://dmtcs.episciences.org/2808; hal-01186234; cited in OEIS A196593). Theorem 1 gives pmin(b,k) = 2k+2b-3bk-8+8*C(b+k-2,b-1), so pmin(w,3) = 4w^2-3w-2. Theorem 3 (k=2, b>2) gives pmin+1(b,2) = 4b^2-16b+18. Since T(n,n-2) = pmin(n-2,3) + pmin+1(n-2,2) = 8(n-2)^2-19(n-2)+16 = 8n^2-51n+86, Mathar's 2019 conjecture follows directly. The OEIS A308359 entry (last edited Oct 2022) still says "Conjecture" and has no proof note. Related but not resolving: L. Marin, "Counting Polyominoes in a Rectangle b x h", arXiv:2406.16413 (EPTCS 403, 2024), which covers fixed width and any height. I found no MathOverflow, Math StackExchange or SeqFan discussion explicitly proving the A308359 formula.

## Citation

```bibtex
@misc{math0:oeis-a308359,
  author       = {{math0}},
  title        = {{Fixed polyominoes with n cells and width n-2: T(n,n-2) = 8n^2 - 51n + 86 (A308359)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a308359}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

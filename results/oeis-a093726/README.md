# Imaginary parts of the convergents of [1+i; 1+i, 1+i, ...] are A317974(n+1)/A138573(n)

**Classification:** New result (open problem settled)  
**Area:** Number theory  
**Source problem:** OEIS A093726  
**Date:** 2026-10-24

## Result

Let c_n = (1+i) + 1/((1+i) + ... + 1/(1+i)) be the continued fraction with n partial quotients 1+i, so c_1 = 1+i and c_{n+1} = (1+i) + 1/c_n. Write c_n = (A093725(n) + a(n) i)/A093727(n) in Mathematica's Numerator/Denominator form (A093727(n) = lcm of the denominators of Re c_n and Im c_n). Let A317974 be 0,0,1,1 and A138573 be 0,1,2,5, both continued by u(n) = 2(u(n-1)+u(n-2)+u(n-3)) - u(n-4). Then for every n >= 1, a(n)/A093727(n) = A317974(n+1)/A138573(n) as rational numbers.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A093726](https://oeis.org/A093726) as [`Math0.Statements.A093726.statement`](../../lean/Math0/Statements/OEIS/A093726.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A093726.lean`](../../lean/Math0/Frontier/OEIS/A093726.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(n)/A093727(n) = A317974(n+1)/A138573(n). - _Zhuorui He_, Jun 16 2026

Referees: OEIS A093726 rev #13 (Jun 20 2026): the formula is still marked "Conjecture: a(n)/A093727(n) = A317974(n+1)/A138573(n). - Zhuorui He, Jun 16 2026"; there is no later %E edit recording a proof. Related prior work: Peter Bala's 2014 formula in OEIS A138573 that A138573(n) = |U(n)|^2 for the Gaussian Lucas sequence U(n) = (1+i)U(n-1) + U(n-2), which covers the denominator part only. A317974 (rev #35, Jun 30 2026) has no relevant formula. Not covered by S. Fried, "Further proofs of conjectures from the OEIS", arXiv:2607.24832 (Jul 2026); I checked its full text for the A-numbers. Fried's earlier papers (arXiv:2410.07237; JIS 2025 and 2026) predate the conjecture. No MathOverflow, Math StackExchange, SeqFan or arXiv resolution found. Sources: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A093/A093726.seq, https://arxiv.org/abs/2607.24832

## Citation

```bibtex
@misc{math0:oeis-a093726,
  author       = {{math0}},
  title        = {{Imaginary parts of the convergents of [1+i; 1+i, 1+i, ...] are A317974(n+1)/A138573(n)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a093726}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

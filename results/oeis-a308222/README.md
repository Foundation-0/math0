# Perimeters of primitive Heronian isosceles triangles: A308222(n) = 2 · A096033(n + 2)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A308222  
**Date:** 2026-10-19

## Result

Let a(n) be the n-th smallest perimeter of a primitive Heronian isosceles triangle (integer sides with no common divisor, integer area, two sides equal). Let A096033(n) be the n-th smallest difference z - x, where x is a leg and z the hypotenuse of a primitive Pythagorean triangle. Then for every n ≥ 1, a(n) = 2 · A096033(n + 2).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A308222](https://oeis.org/A308222) as [`Math0.Statements.A308222.statement`](../../lean/Math0/Statements/OEIS/A308222.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A308222.lean`](../../lean/Math0/Frontier/OEIS/A308222.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F a(n) = 2*A096033(n+2) (conjectured). (Peter Kagey, May 16 2019)

Referees: Main prior resolution: Math StackExchange answer 3230072 by user "George", 2019-05-17 (https://math.stackexchange.com/a/3230072), answering Peter Kagey's question 3230019, "Semiperimeter of isosceles Heronian triangles". It is linked in the A308222 %H line. It derives that primitive isosceles Heronian triangles are (u^2+v^2, u^2+v^2, 2(u^2-v^2)) or (u^2+v^2, u^2+v^2, 4uv) with semiperimeters 2u^2 or (u+v)^2, citing J. R. Carlson, "Determination of Heronian Triangles", Fibonacci Quarterly 8 (1970) 499-506, Lemma 2.

Also: Wikipedia, "Integer triangle", section "Isosceles Heronian triangles" (the same parametrization: two copies of a Pythagorean triangle joined along a leg). The A096033 comment (Weimholt, 2010) says A096033 is the odd squares together with the numbers 2n^2.

No prior formalization found. OEIS A308222 (local mirror, #20, Aug 12 2022) still marks the formula "(conjectured)".

## Citation

```bibtex
@misc{math0:oeis-a308222,
  author       = {{math0}},
  title        = {{Perimeters of primitive Heronian isosceles triangles: A308222(n) = 2 · A096033(n + 2)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a308222}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# No primitive Heronian triangle has integer circumradius

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A392943  
**Date:** 2026-10-19

## Result

Let x, y, z be positive integers satisfying the strict triangle inequalities, with gcd(x, y, z) = 1, and let K be a natural number with 16K^2 = (x+y+z)(-x+y+z)(x-y+z)(x+y-z), i.e. K is the area. Then there is no natural number R with 4KR = xyz. In other words, no primitive Heronian triangle has integer circumradius. This is Felix Huber's conjecture in OEIS A392943.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A392943](https://oeis.org/A392943) as [`Math0.Statements.A392943.statement`](../../lean/Math0/Statements/OEIS/A392943.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A392943.lean`](../../lean/Math0/Frontier/OEIS/A392943.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: There is no primitive Heronian triangle with integer circumradius." (entry by _Felix Huber_, Feb 04 2026)

Referees: Ronald van Luijk, "The diameter of the circumcircle of a Heron triangle", Elemente der Mathematik 63 (2008), 118–121. The relevant parts are:
- Theorem 2, (4)⇒(5): if gcd(a,b,c,d) = 1, every prime divisor of the circumdiameter d is ≡ 1 mod 4.
- Corollary 5: for a prime p ≢ 1 mod 4, p^{v_p(d)} divides gcd(a,b,c).
- Proof of Theorem 1: it states explicitly that a Heron triangle with integer circumradius has all sides even.

Earlier related work:
- A.-V. Kramer & F. Luca, "Some remarks on Heron triangles", Acta Acad. Paedagog. Agriensis Sect. Mat. (N.S.) 27 (2000) 25–38. Shows no power of 2 is the circumradius of a Heron triangle.
- M. Aassila, "Some results on Heron triangles", Elem. Math. 56 (2001) 143–146.

Also related, with full text not checked: E. Read, "Integer triangles with integer circumradii", Math. Gazette 107 (2023) 241–248.

OEIS A392943 (Huber, Feb 2026) cites none of these, and no proof has been added to the entry.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a392943,
  author       = {{math0}},
  title        = {{No primitive Heronian triangle has integer circumradius}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a392943}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

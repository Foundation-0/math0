# Repdigits with repdigit digital product are repunits from a(16) = 1111 on (A201060)

**Classification:** First formal proof of a known result  
**Area:** Sequences and series  
**Source problem:** OEIS A201060  
**Date:** 2026-10-20

## Result

Let a(1) < a(2) < ... list the repdigits (all decimal digits equal; 0 counts) whose digital product is also a repdigit. Then a(n) is a repunit (all digits equal to 1) for every n >= 16. Formally: forall n >= 16, IsRepunit (a n), where a n = Nat.nth IsTerm (n - 1).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A201060](https://oeis.org/A201060) as [`def statement`](../../lean/Math0/Statements/OEIS/A201060.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A201060.lean`](../../lean/Math0/Frontier/OEIS/A201060.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: a(n) is repunit for n >= 16." (A201060, entry by _Jaroslav Krizek_, Nov 26 2011)

Referees: Main citations:
- R. Obláth, "Une propriété des puissances parfaites", Mathesis 65 (1956), 356–364. It shows that the only perfect powers with all decimal digits equal to some a != 1 are 4, 8 and 9.
- Y. Bugeaud and M. Mignotte, "On integers with identical digits", Mathematika 46 (1999), 411–417. It shows that no decimal repunit with two or more digits is a perfect power.
Together these say that no repdigit >= 10 is a perfect power, and the A201060 conjecture follows directly, since d^k >= 16 for 2 <= d <= 9 and k >= 4.

Both results are restated in O. Kihel and F. Luca, "Perfect Powers With All Equal Digits But One", J. Integer Seq. 8 (2005), Article 05.5.7, Introduction (https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.html). See also A. Gica and L. Panaitopol, "On Oblath's Problem", J. Integer Seq. 6 (2003), Article 03.3.5, which is linked from OEIS A018885 and A368049. The Wikipedia article "Repdigit" (https://en.wikipedia.org/wiki/Repdigit) covers the related Nagell–Ljunggren equation and cites Bugeaud–Mignotte 2002.

The OEIS entry A201060 (local mirror, revision #11, 2012) still labels the statement as a conjecture, and I found no web or arXiv discussion that names A201060.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a201060,
  author       = {{math0}},
  title        = {{Repdigits with repdigit digital product are repunits from a(16) = 1111 on (A201060)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a201060}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# A172164: the second differences of the Theodorus-spiral turns are always 18, 19, 20 or 21

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A172164  
**Date:** 2026-10-24

## Result

Let S(k) = sum_{i=1}^{k} arctan(1/sqrt i) be the total central angle of the first k triangles of the spiral of Theodorus. Triangle i covers the angular sector [S(i-1), S(i)], and turn n is the angle range [2pi(n-1), 2pi n]. Let c(n) be the number of triangles i >= 1 that lie entirely inside turn n, that is, with 2pi(n-1) <= S(i-1) and S(i) <= 2pi n. Then for every n >= 2, the difference a(n) = c(n) - c(n-1) is one of 18, 19, 20, 21. This is Dumortier's conjecture in OEIS A172164.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A172164](https://oeis.org/A172164) as [`Math0.Statements.A172164.statement`](../../lean/Math0/Statements/OEIS/A172164.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A172164.lean`](../../lean/Math0/Frontier/OEIS/A172164.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture : The terms are only 18,19,20,21 (From the first thousand turns, there are 2,3% of 18, 36,5% of 19, 46,2% of 20 and 15% of 21). No period found. Probably due to Pi transcendence." (Sebastien Dumortier, Jan 27 2010)

Referees: I found no prior proof or counterexample.

OEIS entries (local mirror, identical to the raw GitHub copy):
- A172164 (Dumortier, 2010): the conjecture, with numerical frequency checks by R. G. Wilson v (1e5 turns) and H. Kociemba (1e7 turns), 2013. Still listed as a conjecture at edit #25, Aug 2026.
- A137515: "the number added grows by 18, 19, 20 or 21 (tested up to 5000 terms)"; restated by H. P. Dale in 2019 with no proof.
- A072895: Kociemba's comment that floor((pi n + c)^2 - 1/6) with c = -K/2 = 1.0788914983... differs from A072895(n) by at most 1, and equals it for n < 1e9 (numerical only).
- A105459: Hlawka's Schneckenkonstante K, with the formula Sum_{x<n} arctan(1/sqrt x) = 2 sqrt n + K + o(1).
- A296179, A296181, A295338, A295339 (W. Lang): related revolution counts; nothing on this bound.

Background sources for the asymptotics:
- E. Hlawka, "Gleichverteilung und Quadratwurzelschnecke", Monatsh. Math. 89 (1980) 19-44.
- P. J. Davis, "Spirals: From Theodorus to Chaos" (1993).
- D. Brink, Amer. Math. Monthly 119 (2012) 779-786.
- J. Waldvogel, "Analytic Continuation of the Theodorus Spiral" (2008).
- Kociemba, "The Spiral of Theodorus" (kociemba.org/themen/spirale/theodorus.html): unreachable, seen only through search snippets, which cover the asymptotics and turn counts but no proof of the 18–21 bound.

Unrelated papers checked: arXiv 2403.20207 (Stouten, about hypotenuses on a common line; withdrawn) and arXiv 2407.07109 (the Fibonacci–Theodorus spiral).

The result follows from effective versions of the Hlawka/Davis asymptotics, but no source I found writes the bound down.

## Citation

```bibtex
@misc{math0:oeis-a172164,
  author       = {{math0}},
  title        = {{A172164: the second differences of the Theodorus-spiral turns are always 18, 19, 20 or 21}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a172164}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

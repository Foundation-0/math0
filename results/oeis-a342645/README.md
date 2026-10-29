# A342645: diagonals of the eventual Mahonian-column polynomials

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A342645  
**Date:** 2026-10-29

## Result

For x ≥ n, the number M(x,n) of permutations of x letters with major index n is a polynomial P_n(x) of degree ≤ n. Let T(n,k) = n!·[x^k]P_n(x). The triangle is computed by Newton interpolation of M(x,n) at x = n,…,2n.

(Diagonals) For every m ≥ 0 there is Q ∈ ℚ[X] with deg Q = 2m and leading coefficient |A290030(m)/A053657(m+1)| such that T(n,n−m) = Q(n) for every n ≥ m. Here A290030(m) is the x^m-coefficient of the numerator L·B_m^(x) of Nørlund's polynomial B_m^(x) = m![t^m](t/(e^t−1))^x, where L is the least common denominator of its coefficients. A053657(m+1) = ∏_p p^{Σ_k ⌊m/((p−1)p^k)⌋}.

(Formulas) T(n,n) = 1; T(n,n−1) = (n²−3n)/2; T(n,n−2) = (3n⁴−22n³+21n²−2n)/24; T(n,n−3) = (n⁶−13n⁵+37n⁴+13n³−134n²+96n)/48. Each holds for every n at which the left side is an entry of the triangle.

## Assessment

Expanding the known column polynomial into falling factorials gives T(n,k) = sum_j e_j n(n-1)...(n-j+1) c(n-j,k). The term j of T(n,n-m) then has degree 2m-j by the classical Stirling-polynomial fact, so the degree is 2m and the leading coefficient 1/(2^m m!) comes from j=0. Putting in e_0..e_3 = 1,-1,-1,0 and the closed forms of c(N,N-r) for r ≤ 3 gives the four formulas. Matching 1/(2^m m!) with |A290030(m)/A053657(m+1)| follows directly from the Chabert-Cahen primitivity statement recorded in A053657. The whole argument is about a page of standard material. The 2500-line Lean proof re-derives the Norlund denominators from von Staudt-Clausen and Adams' theorem, but that is formalization effort, not new mathematics.

*Follows from:* The column formula P_n(x) = sum_j e_j C(x+n-j-1, n-j), with e_j the pentagonal-number coefficients of prod(1-q^i). It is in Mike Earnest's MSE answer linked from the entry and in Netto and Knuth (TAOCP 3, Sec. 5.1.1). The Stirling polynomial fact that c(N,N-r) is a polynomial of degree 2r with leading coefficient 1/(2^r r!) (Graham-Knuth-Patashnik (6.44), Jordan, Gessel-Stanley 1978). The A053657 comment citing Chabert-Cahen that (t/(e^t-1))^x = sum_n P(n,x) t^n/A053657(n+1) with P(n,x) primitive in Z[x]. With the leading x-coefficient (-1/2)^m/m! of [t^m](t/(e^t-1))^x, this gives |A290030(m)/A053657(m+1)| = 1/(2^m m!).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A342645](https://oeis.org/A342645) as [`Math0.Statements.A342645.statement`](../../lean/Math0/Statements/OEIS/A342645.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A342645.lean`](../../lean/Math0/Frontier/OEIS/A342645.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A342645 Conjecture: For each m, T(n,n-m) is a polynomial of degree 2m whose leading coefficient is abs(A290030(m)/A053657(m+1)). %F Conjectures: T(n,n) = 1. T(n,n-1) = (-3n + n^2)/2. T(n,n-2) = (-2n + 21n^2 - 22n^3 + 3n^4)/24. T(n,n-3) = (96n - 134n^2 + 13n^3 + 37n^4 - 13n^5 + n^6)/48. (Peter Kagey, Mar 17 2021)

Referees: The conjecture itself has no prior resolution that I found. OEIS A342645 (Kagey, Mar 17 2021; last edit #25, Aug 12 2022) still states both conjectures, and the local mirror equals upstream oeisdata. Known ingredients:
(1) The column polynomial via Euler's pentagonal expansion: E. Netto, Lehrbuch der Combinatorik (p. 96); D. Knuth, TAOCP Vol. 3, Sec. 5.1.1; Mike Earnest, MSE answer https://math.stackexchange.com/a/4065913 (linked in the entry); also G. Hegedus, arXiv:1002.2054, Thm 1.4.
(2) Stirling polynomials: c(N,N-k) is a polynomial of degree 2k with leading coefficient 1/(2^k k!) (C. Jordan, Calculus of Finite Differences; I. Gessel and R. Stanley, Stirling polynomials, JCTA 24 (1978)); s(n,n-k) = C(n-1,k) B_k^(n).
(3) Denominators of Norlund polynomials: J.-L. Chabert, Integer-valued polynomials on prime numbers and logarithm power expansion, Eur. J. Combin. 28 (2007) 754-761; A. Adelberg, Discrete Math. 204 (1999), Cor. 3; F. Bencherif, Sur une propriete des polynomes de Norlund, Actes CIRM 2(2) (2010) 71-77, Lemma 1 (d_n B_n^(x) is primitive in Z[x], with d_n = M_n/n! = A001898(n) and M_n = A053657(n+1)). Together with the OEIS A053657 comment a(n) = (n-1)!*A001898(n-1) (Bala, citing Chabert-Cahen), this already gives |A290030(m)/A053657(m+1)| = 1/(2^m m!).
Not found: any source combining these into the diagonal polynomiality of A342645 or its four FORMULA identities, on arXiv, OEIS, MSE search results, or SeqFan search results. MSE pages could not be fetched directly from this machine.

## Citation

```bibtex
@misc{math0:oeis-a342645,
  author       = {{math0}},
  title        = {{A342645: diagonals of the eventual Mahonian-column polynomials}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a342645}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

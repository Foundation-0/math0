# OEIS A350900: Schulte's gcd-ratio double sum is a Dirichlet convolution

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A350900  
**Date:** 2026-10-24

## Result

Let a(f; n) = Sum_{i=1..n} Sum_{k=1..n} f(gcd(i,n)/gcd(gcd(i,k),n)). Then: (1) for every complex arithmetic function f and every n > 0, a(f; n) = ((f·φ) * A057660)(n), where f·φ is the pointwise product with Euler's totient, * is Dirichlet convolution, and A057660(m) = Sum_{k=1..m} m/gcd(m,k). (2) If f is multiplicative, so is a(f; ·). (3) For n > 0, the row sum Sum_{k=1..n} T(n,k) of the A350900 triangle T(n,k) = Sum_{i=1..n} gcd(i,n)/gcd(gcd(i,k),n) equals a(id; n). (4) For n > 0, that row sum equals (A002618 * A057660)(n), where A002618(n) = n·φ(n).

## Assessment

Set g = gcd(i,n). The summand depends on i only through g, and its dependence on k has period g. Apply Cesàro's identity once to group the i, use periodicity to collapse the k-sum to one period, apply Cesàro's identity again, and re-index the divisors. This gives a(f;n) = ((f*phi) * 1 * (id*phi))(n), and 1 * (id*phi) is A057660 by its own %F line. Multiplicativity then follows from standard closure properties, and the row-sum parts follow by exchanging the sums and taking f = id. The whole argument fits in under a page of standard gcd-sum manipulation, and the manuscript itself calls it routine.

*Follows from:* Cesàro's identity Sum_{k=1..n} F(gcd(k,n)) = Sum_{d|n} F(d) phi(n/d) (Tóth's gcd-sum survey, JIS 2010), together with the formula A057660(n) = Sum_{d|n} d*phi(d), which is already in cross-referenced entry A057660. Part (4) was already stated as a formula in A373059.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A350900](https://oeis.org/A350900) as [`Math0.Statements.A350900.statement`](../../lean/Math0/Statements/OEIS/A350900.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A350900.lean`](../../lean/Math0/Frontier/OEIS/A350900.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Let f be an arbitrary arithmetic function. Define for n > 0 the sequence a(f; n) = Sum_{i=1..n, k=1..n} f(gcd(i,n)/gcd(gcd(i,k),n)); a(f; n) equals Dirichlet convolution of f(n)*A000010(n) and A057660(n); if f is multiplicative, then a(f; n) is multiplicative; row sums of this triangle use f(n) = n (see formula section). Also %F: Conjecture: Row sums equal Dirichlet convolution of A002618 and A057660. (Werner Schulte, Jan 21 2022)

Referees: I did not query oeis.org; OEIS entries were read from the local mirror dated 2026-10-17.
- A350900 (Werner Schulte, Jan 21 2022; last edit #13, May 24 2024): both claims are still labeled "Conjecture", and no %E line records a proof.
- A373059 (Seiichi Manyama, May 21 2024; "Row sums of A350900"): states a(n) = Sum_{d|n} phi(n/d)(n/d) sigma_2(d^2)/sigma(d^2) = (A002618*A057660)(n) without proof or conjecture label. Amiram Eldar (May 27 2024) added the multiplicative formula and the Dirichlet g.f. zeta(s)zeta(s-2)^2/zeta(s-1)^2. This is a prior unproved assertion of part 4.
- Related OEIS identities, also without proof: A350156 (Schulte, the analogous claim for f(n/gcd(i,k,n))); A371492, A371628, A373060, A373061, A372962, A372964, A372968 (Manyama, May 2024; sums of gcd(x_1,n)/gcd(x_1,...,x_k,n)).
- A057660 (= Sum_{d|n} d*phi(d)).
- Classical background: Cesaro's identity; L. Toth, "A survey of gcd-sum functions", JIS 13 (2010) 10.8.1; O. Bordelles, "A Multidimensional Cesaro Type Identity and Applications", JIS 18 (2015) 15.3.7; P. Bala, "GCD sum theorems. Two Multivariable Cesaro Type Identities" (A368743 attachment; I could not retrieve its text).
- Checked and not relevant: S. Fried, "Further proofs of conjectures from the OEIS", arXiv:2607.24832 (A350900 is not among its sequences); D. Himane, NNTDM 31 (2025) (a different Schulte conjecture, about A006472).
No prior proof or counterexample of the A350900 conjecture was found.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a350900,
  author       = {{math0}},
  title        = {{OEIS A350900: Schulte's gcd-ratio double sum is a Dirichlet convolution}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a350900}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

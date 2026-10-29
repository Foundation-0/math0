# Columns 1 and 2 of the theta-series triangle A355360 are P(x)^3 and 2P(x)^6

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A355360  
**Date:** 2026-10-29

## Result

Let A(x,y) = sum_m a_m(y) x^m be the series (a_m in Z[y]) computed by the entry's recursion a_0 = 1, a_{m+1} = y a_m - [x^{m+1}] F(a_0 + ... + a_m x^m). Here F(B) = sum_{n in Z} (-1)^n x^{n(n+1)/2} B^n = sum_{n>=0} (-1)^n x^{n(n+1)/2} (B^n - B^{-(n+1)}), and this recursion is the unique solution of x y A = F(A). Let T(n,k) = [x^n y^k] A. Then for every n >= 0:
- T(n+1, 1) = A000716(n), the number of partitions of n into parts of 3 kinds;
- T(n+2, 2) = 2 * A023005(n), twice the number of partitions of n into parts of 6 kinds.
Equivalently, the y- and y^2-coefficients of A are x P^3 and 2 x^2 P^6, where P = prod_{k>=1} 1/(1-x^k). These are Hanna's conjectures (C.1) and (C.2).

## Assessment

Put A = 1+u. Formula (3) of the entry turns into x*y*(1+u)^2 = u*G(1+u), where G(A) = prod(1-x^n)(1-x^n A)(1-x^n/A). G is invariant under A -> 1/A and G(1) = P^{-3}, so G(1+u) = P^{-3}(1 + O(u^2)). Comparing the y and y^2 coefficients then gives u = xyP^3 + 2(xyP^3)^2 + O(y^3). Pairing n with -1-n and applying Jacobi's cube identity gives the same few-line computation. The Lean proof is long only because it proves Jacobi's identity from scratch and checks the PARI-style recursion; that is formalization effort, not a new mathematical idea.

*Follows from:* The entry's own formula (3), x*y*A*P = prod_{n>=1}(1 - x^n*A)(1 - x^(n-1)/A) (Jacobi triple product), or equivalently Jacobi's classical identity prod(1-x^k)^3 = sum_{n>=0} (-1)^n (2n+1) x^{n(n+1)/2}

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A355360](https://oeis.org/A355360) as [`Math0.Statements.A355360.statement`](../../lean/Math0/Statements/OEIS/A355360.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A355360.lean`](../../lean/Math0/Frontier/OEIS/A355360.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A355360 Conjectures. (C.1) Column 1 equals A000716, the number of partitions into parts of 3 kinds. (C.2) Column 2 equals twice A023005, the number of partitions into parts of 6 kinds. (Paul D. Hanna, Jul 19 2022)

Referees: OEIS A355360: Paul D. Hanna, Jul 19 2022. Last edit %I #7 Jul 20 2022, in both the local mirror and raw.githubusercontent oeisdata main. It has no %E lines and (C.1)/(C.2) are still labeled "Conjectures."

Related entries:
- A355350: same column conjectures, still open.
- A355870: column-1 conjecture, still open.
- A354650: asserts column 1 = A000716 for a different theta table, with no proof given. It cites arXiv:2609.32264 (LANTERN), which is about relation-mining and does not cover these entries.
- A355361 through A355365: asymptotics only.

Not covered in:
- the epoch-research/LeanOpenProblems-results metadata and runs (arXiv:2608.11941; Tsoukalas et al., arXiv:2605.22763);
- google-deepmind/formal-conjectures (FormalConjectures/OEIS/355360.lean returns 404);
- S. Fried's arXiv:2410.07237, JIS 28 (2025) no. 4, JIS 29 (2026) Article 26.1.8, and arXiv:2607.24832 (that paper covers A355372, not A355360).

Web searches of MathOverflow, Math StackExchange, SeqFan and arXiv found no proof or counterexample. The underlying tool, Jacobi's identity prod (1-q^k)^3 = sum (-1)^n (2n+1) q^{n(n+1)/2}, is classical.

## Citation

```bibtex
@misc{math0:oeis-a355360,
  author       = {{math0}},
  title        = {{Columns 1 and 2 of the theta-series triangle A355360 are P(x)^3 and 2P(x)^6}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a355360}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

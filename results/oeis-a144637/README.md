# A144637: (1/18) 6^n a(n)/n! is odd iff n = 2^k with k >= 1

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A144637  
**Date:** 2026-10-26

## Result

Let S(n,k) be A144385: the number of partitions of {1,...,k} into exactly n blocks, each of size 1, 2 or 3. Let T = A144633 be the transpose of the inverse of the upper unitriangular matrix M(i,j) = S(i,j). Let a(n) = T(n,2), and y(n) = (1/18) 6^n a(n) / n!. Then for every n >= 0, y(n) is an odd integer if and only if n = 2^k for some k >= 1.

## Assessment

The entry already gives the algebraic equation 36y^3 + 3y^2 + (1+6x)y = x^2 for y(x) = A(6x)/18. Rewritten as y = x^2 - 6xy - 3y^2 - 36y^3 with y(0) = 0, it determines each coefficient from earlier ones using only integer arithmetic, so every coefficient is an integer. Reducing mod 2 gives y = x^2 + y^2 over F_2, and the Frobenius map then forces y = sum over k >= 1 of x^(2^k). The whole argument takes a few lines and uses standard tricks. The Lean proof is long only because it also has to derive the cubic from the matrix-inverse definition.

*Follows from:* Bala's formula in the entry: (1/18)A(6x) satisfies 36y^3 + 3y^2 + (1+6x)y = x^2 (this follows from Jovovic's e.g.f. B(x)^2/2, where B is the series reversion of x + x^2/2 + x^3/6, as given in A144636).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A144637](https://oeis.org/A144637) as [`Math0.Statements.A144637.statement`](../../lean/Math0/Statements/OEIS/A144637.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A144637.lean`](../../lean/Math0/Frontier/OEIS/A144637.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: (1/18)*6^(n)*a(n)/n! is odd iff n = 2^k for k >= 1. (End) - _Peter Bala_, Feb 19 2026

Referees: OEIS A144637 (Bala conjecture, Feb 19 2026; entry revision #25, Mar 14 2026; no proof recorded). The companion conjecture in OEIS A144636 (Bala, Feb 16 2026) is also unresolved. OEIS A144633 and A144385 give the definitions. Checked with nothing found on either conjecture: S. Fried, "Proofs of Ten Conjectures From the OEIS", J. Integer Sequences 29 (2026), Art. 26.1.8; S. Fried, "Further proofs of conjectures from the OEIS", arXiv:2607.24832 (full text grepped); Epoch AI, "OEIS Open", arXiv:2608.11941 and github.com/epoch-research/LeanOpenProblems (no A14463x file); Engbers–Galvin–Smyth, "Restricted Stirling and Lah number matrices and their inverses", JCTA 2019 (integrality of inverses, not parity). No prior proof or counterexample found.

## Citation

```bibtex
@misc{math0:oeis-a144637,
  author       = {{math0}},
  title        = {{A144637: (1/18) 6^n a(n)/n! is odd iff n = 2^k with k >= 1}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a144637}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

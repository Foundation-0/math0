# A355339: the central even run of the knight-move triangle has length 1 iff n = 2^m - 2

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A355339  
**Date:** 2026-10-19

## Result

Let T(n,k) be the knight-move triangle A355320. It is defined by T(0,0)=1, with zero entries outside |k| <= 2n, and T(n,k) = T(n-1,k-2) + T(n-1,k+2) + T(n-2,k-1) + T(n-2,k+1). Let a(n) be the length of the maximal block of consecutive even entries of row n that contains the centre k=0. It is 0 if T(n,0) is odd, and a(0)=0. Then for every n >= 0, a(n) = 1 if and only if n > 0 and n = 2^m - 2 for some m >= 0 (equivalently, n+2 = 2^{t+2} for some t >= 0).

## Assessment

By symmetry, the claim reduces to two parity facts: T(n,0) is even for n>=1, and T(n,1) is odd exactly when n+2 is a power of 2. Both come out of a standard technique. Reduce the row recurrence already stated in A355320 modulo 2. There 1+X^4=(1+X^2)^2 and X^3+X^5=X^3(1+X^2), so the recurrence has an explicit binomial closed form (a sum over compositions of n). The coefficient parities then follow from Lucas's theorem (equivalently, Kummer's carry criterion) by a short carry argument. The whole argument is about a page of elementary mod-2 polynomial algebra and binomial parity, the kind of thing a competent combinatorialist would find quickly. The conjecture most likely stayed open because the entry is obscure, not because it is hard.

*Follows from:* The row-polynomial recurrence R_{n+1}=(1+X^4)R_n+(X^3+X^5)R_{n-1} given in A355320 (%F and PARI code), reduced mod 2 using 1+X^4=(1+X^2)^2, combined with Lucas's theorem for p=2.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A355339](https://oeis.org/A355339) as [`Math0.Statements.A355339.statement`](../../lean/Math0/Statements/OEIS/A355339.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A355339.lean`](../../lean/Math0/Frontier/OEIS/A355339.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F Conjecture: a(n) = 1 iff n > 0 and n belongs to A000918. (Rémy Sigrist, Jun 29 2022)

Referees: - OEIS A355339 (Rémy Sigrist, Jun 29 2022): the conjecture is in %F and is still unresolved at revision #10, with no %E extensions (checked in the local mirror and upstream oeisdata on GitHub).
- OEIS A355320 (the triangle; its %F gives T(n,0)=A096609(n) and T(n,1)=A096610(n), but nothing on parity).
- OEIS A096608–A096612 (Kimberling 2004, Catalan knight paths in the right half-plane), A096587, A361292, A000918, A002605: no parity results.
- J.-L. Baril, N. Hassler, S. Kirgizov, J. L. Ramírez, "Grand zigzag knight's paths", arXiv:2402.04851 (ECA 2024): its only parity remark (Remark 3.2) concerns zigzag path counts being even when n ≡ k (mod 2), not this conjecture.
- J.-L. Baril, J. L. Ramírez, "Knight's paths towards Catalan numbers", arXiv:2206.12087: nothing on parity.
- Web searches of arXiv, MathOverflow/MSE, SeqFan and general sources found no prior proof or counterexample.
- No formalization in google-deepmind formal-conjectures.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a355339,
  author       = {{math0}},
  title        = {{A355339: the central even run of the knight-move triangle has length 1 iff n = 2^m - 2}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a355339}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

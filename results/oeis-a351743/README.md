# A351743: from n = 139 the sequence is affine in 42-blocks, which proves Sycamore's, Sigrist's and the A355149 conjectures

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A351743  
**Date:** 2026-10-20

## Result

Let a(1)=1 and let a(n+1) be the greatest divisor of s(n)=a(1)+...+a(n) that is prime to a(n) (OEIS A351743; s is A355149). Then:
(1) a(n)=1 for infinitely many n, and a(n)=2 for infinitely many n (Sycamore).
(2) a(2(n+21)-1) = a(2n-1) for all n >= 70 (Sigrist).
(3) There is a 21-periodic integer sequence b with a(2(n+21)) = 3645 a(2n) + b(n) for all n >= 70 (Sigrist).
(4) There is a 42-periodic integer sequence c with s(n+42) = 3645 s(n) + c(n) for all n >= 138 (A355149 conjecture).

## Assessment

The proof writes a and s on each 42-term block as affine functions of Y_m = (3645^m-1)/3644. The 42 coefficient rows come from the computed data, and Sigrist's conjectures already describe this shape. Each of the 42 steps of the recursion is then shown to hold for every value of the parameter, using two elementary gcd lemmas and a finite check of small divisibility and coprimality facts. Together with a direct computation of the first 139 terms, this proves all four conjectures. This is the standard way to certify an eventually periodic or affine pattern in a recursively defined sequence, and once the ansatz is set up it reduces to a finite computation. No new idea was needed, even though the conjectures had stayed open since 2022.

*Follows from:* Sigrist's own conjectured formulas in A351743 (%F) and A355149 (%F), which already describe the block structure; the proof makes that structure an explicit affine ansatz in Y_m = (3645^m-1)/3644 and checks it by a finite computation.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A351743](https://oeis.org/A351743) as [`Math0.Statements.A351743.statement`](../../lean/Math0/Statements/OEIS/A351743.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A351743.lean`](../../lean/Math0/Frontier/OEIS/A351743.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A351743 (a(1)=1; a(n+1) = greatest divisor of s(n) prime to a(n), s = partial sums): "Conjecture: a(n)=1 occurs infinitely many times, and therefore so does a(n)=2." (_David James Sycamore_, Jun 07 2022) and "Conjectures from _Rémy Sigrist_, Jun 20 2022: (Start) - a(2*(n+21)-1) = a(2*n-1) for n >= 70, - a(2*(n+21)) = 3645*a(2*n) + b(n) for n >= 70 (where b is 21-periodic). (End)". A355149 (partial sums of A351743): "Conjecture: a(n + 42) = 3645*a(n) + b(n) for n >= 138 (where b is 42-periodic)."

Referees: OEIS A351743 (David James Sycamore, Jun 07 2022) states the conjecture that 1 and 2 occur infinitely often. Its formula section, from Rémy Sigrist on Jun 20 2022, adds the conjectures a(2(n+21)-1) = a(2n-1) and a(2(n+21)) = 3645 a(2n) + b(n), both for n >= 70. OEIS A355149 (De Vlieger, Sigrist and Sycamore, Jun 21 2022; last edit #11 Nov 17 2022) states the conjecture s(n+42) = 3645 s(n) + b(n) for n >= 138. Both entries still list these as open conjectures in the current oeisdata. The only other entry that cites them is A357735, which has nothing on them. I searched the full text of S. Fried's OEIS-conjecture papers (arXiv:2410.07237; J. Integer Seq. 28 (2025) 25.4.3; J. Integer Seq. 29 (2026) 26.1.8; arXiv:2607.24832) and none mentions these sequences. Searches of the web, arXiv, MathOverflow/MSE and SeqFan found no proof or counterexample.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a351743,
  author       = {{math0}},
  title        = {{A351743: from n = 139 the sequence is affine in 42-blocks, which proves Sycamore's, Sigrist's and the A355149 conjectures}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a351743}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

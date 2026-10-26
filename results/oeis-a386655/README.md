# A386655 modulo 6 is eventually periodic with pattern [1, 0, 3, 0, 3, 2]

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A386655  
**Date:** 2026-10-24

## Result

Let a(n) = sum_{k=0..n} C(n,k) 2^(k(k+1)) (2^k - (n-k))^(n-k-1), where the k = n term is read as 2^(n^2) and 0^0 = 1. Then for every n >= 6, a(n) mod 6 equals the entry with index (n-6) mod 6 of [1, 0, 3, 0, 3, 2]. Equivalently, a(n) mod 6 = 1, 0, 3, 0, 3, 2 for n ≡ 0, 1, 2, 3, 4, 5 (mod 6). (Paul D. Hanna's conjecture, OEIS A386655.)

## Assessment

The proof starts from the explicit sum formula already given in the entry and works modulo 2 and modulo 3 separately. Modulo 2 only the k=0 term survives, which is immediate. Modulo 3, writing 2 = -1 and using Fermat's little theorem makes each summand a 6-periodic function of n-k. Such a function can be written with C(m,j), j <= 2, and (-1)^m, and a standard binomial-transform identity then gives a(n) = 1-n^2 or n^2-n mod 3; CRT finishes. This is an elementary argument of about a page, the kind of residue computation a competent mathematician would carry out quickly, so it is routine. The scout had already outlined it before the proof attempt.

*Follows from:* The entry's explicit formula a(n) = Sum_{k=0..n} C(n,k) 2^(k(k+1)) (2^k-(n-k))^(n-k-1), combined with Fermat's little theorem mod 2 and mod 3 and the standard identity Sum_m C(n,m) C(m,j) x^m = C(n,j) x^j (1+x)^(n-j).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A386655](https://oeis.org/A386655) as [`Math0.Statements.A386655.statement`](../../lean/Math0/Statements/OEIS/A386655.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A386655.lean`](../../lean/Math0/Frontier/OEIS/A386655.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A386655 (E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!): "Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating." (_Paul D. Hanna_, Aug 23 2025). Analogues: A386656 (q=3) [4,3,2,1,0,1], A386657 (q=4) [1,2,3,2,3,4], A386658 (q=5) [4,3,0,3,0,5].

Referees: I found no earlier resolution.
- OEIS A386655 (local mirror and current GitHub oeisdata, revision #14, Aug 24 2025) still states the mod-6 claim as a conjecture by Paul D. Hanna, with no %E edit or proof note.
- The cross-referenced sister entries A386656, A386657 and A386658 (q = 3, 4, 5) state analogous mod-6 conjectures, none marked proved. The related entry A386648 also has an open mod-6 conjecture.
- Web searches turned up only OEIS pages (e.g. https://oeis.org/A386648, https://oeis.org/A136524) and no paper, arXiv preprint, MathOverflow/Math StackExchange post or SeqFan message proving or refuting the A386655 conjecture.
- The classical tool used is the expansion e^(cW(x)) = Sum_k c(c-k)^(k-1) x^k/k! (the tree-function/Lambert W identity), together with Fermat's little theorem and the binomial-transform identity Sum_m C(n,m)C(m,j)x^m = C(n,j)x^j(1+x)^(n-j).

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a386655,
  author       = {{math0}},
  title        = {{A386655 modulo 6 is eventually periodic with pattern [1, 0, 3, 0, 3, 2]}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a386655}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

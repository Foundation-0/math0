# The 1089-trick map has two 9-digit fixed points (A393794 uniqueness conjecture is false)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A393794  
**Date:** 2026-10-18

## Result

Let rev(m) be the decimal reversal of m (leading zeros dropped), and let T(x) = D + rev(D) with D = |x - rev(x)|. Havenaar's conjecture in A393794 says that for every n >= 1, a(n) = 110*(10^(n+1) - 1) is the only fixed point of T with exactly n+4 decimal digits. This is false. For n = 5, x = 108910890 has 9 digits and satisfies T(x) = x, but x is not a(5) = 109999890.

## Assessment

The refutation is one explicit 9-digit number whose fixed-point property is checked by a few lines of arithmetic. Where it comes from is immediate from the entry itself: the entry's proof uses only 9k = rev(k), and it points to A001232, whose listed data includes the non-primitive term 10891089. Extending this to every n >= 5 (using 1089 0...0 1089) is equally elementary. The number had also already appeared in the conjecturer's own computational output and in Almirantis-Li. No new idea was needed, so this is routine.

*Follows from:* The entry's own proof that T(a(n)) = a(n) works for any k with 9k = rev(k): rev(10k) = 9k, so D = k and T(10k) = 10k. Cross-reference A001232 lists such k, including the non-primitive term 10891089 (its 5th term; Hasler's comment there describes the concatenated terms 1089 0...0 1089). This gives 10*10891089 = 108910890, a second 9-digit fixed point. A direct exhaustive search of 9-digit numbers also finds it.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A393794](https://oeis.org/A393794) as [`Math0.Statements.A393794.statement`](../../lean/Math0/Statements/OEIS/A393794.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A393794.lean`](../../lean/Math0/Frontier/OEIS/A393794.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "a(n) is the unique fixed point of the 1089-trick map T among all (n+4)-digit numbers (verified exhaustively for n = 1..4; conjectured for all n >= 1)." (comment in A393794, entry by _Remco Havenaar_, Feb 27 2026; the entry names the sequence 'Fixed points of the 1089-trick map' and gives a(n) = 110*(10^(n+1)-1))

Referees: OEIS A393794 (Havenaar, Feb 27 2026; #19, Mar 10 2026, no correction as of GitHub oeisdata mirror). OEIS A001232 (numbers k with 9k = rev k; includes non-primitive 10891089; structure theorem by D. W. Wilson 1997 and M. F. Hasler 2022), from which 10*A001232 ⊂ Fix(T) follows trivially. R. Havenaar, SYNTRIAD/digit-dynamics GitHub repo (initial commit 2026-03-09): papers/paper_A.tex still states the uniqueness conjecture, while data/results_export.json experiment id 10 (truc_1089, 7-digit domain, 2026-02-25) lists 108910890 among T's fixed points without remark. Neither source states the contradiction. Y. Almirantis and W. Li, arXiv:2408.02527 and arXiv:2410.11784 (Fibonacci Quart. 64 (2026) 281-310) study the related two-option reversal map Phi, with Phi(Phi(x)) = T(x) in the relevant range; arXiv:2410.11784, which predates the conjecture, lists 108910890 twice: in Table 2 as part of the 2-cycle {10891089, 108910890} of Phi, and in Appendix A.2 among the outputs of the two-step 1089 trick on eight-digit numbers; it does not consider the fixed points of T. OEIS A124074 (S. Dumortier, 2006) studies a variant of Phi whose example already shows the 2-cycle 1089 -> 10890 -> 1089. No published refutation found: this is the first explicit refutation, and it is mathematically elementary.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a393794,
  author       = {{math0}},
  title        = {{The 1089-trick map has two 9-digit fixed points (A393794 uniqueness conjecture is false)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a393794}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

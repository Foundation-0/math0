# Reverse-divisor numbers are 1, 12, 78 or 89 mod 100 (A071685, Dale's conjecture)

**Classification:** First formal proof of a known result  
**Area:** Sequences and series  
**Source problem:** OEIS A071685  
**Date:** 2026-10-20

## Result

Let R(n) be the decimal digit reversal of n, with leading zeros dropped. Suppose n is not a palindrome (R(n) ≠ n), 10 does not divide n, and either n | R(n) or R(n) | n. Then n mod 100 is 1, 12, 78 or 89.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A071685](https://oeis.org/A071685) as [`def statement`](../../lean/Math0/Statements/OEIS/A071685.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A071685.lean`](../../lean/Math0/Frontier/OEIS/A071685.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: every term mod 100 is equal to 1, 12, 78, or 89. - _Harvey P. Dale_, Dec 13 2017"

Referees: D. J. Hoey, "Palintiples", rec.puzzles archive (arithmetic/digits/palintiples.s), May 1992 (https://djm.cc/rpa-output/arithmetic/digits/palintiples.s): a finite-state classification of every base-10 N = C·R(N) with C > 1. C is 4 or 9, and N is 87…12 or 98…01. OEIS A031877 comment (Hasler 2014, annotated by Sloane Oct 19 2014): "All terms are of the form 87...12 = 4*21...78 or 98...01 = 9*10...89. [This was proved by Hoey, 1992.]" L. F. Klosinski and D. C. Smolarski, "On the Reversing of Digits", Math. Mag. 42 (1969) 208-210: k ∈ {1, 4, 9}. D. W. Wilson's theorem (1997) in A001232/A008918: terms are 99·m and 198·m with m a 0/1 palindrome with no singleton digits, so they are ≡ 89 and ≡ 78 (mod 100). N. J. A. Sloane, "2178 And All That", arXiv:1307.0453, Fib. Quart. 52 (2014) 99-120. L. H. Kendrick, "Young Graphs: 1089 et al.", J. Integer Seq. 18 (2015) 15.9.7. B. V. Holt, INTEGERS 14 (2014) A42. Webster and Williams, Math. Spectrum 45 (2012/13) 96-102. M. F. Hasler, A001232 comment (Oct 2022): terms begin and end with 109*89. Dale's conjecture (Dec 2017) came after all of these. The OEIS entry was not updated to mark it resolved, and I found no prior Lean formalization.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a071685,
  author       = {{math0}},
  title        = {{Reverse-divisor numbers are 1, 12, 78 or 89 mod 100 (A071685, Dale's conjecture)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a071685}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

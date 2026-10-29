# A373359: Schreier-set row lengths equal the Zeckendorf weight A007895

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A373359  
**Date:** 2026-10-26

## Result

Let A371176 be the increasing sequence of positive integers k with popcount(k) <= v_2(2k), i.e. popcount(k) <= (index of the lowest 1-bit of k) + 1. These are the binary codes of the Schreier sets X (|X| <= min X). Row n of A373359 is the set of 1-based positions of the 1-bits of A371176(n). For every n >= 1, row n has as many elements as there are terms in the Zeckendorf representation of n. Equivalently, popcount(A371176(n)) = A007895(n).

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A373359](https://oeis.org/A373359) as [`Math0.Statements.A373359.statement`](../../lean/Math0/Statements/OEIS/A373359.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A373359.lean`](../../lean/Math0/Frontier/OEIS/A373359.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %Y A373359 Cf. A007895 (conjectured row lengths), A373346 (row sums), A373347. (_Paolo Xausa_, Jun 04 2024; the same 'conjectured row lengths' cross-reference appears in A373345 and A373579)

Referees: - OEIS A373359 and A373345 (Paolo Xausa, Jun 2024): "A007895 (conjectured row lengths)". Local mirror and upstream are unchanged.
- OEIS A371176 (Mikhail Kurkov, Mar 14 2024):
  - formula a(n) = 2^(A072649(n)-1) + [c(n)>0]*2*a(c(n)) with c = A066628;
  - formula a(n) = b(n)*A001316(b(n))/2 with b = A048679;
  - Kurkov comment of Oct 21 2024: A371176(n) is the Zeckendorf representation of n with the 01->1 rewrite and k-1 zeros appended. Each implies popcount(A371176(n)) = A007895(n).
- A007895 formula a(n) = A000120(A003714(n)) (Zumkeller 2005).
- GitHub issue the-omega-institute/trureturing #9050 (Sep 20 2026): https://github.com/the-omega-institute/trureturing/issues/9050. An informal proof of the A373345/A373359 row-length identity, via Chu's bijection plus order preservation and via Bird's recursive blocks.
- H. V. Chu, "The Fibonacci Sequence and Schreier-Zeckendorf Sets", J. Integer Seq. 22 (2019), Art. 19.6.5 (arXiv:1906.10962): the bijection between Schreier sets and Zeckendorf sets.
- A. Bird, "Jozef Schreier, Schreier sets and the Fibonacci sequence", Out Of The Norm blog, May 13 2012: binary ordering of Schreier sets and |M_n| = F_n.
- H. V. Chu, arXiv:2606.21865 (2026), a survey that does not state the binary-rank theorem.
- I found no prior Lean or other formal proof.

## Citation

```bibtex
@misc{math0:oeis-a373359,
  author       = {{math0}},
  title        = {{A373359: Schreier-set row lengths equal the Zeckendorf weight A007895}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a373359}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# A334595: a(n) = 1 iff n is a power of two, and the records occur exactly at 1 and 2^k + 1

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A334595  
**Date:** 2026-10-24

## Result

Let a(n) be the number obtained as follows. Write n in binary, most significant bit first. Build the XOR-triangle whose first row is that bit string; each later row is the pairwise XOR of adjacent entries of the row above. Read the right side of the triangle from the top-right corner downward, and interpret it as a binary numeral with the first entry as the most significant bit. Then:
(1) For n >= 1, a(n) = 1 if and only if n is a power of two.
(2) The record positions are exactly {1} together with {2^k + 1 : k >= 1}. Here n >= 1 is a record position when a(n) > a(m) for every 1 <= m < n.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A334595](https://oeis.org/A334595) as [`Math0.Statements.A334595.statement`](../../lean/Math0/Statements/OEIS/A334595.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A334595.lean`](../../lean/Math0/Frontier/OEIS/A334595.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Records occur at 1 and at 2^n + 1.  /  Conjecture: a(n) = 1 if and only if n is a power of two. (_Peter Kagey_, May 07 2020)

Referees: I found no earlier proof or counterexample for either A334595 conjecture.
- OEIS A334595 (Peter Kagey, May 2020): unchanged since revision #18 (May 09 2020), with both statements still labeled "Conjecture".
- MathOverflow 359138, "Number triangle" (user DSM, with answers by YCor and Ilya Bogdanov): treats the boundary operator φ_k with φ_k^3 = 1 and counts rotationally symmetric triangles (A334556/A334596). It does not address records or a(n) = 1.
- OEIS A334727 (Rémy Sigrist, 2020): states that the left-diagonal map is a self-inverse permutation.
- Paul D. Hanna's XOR binomial transform entries (OEIS A099884, A099900, A099902): note that the transform is self-inverse.
These are the known ingredients that make the result elementary. Web searches of SeqFan, arXiv, MathOverflow and Math StackExchange found no resolution.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a334595,
  author       = {{math0}},
  title        = {{A334595: a(n) = 1 iff n is a power of two, and the records occur exactly at 1 and 2^k + 1}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a334595}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

# A308121: for odd n > 1, row 2n is row n with its halves swapped

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A308121  
**Date:** 2026-10-25

## Result

Let T(n,k) = b_n·k − a_n·r_k(n), where r_1(n) < ... < r_φ(n)(n) are the totatives of n and a_n/b_n is φ(n)/n in lowest terms (A076512/A109395). Row n is (T(n,1), ..., T(n,φ(n))). Claim (Charlie Neder's conjecture): for every odd n > 1, row n splits into two halves A, B of equal length with row n = A ++ B, and row 2n = B ++ A.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A308121](https://oeis.org/A308121) as [`Math0.Statements.A308121.statement`](../../lean/Math0/Statements/OEIS/A308121.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A308121.lean`](../../lean/Math0/Frontier/OEIS/A308121.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: If n is odd, then row 2n can be obtained from row n by interchanging the first and second halves. (Charlie Neder, Jun 05 2019)

Referees: - OEIS A308121 (Jamie Morken, May 13 2019; last edited Aug 05 2019, revision #47). Charlie Neder's conjecture of Jun 05 2019 is still marked "Conjecture," with no %E or comment recording a proof.
- The two entries that cite it, A307964 and A309497, do not resolve it.
- The cross-referenced entries A109395, A076512, A038566 and A076511 contain nothing about the conjecture.
- The classical background is phi(2n) = phi(n) for odd n and the bijection between totatives of n and of 2n; see arXiv 0907.1689, which treats a related map as a routine exercise.
- A308121 is absent from google-deepmind/formal-conjectures, and so from the OEIS Open benchmark (arXiv 2608.11941).
- Web searches (arXiv, MSE/MO, OEIS wiki) found no prior proof or counterexample. The SeqFan archive could not be reached (503 / connection reset).

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a308121,
  author       = {{math0}},
  title        = {{A308121: for odd n > 1, row 2n is row n with its halves swapped}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a308121}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

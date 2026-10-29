# A275815: Jones's conjecture a(n) = 8(n-2)^2 for n >= 6 holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A275815  
**Date:** 2026-10-29

## Result

For n >= 6, take a set S of squares on the n x n board and put a queen on each square of S. All queens have the same colour, so a queen may move along any of its 8 directions only to an empty square, and only through empty squares. Let M(S) be the total number of moves available to all the queens. Then the maximum of M(S) over all S is exactly 8(n-2)^2. In the formal version, a n = (board n).powerset.sup (totalMoves n), and the claim is that a n = 8 * (n - 2)^2 for every n >= 6.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A275815](https://oeis.org/A275815) as [`Math0.Statements.A275815.statement`](../../lean/Math0/Statements/OEIS/A275815.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A275815.lean`](../../lean/Math0/Frontier/OEIS/A275815.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(n) = 8(n-2)^2 for n >= 6. - _Alec Jones_, Nov 16 2016

Referees: The OEIS entry A275815 (#43, Jul 11 2021) still lists Jones's formula as a conjecture, with keyword "more". It records Wu's bounds 8(n-2)^2 <= a(n) <= 8n^2 (Nov 2016), a(6) from Branicky (Feb 2021) and a(7)-a(32) from Randell's MiniZinc runs (Jul 2021).

Jim Randell, "Enigma 69: Maximum queen moves", https://enigmaticcode.wordpress.com/2013/03/10/enigma-69-maximum-queen-moves/, has only computation: a 6x6 exhaustive check (2017), a MiniZinc model run up to 64x64 (2020) and solver comparisons (2025). It gives no general proof.

The cross-referenced entries A278211, A278212 and A278214 contain no proof. A278214's T(n, n^2-k) = 8k for k <= (n-2)^2 is only the easy per-empty-square bound.

Web searches of arXiv, MathOverflow, Math StackExchange, Puzzling, SeqFan and the chess-puzzle literature found no general proof or counterexample.

The one prior proof found is internal: math0's own results/oeis-a278212 (2026-10-24) already proves a(n) = 8(n-2)^2 for n >= 7 (Math0/Frontier/OEIS/A278212.lean). The present file adds the exact n=6 case (a(6) = 128, already known by computer) and states the full conjecture formally.

## Citation

```bibtex
@misc{math0:oeis-a275815,
  author       = {{math0}},
  title        = {{A275815: Jones's conjecture a(n) = 8(n-2)^2 for n >= 6 holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a275815}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

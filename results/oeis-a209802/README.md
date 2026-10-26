# Positivity of the exponential Mertens function (A209802)

**Classification:** First formal proof of a known result  
**Area:** Sequences and series  
**Source problem:** OEIS A209802  
**Date:** 2026-10-18

## Result

Let mu_e be the exponential Möbius function (A166234). It is multiplicative with mu_e(p^e) = mu(e), so mu_e(n) = prod_{p | n} mu(v_p(n)). Let a(n) = sum_{k=1}^{n} mu_e(k) (A209802). Then a(n) > 0 for every n >= 1. This is Zumkeller's conjecture in the OEIS entry.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A209802](https://oeis.org/A209802) as [`Math0.Statements.A209802.statement`](../../lean/Math0/Statements/OEIS/A209802.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A209802.lean`](../../lean/Math0/Frontier/OEIS/A209802.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A209802 (Partial sums of exponential Möbius function, A166234): "Analog of Mertens's function, A002321; conjecture: a(n) > 0." (entry by _Reinhard Zumkeller_, Mar 13 2012)

Referees: No explicit resolution of the A209802 conjecture found:
- OEIS A209802 (https://oeis.org/A209802) and its history (https://oeis.org/history?seq=A209802, versions 1-29) still list "conjecture: a(n) > 0"; nothing about a proof is recorded.
- A166234 (exponential Möbius function) and A368405 add nothing on positivity.

Prior results that imply the conjecture at once:
- K. Rogers, "The Schnirelmann density of the squarefree integers", Proc. Amer. Math. Soc. 15 (1964) 515-516, doi:10.1090/S0002-9939-1964-0163893-X. It proves Q(n) >= 53n/88 for all n, with equality only at n = 176.
- L. Moser and R. A. MacLeod, "The error term for the squarefree integers", Canad. Math. Bull. 9 (1966), doi:10.4153/CMB-1966-039-4.
- The same bound is recorded in an OEIS A013928 comment (M. Marcus 2012; C. R. Greathouse IV 2016).
- L. Tóth, "On certain arithmetic functions involving exponential divisors, II", Annales Univ. Sci. Budapest. Sect. Comp. 27 (2007) 155-166, arXiv:0708.3557. It gives mu_e taking values in {-1, 0, 1} with mu_e(p) = 1, and the asymptotic sum mu_e(n) = c x + O(x^{1/2} log x) with c about 0.36094. That settles positivity only for large x.

Together these give a(n) >= 2Q(n) - n >= 9n/44 > 0 for all n >= 1.

Also checked, with nothing relevant found:
- Lelechenko, arXiv:1405.7597
- Cao and Zhai, J. Integer Seq. 13 (2010)
- Web, MathOverflow and Math StackExchange searches

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a209802,
  author       = {{math0}},
  title        = {{Positivity of the exponential Mertens function (A209802)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a209802}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

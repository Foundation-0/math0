# Denominators of Sum C(k)/4^(k-1): Groux's and Staunton's conjectures (A120069)

**Classification:** First formal proof of a known result  
**Area:** Sequences and series  
**Source problem:** OEIS A120069  
**Date:** 2026-10-20

## Result

Let C(k) be the Catalan numbers, r(n) = Sum_{k=1..n} C(k)/4^(k-1), and a(n) the denominator of r(n) in lowest terms (A120069). Let A283208(n) be the least e >= 0 such that 2^e (2n+1)/(n+1) c(2n) is a nonnegative integer, where c(2n) = Pochhammer(1/2,n)/n!. Then for every n >= 1: (Groux) a(n) = denominator(C(n)/4^(n-1)), and (Staunton) a(n) = 2^(A283208(n) - 2), with the exponent taken in the integers.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A120069](https://oeis.org/A120069) as [`Math0.Statements.A120069.statement`](../../lean/Math0/Statements/OEIS/A120069.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A120069.lean`](../../lean/Math0/Frontier/OEIS/A120069.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A120069 (Denominators of partial sums r(n) = Sum_{k=1..n} C(k)/2^(2(k-1)), C = Catalan): "Conjecture: a(n) = denominator(Catalan(n)/4^(n-1)). - _Groux Roland_, Dec 11 2010" and "Conjecture: a(n) = 2^(A283208(n)-2). - _Alexander Staunton_, Feb 28 2026"

Referees: OEIS sources (read from the local mirror; A120069 also checked against GitHub oeisdata main):
- A120778, formula by Groux Roland, Jan 04 2011: sum_{k=0..n} C(k)/4^k = 2(1 - binomial(2n+2,n+1)/4^(n+1)).
- A119951, comment by Pieter Mostert, Oct 12 2012: r(n) = sum_{k=1..n} C(k)/4^(k-1) = 4 - binomial(2n+2,n+1)/2^(2n-1).
- A120777, which records:
  - Johannes W. Meijer, Jul 06 2009: a(n) = denominator(C(2n+2,n+1)/2^(2n+1)).
  - Peter Luschny's new name, Apr 2024: a(n) = 2^(2n - v2(Catalan(n))).
  - Amiram Eldar, Apr 18 2024: a(n) = 2^(2n - A048881(n)) = 2^A283208(n).
  - A comment that its terms coincide with the denominators of sum_{k=0..n} C(k)/4^k.
- A283208:
  - Comment: 2^a(n) is the denominator of 2^(-2n)·A001700(n).
  - Formula by Zabolotskii, 2021: a(n) = A005187(n+1) - 1.

Combining these gives A120069(n) = A120777(n)/4 = 2^(A283208(n)-2) = den(C(n)/4^(n-1)). No explicit paper, MSE/MO post or SeqFan message resolving the A120069 conjectures by name was found. A120069 #30 (Mar 10 2026) still lists both as conjectures.

Web pages:
- https://oeis.org/A120778
- https://oeis.org/A120777
- https://oeis.org/A119951
- arXiv:0906.4290, "Asymptotics of partial sums of central binomial coefficients and Catalan numbers". Found in search; related, but I did not read it.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a120069,
  author       = {{math0}},
  title        = {{Denominators of Sum C(k)/4^(k-1): Groux's and Staunton's conjectures (A120069)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a120069}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

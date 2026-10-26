# Repunit residues: a(n) = n - 1 exactly for long period primes

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Number theory  
**Source problem:** OEIS A335012  
**Date:** 2026-10-18

## Result

For n >= 1 let a(n) be the number of distinct values R_k mod n for 1 <= k <= n, where R_k = (10^k - 1)/9 is the k-th repunit. Then a(n) = n - 1 if and only if n is a long period prime (A006883): n is prime and either n = 2 or the multiplicative order of 10 modulo n is n - 1.

## Assessment

The proof is an elementary argument of about a page. If n is even or a multiple of 5, every repunit is odd, or is 1 mod 5, so too few residues are hit. For gcd(n,10)=1 the residues are purely periodic with period L = min{k : n | R_k}. When 3 does not divide n, L = ord_n(10) <= phi(n), and L = n-1 forces n to be prime. When 3 divides n, R_k ≡ k (mod 3) forces 3 | L, while n-1 ≡ 2 (mod 3). The main case, gcd(n,30)=1, is essentially Israel's comment in the entry, and the cases of multiples of 2, 3 and 5 are quick standard observations, so a competent number theorist would find the whole proof quickly.

*Follows from:* Robert Israel's comment in A335012 itself, a(n) = A084680(n) (the order of 10 mod n) when gcd(n,30)=1, together with ord_n(10) <= phi(n) <= n-1 (equality forcing n prime), and the standard congruence R_k ≡ k (mod 3).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A335012](https://oeis.org/A335012) as [`Math0.Statements.A335012.statement`](../../lean/Math0/Statements/OEIS/A335012.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A335012.lean`](../../lean/Math0/Frontier/OEIS/A335012.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(n) = n-1 if and only if n is a long period prime (A006883), that is, n is a prime and the decimal expansion of 1/n has period n-1. (entry by _Sen-Peng Eu_, May 19 2020)

Referees: OEIS A335012 (Sen-Peng Eu, May 19 2020): the current revision #31 (Mar 12 2026) still lists this as a conjecture, with no %E line recording a resolution. In the same entry, Robert Israel's comment (Jun 25 2020) gives a(n) = A084680(n), the order of 10 mod n, when gcd(n,30) = 1. That implicitly settles the coprime-to-30 case but not n divisible by 2, 3 or 5. Cross-references: A006883 (long period primes, including 2) and A084680; neither mentions a proof. Background only: https://en.wikipedia.org/wiki/Repunit (pigeonhole argument that some repunit is a multiple of n; R_k ≡ k mod 3), https://en.wikipedia.org/wiki/Full_reptend_prime, https://mathworld.wolfram.com/FullReptendPrime.html. Web searches of arXiv, MathOverflow, Math StackExchange, SeqFan and the Google index found no earlier proof or counterexample.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a335012,
  author       = {{math0}},
  title        = {{Repunit residues: a(n) = n - 1 exactly for long period primes}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a335012}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

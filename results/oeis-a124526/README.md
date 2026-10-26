# Hanna's conjecture A124418(n,k) = k! * A124526(n,k) (partitions with k mixed-parity blocks) proved

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A124526  
**Date:** 2026-10-21

## Result

For all n >= 0 and 0 <= k <= floor(n/2): the number A124418(n,k) of set partitions of {1,...,n} with exactly k blocks containing both an odd and an even entry equals k! * A049020(floor(n/2),k) * A049020(floor((n+1)/2),k), where A049020(m,k) = sum_{i=0}^{m} S2(m,i) * C(i,k) and S2 is the Stirling number of the second kind. (The proof does not need the bound k <= floor(n/2); the identity holds for every k.)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A124526](https://oeis.org/A124526) as [`Math0.Statements.A124526.statement`](../../lean/Math0/Statements/OEIS/A124526.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A124526.lean`](../../lean/Math0/Frontier/OEIS/A124526.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A124526: "A124418(n,k) = k!*T(n,k) (conjecture)."; A124418 %F: "Conjecture: T(n,k) = k!*A049020([n/2],k)*A049020([(n+1)/2],k) ... - _Paul D. Hanna_, Nov 08 2006"

Referees: OEIS entries read from the local mirror: A124526, A124418 (Hanna's 2006 conjecture in %F; Heinz's 2013 alternative Maple program uses the equivalent product formula), A049020 (cites East–Gray and Halverson–Jacobson), A244489, A124419 (k=0 column: Bell(floor(n/2))·Bell(ceil(n/2))), A124529, A362495.

Prior proofs, stated in partition-monoid and partition-category language:
- J. East and R. D. Gray, "Diagram monoids and Graham–Houghton graphs: Idempotents and generating sets of ideals", J. Combin. Theory Ser. A 146 (2017) 63–128, doi:10.1016/j.jcta.2016.09.001, arXiv:1404.2359. Proof of Theorem 7.5 and Remark 7.7: |J_r(P_n)| = ρ_{nr}^2·r!, with ρ_{nr} = Σ_j S(n,j)C(j,r). This is the even-n case.
- T. Halverson and T. N. Jacobson, "Set-partition tableaux and representations of diagram algebras", arXiv:1808.08118 (Algebraic Combinatorics 2020), Remark 3.23: the rank-m diagrams in P_k number |W^m_k|^2·m!, where |W^m_k| = A049020(k,m).
- I. Đurđev, I. Dolinka and J. East, "Sandwich semigroups in diagram categories", arXiv:1910.10286 (Internat. J. Algebra Comput. 2021), Proposition 4.11 and Remark 4.12: for the partition category P_{mn}, |D_r| = r!·[Σ_q C(q,r)S(m,q)]·[Σ_q C(q,r)S(n,q)]. Taking m = ⌈n/2⌉ and n = ⌊n/2⌋ gives the full conjecture.

Checked and not relevant: Yaqubi–Mirzavaziri arXiv:2608.30097; Ehrenborg–Hedmark–Hettle (JIS 2017, odd/even block sizes); Shattuck arXiv:1401.6588.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a124526,
  author       = {{math0}},
  title        = {{Hanna's conjecture A124418(n,k) = k! * A124526(n,k) (partitions with k mixed-parity blocks) proved}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a124526}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```

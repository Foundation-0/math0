# Where Foundation0 can make progress in mathematics

A survey made on 18 October 2026 by an AI research agent for Foundation0's
[deep-fields scouting](https://github.com/Foundation-0/f0/tree/claude/sleepy-pasteur-k5knht/deep-fields). The full
report, with every source, is
[deep-fields/scouting/mathematics.md](https://github.com/Foundation-0/f0/tree/claude/sleepy-pasteur-k5knht/deep-fields/scouting/mathematics.md).

- The codetables.de counts were re-checked against the live tables the same day ([data](data/codetables/)).
- Other figures are leads to re-check, not facts of record.
- Areas that become projects get their own repository.

## The main lesson: the famous long tails are taken

Between July and October 2026, people working with AI agents swept the well-known record tables, often within weeks.
A table being public with gaps no longer means it is overlooked. The quiet places are:

- tables where checking a result needs a specialised checker, such as minimum distance over GF(q) or quantum code
  distance;
- the upper-bound and proof side of tables, as opposed to new constructions;
- open-problem lists buried in handbooks and surveys;
- conjectures left in OEIS entries.

The last of these is the "neglected frontier" track already under way in math0 (branch
`claude/math-capabilities-showcase-961iya`).

| Crowded now | Evidence |
|---|---|
| Friedman's Packing Center | 7 or more finders on one page in 2026 |
| Degree/diameter table | About 15 new contributors, Jul–Oct 2026 |
| Brouwer's constant-weight codes | About 12 contributors, Aug–Oct 2026; CPro1 and Echols papers |
| Kéri covering codes | 83 improvements in Aug 2026, the first since 2011 |
| Sorting networks | Five improvements on 13 Oct 2026 |
| Classical Ramsey numbers | AlphaEvolve; an integer-programming paper with 25 bounds |
| Cages, kissing numbers | Several 2025–26 papers |
| Erdős problems | A DeepMind proof agent; formal-conjectures |
| Busy Beaver BB(6) | An active community |
| Covering designs, covering arrays | Frozen or behind a sign-in; CPro1 failed on both |

## 1. Linear codes over GF(3)–GF(9), both bounds

**Open question.** 80,652 entries in the non-binary fields of [codetables.de](https://www.codetables.de/BKLC/index.html)
have a lower bound below the upper bound. 19,318 of them are marked "constructions missing"
([census, 18 Oct 2026](data/codetables/)). In a sample of 210 entries, 77% were last changed in 2001–2009. AI work
has gone to the binary table.

**Fit.** Exact search plus exact checking, the pattern of Foundation0's GF(2) circuit work.

**Checking.** A generator matrix, whose minimum distance anyone can recompute; or an exact rational LP dual for an
upper bound. Submissions go to Markus Grassl (codes@codetables.de), who is active.

**First step.** An open-source minimum-distance checker over GF(q) (Brouwer–Zimmermann), validated against the
generator matrices stored on the table's pages. Then search outside Grassl's own quasi-cyclic index-2 sweep:
quasi-twisted codes of index 3–4, constacyclic shifts, and one-column extensions of record codes.

**Caution.**
- Many gaps come from weak upper bounds. For GF(7) the median gap is 3 for n ≤ 50 but 9 for n > 50, where Grassl
  calls the upper bounds "rather weak". So the number of lower bounds that can actually be improved is smaller than
  80,652.
- Grassl's own sweep may get there first. Re-run the census to see which entries move.

## 2. OEIS "Empirical" recurrences by R. H. Hardin

**Open question.** About 16,180 entries give recurrences found by computer from counting arrays under local rules,
mostly unproved ([search](https://oeis.org/search?q=Empirical+author%3AHardin)). Only 16 mention "proved".

**Fit.** For a fixed width, a transfer matrix proves them mechanically. This is a corner of the OEIS frontier that
can be swept systematically.

**Checking.** A transfer matrix T with start and end vectors. If T has dimension D, a claimed recurrence of order r
that holds on the first D + r terms holds for every term. A small program can check this, and so can Lean.

**Caution.** The OEIS's AI policy, approved 29 Aug 2026, **bans bulk or serial automated submissions without prior
permission** ([policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions)). This applies to every OEIS track in
math0. Publish proofs here or on Zenodo, and ask the editors before submitting anything in bulk.

## 3. Open existence questions in combinatorial designs

**Open question.**
- 2,773 open cases of circulant weighing matrices with n ≤ 1000 in Gordon's dataset v1.3
  ([page](https://dmgordon.org/circulant-weighing-matrices/), [Zenodo](https://doi.org/10.5281/zenodo.10775927)).
  Of these, 270 have n ≤ 300.
- The Handbook design types that CPro1 never tried ([CPro1](https://github.com/Constructive-Codes/CPro1)).

**Checking.** The first row of the matrix, or the design itself, checked instantly.

**First step.** Exclude the 8 cases proved impossible in Aug 2026 ([2608.18468](https://arxiv.org/abs/2608.18468)).
Then add circulant weighing matrices as a CPro1 design type, using the open list as instances.

## 4. Small Ramsey numbers outside the classical table

**Open question.** Radziszowski's survey, revision #18 of 24 Apr 2026
([pdf](https://cs.rit.edu/~spr/ElJC/ejcram18.pdf)), has gap entries for K_k − e, books, wheels, cycles, C4 versus
stars, and 3-colour lower bounds. AI attacks so far targeted only classical R(s,t) and R(3,n).

**Checking.** A colouring, with an independent check for forbidden subgraphs.

**Odds.** Higher prestige, lower chance of a result within days.

## 5. Qubit stabilizer codes

29,459 of 33,152 entries are open for n ≤ 256 ([table](https://www.codetables.de/QECC/index.html)). This is also
area 4 of physics0's survey; coordinate with it there.

## 6. Graffiti and Written-on-the-Wall conjectures (lower priority)

- About 1,000 conjectures; several refuted in 2025–26.
- 57 of the Written-on-the-Wall II conjectures are now in formal-conjectures.
- No maintained list of which ones remain open.

## Practical advice

- Contact maintainers before submitting in bulk: Grassl, Gordon, Radziszowski, and the OEIS editors.
- Build the exact checker and the certificate format first.
- Move fast. The degree/diameter table went from quiet to about 15 contributors in three months.
- One unconfirmed lead: the [subspace-codes table](http://subspacecodes.uni-bayreuth.de/news/) has posted no news
  since 2017.

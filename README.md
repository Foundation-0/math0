# math0

Foundation-0's home for machine-checkable mathematics. As of 14 Nov 2026 ([owner directive](https://github.com/aska-digital/corpus/blob/main/principles/directives.md), [PR #122](https://github.com/aska-digital/corpus/pull/122)), this repository is the consolidation point for three strands that are landing here:

| Strand | In this repo |
|---|---|
| **Integer multiplication** | **Incoming.** Audits and certificates will live here; background and links stay in [f0](https://github.com/Foundation-0/f0) and [fdn0.org/research/integer-multiplication/](https://fdn0.org/research/integer-multiplication/). |
| **CrocSwap math** | **Incoming.** No CrocSwap-specific tree in the repo yet. |
| **Base math** | **Incoming.** Shared numeric and proof scaffolding will land here; nothing dedicated is checked in yet. |

What is here today:

- **[AREAS.md](AREAS.md)** — survey of where Foundation-0 can make progress in mathematics.
- **[data/codetables/](data/codetables/)** — census snapshot and script for open entries on [codetables.de](data/codetables/README.md) (see that README for files and how to re-run the census).
- **[studies/ROUND7_PURE_MATH_PROVENANCE.md](studies/ROUND7_PURE_MATH_PROVENANCE.md)** — Wave 2 Round 7 independently verified (`AUDIT-069R`, `AUDIT-070R`, `AUDIT-071R`) zero-float exact rational complexity, SAT-forensics, and benchmark-identifiability studies (`191/191` `100.0%` `aletheia v1.4.0` R5 mutation killed).
- **[studies/ROUND5_PURE_MATH_PROVENANCE.md](studies/ROUND5_PURE_MATH_PROVENANCE.md)** — two independently verified, zero-float pure-stdlib mathematical studies (`AUDIT-058R`, `AUDIT-060`, `49/49` + `49/49` R5 mutation-killed): CAMAIL SSM/DeltaNet/RKHS Schur & lattice-quantization exact tomography, and alphaXiv formal-math (Feige Lean 4 census, sumset carry-automaton Collatz–Wielandt repair & 462-set base-12 classification, HOPE Hilbert Schur obstruction & finite $H_2..H_8$, and $S_4/A_5$/FPRM/QRR recurrence bridges).

Other mathematics spin-outs are listed under [Projects](#projects) below. Work is in the open: results should be backed by something a machine can re-check, with credit for people and models.

## Spin-offs

A strand that outgrows a single tree gets its own repository. The new repo branches from math0 (or from the commit where the strand lived) and links back here for history and shared rules.

[physics0](https://github.com/Foundation-0/physics0) is the existing pattern: physics work started consolidated, then spun into focused repos (for example fractals and gravity) while physics0 remains the hub.

## Projects

| Project | Question | Status |
|---|---|---|
| [incentre-lattices](https://github.com/Foundation-0/incentre-lattices) | Where does one rule (join the incentres of a square's four triangles) lead, in any number of dimensions? | Preprint on Zenodo; not peer reviewed. |
| Integer multiplication (consolidating here; see table above) | Which claims in the race to lower the integer multiplication exponent hold up, and how far has each been checked? | Tracker feed paused since 11 Oct 2026; vault material incoming in math0. |
| [formal-claims-audit](https://github.com/Foundation-0/formal-claims-audit) | Does the formal (Lean) statement of an AI-claimed result say what its paper claims? | Not started. |
| [covering-min-modulus](https://github.com/Foundation-0/covering-min-modulus) | Does the record covering system with minimum modulus 42 check out, and is there one with 43? | Not started. |
| [gfq-codes](https://github.com/Foundation-0/gfq-codes) | Which open entries in the tables of linear codes over GF(3) to GF(9) can be improved? | Research underway. First claimed result: an exact Delsarte certificate excludes a linear [55,10,40] code over GF(7), with two independent arithmetic checks and a written proof. Human review is pending. |
| [rigid-realizations](https://github.com/Foundation-0/rigid-realizations) (with [physics0](https://github.com/Foundation-0/physics0)) | Can all 880 complex realizations of the 10-vertex rigid framework be real? | Claimed in [rigid-realizations PR #14](https://github.com/Foundation-0/rigid-realizations/pull/14) (`af32f535`), pending independent verification: L880 all 880 real (r_2(10) = c_2(10) = 880; planar asymptotic lower bound 440^(1/7) ≈ 2.385811^n); L880 at Bartzos et al. lengths ≥ 868; G160 ≥ 132; L136 not certified (spec targets r_2 = 136, all real, at the repo's rational lengths); Prism_6 and L344 certificates not yet in repo; r_2(12) ≥ 4,128 (L344 glued with Prism_6 on an L344 triangle) conditional on a Prism_6 certificate built on an L344 face. |

## How results are checked in every project

- **Certificates anyone can re-check.** A generator matrix, a list of congruences, a proof file. Where possible, two checkers that share no code.
- **Formal proofs are read, not only compiled.** A proof checker confirms a proof proves its formal statement. Someone still compares that statement with the claim in words.
- **Plain status labels.** Each result says whether it is claimed, a preprint, peer reviewed, replicated or formally verified, and who has (or has not) reviewed it.
- **Maintainers first.** Before submitting results to a table or a problem list in bulk, ask its maintainer.
- **Credit.** Prior work and table maintainers are cited where they are used. Each project records which AI model did what.

### Re-running the codetables census

From `data/codetables/`:

```bash
python census.py
```

Use `python census.py --csv entries.csv` to export the full entry list locally. Details are in [data/codetables/README.md](data/codetables/README.md).

## Taking part

AI agents start with Foundation0's [guide for agents](https://github.com/Foundation-0/f0/blob/main/JOIN.md), then a project's AGENTS.md and its open issues. People can say hello on the [forum](https://github.com/Foundation-0/f0/discussions).

Directed by Ahraz Arifuddin

Researched and verified by different model families across Gemini, Claude, Grok, OpenAI, and Muse
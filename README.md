# math0

The hub for Foundation0's mathematics work: in the open, with every result backed by something a machine can check, and credited to the people and the AI models that did the work.

This repository directs the effort. It keeps:

- the list of projects;
- the survey of where to go next, [AREAS.md](AREAS.md);
- shared data, such as the census of open entries on codetables.de in [data/codetables/](data/codetables/);
- the shared rules for checking results.

A study small enough to be a single note can start here. Once it grows beyond that (code, certificates, data), it gets its own repository and is listed below.

## Projects

| Project | Question | Status |
|---|---|---|
| [incentre-lattices](https://github.com/Foundation-0/incentre-lattices) | Where does one rule (join the incentres of a square's four triangles) lead, in any number of dimensions? | Preprint on Zenodo; not peer reviewed. |
| [Integer multiplication race](https://fdn0.org/research/integer-multiplication/) (tracked in [f0](https://github.com/Foundation-0/f0)) | Which claims in the race to lower the integer multiplication exponent hold up, and how far has each been checked? | The tracker's feed has been paused since 11 Oct 2026. |
| [formal-claims-audit](https://github.com/Foundation-0/formal-claims-audit) | Does the formal (Lean) statement of an AI-claimed result say what its paper claims? | Not started. |
| [covering-min-modulus](https://github.com/Foundation-0/covering-min-modulus) | Does the record covering system with minimum modulus 42 check out, and is there one with 43? | Not started. |
| [gfq-codes](https://github.com/Foundation-0/gfq-codes) | Which open entries in the tables of linear codes over GF(3) to GF(9) can be improved? | Not started. |
| [rigid-realizations](https://github.com/Foundation-0/rigid-realizations) (with [physics0](https://github.com/Foundation-0/physics0)) | Can all 880 complex realizations of the 10-vertex rigid framework be real? | Claimed in [rigid-realizations PR #14](https://github.com/Foundation-0/rigid-realizations/pull/14) (`af32f535`), pending independent verification: L880 all 880 real (r_2(10) = c_2(10) = 880; planar asymptotic lower bound 440^(1/7) ≈ 2.385811^n); L880 at Bartzos et al. lengths ≥ 868; G160 ≥ 132; L136 not certified (spec targets r_2 = 136, all real, at the repo's rational lengths); Prism_6 and L344 certificates not yet in repo; r_2(12) ≥ 4,128 (L344 glued with Prism_6 on an L344 triangle) conditional on a Prism_6 certificate built on an L344 face. |

## How results are checked in every project

- **Certificates anyone can re-check.** A generator matrix, a list of congruences, a proof file. Where possible, two
  checkers that share no code.
- **Formal proofs are read, not only compiled.** A proof checker confirms a proof proves its formal statement. Someone
  still compares that statement with the claim in words.
- **Plain status labels.** Each result says whether it is claimed, a preprint, peer reviewed, replicated or formally
  verified, and who has (or has not) reviewed it.
- **Maintainers first.** Before submitting results to a table or a problem list in bulk, ask its maintainer.
- **Credit.** Prior work and table maintainers are cited where they are used. Each project records which AI model did
  what.

## Taking part

AI agents start with Foundation0's [guide for agents](https://github.com/Foundation-0/f0/blob/main/JOIN.md), then a
project's AGENTS.md and its open issues. People can say hello on the
[forum](https://github.com/Foundation-0/f0/discussions).

Directed by Ahraz Arifuddin

Researched and verified by different model families across Gemini, Claude, Grok, OpenAI, and Muse

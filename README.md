# math0

**Mathematics produced by Claude and checked by the Lean kernel.**

math0 is a collection of mathematical results produced by Claude, an AI model developed by
Anthropic. It adds one rule that natural-language manuscripts cannot meet on their own:

> A result is listed here only if a complete Lean 4 proof of it exists, compiled against
> Mathlib, using no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, **and the
> statement it proves was written by someone else.**

The statements come from Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository. It is a
public, independently curated collection of formalized open problems: Erdős problems, Ben Green's
100 open problems, OEIS conjectures, Wikipedia lists, problems from papers and books. math0
imports that repository at a pinned commit. Each math0 proof then states its theorem as *the type
of the upstream declaration* and is checked against it syntactically. A proof therefore cannot
quietly prove an easier statement than the one the problem's curators wrote down.

## Why verification first

Proof-shaped text is cheap to produce and expensive to check, whether a human or a model wrote
it. Large collections of AI-generated manuscripts already have to issue withdrawals when referees
find gaps. math0 treats the kernel-checked proof as the deliverable and the manuscript as
commentary on it. If the Lean proof compiles and the audit passes, the theorem holds; the
manuscript only explains why.

## What every result carries

| Artifact | Where |
|---|---|
| Lean proof of the exact upstream statement | [`lean/Math0/`](lean/Math0) |
| Machine audit (statement match + axiom whitelist) | last line of every Lean file, re-run by CI |
| Classification after adversarial review | [`CONTENTS.md`](CONTENTS.md), [`catalog.json`](catalog.json) |
| Human-readable manuscript (LaTeX + PDF) | `results/<slug>/` |

Results are classified honestly, after independent referees have tried to refute them:

* **New result:** the upstream problem was open, the formal statement is faithful, and the
  proof settles it.
* **First formal proof of a known result:** the mathematics was known, but no machine-checked
  proof of it existed.
* **Independent formal proof:** a Lean proof of an implying statement already exists elsewhere.
  It is listed for completeness, not as a contribution.
* **Misformalization found:** the upstream statement can be settled for a reason unrelated to the
  intended mathematics (a degenerate case, a missing hypothesis). That is not a solution of the
  problem. It is reported so that the statement can be fixed upstream.

## How the audit works

[`lean/Math0/Audit.lean`](lean/Math0/Audit.lean) defines the commands that end every result
file:

```lean
#math0_proves  Math0.Erdos10.erdos_10_grechuk_example Erdos10.erdos_10.variants.grechuk_example
#math0_refutes ...   -- our theorem's type must be exactly `¬ (upstream type)`
#math0_answers ...   -- value questions: upstream `X.answer` replaced by an explicit value
```

Each command fails the build unless:

1. the type of our theorem is syntactically identical to the upstream statement, or to its
   negation (up to metadata only, with no unfolding); and
2. `Lean.collectAxioms` reports nothing beyond `propext`, `Classical.choice` and `Quot.sound`.
   This rejects `sorry`, `native_decide` (`Lean.ofReduceBool`) and any custom axiom.

CI ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)) rebuilds everything from a clean
checkout. Locally:

```sh
scripts/verify.sh        # needs elan; fetches the Mathlib cache and builds every result
```

## How the results were produced

All mathematics and Lean code here was produced by Claude running in Claude Code, orchestrated as
multi-agent workflows:

1. **Triage.** Every one of the 2,787 open or unproven research statements in formal-conjectures
   was read and scored for tractability. Statements that can be "solved" vacuously (for example
   by restating the question as its own answer) were flagged and excluded.
2. **Prove.** For each selected statement, a solver agent works out the mathematics and then
   iterates against the Lean compiler until the proof is complete and the audit passes.
3. **Referee.** Independent agents try to refute every claimed proof. They recompile it, check
   for forbidden constructs and modified dependencies, judge whether the formal statement is
   faithful to the intended problem, and, for open problems, search the literature for prior
   resolutions.

Human review of the manuscripts is welcome. Please open an issue for any error, including a
misclassification.

## Layout

```
README.md          this file
CONTENTS.md        catalogue of results (generated from catalog.json)
catalog.json       machine-readable list of every claim math0 makes
history.md         release log
results/<slug>/    per-result README, manuscript (paper.tex, paper.pdf), citation
lean/              Lake project: Math0/Audit.lean, Math0/<Source>/<Result>.lean
scripts/           verify.sh, gen_contents.py, build_papers.sh
```

## License

Lean code and scripts: Apache-2.0. Manuscripts and documentation: CC-BY-4.0. Statements imported
from formal-conjectures remain under their original licenses.

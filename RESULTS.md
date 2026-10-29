# math0 results

**Mathematics produced by Claude and checked by the Lean kernel.** This is one of the projects listed in
math0's [README](README.md).

math0 is a collection of mathematical results produced by Claude, an AI model developed by
Anthropic. It adds one rule that natural-language manuscripts cannot meet on their own:

> A result is listed here only if a complete Lean 4 proof of it exists, compiled against
> Mathlib, using no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, **and the
> statement it proves either was written by someone else, or was formalized by math0 and frozen
> before the proof, and is shown next to its source text.**

Two kinds of statement are used (see [Two tracks](#two-tracks)):

* **Written by someone else** (the formal-conjectures track). These come from Google DeepMind's
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository, a public,
  independently curated collection of formalized open problems: Erdős problems, Ben Green's 100
  open problems, OEIS conjectures, Wikipedia lists, problems from papers and books. math0 imports
  that repository at a pinned commit. Each math0 proof states its theorem as *the type of the
  upstream declaration* and is checked against it syntactically, so it cannot quietly prove an
  easier statement than the one the problem's curators wrote down.
* **Formalized by math0** (the frontier track). Here math0 writes the statement itself, from a
  conjecture in an OEIS entry. Its definitions are checked by the kernel against the OEIS data,
  but its fidelity to the OEIS text rests on a separate reviewing agent and on you. So every
  result page quotes the OEIS conjecture next to the formal statement, each statement is frozen by
  hash before the proof, and CI rejects any change to a frozen statement.

## Highlights

<!-- HIGHLIGHTS:START -->
**153 verified results.** 74 new results, 55 first formal proofs of known results, 18 independent formal proofs, 6 misformalization reports. Full list: [CONTENTS.md](CONTENTS.md).

New results: OEIS conjectures settled, each checked by the Lean kernel, with no earlier proof or counterexample found by an independent novelty referee. An independent assessor judged the difficulty of each of these: 0 substantial and 68 routine (a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search); 6 not yet assessed. Most of these conjectures had stayed open for lack of attention, not because they were hard; each result page gives the assessor's reasons.

* [3 × 3 lower triangles with neighbours differing by at most two: a(n) = 1047 n - 1459 for n > 2 (A195249)](results/oeis-a195249/README.md) ([paper](results/oeis-a195249/paper.pdf))
* [3^(3^18) + 2 is divisible by 31^2, so Hilliard's squarefree conjecture (A083020) fails](results/oeis-a083020/README.md) ([paper](results/oeis-a083020/paper.pdf))
* [A090905: every row ends at twice the largest prime of the previous row (Murthy's conjecture proved)](results/oeis-a090905/README.md) ([paper](results/oeis-a090905/paper.pdf))
* [A106505: common sides of A/2A primitive triangles are periodic mod 8, so a(n+5) = a(n) + 8](results/oeis-a106505/README.md) ([paper](results/oeis-a106505/paper.pdf))
* [A123710: the rows of inv(floor(n/k)) with four nonzero entries are 6 and the proper prime powers](results/oeis-a123710/README.md)
* [A126127: Israel's conjectured bivariate g.f. of the inverse square of A061554 holds](results/oeis-a126127/README.md)
* [A127752 mod 2 is the first Feigenbaum symbolic sequence A035263](results/oeis-a127752/README.md) ([paper](results/oeis-a127752/paper.pdf))
* [A144637: (1/18) 6^n a(n)/n! is odd iff n = 2^k with k >= 1](results/oeis-a144637/README.md)
* [A172164: the second differences of the Theodorus-spiral turns are always 18, 19, 20 or 21](results/oeis-a172164/README.md) ([paper](results/oeis-a172164/paper.pdf))
* [A178295: collinear 4-subsets of {0,...,4}^n number 9^n/2 + 3*7^n/2 - 2*5^n (Mathar's conjecture, all three formulas)](results/oeis-a178295/README.md) ([paper](results/oeis-a178295/paper.pdf))
* [A223395: walks on the 4 x 4 grid graph satisfy Hardin's recurrence, Barker's g.f. and closed form](results/oeis-a223395/README.md) ([paper](results/oeis-a223395/paper.pdf))
* [A249151(k) = k exactly when k + 1 is prime (Karttunen's conjecture, A249434/A249151)](results/oeis-a249434/README.md) ([paper](results/oeis-a249434/paper.pdf))
* [A275815: Jones's conjecture a(n) = 8(n-2)^2 for n >= 6 holds](results/oeis-a275815/README.md)
* [A308107: Barker's rational generating function and order-15 recurrence for the sum of smallest sides of scalene integer triangles](results/oeis-a308107/README.md) ([paper](results/oeis-a308107/paper.pdf))
* [A308121: for odd n > 1, row 2n is row n with its halves swapped](results/oeis-a308121/README.md) ([paper](results/oeis-a308121/paper.pdf))
* [A332010: the average first letter of one-descent derangements has denominator 2^(n-2)](results/oeis-a332010/README.md) ([paper](results/oeis-a332010/paper.pdf))
* [A334595: a(n) = 1 iff n is a power of two, and the records occur exactly at 1 and 2^k + 1](results/oeis-a334595/README.md) ([paper](results/oeis-a334595/paper.pdf))
* [A338885: the smallest number in row 655 is 104, not A228286(655) = 115](results/oeis-a338885/README.md) ([paper](results/oeis-a338885/paper.pdf))
* [A342645: diagonals of the eventual Mahonian-column polynomials](results/oeis-a342645/README.md)
* [A348484: no two squares two steps apart; the conjectured formula holds](results/oeis-a348484/README.md) ([paper](results/oeis-a348484/paper.pdf))
* [A355339: the central even run of the knight-move triangle has length 1 iff n = 2^m - 2](results/oeis-a355339/README.md) ([paper](results/oeis-a355339/paper.pdf))
* [A363609: a(k^3) = 6k(k+2), the cube is the optimal polycube of k^3 dice](results/oeis-a363609/README.md) ([paper](results/oeis-a363609/paper.pdf))
* [A386538: moving the circle's center off the grid enlarges the max lattice polygon (counterexample at n = 7)](results/oeis-a386538/README.md) ([paper](results/oeis-a386538/paper.pdf))
* [Alexandersson's recurrence for the row polynomials of A395454 holds (rows counted from 1)](results/oeis-a395454/README.md) ([paper](results/oeis-a395454/paper.pdf))
* [Bar tilings of the smallest-perimeter rectangle: a(n+1) = 4 a(n) for odd n >= 3 (A394981)](results/oeis-a394981/README.md) ([paper](results/oeis-a394981/paper.pdf))
* [Barker's order-20 recurrence for the lines through an 8 x n grid holds](results/oeis-a160848/README.md) ([paper](results/oeis-a160848/paper.pdf))
* [Columns 1 and 2 of the theta-series triangle A355360 are P(x)^3 and 2P(x)^6](results/oeis-a355360/README.md)
* [Diagonal sums of A368846 equal A229580 (Luschny's conjecture)](results/oeis-a368846/README.md)
* [Domino towers of height 2 and of height n-1, n-2, n-3 (A333650): all four Kagey/Luschny conjectures](results/oeis-a333650/README.md) ([paper](results/oeis-a333650/paper.pdf))
* [Even and odd legs with odd prime factors ≡ 3 (mod 4): a(n)/n → π (A354571, A354570)](results/oeis-a354571/README.md) ([paper](results/oeis-a354571/paper.pdf))
* [Internal n-gons in a regular n-gon: triple points occur only for n = 3, 4, 6, and otherwise there are n k^2 + 1 regions (Shannon's A357216 conjecture)](results/oeis-a357216/README.md) ([paper](results/oeis-a357216/paper.pdf))
* [Irwin's nested sums give column 0 of the triangle A132615 (A132616)](results/oeis-a132616/README.md)
* [Kagey's conjecture for A278212: a(n) = floor(A275815(n)/2), via exact bishop and queen maxima from flow (LP-dual) certificates](results/oeis-a278212/README.md) ([paper](results/oeis-a278212/paper.pdf))
* [Kagey's order-10 recurrence for no-leaf subgraphs of the 5 × n grid holds](results/oeis-a320099/README.md)
* [Kurkov's recursion for the row polynomials of convolution triangles holds](results/oeis-a357583/README.md)
* [Kurkov's rook-tour conjecture for A001040: 2·n!·a(n) counts opposite-line Hamiltonian paths of K_n □ K_2](results/oeis-a001040/README.md)
* [Mathar's order-6 recurrence for A121750 (even-length columns in deco polyominoes) holds for all n >= 7](results/oeis-a121750/README.md) ([paper](results/oeis-a121750/paper.pdf))
* [O'Sullivan's Gaussian-polynomial / Chebyshev representation conjecture (A267486), proved](results/oeis-a267486/README.md)
* [OEIS A350900: Schulte's gcd-ratio double sum is a Dirichlet convolution](results/oeis-a350900/README.md) ([paper](results/oeis-a350900/paper.pdf))
* [Prime-Minesweeper on the A060734 array: a(n) < 6, and a(n) = 5 only at n = 6](results/oeis-a326407/README.md) ([paper](results/oeis-a326407/paper.pdf))
* [Schulte's conjectures on A281000, T(n,k) = C(2n+1,2k+1)·Cat(n-k): antidiagonal sums and matrix inverse](results/oeis-a281000/README.md) ([paper](results/oeis-a281000/paper.pdf))
* [Signed A350557 is the matrix inverse of A350512, proved](results/oeis-a350557/README.md)
* [Stephan's conjectured g.f. for A242396 is false (first failure at n = 97)](results/oeis-a242396/README.md) ([paper](results/oeis-a242396/paper.pdf))
* [The Golomb-row triangle A113676 and Levine's sequence A014644](results/oeis-a113676/README.md) ([paper](results/oeis-a113676/paper.pdf))
* [The generating function of A022445 (closed self-avoiding walks in the strip {0,1,2} x Z)](results/oeis-a022445/README.md)
* [The inverse of the 1/Catalan band triangle (A127767) has integer entries](results/oeis-a127767/README.md) ([paper](results/oeis-a127767/paper.pdf))
* [The inverse of the triangle 1/n! [k ≤ n ≤ 2k] is an integer triangle](results/oeis-a127755/README.md)
* [The least number of inequivalent cells of a (6k+5)-iamond is 3(k+1)](results/oeis-a369366/README.md) ([paper](results/oeis-a369366/paper.pdf))
* [The row sums of the generalized Deutsch triangle A188474 are A137398](results/oeis-a188474/README.md)
* [The row-LCM of denominators of the cube of the mean matrix is n · lcm(1..n)²](results/oeis-a119936/README.md) ([paper](results/oeis-a119936/paper.pdf))
* [The subword complexity polynomial S(n,x) has leading coefficient n(n+1)/2 (A341761, Guo's conjecture)](results/oeis-a341761/README.md) ([paper](results/oeis-a341761/paper.pdf))
* [The toothpick spiral around n hexagonal cells (A182617): a(n) = 2n + ceil(sqrt(12n - 3))](results/oeis-a182617/README.md)
* [The triple-gcd Pascal triangle A129455: T(n,k) is an integer, divisible by C(n,k), and T(n,k)/C(n,k) is a sixth power](results/oeis-a129455/README.md) ([paper](results/oeis-a129455/paper.pdf))
* [A116184: Adamchuk's conjectures on 37^3 dividing the numerator of sum_{k=1}^{36} 1/k^n](results/oeis-a116184/README.md) ([paper](results/oeis-a116184/paper.pdf))
* [A262957: Israel's b(n), c(n) are coprime integers and a(n) = b(n)](results/oeis-a262957/README.md) ([paper](results/oeis-a262957/paper.pdf))
* [A356360: the continued-fraction denominators are 1 or prime](results/oeis-a356360/README.md) ([paper](results/oeis-a356360/paper.pdf))
* [A375522: S2(n) - S1(n) = 1 fails at n = 42 (the difference is 5)](results/oeis-a375522/README.md) ([paper](results/oeis-a375522/paper.pdf))
* [Convergents of [1; 1/2, 1/3, ..., 1/n]: numerator + denominator = 2^(v2(n!) + v2((n+1)!)) (A092054)](results/oeis-a092054/README.md) ([paper](results/oeis-a092054/paper.pdf))
* [Imaginary parts of the convergents of [1+i; 1+i, 1+i, ...] are A317974(n+1)/A138573(n)](results/oeis-a093726/README.md) ([paper](results/oeis-a093726/paper.pdf))
* [OEIS A362086: every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-3)))) except 9 is 1 or a prime](results/oeis-a362086/README.md) ([paper](results/oeis-a362086/paper.pdf))
* [OEIS A363482: apart from 49, every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-5)))) is 1 or a prime](results/oeis-a363482/README.md) ([paper](results/oeis-a363482/paper.pdf))
* [Repunit residues: a(n) = n - 1 exactly for long period primes](results/oeis-a335012/README.md) ([paper](results/oeis-a335012/paper.pdf))
* [Zeros of a(3n) for the signed Stern sequence A005590 are exactly the fibbinary numbers](results/oeis-a005590/README.md) ([paper](results/oeis-a005590/paper.pdf))
* [A326602: a(n) is odd iff n is a square](results/oeis-a326602/README.md) ([paper](results/oeis-a326602/paper.pdf))
* [A351743: from n = 139 the sequence is affine in 42-blocks, which proves Sycamore's, Sigrist's and the A355149 conjectures](results/oeis-a351743/README.md) ([paper](results/oeis-a351743/paper.pdf))
* [A386655 modulo 6 is eventually periodic with pattern [1, 0, 3, 0, 3, 2]](results/oeis-a386655/README.md) ([paper](results/oeis-a386655/paper.pdf))
* [Every n not divisible by 5 has a multiple with only prime digits (A342992)](results/oeis-a342992/README.md) ([paper](results/oeis-a342992/paper.pdf))
* [Lang's conjecture a(n) = A250400(n+1)/(n+1) for A294512 fails at n = 164](results/oeis-a294512/README.md) ([paper](results/oeis-a294512/paper.pdf))
* [Odd descending-by-2 multiples exist exactly when 125 does not divide 2n+1 (A062887)](results/oeis-a062887/README.md) ([paper](results/oeis-a062887/paper.pdf))
* [Odd terms of A323695 occur only at n = k(k+2)](results/oeis-a323695/README.md) ([paper](results/oeis-a323695/paper.pdf))
* [The 1089-trick map has two 9-digit fixed points (A393794 uniqueness conjecture is false)](results/oeis-a393794/README.md) ([paper](results/oeis-a393794/paper.pdf))
* [The only fixed points of reverse(x) - maxdigit(x) are 0 and 89](results/oeis-a097154/README.md) ([paper](results/oeis-a097154/paper.pdf))
* [There are no 5-Rotation Cycle Primes (A086004, Conjecture 2)](results/oeis-a086004/README.md) ([paper](results/oeis-a086004/paper.pdf))
* [Yanev's identity for A073642 (sum of the positions of the 1-bits)](results/oeis-a073642/README.md) ([paper](results/oeis-a073642/paper.pdf))
<!-- HIGHLIGHTS:END -->

## Two tracks

1. **Third-party statements.** Proofs of statements in formal-conjectures, checked against the
   upstream declaration with no possibility of restating the goal.
2. **The neglected frontier.** The curated lists (Erdős problems, Green's list, formal-conjectures)
   are now swept continuously by several groups and automated reviewers. The referees in our first
   track kept finding that "open" items had been settled weeks earlier. So math0 also mines
   material almost nobody revisits: conjectures that OEIS contributors left in sequence entries,
   in the "unglamorous" corners of number theory and geometry. These include patterns in series,
   awkward fractions (Egyptian fractions, odd continued fractions, harmonic-number denominators)
   and irregular shapes (lattice polygons, integer triangles, grid configurations).
   Each such statement is formalized by one agent, with its definitions checked by the kernel
   against the OEIS data. A second agent then reviews it for fidelity to the OEIS text and freezes
   it (by hash) before a third agent attempts a proof or counterexample, which is checked with
   `#math0_settles`.

   Frozen statements are listed in
   [`lean/Math0/Statements/FROZEN.sha256`](lean/Math0/Statements/FROZEN.sha256), and CI enforces
   three rules. Each file must still match its hash. The list is append-only: a frozen line can
   never be edited or removed, even together with its statement. And from 26 October 2026, each
   new statement is committed, in its own commit, before the proof that settles it, so the order
   is visible in the git history and the statement can be reviewed on its own. The statements
   frozen before that date were committed together with their proofs; they are listed in
   [`FROZEN_WITH_PROOF.txt`](lean/Math0/Statements/FROZEN_WITH_PROOF.txt), and for them the
   freeze order is recorded only in the pipeline's logs. Statements that are frozen but not yet
   settled are compiled by CI too, through
   [`lean/Math0/Statements.lean`](lean/Math0/Statements.lean).

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

* **New result (conjecture settled; no earlier resolution found):** the conjecture was stated as
  open in its source, the formal statement is faithful, the proof settles it, and an independent
  novelty referee found no earlier proof or counterexample. This says nothing about difficulty:
  many of the OEIS conjectures settled here yield to short, elementary arguments, and some
  counterexamples refute the conjecture only as literally stated. The result pages say so where
  it applies.
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
#math0_refutes_every_answer ...  -- misformalized value questions: false for every possible answer
#math0_settles ...   -- frontier track: proves or refutes a frozen math0 statement (a sorry-free Prop)
```

Each command fails the build unless:

1. the type of our theorem is syntactically identical to the upstream statement, or to its
   negation (up to metadata only, with no unfolding); and
2. `Lean.collectAxioms` reports nothing beyond `propext`, `Classical.choice` and `Quot.sound`.
   This rejects `sorry`, `native_decide` (`Lean.ofReduceBool`) and any custom axiom.

CI ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)) runs on every push and pull
request. It uses no build cache other than Mathlib's prebuilt oleans, so every math0 module (and
every formal-conjectures module it imports) is elaborated and checked by the kernel again, never
replayed. It then checks that exactly one statement check ran per catalogue entry, checks the
frozen statements ([`scripts/check_freeze.py`](scripts/check_freeze.py)), and runs the audit's
own tests in [`tests/audit/`](tests/audit): files that the audit must reject (a `sorry`,
`native_decide`, a custom axiom, a weaker or merely definitionally equal statement, a statement
hiding a `sorry`, the wrong polarity) and a file it must accept. A weekly workflow
([`kernel-replay.yml`](.github/workflows/kernel-replay.yml)) also replays every declaration of
every math0 module through the kernel with `leanchecker`, and runs the independent
[axiom-audit](https://github.com/leanprover-community/axiom-audit). Locally:

```sh
scripts/verify.sh --clean   # needs elan; fetches the Mathlib cache and rebuilds every result
scripts/test_audit.sh       # the audit's own tests
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
README.md          the math0 hub
RESULTS.md         this file
CONTENTS.md        catalogue of results (generated from catalog.json)
catalog.json       machine-readable list of every claim math0 makes
history.md         release log
results/<slug>/    per-result README, manuscript (paper.tex, paper.pdf), citation
lean/              Lake project: Math0/Audit.lean, Math0/<Source>/<Result>.lean
scripts/           verify.sh, test_audit.sh, check_freeze.py, gen_contents.py, gen_root.py
tests/audit/       files the audit must reject (fail/) or accept (pass/)
```

## License

Lean code and scripts: Apache-2.0. Manuscripts and documentation: CC-BY-4.0. Statements imported
from formal-conjectures remain under their original licenses.

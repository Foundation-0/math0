# Provenance and status: the "carbon" drops of 13 November 2026

**Status: claimed, pending review.** No maintainer of math0 or of CrocSwap/integer-mult-bounds has reviewed these
packages. None claims a new kappa, and none has been submitted upstream.

The Drive folder `carbon` (id `1n5ARa7UlHNqDISekPh_gdiOet2xLjjmH`, created 2026-11-13T19:48:32Z) holds three
subfolders, `1`, `2` and `3`, each a self-contained research package for
[CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds). They were written by AI agents
working for Ahraz Arifuddin (Aska Digital), per the Drive owner and the packages' own attribution. Here they are
renamed by subject. Every file is byte-identical to Drive except one renamed PDF.

| Here | Drive | What it is |
|---|---|---|
| [`cubic-general-frames-and-2adic-obstruction/`](cubic-general-frames-and-2adic-obstruction/) | `1/research/cubic-general-frames-and-2adic-obstruction/` and `1/Cubic Repair Frontier Bounds.pdf` | 3-query dyadic cubic repairs: a 2-adic obstruction for monic frames at 82 of 99 odd-S arities in 3 <= r <= 200, and 20 new general-frame witnesses. Python verifier, independent checker, JSON certificates, a C++20 search, and a 5-page paper (PDF only). |
| [`base-math-convergence/`](base-math-convergence/) | `2/integer_mult_base_math_convergence_bundle/` and `2/base_mathematics_power_sum_farkas_conservation_explorer.html` | `research/conservation-quotient-bounds`: a cut-rank checker, a closed-form decoder, power-sum enclosures and a Farkas ceiling. Python and C11 checkers, a Lean module, tests, and a standalone HTML explorer (inline script only, no external loads). |
| [`frontier7000-spread-scan/`](frontier7000-spread-scan/) | `3/frontier7000_spread_scan_bundle/` | `research/frontier7000-spread-scan`: a mean-preserving-spread audit of the #7000 call histograms. Python and C11 checkers, a Lean module, tests. |

The second and third keep their bundle layout (`SHA256SUMS` beside `research/<package>/`) so their commands run as
written from the bundle folder.

## Source files and digests

| File | Drive id | Drive modified (UTC) | SHA-256 |
|---|---|---|---|
| `1/.../CERTIFICATES.json` | `1Ttg1S3OMOG9ds59RRag-UJPTzIqeJ5tm` | 2026-11-13T13:45:02Z | `697498fee5a1492d3dd86b3e27a6a434f75434d5a5f167081cad2f0c43e4c725` (matches `VERIFY.json`) |
| `1/Cubic Repair Frontier Bounds.pdf`, here `cubic-repair-frontier-bounds.pdf` | `1UUNEX1_xaIJJV9xk7fKnNIuOO2fqLMAs` | 2026-11-13T19:39:55Z | `17e78eef2d8b089593d8d831a5a7358f3ba72d891078807ebbb6f34bf2a6d964` |
| `2/.../SHA256SUMS` | `1V9vRpqKjGPMUnbBMJP_kbJRb9ovS3VbQ` | 2026-11-13T18:01:38Z | covers all 11 package files; `sha256sum -c` passes |
| `2/base_mathematics_power_sum_farkas_conservation_explorer.html` | `1Sftz6jVNPeGC78vvMHZP0xarQfh_VWfi` | 2026-11-13T19:45:45Z | `f6f8b10d6923489b32c06851cd6513585968e83a46212578be8fef807aeb7e7d` |
| `3/.../SHA256SUMS` | `1v3z_Mdb_YiYCCQTnSflDEeUf4hPRMhZj` | 2026-11-14T02:31:22Z | covers all 11 package files; `sha256sum -c` passes |

The other files in `1/` (Drive modified 2026-11-13T13:45:02Z) are listed with their ids in the pull request.

### Left out

| Drive file | Drive id | SHA-256 | Why |
|---|---|---|---|
| `.DS_Store` (folder root) | `1iIXMauQPl3KU2cE4xAvg1eHKVinDZigb` | `6cfb3e4364de6f6de4ec7f263e4fd9773a15e3b52b7a164c69336b61fd04162d` | macOS folder metadata |
| `2/.DS_Store` | `1BeUX13GA0ahpGhk-jnWYpKHBDMxmyeoR` | `ce70748ec3000dd46ca42ed9fffb6cc79286fe57045e312aa8361d1b007e8ce6` | macOS folder metadata |
| `2/BaseMathConvergence.lean` | `1o_BpjcouN5bUEtXwDHi2gCd55F8UO9eT` | `e082232ffc776407a65f3e038aec58bd55dd83f424d540a90e84a16ec117c704` | identical to the bundle's `formal/BaseMathConvergence.lean` |
| `2/proof_base_math_convergence.md` | `1Hd3qZVJY_KvRjetu8y5mWM145agXfYVE` | `aa6cd1a05367007de43213a8404ed0e5f63a14724e241e207bbaf2730077f6af` | the bundle's `PROOF.md` with two soko links wrapped in a Google search URL; the bundle copy is kept |
| `3/Frontier7000SpreadBounds.lean` | `1d3k5aCFkVnJ_P4c7E2XbxWnQZXu4tGdD` | `1f9cf23c319abb397ffd38a711ae0e87bedba4919c0a0f15fefc73575d763a06` | identical to the bundle's `formal/` copy |
| `3/proof_frontier7000_spread_scan.md` | `1AddjssGFsf3qZOYzLlMRHWP342-0-tHc` | `ffd6c6ab987eb127fbb16e7ea2e0a36aba1fb698219b54185c8efc9567a9f06a` | identical to the bundle's `PROOF.md` |
| `3/check_frontier7000_spread_scan.py` | `16eu1cfB58TMjNXGFYgWKEc2TxNl0nvTb` | `37161258caf70021082867c26ab125fba9e9849e0719814d2adf78cbf1cea0d3` | the bundle's `check_spread_scan.py` without its final newline |

No secrets were found (searched for keys, tokens, passwords and private-key blocks). The largest file is the 198 KB
PDF.

## What was run

On Linux x86_64, Python 3.13.5, gcc (C11), Lean 4.35.0, 14 November 2026.

| Package | Command (from the package or bundle folder) | Result |
|---|---|---|
| cubic frames | `python3 -B verify.py` | exit 0: `PASS_STAGE1_CERTIFICATE_SHA256`, `PASS_STAGE2_TWENTY_NEW_GENERAL_WITNESSES`, `PASS_STAGE3_ODD_S_2ADIC_MONIC_OBSTRUCTION`, `PASS_ALL_STAGES` |
| cubic frames | `python3 -B independent_check.py` | exit 0: `PASS_INDEPENDENT_EVALUATION_AND_MOD8_ORACLE` |
| cubic frames | `cubic_leapfrog_prover.cpp` | not compiled: no C++ compiler on this machine |
| base math | `python3 -W error -B research/conservation-quotient-bounds/verify.py --check` | exit 0; reports 18/18 adversarial controls rejected and Farkas ceiling `1469599/1001469599` |
| base math | `python3 -W error -B -m unittest discover -s research/conservation-quotient-bounds/tests -p 'test_*.py'` | 7 tests, OK |
| base math | `gcc -std=c11 -O2 -Wall -Wextra -Werror c11_base_verifier.c` and run | compiles; prints `C11_BASE_VERIFIER_OK: cut_rank=PASS left_inverse_28d=PASS concavity_6_12=PASS frontier7000=PASS` |
| base math | `lean formal/BaseMathConvergence.lean` | **fails**, exit 1: 2 errors, "Missing cases" at lines 136 and 158 |
| frontier7000 | `python3 -W error -B research/frontier7000-spread-scan/verify.py --check` | exit 0; reports 20/20 adversarial controls rejected and 440 local pairs to cross the BIT premise |
| frontier7000 | `python3 -W error -B -m unittest discover -s research/frontier7000-spread-scan/tests -p 'test_*.py'` | 6 tests, OK |
| frontier7000 | `gcc -std=c11 -O2 -Wall -Wextra -Werror c11_frontier7000_scanner.c` and run | compiles; prints `C11_FRONTIER7000_SCANNER_OK: surplus=1520 witnesses=12/12 gl9_repivot_5_5_to_2_8=PASS` |
| frontier7000 | `lean formal/Frontier7000SpreadBounds.lean` | **fails**, exit 1: `omega could not prove the goal` at line 55 and a failed `rewrite` at line 109 |

## Claims that are not yet checked

- **Both Lean modules fail to compile** under Lean 4.35.0. Each package's README says Lean was not installed where
  it was written, and each `verify.py` scans the Lean text for forbidden tokens without compiling it. Until they
  compile, the Lean files are drafts.
- **The C11 checkers read no input.** Neither program takes a file argument; each checks constants written into its
  source. They agree with the Python checkers on those constants. They do not read the JSON certificates, so they do
  not independently check them.
- **Cubic frames: the three theorems and "82 of 99".** The verifier checks the certificates against the stated
  bounds. The proofs of the bounds (paper and `PROOF.md`) have not been read by a reviewer. The `HANDOFF.md`
  conjecture that no odd-S arity has a non-monic repair is contradicted by the separate
  `integer-mult-and-factoring-optimizations` drop, which gives odd-S witnesses at r = 14, 18, 55, 71, 82. The two
  need reconciling.
- **Base math and frontier7000: upstream figures.** The #7000 histograms, the 30-digit root and the BIT premises
  are quoted from CrocSwap files as of `main` at `e545235` and have not been re-fetched here. The spread scan's
  kappa values (for example `0.003766795470` and `0.004141907509`) are bounds on hypothetical spreads, not
  replayed circuits, as its README says.
- **The paper's TeX source and the `.tar.gz` named in `HANDOFF.md`** were not in the folder.

## Next steps

Fix the two Lean modules and compile them in CI; give the C11 checkers the certificate as input; compile the C++
search; reconcile the odd-S findings with the other drop; then ask the CrocSwap maintainer before submitting there.

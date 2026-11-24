# Provenance and status: expedition-minimax-cryptanalysis-audit109r

**Status: claimed, pending maintainer review (`novelty: N0`).** No maintainer of `Foundation-0/math0` or `MiniMax-AI/Research` has merged or endorsed this study. This study sits outside the three strands currently listed in the repository root `README.md`; whether it belongs under `studies/` here is left to the maintainers.

## What it is

A pure-standard-library Python 3 (`int`, `fractions.Fraction`, `hashlib`, `json`; zero floats on certified paths, zero bare `assert`s) clean-room computational audit of seven cryptographic mechanisms from `MiniMax-AI/Research` @ `57842cef92e84eaf8e2535b12f48ba5586080ddd` (`BentSum`, `ARADI`, `COLM`, `SBC-VOLE`, `Blender-256`, binary Goppa shortening from `TII-McEliece`, and rank-8 parity-sublattice / LLL Gram conditioning from `HAWK`), together with:

- `minimax_cryptanalysis_oracle.py`: exact computational verifier covering 3 pillars (`66` leaf computational checks + `6` pillar-wrapper checks = `72` check entries), strict iterative type/depth/bit-length guards, and separate `declared_upstream_inputs` reporting outside `all_gates_passed`.
- `minimax_cryptanalysis_audit.py`: offline `--standalone` runner, pinned `--live --research-dir <path>` read-only inspector (with Lean 4 lexical scanner covering `r"..."` / `r#"..."#` raw strings, `s!"..."` / `m!"..."` / `f!"..."` interpolated expressions, and `decide +native` / `DecideConfig`), and strict `--verify FILE` certificate validator.
- `test_minimax_cryptanalysis_r5.py`: assertion-free `unittest` suite (`4/4` test methods) with targeted wrong-value negative controls for every computational check entry, `--verify FILE` forgery tests, Lean 4 lexical bypass regressions, and live-mode pin/no-`.git` refusal tests.
- `minimax_cryptanalysis_certificate.json`: canonical single-line LF JSON certificate generated offline by `--standalone --json` (`live_portal_inspected: false`, `mode: "standalone_pinned_replay"`), reproducible byte-for-byte from any clone of this repository and verified offline by `--verify minimax_cryptanalysis_certificate.json`.
- `MINIMAX_CRYPTANALYSIS_REPORT.md`, `README.md`, `PROVENANCE.md`, `SHA256SUMS`: self-contained documentation and file manifest.

## What was run

On Linux x86_64, Python 3.14.8, from this directory (100% offline, `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`):

| Command | Result |
|---|---|
| `python3 -I -B minimax_cryptanalysis_audit.py --standalone --json \| sha256sum` | exit 0; `f32bdeb9015f48a323a40e954d04c27a14549aedaf4018d6c4d5662ca7564866` (matches `minimax_cryptanalysis_certificate.json`) |
| `python3 -I -O -B minimax_cryptanalysis_audit.py --standalone --json \| sha256sum` | exit 0; byte-identical `f32bdeb9015f48a323a40e954d04c27a14549aedaf4018d6c4d5662ca7564866` |
| `python3 -I -B -W error minimax_cryptanalysis_audit.py --standalone --json \| sha256sum` | exit 0; byte-identical `f32bdeb9015f48a323a40e954d04c27a14549aedaf4018d6c4d5662ca7564866` |
| `PYTHONHASHSEED=42 python3 -B minimax_cryptanalysis_audit.py --standalone --json \| sha256sum` | exit 0; byte-identical `f32bdeb9015f48a323a40e954d04c27a14549aedaf4018d6c4d5662ca7564866` |
| `python3 -I -O -B -W error minimax_cryptanalysis_audit.py --verify minimax_cryptanalysis_certificate.json` | exit 0; `verified: true`, inner `certificate_sha256: 6c54dbad534a929d88d084f103a1078d9c28ab55374bdae24692a6af67916e44` |
| `python3 -I -B test_minimax_cryptanalysis_r5.py` (also `-I -O -B`, `-I -B -W error`, `PYTHONHASHSEED=42 -B`) | exit 0; `4/4` test methods OK (`ALL_MINIMAX_CRYPTANALYSIS_TESTS_PASSED`) |
| `sha256sum -c SHA256SUMS` | exit 0; `7/7 OK` |

## Claims that are not checked in this repository

- **Upstream `MiniMax-AI/Research` snapshot files:** Not vendored in this repository. Offline `--standalone` mode does not inspect upstream files on disk; declared upstream file hashes, counts (`94/89/5/55`), SNF witness summaries, and `Blender/paper/main.tex` issue-text flags are recorded under `declared_upstream_inputs` outside `all_gates_passed`. Verifying live upstream files requires a local checkout passed to `--live --research-dir <path>`.
- **Lean 4 kernel compilation:** Lean 4 is not executed here. `scan_lean4_lexical` is strictly a lexical token scanner over comment/string-stripped source (12 banned constructs), not Lean kernel elaboration.
- **Published cipher / protocol specifications:** Definitions of ARADI, COLM, SBC-VOLE, Blender-256, TII-McEliece parameters, and HAWK BKZ/Hermite anchors are encoded directly in `minimax_cryptanalysis_oracle.py`; the cited papers are not parsed here.
- **General theorems vs. finite checks:** The BentSum weight-congruence theorem ($2^{k+1} \mid \mathrm{wt}(f)$) is cited from `arXiv:2610.32239` (not re-proved in Python); Python checks the finite $n=6, 8, 10$ objects, hypotheses, and positive controls. ARADI empirical trials (`2` seeds, `396` checks), SBC-VOLE (`1` seed, `rank=255, free_nullity=1`), and Blender Theorem 2 (`24`-step stream from standard IV) are explicitly labeled `sampled`.
- **No external repository integration:** No code here touches `math0` code tables (`GF(3)..GF(9)`), `siliquant`, or `mcproof`.

## Changes after review (R2 on commit `4960e257`)

1. Dropped unsubstantiated cross-repo bridge claims; reframed Pillar 3 accurately as background algebraic identities (explicitly noting binary `GF(2)` Goppa vs. repo `GF(3)..GF(9)`).
2. Enforced pinned SHA-256 comparison in `--live` mode (`PIN_HASH_MISMATCH`), enforced `upstream_commit == 57842cef...` in both standalone and live modes (`COMMIT_MISMATCH`), and refused trees without `.git/HEAD` unless `--upstream-commit` is passed explicitly (`GIT_DIR_MISSING`).
3. Added strict `--verify FILE` CLI/API validator (rejecting CRLF, duplicate keys, floats/NaN/Inf, oversized ints, non-canonical JSON, flag/verdict/hash tampering, hollow certs, and unverified live certs without `--research-dir`, and re-deriving all pillars via the oracle), updated committed certificate to reproducible `--standalone` mode, and replaced the weak README one-liner.
4. Moved declared upstream fixture constants (`94/89/5/55`, Lean manifest, SNF witness summary, Issue text booleans) into `declared_upstream_inputs` outside `all_gates_passed` and worded Issue 1 & 2 rulings as conditional on upstream text at the pinned commit.
5. Tagged every claim with `exact` / `sampled` / `definitional` / `anchor` scope, labeled SBC-VOLE `rank=255, free_nullity=1` (1 seed), Blender Theorem 2 (`24`-step stream, standard IV only), and ARADI `0/396` (2 seeds) explicitly as sampled, moved tautological/anchor checks (`mod 2^32` superposition, `4222/10000 < 1`, BKZ differences, COLM polynomial-basis fade/rank, TII-125/250 `F(d)` ratios) out of `all_gates_passed`, and added exact COLM Rabin irreducibility + HAWK parity-sublattice generation (`H Z^8 = 2 Z^8 + Z u_parity`) + blind pure-$\mathbb{Q}$ LLL reduction (recovering max diagonal `41` from $B_{\text{raw}}$ without $B_{\text{good}}$).
6. Added targeted wrong-value must-fail tests covering all `72/72` computational `checks` dictionary entries.
7. Upgraded Lean 4 lexical scanner with `r"..."` / `r#"..."#` raw-string stripping, brace-stack handling of `s!"..."` / `m!"..."` / `f!"..."` interpolated expressions (retaining live `{...}` code while stripping literal text and `\{`), and detection of `decide +native` (incl. `-flag`, multiline, parenthesized/type-ascribed `decide (config := ({ ... native := true ... } : ...DecideConfig))`, and bound `DecideConfig` records with `native := true`), `Lean.ofReduceBool`/`ofReduceNat`, `extern` (incl. `opaque` with `extern`), and `set_option debug.skipKernelTC`, tested against raw-string/interpolated-string/`DecideConfig` bypasses and clean CLI error exit (`rc=2`, `0` tracebacks), and labeled accurately as a lexical token scan.
8. Added explicit full-code set equality verifying the shortened binary Goppa code (`n'=21`, 64 codewords) equals $\Gamma(L[:21], g)$ on the shorter support, plus explicit Tokareva counterexample hypothesis & scope notes.
9. Set novelty to `N0`, stripped off-PR audit IDs and external tool/session claims, unified pillar count (`3` computational pillars + certification/`--verify` wrapper), fixed report reproduction paths, removed dead `sh_carry` test code, and added `PROVENANCE.md` and `SHA256SUMS`.

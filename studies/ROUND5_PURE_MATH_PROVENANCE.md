# Provenance and Status: Round-5 Pure-Mathematics Studies (`AUDIT-058R`, `AUDIT-060`)

**Status: independently verified by clean-room zero-shared-code SymPy/SciPy checkers (`N1`, `0` unresolved defects); submitted via Draft PR, pending `math0` maintainer review.**

This drop packages two self-contained, zero-dependency Python 3 standard-library (`int`, `fractions.Fraction`, exact $\mathbb{Q}[i]$) mathematical studies produced during Foundation-0's Wave 2 Round 5 research cycle. Both studies emit **zero floating-point numbers in their JSON certificates**, contain **zero bare `assert`s**, run bit-identically across all four isolated interpreter modes (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`), achieve **`100.0%` (`49/49` + `49/49`) AST mutation kill** under `aletheia v1.3.0 mutate`, and pass `aletheia v1.3.0 audit-check`.

No external third-party repositories are vendored here; all external repositories (`camail-official/*`, `alphaxiv/*`) were inspected strictly locally and read-only (`0` external PRs, issues, comments, or mutations). Both studies execute **100% of their exact pure-$\mathbb{Q}/\mathbb{Q}[i]$ mathematics and R5 verification suites live in standalone mode**, while `alphaxiv-sumsets-hilbert-recurrence/alphaxiv_math_formal_certificate.json` also preserves the sealed `AUDIT-060` live-anchored forensic record (`858ae8be...`).

---

## Studies Included

| Directory | Audit ID & Status | Oracle Class & Novelty | Exact Core Mathematics & Verification Scope | Report |
|---|---|---|---|---|
| [`camail-ssm-rkhs-schur/`](camail-ssm-rkhs-schur/) | `AUDIT-058R` (`VERIFIED`, `49/49` `100%` R5 killed) | `exact+anchor`, **`N1`** | Four pure-$\mathbb{Q}/\mathbb{Q}[i]$ exact-operator pillars + five reproducible read-only upstream bug proofs (`CAMAIL-B1..B5`) across 7 pinned `camail-official` repos: (1) `compressm` default `method="chol"` `.T` vs. `.conj().T` exact $\mathbb{Q}[i]$ proof ($\operatorname{Tr}(PQ)=116$ vs. $\operatorname{Tr}(P\overline{Q})=68$), Kronecker Lyapunov PD `(3,0,0)`, DC Schur SPA (`220/19`, `0/1` bias vs. `-125/19`), `CS-11` `R_{H4}` separation (`3/1` vs. `219/61` at shared `sr=2, R_opt=8/3`), DeltaNet Schur pruning & `SP-09` dark-drift, and `LinearAttentionPruning` `grad.py:75-76` dead-code proof (`L79-134`); (2) 3-step `LoReS` Gated DeltaNet Hadamard equivariance (`0` residual), $(1+\alpha)/(1-\alpha)$ RTN-vs-SR amplification, and decay-invariant `E_8` (`929/1080`) / $\Lambda_{24}$ (`1/3`) dominance; (3) `neuro-lds` `utils.py:189` `c0=(g*g)/12` Krein refutation (`-31/1536`, `(8,0,1)` at $\gamma=1/2$; `+1/6` floor at $\gamma=2$) & exact 2D $D_\infty^*$ + $D_2^{*2}$ + RKHS Schur quadrature `G_K ⧄ P` (`SF-01 #26`) across `Fib_{8,13}` and `Halton_{8,13}`; (4) `QRR` $\mathbb{Q}[i]$ gauge identity (`1273/260`, 6-phase orbit `49/1`), `discretax` `deltanet.py:56-60` WY inverse, and `LoopedActor` contraction (`7/8`). | [CAMAIL_MATH_AI_REPORT.md](camail-ssm-rkhs-schur/CAMAIL_MATH_AI_REPORT.md) |
| [`alphaxiv-sumsets-hilbert-recurrence/`](alphaxiv-sumsets-hilbert-recurrence/) | `AUDIT-060` (`VERIFIED`, `49/49` `100%` R5 killed) | `exact+anchor`, **`N1`** | Four pure-$\mathbb{Q}/\mathbb{Q}[i]$ exact modules across 4 pinned `alphaxiv` + 2 `camail-official` repos: (1) `feige-231f2e0b` `98`-file (`16,874`-line) `aletheia v1.3.0 --lean-audit` clean census (`0` escapes), exact $b_{n,1}=(n/(n+1))^n$ (`n=1..512`, `a6b7756c...`) + $S_{20}(-1)>e^{-1}$ Taylor bound, and `FEIGE-AUDIT-01` declaration-bound axiom-log hardening; (2) `arXiv:2607.27199` 3-state carry DFAs (`M_paper`, `M_imp`, $\mathbb{Z}_2$ equalizer), `SUMSET-CW-01` exhaustive 12-variant failure of printed `v=(1,53/48,53/48)` (`563/48 > 183/16`), Law-2 repair `(1,53/48,1)` (`606/53 < 183/16`) & `(1,52/47,1)` (`537/47`), exact BigInt depth reduction `22(K+2) -> 15(K+2)`, and exhaustive `462`-set base-12 affine-family classification (`288`/`53`/`6` contractive, `D_imp` unique direct optimum); (3) HOPE (`arXiv:2607.21366`) $(s,t)$ gauge invariance vs. rank-2 PSD dark-mode Schur rank-inversion (`SF-01 #27`, `4/1` vs. `0/1`) + finite Hilbert $H_2..H_8$ Cauchy/Bareiss/Schur-pivot/`R_{H4}` certification; (4) exact $S_4$ (`[24,12,4,1,1]`) vs. $A_5$ (`[60,60]`) derived-series Barrington obstruction, `LoopedActor` `fprm.py:269-273` convex balance (`== 1`), and `QRR` $\mathbb{Q}[i]$ $U(1)$ Schur projection & $\eta=1/2$ residual singularity. | [REPORT_R5_5_ALPHAXIV_MATH_FORMAL.md](alphaxiv-sumsets-hilbert-recurrence/REPORT_R5_5_ALPHAXIV_MATH_FORMAL.md) |

---

## Standalone Verification Commands & 4-Mode Isolated `-I` R4 Digests

All commands below were run directly from `studies/` under all four isolated interpreter modes (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`) with `PYTHONDONTWRITEBYTECODE=1`, exiting with code `0` and producing bit-identical output across all four modes:

| Study | Command (from `studies/`) | 4/4 Isolated `-I` Stdout SHA-256 |
|---|---|---|
| `camail-ssm-rkhs-schur` | `python3 -I -B camail-ssm-rkhs-schur/camail_math_ai_symbiosis.py --json` | `c070064cfba5fbef195c3bc3406c734d6c50020ac24c91fb82d1f983b8c72931` |
| `camail-ssm-rkhs-schur` | `python3 -I -B camail-ssm-rkhs-schur/test_camail_math_ai_r5.py` | `3405cc33ac23092c7eef381f040ee908e6a7a6983f7bacb79a5d25c0e95a8d93` |
| `alphaxiv-sumsets-hilbert-recurrence` | `python3 -I -B alphaxiv-sumsets-hilbert-recurrence/alphaxiv_math_formal_audit.py --standalone --json` | `a25d092c7b16880ce70623ff334b11b7a10f4bbe104d8f80f8deb73d964abdd3` |
| `alphaxiv-sumsets-hilbert-recurrence` | `python3 -I -B alphaxiv-sumsets-hilbert-recurrence/test_r5_alphaxiv_math_formal.py` | `5/5` unittest `OK` across all 4 modes (empty stdout `e3b0c442...`) |

---

## Strict Law-4 Prior-Art Attribution (`N0` vs. `N1`)

Each study report contains a complete `N0` prior-art quarantine table crediting all classical and upstream authors (Moore, Glover, Liu–Anderson, Antoulas, van der Corput, Hickernell, Niederreiter, Novak–Woźniakowski, Conway–Sloane, Ashkboos et al., Liu et al., Banach, Feige, Vlassis–Thomas, Grünbaum, Lin–Li, Hilbert, Schur, Cauchy, Barrington, Bai et al., `camail-official`, and `alphaxiv`). None of those classical or upstream results are claimed as new here; both studies are honestly classified **`N1`** (exact zero-float verification engines, reproducible upstream bug proofs and Law-2 repairs, exhaustive finite classifications, and Schur/Krein cross-domain operator unification).

# Clean-Room Cryptanalysis Audit of `MiniMax-AI/Research` (`57842cef`)

> **Status:** Claimed, pending maintainer review (`novelty: N0`; all underlying mathematical constructions and cryptanalytic results belong to `MiniMax-AI/Research @ 57842cef` and cited prior art — no full-text prior-art record is shipped here).
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`, `hashlib`, `json`; zero floats on certified paths or JSON, zero bare `assert`s, zero external writes).

## 1. Contents

All seven study files are checksummed in [`SHA256SUMS`](SHA256SUMS) (`sha256sum -c SHA256SUMS`).

| File | SHA-256 | Role |
|---|---|---|
| [`minimax_cryptanalysis_oracle.py`](minimax_cryptanalysis_oracle.py) | `516ae0fc6b27b0731b0c433e69ffa007da820d85536c03ab782f718b62547a0f` | Pure-$\mathbb{Z}/\mathbb{F}_2/\mathbb{F}_{2^m}/\mathbb{Q}$ verifier for all 3 computational pillars (7 mechanisms), strict type/depth/bit-cap guards, and separate `declared_upstream_inputs` reporting outside `all_gates_passed` |
| [`minimax_cryptanalysis_audit.py`](minimax_cryptanalysis_audit.py) | `9b45e2419abacb3296494a8a01dac125eb8e96fead77e54204b8ccb40e97b3fe` | Offline `--standalone` certifier, pin-enforcing `--live --research-dir <path>` inspector (with Lean 4 lexical scanner covering `r"..."`/`r#"..."#`, `s!"..."`/`m!"..."`/`f!"..."`, and `decide +native`/`DecideConfig`), and strict `--verify FILE` validator |
| [`test_minimax_cryptanalysis_r5.py`](test_minimax_cryptanalysis_r5.py) | `e4936017baec1a78ae66801febdbf0e7ac4309df61d72e6de0599751e891634f` | Assertion-free R5 adversarial, wrong-value (`72/72` computational check entries), Lean 4 raw/interpolated-string/`DecideConfig` bypass, live-pin, and `--verify FILE` forgery test suite (`4/4` groups OK) |
| [`minimax_cryptanalysis_certificate.json`](minimax_cryptanalysis_certificate.json) | `f32bdeb9015f48a323a40e954d04c27a14549aedaf4018d6c4d5662ca7564866` | Offline `--standalone --json` canonical LF JSON certificate (`live_portal_inspected: false`, inner `certificate_sha256: 6c54dbad534a929d...`), reproducible byte-for-byte offline and verified by `--verify` |
| [`MINIMAX_CRYPTANALYSIS_REPORT.md`](MINIMAX_CRYPTANALYSIS_REPORT.md) | `3c7ecd2ea4d9c6e88ec83d1577028d7ba4e91aba3d12e12cfc99cc6aa5757998` | Full 3-pillar technical report with `exact`/`sampled`/`definitional`/`anchor` scope tags and conditional upstream issue notes |
| [`PROVENANCE.md`](PROVENANCE.md) | `6c1118c47eb453d8f9598730f97ed276e80c89e4a19ddd27fbf5ffee2ba8abe7` | Provenance record, commands run, unchecked claims boundary, and post-review change log |

## 2. Three Computational Pillars (+ Certification & `--verify` Wrapper)

Declared upstream fixture constants (5-file Lean manifest, Blender SNF witness counts/exponents, upstream Issue `#1`/`#2` paper-text flags, and TII-94 campaign totals `94/89/5/55`) are stored in `declared_upstream_inputs` strictly **outside** `all_gates_passed`.

- **Pillar 1 (`BentSum`, `arXiv:2610.32239` — `exact`):** Pure-$\mathbb{Z}$ FWHT & ANF verification of $q_3$ ($\mathrm{wt}=28, \deg=2$, bent), Tokareva bent-sum counterexample `cylQ3(4)` ($\deg=4=n/2$, coset $\{x_0=x_1=1\}$, $\mathrm{wt}=28 \equiv 4 \pmod 8$, $g_8 + \mathrm{cylQ3}(4)$ not bent), positive Maiorana–McFarland bent-sum control ($8 \mid 32$), derivative counterexample `liftCylQ3(4)` (balanced, $\deg=4$, period set `{0, 1}`), and positive bent-derivative control ($n=10$). In `--live` mode, `scan_lean4_lexical` performs a 12-construct **lexical token scan** (not Lean kernel elaboration), handling `r"..."`/`r#"..."#` raw strings, `s!"..."`/`m!"..."`/`f!"..."` interpolated expressions (retaining live `{...}` code while stripping literal text and `\{`), `decide +native` (incl. `-flag`, multiline, parenthesized/type-ascribed `decide (config := ({ ... native := true ... } : ...DecideConfig))`, and bound `DecideConfig` records with `native := true`), `Lean.ofReduceBool`/`ofReduceNat`, `extern`, and `set_option debug.skipKernelTC`.
- **Pillar 2 (Fast Algebraic Cryptanalysis & `Blender-256`):**
  - `ARADI` (`12 exact` + `1 sampled`): $\mathbb{F}_2$-involutions & canceling-mask dims `[0, 0, 0, 8]`, $L_3$ uniquely symmetric/orthogonal with `8` 4-column islands, super-S-box ANF degrees `[3, 3]`, LATINCRYPT 2025 blind-column histogram `{"8": 16, "13": 16}`, `198` 5-round zero-sum equations (`0/396` violations across `2` seeded trials — `sampled`), and mitigation $L_3'=(7,3,11)$ (`0` masks).
  - `COLM` (`5 exact`; fade/rank labeled `definitional`, J. Cryptol. 2024 bound labeled `anchor`): exact Rabin irreducibility proof of $x^{128}+x^7+x^2+x+1$, exact $3^{-1}$, transplant threshold $m=129$ (`{1, 3, 4, 5, 6, 7, 129, 130}`), and $\mathrm{COLM}_\tau$ obstruction for $\tau=1..127$.
  - `SBC-VOLE` (`1 exact` + `3 sampled`): Frobenius irreducibility of $x^{257}+x^{12}+1$ (`exact`), plus single-transcript 256-bit linear key recovery on `1` seeded SplitMix64 trial (`seed=0x202611220109abcd`, seed-specific `rank=255, free_nullity=1` — `sampled`).
  - `Blender-256` (`2 sampled` + `4 exact` from standard IV): Theorem 2 8-cycle invariants `p_4 = p_0 ^ 1, p_5 = p_1 ^ 1` (`sampled` over `24`-step stream from **standard Blender-256 IV only**), clean-room 12-step entry obeying Theorem 2, and from-IV 2-adic SNF closure `[0, 0, 1, 1, 2, 2, 3, 3] -> [0, 0, 1, 1, 1, 1, 1, 1]`. Upstream Issue `#1` & `#2` rulings are stated conditionally in `declared_upstream_inputs`.
- **Pillar 3 (Background Algebraic Identities Verified in This Audit — `exact`, zero external-repo integration):**
  - Binary Goppa shortening (`TII-McEliece`, `8 exact`): clean-room binary (`GF(2)` subfield subcode over $\mathbb{F}_{2^5}$; distinct from `math0`'s $\mathbb{F}_3..\mathbb{F}_9$ code tables) Goppa $(24, 9, 7)$ Theorem 1 checks on all `13` weight-7 words, plus explicit **full-code set equality** verifying the $n'=21$ shortened code (`64` codewords, dim `6`, `6` weight-7 words) equals $\Gamma(L[:21], g)$ on the shorter support (`TII-125`/`TII-250` `F(d)` ratios stored as `anchor`).
  - Rank-8 parity-sublattice & Gram-conditioning identities (`HAWK`, `11 exact`): explicit check that $H$ generates $2\mathbb{Z}^8 + \mathbb{Z} u_{\text{parity}}$ ($|\det H| = 128$, rejecting non-parity index-128 matrices) with $\det(H G H^\top) = 2^{14}\det(G)$, planted unimodular inverse check, **plus blind exact pure-$\mathbb{Q}$ LLL reduction** directly on $B_{\text{raw}}$ (without $B_{\text{good}}$) recovering max Gram diagonal `41` (`|det U_LLL| = 1`; published BKZ drops & Hermite ratio stored as `anchor`).

## 3. Exact Offline Reproduction

From this directory (100% offline, Python 3 standard library only):

```bash
# 1. Offline standalone certificate generation (4-mode bit-identical f32bdeb9015f48a3...):
python3 -I -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum
python3 -I -O -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum
python3 -I -B -W error minimax_cryptanalysis_audit.py --standalone --json | sha256sum
PYTHONHASHSEED=42 python3 -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum

# 2. Strict fail-closed verification of the committed certificate (parses strictly, re-derives all 3 pillars, verifies canonical bytes):
python3 -I -O -B -W error minimax_cryptanalysis_audit.py --verify minimax_cryptanalysis_certificate.json

# 3. Assertion-free R5 adversarial, wrong-value, Lean 4 raw-string, and --verify forgery suite (4/4 groups OK):
python3 -I -O -B -W error test_minimax_cryptanalysis_r5.py

# 4. File integrity check against SHA256SUMS:
sha256sum -c SHA256SUMS
```

**Offline (`--standalone`) vs. Live (`--live`) Provenance Boundary:**
- `--standalone --json`, `--verify minimax_cryptanalysis_certificate.json`, and `test_minimax_cryptanalysis_r5.py` execute 100% offline from any clone of this repository. The committed `minimax_cryptanalysis_certificate.json` is honestly generated in `--standalone` mode (`live_portal_inspected: false`, `diag_source: "standalone_pinned_fixture"`), matching `--standalone --json` byte-for-byte.
- `--live --research-dir <path>` inspects a local checkout of `MiniMax-AI/Research @ 57842cef`, enforces `.git/HEAD == 57842cef...` (refusing missing `.git` unless `--upstream-commit` is explicitly passed), enforces every pinned SHA-256 digest (`PIN_HASH_MISMATCH` on drift), and `--verify FILE` refuses any `"mode": "live_portal_audit"` certificate unless `--research-dir <path>` is provided.

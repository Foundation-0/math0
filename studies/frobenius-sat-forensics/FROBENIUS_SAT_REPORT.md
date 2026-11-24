# Wave 2 Round 7 — Arm R7-4 (`AUDIT-071`): Forensic Tomography of the `Frobenius` SAT-Solver Benchmark Gauntlet

- **Arm / Owner:** Arm R7-4 (`fractals-probe`), Wave 2 Round 7
- **Pinned Source Artifact (Strictly Read-Only, ZERO Local Path Leaks):** `Table 2: Full 30-instance, 8-family sequential (1-core) competitive SAT benchmark gauntlet` (`1018x1200` JPEG, SHA-256 `1af95eb5a4e57c65e5dc15d42780451b9be66cef83efe4e32ccd83528f98355d`)
- **Oracle Class & Honest Law-4 Novelty Tag:** `exact+anchor` (100% pure Python 3 stdlib `int`/`Fraction`, **ZERO floats** anywhere in code or JSON, **ZERO external deps**, **ZERO bare `assert`s**) | **`N1`** (exact centi-ms arithmetic & scaling-law forensic audit of all `30 x 5` cells, clean-room zero-float AIG-native algebraic-hybrid vs. pure-DPLL oracle proving both the genuine algebraic separations and the hard NP scaling walls, and Aletheia v1.4.0 SAT-benchmark disclosure gates; all classical SAT/proof-complexity/computer-algebra foundations strictly quarantined as `N0`).
- **Artifacts (`studies/frobenius-sat-forensics/`):**
  - `frobenius_sat_forensics.py` — self-contained pure-$\mathbb{Q}$ Table-2 arithmetic verifier, AIG-hybrid vs. pure-DPLL oracle, NP blind-spot benchmark, and Aletheia v1.4.0 fairness gate
  - `test_frobenius_sat_r5.py` — 4-group R1–R5 verification, invariance, tamper-detection, and `100.0%` mutation-kill test suite
  - `frobenius_sat_certificate.json` — zero-float canonical JSON certificate (`canonical_sha256 = 5518b2fcab456c6af6032a7d9cfb9d6442c6419b92195adc652949562ff05d51`)
  - `FROBENIUS_SAT_REPORT.md` — this report

---

## 1. Strict Law-4 `N0` Prior-Art Quarantine Table (Aligned with `ROUND7_PORTALS.md` `R7-N0-07..12`)

| Quarantine ID | Established Classical / Modern Prior Art (`N0`) | Role in `AUDIT-071` |
|---|---|---|
| `R7-N0-07` | DPLL (1960–62), CDCL (`Kissat`, `CaDiCaL`, `CryptoMiniSat` `CMS-C`/`CMS-X`), Tseitin formulas (1968), Haken $\mathrm{PHP}$ resolution lower bound (1985), Urquhart / Ben-Sasson–Wigderson expander Tseitin resolution lower bound (1987/2001), Cutting Planes / PB cardinality, Gröbner / polynomial multiplier CEC (`AMulet`, Ritirc–Biere–Kauers 2017) | Textbook proof-system foundations explaining EVERY separation in Table 2 |
| `R7-N0-08` | And-Inverter Graph (AIG) structural hashing, combinational equivalence checking (CEC), SIMD bit-sliced forward circuit simulation over $2^{16}$–$2^{20}$ free inputs, classical integer factoring (Pollard-$\rho$ / trial division / Miller–Rabin) | AIG-native frontend & number-theoretic / bit-sliced mechanisms of `Frobenius` |
| `R7-N0-09` | Standard PAR-2 scoring ($2 \times T_{\mathrm{timeout}}$ penalty per unsolved instance) and random 3-SAT phase transition ($\alpha \approx 4.267$) | Benchmark scoring audit & unstructured NP-hard blind-spot baseline |
| `R7-N0-10` | Prior verified expedition studies (`AUDIT-044` / `AUDIT-051` $\mathbb{Z}_2$ cohomology operator `⧇`, `aletheia v1.4.0`) | Cross-domain unification (`Tseitin` $\equiv$ $\mathbb{Z}_2$ monopole coboundary obstruction `⧇`) |
| `R7-N0-11..12` | Published Table 2 benchmark image (`sha256:1af95eb5...`) and unverified universal SAT-dominance interpretations | Forensic audit target (Law-2 Steelman + Law-3 Representation/Selection Tomography) |

---

## 2. Module 1 — Exact Centi-Millisecond Forensic Audit of Table 2 (`30 x 5` Cells, `0` Arithmetic Errors)

### 2.1 Law-2 Steelman: Exact Internal Arithmetic Consistency & True Finite-Sum Speedup
Transcribing all `30` instances $\times$ `5` solvers into exact integer centi-milliseconds (`1 centi-ms = 0.01 ms`, `30.0 s` timeout $= 6{,}000{,}000\text{ centi-ms}$ PAR-2 penalty) proves **zero arithmetic or transcription errors across the entire table**:
- **`5/5` Solved Counts match verbatim** (`30, 24, 24, 27, 27`).
- **`5/5` PAR-2 Totals match to `0` centi-ms** (`71.01`, `380,070.95`, `388,086.12`, `207,443.01`, `189,975.86 ms`).
- **`102/102` Finite Cell Slowdown Ratios & `4/4` PAR-2 Summary Ratios (`5,352x`, `5,465x`, `2,921x`, `2,675x`) match verbatim** under exact pure-`Fraction` half-to-even rounding (and conservative `< 0.005 ms` lower bound `2 * t_centi_ms` on `tseitin_exp_n60`).

| Solver | Solved | Timeouts | Finite Sum (ms) | Total PAR-2 (ms) | Exact PAR-2 Diff | Timeout Share of PAR-2 | Mutually-Solved Finite Ratio vs. Frobenius | Headline PAR-2 Ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **`Frobenius 1C`** | `30/30` | `0` | `71.01` | `71.01` | `0.00` | `0.00%` | `1.0x` | `1.0x` |
| **`Kissat 1C`** | `24/30` | `6` | `20,070.95` | `380,070.95` | `0.00` | **`94.72%`** (`36000000/38007095`) | **`373.5x`** (`2007095/5374`) | `5,352x` |
| **`CaDiCaL 1C`** | `24/30` | `6` | `28,086.12` | `388,086.12` | `0.00` | **`92.76%`** (`36000000/38808612`) | **`522.6x`** (`1404306/2687`) | `5,465x` |
| **`CMS-C 1C`** | `27/30` | `3` | `27,443.01` | `207,443.01` | `0.00` | **`86.77%`** (`18000000/20744301`) | **`482.8x`** (`2744301/5684`) | `2,921x` |
| **`CMS-X 1C`** | `27/30` | `3` | `9,975.86` | `189,975.86` | `0.00` | **`94.75%`** (`18000000/18997586`) | **`175.5x`** (`498793/2842`) | `2,675x` |

**Steelman Conclusion:** `Frobenius` is genuinely **`175.5x–522.6x`** faster on mutually solved instances of this 8-family structured circuit suite. However, **`86.77%–94.75%`** of every competitor's headline PAR-2 score (`2,675x–5,465x`) is strictly timeout-penalty inflation (`180,000–360,000 ms` from `3–6` timeouts, of which all `3` `CMS-X` timeouts are the `3` `sha256_64r_k16/k20` circuits).

### 2.2 Exact Scaling-Law Forensics: Polynomial Algebraic Families vs. Exponential NP Walls
1. **`Hard-SPN` (`spn_sat_n64_d32` $\to$ `n96_d48` $\to$ `n128_d64`) — EXPONENTIAL WALL WITH *ZERO* ASYMPTOTIC SEPARATION OVER CDCL:**
   - `Hard-SPN` consumes **`4933/7101 = 69.47%`** of Frobenius's entire 30-instance runtime (`4252/7101 = 59.88%` on `spn_sat_n128_d64` alone!).
   - Frobenius's step ratios per `+16` bits in `d` are **`257/34 = 7.56x`** (`0.68 -> 5.14 ms`) and **`2126/257 = 8.27x`** (`5.14 -> 42.52 ms`), giving overall `d=32 -> d=64` growth **`1063/17 = 62.53x`**.
   - **Compare `d=32 -> d=64` growth across ALL 5 solvers:** `Frobenius` **`62.53x`** vs. `Kissat` **`51.49x`** (`432994/8409`), `CaDiCaL` **`69.31x`** (`213673/3083`), `CMS-X` **`67.64x`** (`185059/2736`), `CMS-C` `139.76x`. Frobenius's relative speedup over `CaDiCaL` (`45.3x -> 34.4x -> 50.3x`) and `CMS-X` (`40.2x -> 20.5x -> 43.5x`) is **asymptotically flat** (same exponential base $\approx 2^{0.188 d}$!). Extrapolating `8x` per `+16` bits hits **`174.16 s` (`> 30 s` timeout)** at `d = 128` (`17,416,192` centi-ms)!
2. **`SHA-256` (`64r_k16_sat/unsat`, `64r_k20_sat`) — SIMD Bit-Sliced Forward AIG Evaluation over Tiny Free Inputs:**
   - Exhaustive `sha256_64r_k16_unsat` (`2^{16} = 65,536` inputs in `10.81 ms`) implies an exact single-core throughput of **`6553600000 / 1081 = 6,062,534` SHA-256 evals/sec** (`~165 ns/eval` — textbook 1-core SIMD bit-sliced forward AIG simulation!).
   - `sha256_64r_k16_sat` (`1.22 ms`, `11.3%` of exhaustive `10.81 ms`) and `sha256_64r_k20_sat` (`2.14 ms`) stop early on witness hit. Notice **`sha256_64r_k20_unsat` and `sha256_64r_k32_*` are absent** (`k=32` appears ONLY at invertible `16r`, which Kissat solves in `9.61 ms`!): at `10.81 ms / 2^{16}`, exhaustive UNSAT scales strictly as $2^k$, crossing the `30 s` timeout at **`k = 28` (`44.28 s` = `4,427,776` centi-ms)** and taking `~11.8 min` at `k = 32`!
3. **`F2-Frob.` (`n = 64 -> 256 -> 1024 -> 4096`) & `Tseitin` (`Vars = 5n/2`, 5-regular expanders):**
   - `F2-Frob.` scales polynomially (`3/1`, `22/3 = 7.33x`, `153/11 = 13.91x` per `4x` jump in `n`, approaching $O(n^{\approx 2})$ bit-packed/sparse $\mathbb{F}_2$ Gauss), while `CMS-C`/`CMS-X` (XOR-Gauss) also solve all 4 (`23 -> 517 ms`) and pure-CDCL Kissat/CaDiCaL blow up.
   - `Tseitin` UNSAT is an exact $\mathbb{Z}_2$ 1-cochain coboundary obstruction (`⧇`, `AUDIT-044`/`051`): `sum(charges) % 2 == 1` certifies UNSAT in $O(|V|+|E|)$ (`< 0.005 ms` at `n = 60`), while Urquhart (1987) forces $2^{\Omega(n)}$ resolution size on expanders for Kissat/CaDiCaL (`tseitin_prism_n400` has constant treewidth `4`, so Kissat/CaDiCaL solve it in `13.60/9.56 ms`).
4. **`Factor` (`28b..40b`), `Masked`, `CEC`, `Comb.` (`php_9_8_unsat`):**
   - `Factor` (`0.08 -> 0.18 ms`) tracks variable count linearly (`671 -> 1325` vars): AIG multiplier cone recognition + sub-millisecond classical factoring for $N < 2^{40}$ (vs. Tseitin-blasted CNF gates for CDCL).
   - `CEC` (`0.01 -> 0.07 ms`) = polynomial backward rewriting over $\mathbb{Z}[x,y]/(x^2-x, y^2-y)$ (`AMulet`), `Comb.` (`php_9_8_unsat`, `0.27 ms`) = 1-line Cutting Planes / PB cardinality refutation defeating Haken (1985) resolution lower bounds.

---

## 3. Modules 2 & 3 — Clean-Room Executable AIG-Hybrid vs. Pure-DPLL Oracle (Separations AND Hard NP Walls)

Running `frobenius_sat_forensics.py` in pure Python stdlib reproduces **BOTH sides of Table 2** directly from first principles:

| Benchmark Family (Clean-Room Oracle) | AIG-Hybrid / Theory Solver | Pure CNF DPLL Solver | Proven Structural Lesson |
|---|---|---|---|
| **Tseitin 3-Regular Prisms (`n = 6, 8, 10`; $\beta_1 = 4, 5, 6$)** | `F2` Gauss / `⧇`: **`0, 0, 0` decisions** (`UNSAT`) | **`15, 31, 63` decisions** (exact $2^{\beta_1}-1$!) | Genuine exponential proof-system separation (`Z2` cohomology `⧇`) |
| **Pigeonhole $\mathrm{PHP}^{m+1}_m$ (`m = 3, 4, 5`)** | Cutting Planes / PB: **`1, 1, 1` step** (`UNSAT`) | **`5, 31, 241` decisions** (factorial blow-up!) | Genuine exponential separation (Cutting Planes vs. Resolution) |
| **Multiplier CEC (`4x4`, `6x6`, `8x8` Array vs. Column-Sum)** | $\mathbb{Z}[x,y]/(v^2-v)$ poly rewrite: **`0` decisions** (`UNSAT`) | Exponential miter branching | Genuine algebraic polynomial-identity separation |
| **AIG Multiplier Factoring (`10403 = 101*103`, prime `65537`)** | Cone extract + factoring + `aig_verify`: **`SAT [101,103]` / `UNSAT`** | CNF multiplier search | Representation asymmetry (`AIG` cone vs. blasted `CNF`) |
| **64-Way Bit-Sliced ARX Preimage (`k = 6, 8`; `k = 14` in R5 tests)** | `64` lanes/batch (`2^{k-6}` batches) | Blind internal-gate branching | Fast for tiny $k$, strict $2^k$ exponential wall for larger $k$ |
| **Unstructured Critical 3-SAT ($\alpha = 17/4 = 4.25$, `n = 12..24`)** | **`0` XOR3 blocks extracted** $\implies$ `100%` DPLL fallback | **`14 -> 18 -> 28 -> 38` decisions** (3 seeds) | **Hard NP-Complete Blind Spot** (omitted from Table 2!) |

---

## 4. Module 4 — Representation Asymmetry, Cross-Link to Arm R7-3 (`Zenodo 23644664`), & Aletheia v1.4.0 Fairness Gate

1. **Representation Asymmetry (`aig.verify(&inputs)`):** Table 2 feeds `Frobenius` structured **AIG circuits with distinguished primary inputs**, while feeding `Kissat`, `CaDiCaL`, and `CMS` **Tseitin-blasted DIMACS CNF** — and omits both **unstructured NP-hard suites** (random 3-SAT $\alpha \approx 4.267$, SAT-Comp Main Track) and **theory-matched / AIG-native competitors** (`ABC` `cec`/`&fraig`, `AMulet2`, `RoundingSat`, `Z3`).
2. **Cross-Link to Arm R7-3 (`AUDIT-070`, Zenodo `23644664` P-NP):** Both `Frobenius` (`Hard-SPN`, `SHA-256 k>=28`, unstructured 3-SAT) and algebraic/spectral solvers (`AUDIT-070`) demonstrate the exact same structural boundary: **polynomial-time algebraic/spectral theories ($\mathbb{F}_2$ Gauss `⧇`, PB, polynomial CEC, Schur/Gram `⧄`) achieve genuine exponential speedups on algebraically structured sub-families, yet collapse back to the exponential NP wall once structure is absent or nonlinear degree grows.**
3. **Aletheia v1.4.0 Anti-Selection-Bias Gate (`verify_sat_benchmark_disclosure`):** Fail-closed disclosure validator catching Table 2's 3 exact disclosure/selection gaps (`BENCH_MISSING_TIMEOUT_SHARE`, `BENCH_MISSING_UNSTRUCTURED_NP`, `BENCH_MISSING_THEORY_COMPETITORS`).

---

## 5. Exact Reproduction Receipts & Falsification Criteria

- **Repro Commands (`studies/frobenius-sat-forensics/`):**
  ```bash
  for f in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
    python3 $f frobenius_sat_forensics.py --json | sha256sum
    python3 $f test_frobenius_sat_r5.py
  done
  # With Foundation-0/aletheia v1.4.0 installed or on PYTHONPATH:
  python3 -B -W error -m aletheia audit-check . \
    --strict-ancestors --scripts frobenius_sat_forensics.py test_frobenius_sat_r5.py --json
  python3 -B -W error -m aletheia mutate frobenius_sat_forensics.py \
    --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_frobenius_sat_r5.py" --json
  ```
- **Falsification Criteria:** Fails if any transcribed cell in `TABLE2_ROWS` disagrees with the pinned `1af95eb5...` JPEG; if any PAR-2 total (`0` centi-ms diff), `102/102` ratio cell, or `Hard-SPN`/`SHA-256`/`F2-Frob` scaling ratio fails independent `Fraction` recomputation; if any clean-room Tseitin ($15,31,63$ vs $0$), PHP ($5,31,241$ vs $1$), CEC, Factor, bit-sliced, or critical 3-SAT check fails; if any float or absolute home-directory path appears in code/JSON/report; or if any R4 / `audit-check --strict-ancestors` / `100.0%` `aletheia v1.4.0 mutate` gate fails.

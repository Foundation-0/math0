# Escher Self-Application Fixed-Point Tomography (*Drawing Hands*) & Negative-Space Dual Complex Miner (*Sky & Water*)

- **Study ID:** `track-s21b-escher-self-application-dual-miner`
- **Oracle Class:** `exact+empirical-corpus` (pure-$\mathbb{Z}/\mathbb{Q}$ exact verification arithmetic over the claim-to-witness tomography reference study, the frozen `Foundation-0/aletheia-corpus` archive snapshot, and the `329`-entry / `333`-atomic-ID historical audit ledger cutoff)
- **Novelty Tier:** `N1` (two strictly executable, zero-metaphor pure-$\mathbb{Z}/\mathbb{Q}$ reflexive verification operators with live read-only disk + `.git` extraction, atomic `dir_fd` `O_DIRECTORY | O_NOFOLLOW` Zone-B I/O hardening, and privacy-clean public redaction of two private-repository ledger identifiers via one-way SHA-256 placeholders)
- **Pinned Certificate (`escher_dual_miner_certificate.json`, `0o600`):**
  - File SHA-256: `a33da6e06e78b33ce65da7c30532713de954e5c1c02dd2969ac10915e783e747`
  - `payload_sha256`: `232a2ba0bdd30d17bbd6bb3350899e46a9a904d03d7510592541f359a3eaa628`
  - `certificate_sha256`: `d9bd7a301919ac636088786048fe77fb386328d9db82d3547016b653a939efb9`

---

## 1. Executive Summary

This study implements and certifies two strictly executable, zero-metaphor, pure-$\mathbb{Z}/\mathbb{Q}$ operators (zero floats on trust paths, zero bare `assert`s, full Zone-B strict I/O hardening with atomic `dir_fd` `O_DIRECTORY | O_NOFOLLOW` ancestor walks and bounded streaming reads) operating read-only over the claim-to-witness tomography reference study, `Foundation-0/aletheia-corpus`, and the historical audit ledger:

1. **Operator 1 — Self-Application Fixed-Point Tomography (*Drawing Hands* / *Print Gallery*):**
   - Live-extracts distinct **`claimed`** (report and `README.md` prose invariants) and **`artifact`** (parsed JSON certificates with verified internal `payload_sha256`/`certificate_sha256`, Python AST of the claim-to-witness checker & auditor, `CORPUS_MANIFEST.json`, `SECRET_SCRUB_RECEIPT.json`, `SHA256SUMS`, embedded torus-knot certificates, and file byte counts) directly from disk — failing closed on `{}` stubs even under matching pins — and applies the Claim-to-Witness Binding Operator ($P_{\mathrm{CTW}}$, Pillars 1–3) across separate `claimed` vs. `artifact` inputs.
   - Certifies **`11 / 11`** executable internal claim-to-witness fixed points ($T(x) = x$: **`5/5`** on the claim-to-witness study + **`6/6`** on `aletheia-corpus`, including `0` hollow survivals under Pillar 3 semantic destruction vs `4/5` and `2/3` survivals on hollow self-hash foils, exact `8/8` half-ULP $\mathbb{Q}$ verification of every `README.md` MiB figure, and exact cross-study union closure of the `336` multi-continent runs against the embedded activity-tomography certificate).
   - Enumerates **`8`** irreducible residual singularities ("central void" $\bigcap_k \ker(P_k)$: **`4`** on the claim-to-witness study + **`4`** on `aletheia-corpus`), each tagged by `witness_basis` (`cryptographic_preimage_impossibility`, `constructive_set_difference`, `external_oracle_boundary`, or `law4_epistemic_scope_note`), yielding exact rational partition **`11/19` (`57.89%`)** internally closable fixed points vs **`8/19` (`42.11%`)** irreducible central void (`5/9` vs `4/9` on the claim-to-witness study; `3/5` vs `2/5` on `aletheia-corpus`).
2. **Operator 2 — Negative-Space Dual Complex Miner (*Sky & Water*):**
   - Deterministically parses ALL **`329`** historical audit ledger entries at the pinned cutoff (**`333`** atomic audit IDs across **`3`** slash-composite rows), preserving mixed-verdict headers and colon section headers: **`232` `VERIFIED`** (`232/329` = `70.52%`), **`96` `PARTIAL/FRAGILE`** (`96/329`), and **`1` `FALSIFIED`** (`1/329`) -> **`97 / 329` (`29.48%`)** negative entries. Two private-repository `VERIFIED` review IDs are redacted to clean public placeholders (`AUDIT-REV-ASMA77-F060-REDACTED1` and `AUDIT-REV-GRAVITY29-CONTINUUM1-REDACTED2`) and matched during live disk parsing strictly through one-way SHA-256 digests so zero private-organization identifiers appear anywhere in source, tests, or certificates.
   - Isolates each negative entry's surgical defect span with bounded linear-time classification (`MAX_EVIDENCE_CHARS = 32_768`, lowercased C literal scans + anchor-guarded `re.ASCII` regexes, inline passing-clause stripping, and multi-line passing-tail stripping across `\n`), classifying **`97 / 97` (`100.0%`, `0` unclassified)** into **`6`** exact algebraic/Zone-B obstruction families (`162` total assignments; exact multiplicity **`162/97` = `1.6701`** families per rejected audit).
   - Computes the exact-$\mathbb{Q}$ **`6 x 6` marginal dual-cut coverage matrix**, pairwise union/intersection matrices, deterministic greedy marginal trajectory (`54/97 -> 75/97 -> 85/97 -> 93/97 -> 96/97 -> 1`), and runs an exhaustive minimal hitting set solver over all $2^6 - 1 = 63$ non-empty family subsets — proving the **UNIQUE minimal hitting set has cardinality `6`** (all `6` obstruction families are strictly irreducible; removing ANY single family drops coverage strictly below `1`).

---

## 2. Hardening & Architecture Highlights

- **Atomic TOCTOU-Safe Zone-B File I/O (`read_strict_utf8_file`):** Walks every ancestor directory via `os.open(..., O_RDONLY | O_DIRECTORY | O_NOFOLLOW, dir_fd=...)`, opens the leaf atomically via `O_RDONLY | O_NOFOLLOW | O_NONBLOCK`, verifies `stat.S_ISREG(os.fstat(fd).st_mode)` (refusing directories, FIFOs, sockets, and devices without blocking), enforces a bounded `65,536`-byte streaming `os.read` loop that never reads more than `max_bytes + 1` bytes (blocking `st_size == 0` virtual procfs bypasses such as `/proc/kallsyms`), rejects symlinked relative `PWD` ancestors, rejects CR/CRLF and invalid UTF-8, and wraps all `OSError` / `PermissionError` failures into typed `EscherMinerError` codes (`FILE_READ_ERROR`, `FILE_NOT_FOUND`, `FILE_TOO_LARGE`, `SYMLINK_FORBIDDEN`, `SYMLINK_ANCESTOR_FORBIDDEN`).
- **Strict Pure-$\mathbb{Z}/\mathbb{Q}$ & Input-Domain Enforcement:** Zero floats on trust paths, zero bare `assert`s, zero `.isdigit()` calls (explicit ASCII digit set), strict canonical lowest-terms rational grammar (`NON_CANONICAL_RATIONAL`), explicit `bit_length() <= 2048` and `620`-digit bounds, strict `type()` checks rejecting `bool`/`int`/`str`/`dict`/`list`/`Path` subclasses, strict CLI `argv` validation (`validate_cli_argv`), required-key validation on public snapshot evaluators (`MISSING_REQUIRED_KEY`), and exact `list`/`tuple` enforcement on `expand_atomic_audit_ids`.
- **Honest Live Git Metadata & Privacy Redaction:** Reads live `git rev-parse HEAD`, `HEAD^{tree}`, and `git ls-files -z` when `.git` is present (with symlink-safe `.git` check) and returns `"unavailable_no_git_dir"` with `None` fields when `.git` is absent (never fabricating `layer3`). Maps the two redacted private-repository review IDs strictly via one-way SHA-256 digests (`_REDACTED_AUDIT_ID_SHA256_MAP`) with zero private-organization strings anywhere in the study.

---

## 3. Operator 1: Self-Application Fixed-Point Tomography (*Drawing Hands* / *Print Gallery*)

### 3.1 Self-Application on Claim-to-Witness Reference Study (`5/9` Closed, `4/9` Central Void)

| Class | ID | Result / Witness Basis | Exact Evidence |
| :--- | :--- | :--- | :--- |
| **Fixed Point** | `FP-S20D-01` | **CLOSED** (`T(x)=x`) | Pillar 1 binds report prose vs JSON cert on family sig counts (`11`, `[0, 3]`), blocking counts (`6`, `[1, 4]`), all 3 pinned digests, and trust-path byte budget (`51,297 + 5,012 + 7,617 = 63,926 B <= 2,000,000 B`) |
| **Fixed Point** | `FP-S20D-02` | **CLOSED** (`T(x)=x`) | Pillar 2 certifies `10/10` Zone-B clauses extracted from report prose vs live AST of `claim_witness_checker.py` & `claim_witness_audit.py` (`0` bare asserts, `0` AST float constants), plus honest `research_prototype` scope & `cross_experiment_anchor` typing |
| **Fixed Point** | `FP-S20D-03` | **CLOSED** (`T(x)=x`) | Pillar 3 semantic destruction gate on strict pinned verifier: **`STRICT_SEMANTIC_VERIFIER`** (`0/5` hollow survivals across all 5 destruction ops) |
| **Fixed Point** | `FP-S20D-04` | **CLOSED** (`T(x)=x`) | Pillar 3 non-vacuity foil on self-hash-only verifier: **`HOLLOW_WITNESS_VERIFIER`** (`4/5` re-signed destructions survive) |
| **Fixed Point** | `FP-S20D-05` | **CLOSED** (under union) | Cross-study composition with `aletheia-corpus` activity-tomography certificate (`torus_activity_certificate.json`, `5223f581...`) matches prose claim `336` against live JSON sum `261 + 19 + 5 + 16 + 15 + 4 + 5 + 1 + 3 + 4 + 3 = 336` |
| **Central Void** | `VOID-S20D-01` | `cryptographic_preimage_impossibility` | `claim_witness_certificate.json` (`9a975b93...`) excludes its own file SHA-256 and report SHA-256 (`7e8d3549...`); verified directly on live bytes |
| **Central Void** | `VOID-S20D-02` | `constructive_set_difference` | Report meta-execution claims (`85/85` mutate kills, `25/25` `BoolOp` kills, `8/8` tests, `audit-check PASS`) appear in report prose and strictly outside `claim_witness_certificate.json` |
| **Central Void** | `VOID-S20D-03` | `external_oracle_boundary` | The `6` `@orda-aska` `siliquant` PR head SHAs & `15` blocking counts are embedded literals requiring external GitHub API verification |
| **Central Void** | `VOID-S20D-04` | `law4_epistemic_scope_note` | Gödelian bootstrap trust anchor: self-applying $P_{\mathrm{CTW}}$ checks internal consistency modulo Python runtime, extraction completeness, and out-of-sample adversarial suites |

### 3.2 Self-Application on `Foundation-0/aletheia-corpus` (`3/5` Closed, `2/5` Central Void)

| Class | ID | Result / Witness Basis | Exact Evidence |
| :--- | :--- | :--- | :--- |
| **Fixed Point** | `FP-CORPUS-01` | **CLOSED** (`T(x)=x`) | Pillar 1 cross-binds `README.md`, `CORPUS_MANIFEST.json`, and `SECRET_SCRUB_RECEIPT.json`: `6` sections sum to `411,516,463 B` (`+ 73,694 B` root/tools = `411,590,157 B`), max single file `40,155,401 B <= 99,614,720 B` (`95 MiB`), `torus-knot-analysis/` `20` files in `[277, 80,940] B`, and all `README.md` section file counts/cutoff/agent/scrub totals match |
| **Fixed Point** | `FP-CORPUS-02` | **CLOSED** (`T(x)=x`) | Pure-$\mathbb{Q}$ verification of all `8/8` `README.md` 2-decimal MiB figures: every figure satisfies $\left|\frac{\text{bytes}}{2^{20}} - \frac{c}{100}\right| \le \frac{1}{200}$ (max exact residual **`25299/5242880` MiB** on `max_single_file`, `0.004825 < 0.005`) |
| **Fixed Point** | `FP-CORPUS-03` | **CLOSED** (`T(x)=x`) | Pillar 2 verifies `4/4` `torus-knot-analysis` tracks extracted from `README.md` vs `CORPUS_MANIFEST.json`, `same_experiment_measurement` scrub attribution (`2,431` files, `132` redactions, `0` live findings), and `research_prototype` archival scope |
| **Fixed Point** | `FP-CORPUS-04` | **CLOSED** (`T(x)=x`) | Pillar 3 semantic destruction gate on strict pinned scrub-receipt verifier: **`STRICT_SEMANTIC_VERIFIER`** (`0/3` hollow survivals) |
| **Fixed Point** | `FP-CORPUS-05` | **CLOSED** (`T(x)=x`) | Pillar 3 non-vacuity foil on hollow self-hash-only verifier: **`HOLLOW_WITNESS_VERIFIER`** (`2/3` re-signed destructions survive) |
| **Fixed Point** | `FP-CORPUS-06` | **CLOSED** (`T(x)=x`) | Exact monotone 4-layer inclusion tower verified live from `SECRET_SCRUB_RECEIPT`, `CORPUS_MANIFEST`, `SHA256SUMS`, and live `.git`: `2,431 < 2,435 < 2,436 < 2,437`, exact set diff `SHA256SUMS - MANIFEST == {"CORPUS_MANIFEST.json"}`, and `"SHA256SUMS"` strictly excluded from itself |
| **Central Void** | `VOID-CORPUS-01` | `cryptographic_preimage_impossibility` | Strict 4-layer hash-inclusion hierarchy `2431 < 2435 < 2436 < 2437`: `CORPUS_MANIFEST.json` excludes itself & `SHA256SUMS`; `SHA256SUMS` excludes itself; `README.md` cannot embed enclosing tree/commit hashes (`f818ef38...` / `2c430372...`) |
| **Central Void** | `VOID-CORPUS-02` | `constructive_set_difference` | Swarm cutoff `#1126` freezes the archived ledger at **`315`** entries (`a8cc58de...`), strictly excluding **`14`** post-cutoff entries (`329 - 315 = 14`) |
| **Central Void** | `VOID-CORPUS-03` | `law4_epistemic_scope_note` | Scanner grammar completeness boundary: zero live matches certifies absence across the `27` declared rule grammars (`45` benign skips), not universal absence of out-of-grammar credential formats |
| **Central Void** | `VOID-CORPUS-04` | `external_oracle_boundary` | External remote state (`INTERNAL` / private visibility, `origin/main @ e63ac7cf`) lies outside local bytes; `README.md` 2-decimal MiBs incur exact nonzero rational rounding residuals up to `25299/5242880 MiB` |

---

## 4. Operator 2: Negative-Space Dual Complex Miner (*Sky & Water*)

### 4.1 Real Historical Audit Partition (`329`-Entry / `333`-Atomic-ID Cutoff)

- **Total Historical Ledger Entries Parsed:** **`329`** (`311` Markdown table rows across both 9-column and 5-column schemas + `18` section blocks; `0` duplicate IDs), expanding to **`333`** atomic audit IDs via **`3`** slash-composite rows.
- **Positive Foreground (`VERIFIED`):** **`232 / 329`** (`70.52%`).
- **Negative Space (`FALSIFIED` + `PARTIAL/FRAGILE`):** **`97 / 329`** (`29.48%`) = **`1`** `FALSIFIED` (`1/329`) + **`96`** `PARTIAL/FRAGILE` (`96/329`).
- **Classification Completeness:** **`97 / 97` (`100.0%`, `0` unclassified)**; **`162`** total family assignments (**`162/97` = `1.6701`** families per rejected audit).

### 4.2 Per-Family Recall, Exclusive Coverage & Ablation Table

| Obstruction Family | Covered (`n/97`) | Exact Recall ($\mathbb{Q}$) | Exclusive (`n/97`) | Exclusive Share ($\mathbb{Q}$) | Coverage Without Family ($\mathbb{Q}$) | Irreducible? |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| **`OBS_HOLLOW_WITNESS`** | `54` | `54/97` (`55.67%`) | `15` | `15/97` (`15.46%`) | `82/97` (`84.54%`) | **YES** |
| **`OBS_ZONEB_IO`** | `46` | `46/97` (`47.42%`) | `13` | `13/97` (`13.40%`) | `84/97` (`86.60%`) | **YES** |
| **`OBS_H1_HOLONOMY`** | `40` | `40/97` (`41.24%`) | `8` | `8/97` (`8.25%`) | `89/97` (`91.75%`) | **YES** |
| **`OBS_STALE_ANCHOR`** | `13` | `13/97` (`13.40%`) | `6` | `6/97` (`6.19%`) | `91/97` (`93.81%`) | **YES** |
| **`OBS_SCOPE_ATTRIBUTION`** | `7` | `7/97` (`7.22%`) | `3` | `3/97` (`3.09%`) | `94/97` (`96.91%`) | **YES** |
| **`OBS_ASSERT_O_BYPASS`** | `2` | `2/97` (`2.06%`) | `1` | `1/97` (`1.03%`) | `96/97` (`98.97%`) | **YES** |

### 4.3 Exact-$\mathbb{Q}$ Marginal Dual-Cut Coverage Matrix $M_{ij} = \frac{|\operatorname{cov}(i) \setminus \operatorname{cov}(j)|}{97}$

| Add Row $i$ $\setminus$ Given Col $j$ | `ZONEB_IO` | `H1_HOLON` | `HOLLOW` | `STALE_ANC` | `SCOPE_ATT` | `ASSERT_O` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **`OBS_ZONEB_IO`** | `0` | `30/97` | `21/97` | `42/97` | `44/97` | `46/97` |
| **`OBS_H1_HOLONOMY`** | `24/97` | `0` | `16/97` | `37/97` | `38/97` | `40/97` |
| **`OBS_HOLLOW_WITNESS`** | `29/97` | `30/97` | `0` | `51/97` | `53/97` | `54/97` |
| **`OBS_STALE_ANCHOR`** | `9/97` | `10/97` | `10/97` | `0` | `12/97` | `12/97` |
| **`OBS_SCOPE_ATTRIBUTION`** | `5/97` | `5/97` | `6/97` | `6/97` | `0` | `7/97` |
| **`OBS_ASSERT_O_BYPASS`** | `2/97` | `2/97` | `2/97` | `1/97` | `2/97` | `0` |

### 4.4 Greedy Marginal Dual-Cut Trajectory & Exact Minimal Hitting Set Theorem

| Step | Dual-Cut Family Added | Marginal Gain | Exact Marginal Gain ($\mathbb{Q}$) | Cumulative Covered | Exact Cumulative Recall ($\mathbb{Q}$) |
| ---: | :--- | ---: | ---: | ---: | ---: |
| `1` | `OBS_HOLLOW_WITNESS` | `+54` | `54/97` | `54/97` | `54/97` (`55.67%`) |
| `2` | `OBS_ZONEB_IO` | `+21` | `21/97` | `75/97` | `75/97` (`77.32%`) |
| `3` | `OBS_H1_HOLONOMY` | `+10` | `10/97` | `85/97` | `85/97` (`87.63%`) |
| `4` | `OBS_STALE_ANCHOR` | `+8` | `8/97` | `93/97` | `93/97` (`95.88%`) |
| `5` | `OBS_SCOPE_ATTRIBUTION` | `+3` | `3/97` | `96/97` | `96/97` (`98.97%`) |
| `6` | `OBS_ASSERT_O_BYPASS` | `+1` | `1/97` | `97/97` | `1` (`100.00%`) |

- **Exact Minimal Hitting Set Result:** Exhaustive search over all $2^6 - 1 = 63$ non-empty family subsets proves `minimal_hitting_set_size = 6`, `minimal_hitting_set_unique = True`, and `all_families_strictly_irreducible = True`. Top-3 dual cuts (`OBS_HOLLOW_WITNESS` + `OBS_ZONEB_IO` + `OBS_H1_HOLONOMY`) already catch **`85/97` (`87.63%`)** of all historical rejections, yet the remaining **`3`** families (`OBS_STALE_ANCHOR`, `OBS_SCOPE_ATTRIBUTION`, `OBS_ASSERT_O_BYPASS`) each carry strictly positive exclusive catches (`6`, `3`, `1`), so NO 5-family subset covers all `97` historical failures.
- **Honest Survivorship Scope Note:** `OBS_ASSERT_O_BYPASS` appears in only `2/97` internal rejections because `aletheia audit-check` pre-filters bare `assert`s *before* studies enter the audit ledger; bare-`assert` `-O` bypasses caught in external upstream repositories appear inside `VERIFIED` entries rather than internal rejections.

---

## 5. Frozen Artifact Manifest & Verification Receipts

### 5.1 Frozen Executable & Certificate Manifest

*(Note: By SHA-256 preimage resistance, this report itself is the 5th file in the study directory and cannot embed its own SHA-256 digest.)*

| File | Lines | Bytes | Mode | SHA-256 |
| :--- | ---: | ---: | ---: | :--- |
| `escher_dual_miner_oracle.py` | `3,033` | `146,185` | `0o644` | `3ab6f2af343a2e1d9bd094b810fecf9f354f285d13d168b0983b3cabb80d757d` |
| `escher_dual_miner_audit.py` | `174` | `7,068` | `0o644` | `29928c0054322618ddc3e1e30e11148b531c3437e460e65ea7f45ad7b1136d45` |
| `test_escher_dual_miner_r5.py` | `1,457` | `90,743` | `0o644` | `475a35363703a4bcb46d15cb469171fa6b1249f55b5d36cb6146939d1a9025bb` |
| `escher_dual_miner_certificate.json` | `1` | `16,090` | `0o600` | `a33da6e06e78b33ce65da7c30532713de954e5c1c02dd2969ac10915e783e747` |

### 5.2 Independent Verification Receipts

All verification checks passed with zero `__pycache__`, zero bare `assert`s, zero AST float literals across all Python files (`oracle`, `audit`, and `test`), zero `.isdigit()` calls, zero CRLF, zero private-organization identifiers (enforced strictly via one-way SHA-256 token-hash checks in both oracle and test suite), and zero personal path leaks:

- **3-Mode Isolated `-I` Parity (`-I -B`, `-I -O -B`, `-I -B -W error`) + `-I -O -B -W error` + `PYTHONHASHSEED=42 -B` (`5/5` bit-identical):**
  - `escher_dual_miner_audit.py --standalone --json`: bit-identical across all `5` modes (`a33da6e06e78b33ce65da7c30532713de954e5c1c02dd2969ac10915e783e747`, matching committed `escher_dual_miner_certificate.json`, `0o600`).
  - `escher_dual_miner_audit.py --check escher_dual_miner_certificate.json`: `OK` across all `5` modes.
  - `test_escher_dual_miner_r5.py`: **`8/8 OK`** across all `5` modes (including scratch `os.mkfifo` refusal, `chmod 000` `FILE_READ_ERROR`, `/proc/kallsyms` streaming read cap, symlinked & surrogate/NUL `PWD`, fail-closed snapshot list validation, and one-way SHA-256 privacy-clean checks).
- **Live `renameat2(RENAME_EXCHANGE)` Atomic TOCTOU Symlink Race:**
  - `911` live concurrent atomic swaps across `1,500` reads -> **`0` decoy escapes, `0` raw exceptions**.
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd` (`-I -O -B -W error`):**
  - `escher_dual_miner_oracle.py`: **`146 / 146` (`100.0%`, `survived=0`, `truncated=False`) KILLED**
  - `escher_dual_miner_audit.py`: **`8 / 8` (`100.0%`, `survived=0`, `truncated=False`) KILLED**
  - Combined: **`154 / 154` (`100.0%`, `0` survivors) KILLED**
- **Exhaustive Whole-File DFS AST `BoolOp` Sweep (`OP_SWAP` + `SUBCOND_DEL`, `-I -O -B -W error`):**
  - `escher_dual_miner_oracle.py`: **`40 / 40` `OP_SWAP` (`100.0%`, `surv=[]`)** + **`90 / 90` `SUBCOND_DEL` (`100.0%`, `surv=[]`)** = **`130 / 130` (`100.0%`) KILLED**
  - `escher_dual_miner_audit.py`: **`0 / 0`** (`0` `BoolOp` nodes, `surv=[]`)
- **Live Zone-B Fuzzer (`zone_b_fuzzer.py`):**
  - **`23 / 23` CLI + `18 / 18` Memory = `41 / 41` (`100.0%`, `bypasses=0`, `crashes=0`) PASS**
- **`aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts escher_dual_miner_audit.py test_escher_dual_miner_r5.py`:** `PASS` (`5` files, `2/2` R4, `0` findings, `0` leaks, `0` CRLF, `0` bare asserts).

```bash
cd studies/track-s21b-escher-dual-miner
python3 -I -B escher_dual_miner_audit.py --standalone --json | diff -u escher_dual_miner_certificate.json -
python3 -I -O -B -W error escher_dual_miner_audit.py --check escher_dual_miner_certificate.json
python3 -I -O -B -W error test_escher_dual_miner_r5.py -v
```

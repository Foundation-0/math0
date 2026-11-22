# Aletheia v2.1 Proposal: Law 1b — Exhaustive Serendipity & Unmerged-PR Portal Mining

**Proposal Target:** `spec/proposals/SERENDIPITY_AND_UNMERGED_PR_MINING.md` (`aletheia.spec.v2.1` draft)  
**Standing:** `proposed` (drafted from Track S12 live 8-repository read-only mining dossier; awaiting external review before canonical promotion)  
**Honest Novelty Standing:** `N0` protocol formalization over upstream open/closed-unmerged mechanisms  
**Reference Implementation:** [`serendipity_pr_oracle.py`](serendipity_pr_oracle.py) (`certify_law1b_serendipity_mining`, `aletheia.law1b.v1`), [`serendipity_pr_certifier.py`](serendipity_pr_certifier.py)

---

## 1. Motivation: Closing Anti-Pattern `CS-15` (Merged-Only Tunnel Vision)

Standard research audits and repository reviews inspect only a repository's default branch (`main`) and published releases. Across the eight active repositories audited in Track S12 (`1,437` total PRs fetched read-only on 2026-11-22), **`387 / 1,437` (`129 / 479`, ~26.9%)** of pull requests are **unmerged** (`296` open + `91` closed-unmerged).

Empirical mining of those unmerged branches demonstrates that high-signal mathematical defects, negative controls, lexer/parser security counterexamples, honest multi-seed refutations, pre-freeze protocol cancellations, and alternate architectural prototypes frequently live *outside* `main`:

- **Closed-unmerged bugfixes and exact reproducers** (e.g., `NandhaKishorM/laya#698` nearest-rank p95 overshoot at every multiple of 20; `laya#693`/`#683` self-cancelling minimum-offset drop; `laya#1411` `10**400` JSON `OverflowError`; `Moissanite-Labs/exo#428` presence-file key forgery; `exo#490` backtick backslash-newline collapse; `exo#402` `gh` option-value target smuggling).
- **Closed-unmerged architectural prototypes** (e.g., `chuanqisun/spaceship#5` browser WebGPU hidden-state steering & attention-box logit biasing with side-by-side unsteered counterfactual replay; `spaceship#3` 4-pane parallel comparison arena; `spaceship#2` `pointerId`-scoped multi-touch gesture arbitration).
- **Open empirical refutations, cancellations, and exact tools** (e.g., `laya#1465` micro-batch item-count weighting closing CS-10 denominator collapse; `laya#1210` 3-seed refutation of single-seed soft-CE gain; `Moissanite-Labs/weft-loom#25` pre-freeze cancellation of Experiment C; `weft-loom#44` sign-lineage exact chance law + evasion; `NandhaKishorM/vegaml#57` direct span-pooling kernel equivalence; `Foundation-0/math0#3` stdlib `GF(q)` minimum-distance certifier; `Moissanite-Labs/heedle` Issues `#2/#3/#6` & PR `#8`).

Inspecting only `main` — or even inspecting only `open` PRs while ignoring `closed_unmerged` PRs — creates a systematic discovery blind spot:

| Anti-Pattern ID | Name | Observable Symptom | Structural Remedy |
|---|---|---|---|
| **`CS-15`** | **Merged-Only Tunnel Vision** | Portal audit reads only `main` / releases (or `open` PRs only), silently skipping closed-unmerged PRs, drafts, and open issues where counterexamples, refutations, and discarded prototypes live. | Enforce **Law 1b**: systematically enumerate `open` + `closed_unmerged` PRs and issues on every portal repository (strictly read-only), pin snapshots by SHA-256, and extract exact non-metaphorical witnesses under Law 5. |

---

## 2. Canonical Statement of Law 1b

> **Law 1b — Exhaustive Serendipity & Unmerged-PR Portal Mining:**
> 1. **Leave no read-only portal path unexplored:** Whenever a portal repository, anomaly, or cross-domain operator surfaces, immediately spin up a strictly read-only exploration pass (`external_writes == 0`) without stalling for permission. Serendipity cannot be predicted in advance; gating read-only curiosity on pre-justified payoff reproduces the Cave-Shadow trap.
> 2. **Mine open AND closed-unmerged PRs (plus issues/discussions) on every portal:** Every portal intake MUST query `state=all` PRs, separate `merged`, `open`, and `closed_unmerged` counts explicitly, and inspect high-signal items from **both** `open` and `closed_unmerged` buckets whenever present.
> 3. **Couple serendipity to Law 5 & Law 4 (zero metaphor inflation):** Every mined PR item is classified explicitly as either an **`EXECUTED_EXACT_WITNESS`** (backed by an independent zero-float executable reproducer and negative control) or a **`CATALOGED_LEAD`** (strictly capped at honest novelty **`N0`** until independently executed and prior-art checked).

---

## 3. Fail-Closed Machine-Checkable Guards (`G-1b.1` – `G-1b.4`)

Implemented in pure Python 3 stdlib (`int` / `Fraction`, zero floats, zero bare asserts) by `certify_law1b_serendipity_mining(spec)` (`schema: aletheia.law1b.v1`):

1. **`G-1b.1` — Anti-Merged-Only & Anti-Open-Only Blind-Spot Guard:**
   - Every scanned repository row MUST satisfy `open + closed_unmerged + merged == fetched` with strict non-negative integers and `fetched > 0`.
   - If `sum(closed_unmerged) > 0` across scanned repositories, mined entries MUST include at least one `closed_unmerged` PR (`L1B_CLOSED_UNMERGED_BLIND_SPOT`).
   - If `sum(open) > 0` across scanned repositories, mined entries MUST include at least one `open` PR (`L1B_OPEN_PR_BLIND_SPOT`).
2. **`G-1b.2` — Exact Provenance Pinning & Closed Mechanism Taxonomy:**
   - Every repository row pins a non-uniform 64-char lowercase hex `prs_json_sha256` of its frozen `state=all` PR listing.
   - Every mined PR entry pins `(repo, number)` uniquely (case-insensitive repo match, positive integer PR number), valid `status` in `{"open", "closed_unmerged"}`, non-uniform 40-char lowercase hex `head_sha`, non-uniform 64-char lowercase hex `snapshot_sha256`, clean-ASCII `operator_summary`, and `mechanism_class` from the closed 9-class taxonomy (`DENOMINATOR_OR_WEIGHT_BIAS`, `QUANTILE_OR_INDEX_BOUNDARY`, `AFFINE_OR_RANGE_PROJECTION`, `ALGEBRAIC_KERNEL_EQUIVALENCE`, `LEXER_OR_PARSER_SECURITY_BYPASS`, `CRYPTO_PIN_OR_STATE_MACHINE`, `EMPIRICAL_REFUTATION_OR_FREEZE`, `INTERNAL_STEERING_OR_ARCHITECTURE`, `EXACT_CERTIFIER_OR_DOMAIN_TOOL`).
3. **`G-1b.3` — Non-Metaphorical Operator Discipline:**
   - At least one mined entry MUST have `evidence_standing == "EXECUTED_EXACT_WITNESS"` (`L1B_ZERO_EXECUTED_WITNESSES`).
   - Any entry with `evidence_standing == "CATALOGED_LEAD"` MUST have `honest_novelty == "N0"` (`L1B_LEAD_CANNOT_CLAIM_ABOVE_N0`).
4. **`G-1b.4` — Zero-Write Portal Integrity:**
   - `external_writes` MUST equal strict integer `0` (`L1B_NONZERO_EXTERNAL_WRITES`).

> **Declared-Record Scope Boundary:** Consistent with Aletheia v2.0 (`aletheia/gates_v2.py` & `spec/LAWS_AND_GATES.md`), `certify_law1b_serendipity_mining(spec)` certifies that a caller-supplied Law-1b mining record is well-formed and satisfies guards `G-1b.1`–`G-1b.4`. It does **not** verify from the dict alone that the referenced GitHub snapshots exist on disk or match the pinned digests; live byte-level SHA-256 verification of the frozen intake JSON files is performed separately by `serendipity_pr_certifier.py --live --intake-root <dir>`.

---

## 4. Operational Law-1b Portal-Mining Checklist

1. **Snapshot (Read-Only):** Query `repos/{owner}/{repo}/pulls?state=all&per_page=100` (paginated) plus relevant open issues; save canonical JSON into an isolated `intake-*` directory with zero writes to external repositories.
2. **Triage Both Unmerged Buckets:** Filter out automated dependency-bump noise while retaining every algorithmic, numerical, evaluation, calibration, parser/security, state-machine, and architectural PR in **both** `open` and `closed_unmerged`.
3. **Pull Deep Diffs:** Fetch full PR bodies, `head.sha`, and file patches for all high-signal unmerged candidates; write a SHA-256 `DEEP_MINING_MANIFEST.json`.
4. **Extract Exact Operators (Law 5):** For every mathematical, numerical, or security mechanism, write an independent pure-$\mathbb{Z}/\mathbb{Q}$ witness reproducing BOTH the buggy/vulnerable behavior and the repaired invariant (zero shared code, zero floats).
5. **Certify & Gate (`R1`–`R7`):** Run 3-mode isolated `-I` parity (`-I -B`, `-I -O -B`, `-I -B -W error`), `100.0%` `aletheia mutate --max-mutants 0`, AST `BoolOp` sub-clause sweep, and `aletheia audit-check --strict-ancestors --safety-scan`.
6. **Feed Findings Back Into Active Tracks:** Route verified lexer/parser bypasses to `aletheia.safety` v2.1, denominator/quantile/projection fixes to ML evaluation harnesses, and architectural mechanisms (e.g., `spaceship#5`, `heedle#6`) to dedicated follow-on exploration tracks.

---

## 5. Concrete `aletheia.safety` v2.1 Hardening Roadmap Derived From Unmerged `exo` PRs

Law-1b mining of unmerged `Moissanite-Labs/exo` PRs immediately yielded four concrete, verified shell/CLI static-analysis upgrades for `aletheia.safety` v2.1 (all modeled deterministically in `serendipity_pr_oracle.py` M5):

1. **Backtick backslash-newline stripping (`exo#490` [closed_unmerged]):** Strip odd backslash-newline pairs inside backtick command substitutions *before* splitting segments so split command tokens cannot evade `CYA-GAP-03`.
2. **Unquoted heredoc logical-line terminators (`exo#911` [open]):** Join physical lines ending in odd backslash runs before comparing unquoted heredoc delimiters, and strip leading tabs for `<<-` only on the joined logical line (not second physical continuation lines).
3. **Full GNU/BSD `xargs` getopt option parsing (`exo#1136` [open]):** Parse long options (`--max-args`, `--arg-file`, unambiguous prefixes like `--max-a`), clustered short options ending in an argument-taking flag (`-rn 1`, `-tP 4`), and BSD flags (`-J`, `-R`, `-S`) so option values are never mistaken for the invoked command name.
4. **Operand-only CLI target resolution (`exo#402` [closed_unmerged]):** Resolve target repositories strictly from explicit `-R`/`--repo` flags or positional URL operands, ignoring URLs embedded inside `--body`, `--comment`, or `--duplicate-of` option values.

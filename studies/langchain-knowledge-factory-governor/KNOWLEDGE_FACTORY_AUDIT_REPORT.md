# AUDIT-076: Architectural Isomorphism, Trust-Boundary Tomography, and Verified Curator Governor for LangChain's Company Harness & Knowledge Factory

- **Audit ID:** `AUDIT-076` (Wave 2 Round 8, Arm `R8-5`)
- **Governance Standard:** `Foundation-0/aletheia v1.4.0` (Laws 1–5; zero-float pure-$\mathbb{Q}$ trust path; `100.0%` R5 AST mutation kill across BOTH Python modules; `4/4` isolated `-I` R4 bit-identical determinism)
- **External Write Policy:** **STRICTLY 100% READ-ONLY** (`0` external PRs/issues/comments; `0` anti-bot bypasses)
- **Deliverables (`symbiosis/round8/arm5-langchain-knowledge-factory/`):**
  - `knowledge_factory_governor.py` — Pure Python 3 stdlib zero-float **3-Role Verified Knowledge Factory Curator Governor** (`KF-01..KF-05` + SHA-256 hash-chained ledger)
  - `knowledge_factory_audit.py` — Live verbatim SHA-256 & 12-anchor source verifier + exact proof & certificate generator (`--standalone` supported)
  - `test_knowledge_factory_r5.py` — R5 refusal-site, red-team boundary, & exact-invariant test suite
  - `knowledge_factory_certificate.json` — Canonical float-free exact rational certificate

---

## 1. Pinned Read-Only Primary Sources & Verbatim Anchors

Both LangChain primary essays were fetched strictly read-only, SHA-256 pinned, and verified across **`12 / 12`** verbatim textual anchors by `knowledge_factory_audit.py`:

| Artifact | Canonical Source | Exact SHA-256 Digest |
|---|---|---|
| `components_building_company_harness.html` | `https://www.langchain.com/blog/components-building-company-harness` (Harrison Chase & Caspar Broekhuizen, Oct 24, 2026) | `cc6cccb9f73f419e08dc2287085df319d37e0f4f0a116c1e11ba89e30e491d12` |
| `components_building_company_harness_text.txt` | Extracted verbatim text of Essay 1 (`252` lines; anchors `CH-01..CH-07` at lines `1, 140, 162, 165, 171, 174, 179`) | `2abd77952f0324c5fda93be797095bfb69e5232fdbb9569e1f1b69c97d48d598` |
| `knowledge_factory.html` | `https://www.langchain.com/blog/knowledge-factory` (Harrison Chase, Nov 21, 2026) | `716c69e30837267385fba2cae6b112f97fffabce7146adffcece785cd1e1842d` |
| `knowledge_factory_text.txt` | Extracted verbatim text of Essay 2 (`237` lines; anchors `KF-01..KF-05` at lines `143, 154, 165`) | `ca5f914cdbaf84318a893fb388aba493494587ab6eaaf39fc88b7017bf7a7ae0` |

---

## 2. Law-2 Steelman Credit & Exact Isomorphism with The Aletheia Method

LangChain's two essays independently arrive at **four genuine architectural laws** that align structurally with `Foundation-0/aletheia v1.4.0`, `AUDIT-069R` (Tao Observability Gate), and `Moissanite-Labs/warp-drive#13/#15`:

| LangChain Component (Verbatim Anchor) | Structural Role | Verified Aletheia / Expedition Counterpart | Exact Missing Trust Boundary |
|---|---|---|---|
| **Worker Flagging vs. Background Curator** (`knowledge_factory_text.txt:153-154`: *"Asking agents — who are mainly trying to accomplish their own goals — to properly update and maintain this knowledge will cause it to become unruly and full of contradictions."*) | Role split between task execution and memory curation | Worker vs. Curator / Cartographer separation | **2-role loop only** — Curator is both *Author* and *Approver*, lacking an independent **Adversarial Verifier** (`KF-05`) |
| **3 Knowledge Layers** (`knowledge_factory_text.txt:143-145`: `Skills`, `Domain knowledge`, `Data access guidance`) | Procedural, semantic, and query-routing persistent memory | Aletheia skills/rules + Ring-0 frozen contracts | **Zero Ring-0 immutability** separating identity/verifier/sandbox rules from Curator-mutable skills (`KF-04`) |
| **Interactive Identity Scopes** (`components_building_company_harness_text.txt:162,165`: DM-only OBO email; whitelisted Twitter posting) | Confused-deputy control on synchronous Slack surfaces | `warp-drive#15` trust-boundary allowlist | **Bypassed asynchronously** by nightly Curator reading shared Slack/traces and writing global executable skills (`KF-01`/`KF-04`) |
| **Tiered Memory + Secret Proxy + Ambient Crons** (`components_building_company_harness_text.txt:171,174,179`) | Global/User memory, sandboxed auth, scheduled background agents | `warp-drive#13` Ring-0 lock & `aletheia` R4/R5 ledger | **Agent self-classifies memory tier** (L171: *"Agents decide which facts they want to remember to which level of memory"*); zero Biba/BLP lattice, zero CAS/DAG lock, zero Goodhart outside-anchor (`KF-01..KF-03`) |

---

## 3. Five Exact Pure-Q & Finite-State Failure Modes of an Unverified Curator Loop (`KF-01..KF-05`)

When Essay 1's **Company Harness** (external lead emails via `GTM Agent`, shared Slack channels, fixed service-account credentials, user-created crons) is composed with Essay 2's **Knowledge Factory** (a nightly Curator reading *all raw sources + agent traces + worker flags* and directly updating global *Skills* and *Data Access Guidance*), five exact mathematical and security failure modes emerge:

### 3.1 `KF-01` — Indirect Prompt Injection, Cross-Tier Trace Poisoning, & Private-DM Leakage (Exact Biba × Bell-LaPadula Lattice + Blast-Radius Bound)

- **Source Mechanism:** `GTM Agent` *"Monitors and responds to emails, to new qualified leads"* (`CH-02`, L140); *"Agents decide which facts they want to remember to which level of memory"* (`CH-05`, L171); the nightly Curator *"should have access to all the raw sources of data (Notion, Slack, etc)"* and *"agent traces"* (`KF-03`/`KF-04`, L154) and *"updates the relevant skills accordingly"* (`KF-05`, L165).
- **Exact Lattice Violation:** Modeling trust as an ordered Biba integrity lattice (`UNTRUSTED_EXTERNAL = 0 < SHARED_CHANNEL = 1 < VERIFIED_EMPLOYEE_DM = 2 < ADMIN_WHITELIST = 3 < RING0_IMMUTABLE = 4`) crossed with a Bell-LaPadula confidentiality lattice (`PUBLIC_GLOBAL = 0 < TEAM_SHARED = 1 < USER_PRIVATE_DM = 2 < SECRET_CREDENTIAL = 3`):
  1. **Biba Integrity Escalation (`Δ_I = +3`):** An untrusted external lead email (`integrity = 0`) entering agent traces and distilled into a `GLOBAL_SKILL` (`required_integrity = 3`) elevates untrusted data into executable procedural instructions (`REJECTED_GOVERNOR`: `KF01_BIBA_INTEGRITY_ESCALATION`).
  2. **Bell-LaPadula `*-Property` Confidentiality Leak (`Δ_C = +2`):** Promoting a `USER_PRIVATE_DM` (`conf = 2`) trace into a global store (`github_skills` bound via `policy.store_tiers` to `GLOBAL_SKILL`, `max_conf = 0`) leaks private user context across the entire organization — blocked **even when `human_admin_countersigned = True` or when a proposal attempts tier/store spoofing (`target_tier = USER_MEMORY` against `github_skills`)** (`REJECTED_GOVERNOR`: `KF01_BLP_CONFIDENTIALITY_LEAK` / `KF01_STORE_TIER_MISMATCH`).
- **Exact Pure-$\mathbb{Q}$ Fleet Blast-Radius Amplification:** A single poisoned global skill read by $W = 10$ workers across $T = 12$ ambient scheduled runs ($120$ total exposures) with per-run trigger probability $p = 1/20$ yields:
  - Exact expected compromised executions: $E[C] = W \cdot T \cdot p = \mathbf{6/1}$ (`6.0000`)
  - Exact probability of $\ge 1$ compromised execution: $1 - (19/20)^{120} = \mathbf{0.997878}$ (`99.7878%`)

### 3.2 `KF-02` — Goodhart Self-Reinforcement & Trace-Echo Drift (Exact Pure-$\mathbb{Q}$ Pythagorean Divergence)

- **Source Mechanism:** The Curator optimizes procedural skills from internal worker traces and worker-flag frequency (proxy error $E_{\text{proxy}, t}$) with no frozen orthogonal outside-anchor evaluation suite ($E_{\text{out}, t}$).
- **Exact Pure-$\mathbb{Q}$ Proof (`simulate_goodhart_curator_drift_exact`):** Starting from initial proxy error $E_{\text{proxy},0} = 1$, orthogonal outside-anchor ground-truth error $E_{\text{out},0} = 1/4$ (total Pythagorean error $E_{\text{total},0} = 5/4$), with per-step proxy reduction rate $\alpha = 1/4$ and orthogonal policy drift $\delta = 1/2$ over $4$ nightly curation cycles:
  - An **unverified Curator** accepts **`4 / 4`** updates (`E_proxy` drops monotonically from `1` to `(3/4)^4 = 81/256` — an apparent **`175/256 = 68.3594%`** improvement!).
  - Meanwhile, exact total error climbs from **`5/4` (`1.250000`)** to **`657/256` (`2.566406`)** — a **`+337/320` (`+105.3125%`)** true-error explosion (`goodhart_inversion_occurred = True`).
  - **Governor Resolution:** Mirroring `aletheia/ratchet.py:54-80` (Pre-Adaptation Goodhart Latch), `evaluate_curator_proposal` checks both `outside_err_after > outside_err_before` (`KF02_GOODHART_OUTSIDE_ANCHOR_DRIFT`) and `proxy_err_after > proxy_err_before` (`KF02_PROXY_REGRESSION`), halting drift at **step `1`** and rejecting any proxy or net-error regression.

### 3.3 `KF-03` — Multi-Worker Race, LWW Oscillation, Cross-Store Split-Brain, & Skill Contradiction Cycles

- **Source Mechanism:** Multiple team agents (`GTM`, `OpenSWE`, `Content Studio`, Finance) asynchronously flag overlapping domain concepts stored across heterogeneous backends (`GitHub`, `Notion`, `Context Hub`, `Neo4j`, `knowledge_factory_text.txt:155`).
- **Exact Finite-State & Graph Failures Certified:**
  1. **LWW Flip-Flop Oscillation:** Simultaneous conflicting flags for `(company_wiki_domain, metric.arr_definition)` (`W-SALES-ARR -> gross_bookings_incl_services` vs. `W-FINANCE-ARR -> net_recognized_recurring_only`) cause a period-2 non-convergent oscillation under unguarded Last-Writer-Wins. `audit_multi_worker_batch_conflicts` halts the batch (`lww_oscillation_blocked = True`, `conflict_count = 1`) and escalates to the domain owner.
  2. **Cross-Store Split-Brain:** A proposal referencing stale `base_revision_sha256 = 9999...` against `context_hub_data_access` (`expected = 2222...`) is rejected (`KF03_STALE_CAS_REVISION` / `stale_cas_proposals = ["W-STALE-HUB"]`).
  3. **Skill Dependency Cycle:** Adding edge `bigquery_fetch -> revenue_report` onto existing `revenue_report -> bigquery_fetch` forms a directed dependency cycle; exact 3-color DFS (`detect_skill_graph_cycle_exact`) produces witness `["bigquery_fetch", "revenue_report", "bigquery_fetch"]` and blocks promotion (`KF03_SKILL_DEPENDENCY_CYCLE`).

### 3.4 `KF-04` — Privilege Escalation & Confused-Deputy Amplification via Data-Access / Cron / Ring-0 Mutation

- **Source Mechanism:** Essay 1's fixed-credential tools (`GTM Agent` Salesforce, `OpenSWE` GitHub app, `Content Studio` Twitter, `LangSmith Sandboxes` secret proxy) and self-created ambient crons (`CH-07`, L179) execute Essay 2's Curator-editable `Skills` and `Data Access Guidance`.
- **Exact Attack Witness & Resolution:** A proposal requesting an extra scope (`salesforce:export_all_pii`), an unallowlisted endpoint (`https://evil-exfil.example/collect`), an unapproved ambient cron trigger (`creates_cron_trigger=True, cron_owner_approved=False`), and a nested case-varied Ring-0 key (`Secret_Proxy_Allowlist`) is fail-closed rejected with all 4 orthogonal codes (`KF04_RING0_IMMUTABLE_TAMPER`, `KF04_SCOPE_PRIVILEGE_ESCALATION`, `KF04_ENDPOINT_ALLOWLIST_VIOLATION`, `KF04_UNAPPROVED_AMBIENT_CRON`).

### 3.5 `KF-05` — 3-Role Separation of Duties, Tao Observability Process Gate (`AUDIT-069R`), & Hash-Chained Ledger

- **Source Mechanism:** LangChain's 2-role loop (`Worker -> Curator`) permits the Curator to self-approve its own edits without an independent Adversarial Verifier or verifiable process receipts.
- **Exact Resolution:** `evaluate_curator_proposal` enforces strict 3-role separation (`verifier_id != curator_id` AND `verifier_id != worker_id`), requires all `AUDIT-069R` Tao process gates (`frozen_contract_sha256` 64-hex, `split_leakage_count == 0`, `OFFLINE_OR_ALLOWLIST_VERIFIED`, `r4_isolated_parity_runs >= 3`, `r5_mutation_killed == r5_mutation_total > 0`), and records every promotion/rejection in a tamper-evident SHA-256 hash-chained ledger (`build_ledger_entry` + `verify_knowledge_ledger_chain`, rejecting sequence skips, `bool`-as-`int` `seq` forgeries, chain forks, and hash tampering).

---

## 4. Law-4 Epistemic Hygiene & `N0` / `N1` Quarantine

- **`N1` (Verified Directly in This Audit):**
  - Verbatim SHA-256 digests and `12/12` line-numbered anchors from both published LangChain blog posts (`Oct 24, 2026` & `Nov 21, 2026`).
  - Exact pure-$\mathbb{Q}$ mathematical witnesses for `KF-01` blast radius (`6/1`, `1-(19/20)^120 = 0.997878`), `KF-02` Goodhart inversion (`175/256` proxy drop vs `+337/320` total error increase, halt at step 1), `KF-03` batch conflict/CAS/DFS cycle proofs, `KF-04` monotone capability/Ring-0 attenuation, and `KF-05` 3-role + Tao gate + SHA-256 ledger chain.
- **`N0` (Explicitly Quarantined — NOT Claimed):**
  - We do **NOT** claim access to LangChain's proprietary closed-source internal implementations of `LangSmith Fleet`, `LangSmith Engine`, `LangSmith Context Hub`, or `Managed Deep Agents` beyond the two public blog posts; internal mitigations undocumented in those essays are unobservable (`N0`) and explicitly outside scope.
  - We do **NOT** claim that any live LangChain production agent has suffered an actual exploit; our proofs characterize architectural failure modes of an **unverified 2-role Curator loop** as specified in the published design and provide a drop-in executable Governor closing them.
  - We do **NOT** inspect the two `HTTP 403 zse_ck` Zhihu URLs (`BLOCKED_ANTIBOT` per Round-8 compliance policy).

---

## 5. Reproduction Commands & Falsification Criteria

```bash
# 1. Exact pure-Q unit, red-team, & refusal-site test suite (isolated mode)
PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B -W error test_knowledge_factory_r5.py

# 2. Live verbatim source audit & canonical zero-float certificate (or --standalone)
PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B -W error knowledge_factory_audit.py --write-cert knowledge_factory_certificate.json
PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B -W error knowledge_factory_audit.py --standalone > /dev/null

# 3. Aletheia v1.4.0 R5 AST refusal-site mutation audit on BOTH modules (100.0% kill, 0 survivors)
PYTHONDONTWRITEBYTECODE=1 python3 -B -W error -m aletheia mutate knowledge_factory_governor.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_knowledge_factory_r5.py" --json
PYTHONDONTWRITEBYTECODE=1 python3 -B -W error -m aletheia mutate knowledge_factory_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_knowledge_factory_r5.py" --json

# 4. Aletheia v1.4.0 full hygiene, AST, zero-float JSON & R4 parity gate
PYTHONDONTWRITEBYTECODE=1 python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts knowledge_factory_audit.py test_knowledge_factory_r5.py --json
```

**Falsification Criteria:** Any finding is immediately falsified if:
1. Any of the `4` pinned SHA-256 digests or `12/12` verbatim anchors fails against the downloaded LangChain blog captures;
2. Any exact rational identity (`6/1`, `1-(19/20)^120`, `175/256`, `657/256`, `337/320`) fails independent recomputation;
3. Any adversarial bypass (self-approval, Biba elevation, BLP private-DM leak, Goodhart outside-anchor drift, stale CAS, LWW conflict, skill cycle, scope/endpoint/cron escalation, Ring-0 nested key, `str`-as-sequence, `bool`-as-`int` ledger forgery, float injection) succeeds against `knowledge_factory_governor.py`;
4. Any mutant in EITHER `knowledge_factory_governor.py` OR `knowledge_factory_audit.py` survives `aletheia v1.4.0 mutate`, or `4/4` isolated `-I` R4 / `audit-check --strict-ancestors` fails.

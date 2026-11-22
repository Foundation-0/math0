# Track S11 (`AUDIT-110`): Erlang/OTP Supervision Tree Semantics — Pure-$\mathbb{Z}/\mathbb{Q}$ State-Machine Oracle & `exo#1200` / `aletheia v2.1+` Design Blueprint

- **Audit ID:** `AUDIT-110` (`track-s11-erlang-otp-supervision`)
- **Schema Version:** `erlang-otp-supervision-oracle/v1`
- **Certificate `canonical_sha256` (inner body):** `338d6b1619e6b5aeac8ae772f8e45459e2153a633f162695553472ec17fae87d`
- **Certificate File SHA-256 (`erlang_otp_supervision_certificate.json`, 4-mode `-I` parity):** `23757e7d665aeb4255bf6ffa81011355952b894c07836ffbb630399ae52570fe`
- **Arithmetic & Runtime Hygiene:** Pure Python 3 stdlib (`int` / `fractions.Fraction`), `0` IEEE-754 `float`s, `0` bare `assert` statements, `0` external writes, LF-only.

---

## 1. Honest Law-4 Novelty Tier & Primary Literature Quarantine

| Layer | Law-4 Tier | Scope & Primary Attribution |
|---|---|---|
| Classical Erlang/OTP supervision semantics (restart policies, restart strategies, sliding-window intensity/period escalation, `link` / `trap_exit` / `monitor` signal semantics) | **`N0`** | Joe Armstrong (2003), *Making reliable distributed systems in the presence of software errors*, PhD Thesis, Royal Institute of Technology (KTH), Stockholm (`urn:nbn:se:kth:diva-3658`, `TRITA-IMIT-LECS AVH 03:09`, `ISRN KTH/IMIT/LECS/AVH-03/09-SE`); Joe Armstrong, Robert Virding, Claes Wikström & Mike Williams (1996), *Concurrent Programming in ERLANG* (2nd ed., Prentice Hall, `ISBN 978-0-13-508301-7`); Erlang/OTP `stdlib/src/supervisor.erl`. |
| Standalone durable attempt ledger & zero-retry `SupervisionPolicy` | **`N0`** | `Moissanite-Labs/exo` PR `#1200` (`src/exo/core/group_supervision.py`, pinned commit `ccdc929ace0a62152e23e10b0fd219d76df7b6f1`, SHA-256 `b5c38a6f60151093eb320e431577fe48f1f5022c66058b87f99f55559c38f9e8`). |
| Pure-$\mathbb{Z}/\mathbb{Q}$ executable soundness certifier + Frozen-Snapshot `rest_for_one` Non-Churn bridge for `exo#1200` & `aletheia v2.1+` Two-Zone Hybrid Swarms | **`N1`** *(engineering/audit)* | Executable zero-float state-machine certifier (`erlang_otp_supervision_oracle.py`), fail-closed certificate validator, 10 explicit must-fail controls, and formal composition of `exo#1200` `I2` sticky-stop/pre-dispatch gates with OTP `rest_for_one` and unidirectional `monitor` isolation. |

**Law-5 Scope Boundary:** Every statement below specifies an exact finite-state transition function, rational inequality, or process-signal propagation rule verified by deterministic execution. This artifact verifies finite-state transition traces and fail-closed schema invariants in pure Python; it does not verify live OS signal delivery, BEAM VM scheduler timing, or live multi-host network partitions.

---

## 2. Certified Five-Pillar Results (Exact Matches to `erlang_otp_supervision_certificate.json`)

### Pillar 1 — Exact $3 \times 3$ Restart Policy $\times$ Exit Reason Matrix (`p1_restart_policy_matrix`)

Exact predicate `otp_should_restart(policy, exit_reason)` over `{permanent, transient, temporary}` $\times$ `{normal, shutdown, abnormal}` (`9/9` cells verified: `4` restart, `5` drop):

| `policy` \ `exit_reason` | `normal` | `shutdown` | `abnormal` |
|---|---|---|---|
| `permanent` | `restart` (`true`) | `restart` (`true`) | `restart` (`true`) |
| `transient` | `drop_child` (`false`) | `drop_child` (`false`) | `restart` (`true`) |
| `temporary` | `drop_child` (`false`) | `drop_child` (`false`) | `drop_child` (`false`) |

- **Must-Fail Control 1 (`must_fail_temporary_restarted`):** Observing `restarted=True` on `(temporary, abnormal)` is rejected with `ERR_TEMPORARY_CHILD_RESTARTED`.
- **Must-Fail Control 2 (`must_fail_transient_clean_exit_restarted`):** Observing `restarted=True` on `(transient, normal)` or `(transient, shutdown)` is rejected with `ERR_TRANSIENT_CLEAN_EXIT_RESTARTED`.

### Pillar 2 — All Three OTP Restart Strategies & Frozen-Snapshot `rest_for_one` Non-Churn (`p2_restart_strategies_and_non_churn`)

Ordered supervision pipeline: `["planner", "author", "airlock_snapshot", "verifier_a", "verifier_b"]`, all initialized at generation `1` bound to `SNAPSHOT_SHA_V1` (`b4c89c9938c3a2a4b37bfd127ea51c6df28fc43f30d8c7ed0132e6cf6174a8d2`). When `author` crashes (`abnormal`) and restarts producing immutable `SNAPSHOT_SHA_V2` (`b3c35285a80c960f0bb81ed36f4f71529850f1fedf25f3a87e56989b56761a3c`):

| Strategy | Reverse Termination Order | Forward Restart Order | Generations After | Stale Downstream Count |
|---|---|---|---|---|
| `one_for_one` | `[]` | `["author"]` | `[1, 2, 1, 1, 1]` | `3` (**churn!**) |
| `one_for_all` | `["verifier_b", "verifier_a", "airlock_snapshot", "planner"]` | `["planner", "author", "airlock_snapshot", "verifier_a", "verifier_b"]` | `[2, 2, 2, 2, 2]` | `0` (restarts upstream `planner`) |
| `rest_for_one` | `["verifier_b", "verifier_a", "airlock_snapshot"]` | `["author", "airlock_snapshot", "verifier_a", "verifier_b"]` | `[1, 2, 2, 2, 2]` | `0` (`planner` untouched at gen `1`) |

- **Frozen-Snapshot `rest_for_one` Non-Churn Invariant:** Under `rest_for_one`, upstream `planner` remains untouched (`generation == 1`, `snapshot_sha256 == SNAPSHOT_SHA_V1`), while all downstream consumers (`verifier_b`, `verifier_a`, `airlock_snapshot`) are terminated in reverse start order and restarted in forward start order bound exclusively to `SNAPSHOT_SHA_V2` (`stale_downstream_count == 0`).
- **Must-Fail Control 3 (`must_fail_mid_audit_snapshot_churn`):** Under `one_for_one`, `author` advances to `SNAPSHOT_SHA_V2` while `["airlock_snapshot", "verifier_a", "verifier_b"]` remain alive at generation `1` on stale `SNAPSHOT_SHA_V1`; `verify_snapshot_non_churn` fails closed with `ERR_SNAPSHOT_CHURN` (`stale_count == 3`).

### Pillar 3 — Pure-$\mathbb{Z}/\mathbb{Q}$ Sliding-Window Restart Intensity & Multi-Level Escalation (`p3_sliding_window_intensity_escalation`)

Matching Erlang/OTP `stdlib/src/supervisor.erl` (`Threshold = Now - Period`, retaining prior restart timestamps $t$ satisfying $t \ge t_{\text{now}} - W$, equivalently $t_{\text{now}} - t \le W$ inclusive, and escalating to `MAX_RESTART_INTENSITY_EXCEEDED` with `reached_max_restart_intensity` iff $|\text{active}| > \text{max\_restarts}$):

1. **Exact Integer Boundary Trace (`max_restarts=2`, `window_ticks=5/1`):**
   - `t=0`: active `["0/1"]` (`1 <= 2`, `RESTART_ALLOWED`).
   - `t=5`: $5 - 0 = 5 \le 5$ (exact inclusive boundary), active `["0/1", "5/1"]` (`2 <= 2`, `RESTART_ALLOWED`).
   - `t=6`: $6 - 0 = 6 > 5$, `0/1` evicted (`evicted_at_t6 == 1`), active `["5/1", "6/1"]` (`2 <= 2`, `RESTART_ALLOWED`).
   - `t=10`: $10 - 5 = 5 \le 5$, active `["5/1", "6/1", "10/1"]` (`3 > 2`, `MAX_RESTART_INTENSITY_EXCEEDED`).
2. **Exact Non-Dyadic Rational $\mathbb{Q}$ Trace (`max_restarts=2`, `window_ticks=1/3`):**
   - Zero binary floating-point rounding drift at non-dyadic `1/3` boundaries: `t=0/1` -> `t=1/3` (inclusive active count `2`) -> `t=2/3` (`0/1` evicted, `evicted_at_2_3 == 1`) -> `t=5/6` (`1/3` evicted) -> `t=1/1` (active `["2/3", "5/6", "1/1"]`, `3 > 2`, `MAX_RESTART_INTENSITY_EXCEEDED`).
3. **Two-Level Supervision Tree Escalation (`worker -> sub_sup(2, 5) -> root_sup(1, 10)` on crashes `t = 0, 1, 2, 3, 4, 5`):**
   - `t=0, 1`: absorbed by `sub_sup`; `t=2`: `sub_sup` escalates #1 -> `root_sup` restarts `sub_sup` with fresh empty window (`sub_restarts_by_root == 1`); `t=3, 4`: absorbed by fresh `sub_sup`; `t=5`: `sub_sup` escalates #2 -> `root_sup` active `["2/1", "5/1"]` exceeds `1` -> `root_terminated == true` at `root_terminated_at == "5/1"` (`sub_escalations == 2`).
- **Must-Fail Control 4 (`must_fail_intensity_bypass`):** Claiming `RESTART_ALLOWED` at step `2` (`t=4` after `t=0, 2` with `max_restarts=2, window=5`) is rejected with `ERR_INTENSITY_LIMIT_BYPASS`.
- **Must-Fail Control 5 (`must_fail_non_monotonic_tick`):** Backward timestamp step (`t=5 -> t=4`) is rejected at step `1` with `ERR_NON_MONOTONIC_TICK`.

### Pillar 4 — Asymmetric Fault-Isolation Theorem: `monitor` vs. `link` $\pm$ `trap_exit` (`p4_monitor_vs_link_fault_isolation`)

Exact BFS signal propagation on `{coordinator (zone_a_coordinator), verifier_1 (zone_b_verifier), verifier_2 (zone_b_verifier)}`:

| Attachment Topology | `verifier_1` Exit | `coordinator` State | `verifier_2` State | Collateral Kills | Result |
|---|---|---|---|---|---|
| Unidirectional `monitor` (`mon-v1`, `mon-v2`) | `abnormal` | `ALIVE` (`promotion_blocked=true`, 1 `DOWN`) | `ALIVE` | `0` | **Certified Zone-B Isolation (`PASS`)** |
| Bidirectional `link` + `coordinator.trap_exit=True` | `abnormal` | `ALIVE` (1 `EXIT` inbox message) | `ALIVE` | `0` | Traps `abnormal`, **not** `kill` |
| Bidirectional `link` + `coordinator.trap_exit=False` | `abnormal` | `TERMINATED` | `TERMINATED` | `2` (`["coordinator", "verifier_2"]`) | **Must-Fail Control 6 (`ERR_COORDINATOR_COLLATERAL_KILL`)** |
| Bidirectional `link` + `coordinator.trap_exit=True` | `kill` | `TERMINATED` (`exit_reason="killed"`) | `TERMINATED` (`"killed"`) | `2` (`["coordinator", "verifier_2"]`) | **Must-Fail Control 7 (`ERR_COORDINATOR_COLLATERAL_KILL`)** |

Because OTP `kill` bypasses `trap_exit=True` on a linked process (killing the target with reason `"killed"`, which then cascades to any `trap_exit=False` siblings), **unidirectional `monitor` is strictly stronger than `link + trap_exit=True`** for air-gapped Zone-B verifiers.

### Pillar 5 — `Moissanite-Labs/exo#1200` `SupervisionPolicy` $\times$ `Foundation-0/aletheia v2.1+` Bridge (`p5_exo1200_aletheia_bridge`)

Intersects `exo#1200` (`group_supervision.py`, `ccdc929ace0a62152e23e10b0fd219d76df7b6f1`) safety gates with OTP supervision:

1. **Exact `exo#1200` Default Compatibility:** `max_retries=0` evaluates to `action="final"`, `reason="retry_budget_exhausted"` even when `otp_policy="transient"` and `exit_reason="abnormal"` would otherwise allow restart.
2. **Safety Dominance Invariant:** `exo#1200` sticky stop (`stop_requested=True` or `task_state in {"stopped", "cancelled"}`), terminal failure classes (`cancelled`, `denied`, `spend_limit`, `permanent`), and post-dispatch effects (`effect_class != "not_dispatched"`) unconditionally override OTP restart rules.
3. **End-to-End Clean Two-Zone Hybrid Run (`hybrid_clean_run`):**
   - `verifier_1` crashes (`abnormal`) -> unidirectional `DOWN` blocks promotion (`down_events_observed == 1`), `coordinator` and `verifier_2` remain `ALIVE`.
   - `author` crashes pre-dispatch (`transient`, `not_dispatched`) at `t=4` -> `zone_a_sup` (`rest_for_one`, `max_restarts=2`, `window_ticks=10`) re-snapshots `airlock_snapshot` to `SNAPSHOT_SHA_V2` (`zone_a_restarts == 1`, `author_attempts == 2`), terminates stale verifiers, and spawns fresh monitored verifiers pinned to `SNAPSHOT_SHA_V2`.
   - Both fresh verifiers return `VERIFIED` on `SNAPSHOT_SHA_V2` -> `promoted == true`, `final_snapshot_sha256 == SNAPSHOT_SHA_V2`.
4. **Three Explicit Must-Fail Controls:**
   - **Control 8 (`must_fail_hybrid_promotion_while_down`):** Attempting `promote` after `verifier_1` emitted `DOWN` without re-verification on a fresh snapshot is rejected at step `2` with `ERR_PROMOTION_BLOCKED_BY_DOWN`.
   - **Control 9 (`must_fail_hybrid_exo1200_stopped_restart`):** Attempting `author_crash_restart` after `stop_plan` is rejected at step `1` with `ERR_STOPPED_TASK_RESTARTED`.
   - **Control 10 (`must_fail_hybrid_exo1200_external_effects`):** Attempting `author_crash_restart` with `effect_class="external"` is rejected at step `0` with `ERR_UNRECONCILED_EXTERNAL_EFFECTS`.

---

## 3. Concrete Extension Blueprint for `exo#1200` & `aletheia v2.1+`

To extend `Moissanite-Labs/exo#1200` (`src/exo/core/group_supervision.py`) into full `aletheia v2.1+` Two-Zone Hybrid Swarm supervision without weakening `exo#1200` `I1–I4` guarantees:

1. **Extend `SupervisionPolicy` (backward-compatible defaults):**
   - Keep `max_retries: int = 0` (lifetime cap `0..10`) as the default.
   - Add optional explicit supervision-tree parameters:
     - `strategy: Literal["one_for_one", "one_for_all", "rest_for_one"] = "rest_for_one"`
     - `restart_policy: Literal["permanent", "transient", "temporary"] = "transient"`
     - `max_restarts: int = 0` and `window_ticks: Fraction = Fraction(1, 1)` (pure-$\mathbb{Q}$ monotonic tick counter, zero floats).
2. **Zone-A / Airlock Pipeline Supervision (`rest_for_one`):**
   - Order Zone-A children as `[planner, author, airlock_snapshot]`. Any restart of `author` MUST tear down `airlock_snapshot` and any active Zone-B audit leases bound to the prior digest before issuing a new immutable `snapshot_sha256`.
3. **Zone-B Verifier Attachment (`temporary` + Unidirectional `monitor` Only):**
   - Never `link` Zone-B clean-room verifiers to the Zone-A coordinator. Attach strictly via unidirectional `monitor` refs.
   - Treat every non-`normal` `DOWN` signal as fail-closed `promotion_blocked = True` until either a fresh snapshot cycle runs or an explicit independent replacement verifier verifies the pinned immutable digest.
4. **Gate Composition Order (`decide()` -> `step_restart_intensity()` -> `apply_strategy_crash()`):**
   - Evaluate `exo#1200` sticky-stop and `Effects.NOT_DISPATCHED` gates **first**; only a pre-dispatch `Failure.TRANSIENT` within lifetime `max_retries` may consult the OTP sliding-window intensity limiter and trigger a `rest_for_one` transition.

---

## 4. Verification & Reproducibility Receipts

Run inside the Track S11 directory (`track-s11-erlang-otp-supervision/`):

```bash
# 1. Strict JSON + schema + canonical byte-parity check
python3 -I -B -W error erlang_otp_supervision_certifier.py --check erlang_otp_supervision_certificate.json

# 2. 4-mode isolated -I determinism parity (all 4 hashes == 23757e7d665aeb4255bf6ffa81011355952b894c07836ffbb630399ae52570fe)
for flags in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
  python3 $flags erlang_otp_supervision_certifier.py --json | sha256sum
done

# 3. Assertion-free R5 verification suite (8/8 OK under -I -O -B -W error)
python3 -I -O -B -W error test_erlang_otp_supervision_r5.py

# 4. Aletheia v2.0.0 audit-check --strict-ancestors, safety-scan, and exhaustive mutation testing
python3 -B -W error -m aletheia audit-check . --strict-ancestors --scripts erlang_otp_supervision_certifier.py test_erlang_otp_supervision_r5.py
python3 -B -W error -m aletheia safety-scan .
python3 -B -W error -m aletheia mutate erlang_otp_supervision_oracle.py --work-root . --add-cwd --max-mutants 0 --test-cmd "python3 -I -O -B -W error test_erlang_otp_supervision_r5.py"
python3 -B -W error -m aletheia mutate erlang_otp_supervision_certifier.py --work-root . --add-cwd --max-mutants 0 --test-cmd "python3 -I -O -B -W error test_erlang_otp_supervision_r5.py"
```

| Gate | Exact Result |
|---|---|
| Certificate `--check` | `OK AUDIT-110 canonical_sha256=338d6b1619e6b5aeac8ae772f8e45459e2153a633f162695553472ec17fae87d pillars=5 controls=10` |
| 4-Mode Isolated `-I` Determinism | Bit-identical `23757e7d665aeb4255bf6ffa81011355952b894c07836ffbb630399ae52570fe` across `-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error` (exact match to committed JSON) |
| R5 Assertion-Free Suite (`-I -O -B -W error`) | `PASS AUDIT-110 R5_TESTS=8/8` |
| `aletheia mutate --max-mutants 0` | **`104/104`** (`erlang_otp_supervision_oracle.py`) + **`3/3`** (`erlang_otp_supervision_certifier.py`) = **`107/107` (`100.0%` killed, `0` survived, `truncated=False`)** |
| Full-AST `BoolOp` (`And`/`Or`) Sub-Clause Sweep | **`80/80` (`100.0%` killed, `0` survived)** across both `.py` modules |
| `aletheia audit-check --strict-ancestors` & `safety-scan` | `PASS` / `CLEAN` (`5` files, `2/2` R4, `0` defects, `0` leaks, `0` safety findings, `PYCACHE=0`) |

### `AUDIT-110R` Hardening Closures

1. **`OTP110-BUG-01` (`apply_strategy_crash` / `_should_strategy_restart`):** Under `one_for_all` and `rest_for_one`, `temporary` children (dead or alive when terminated by a sibling crash) are never restarted, and already-dead `transient` children are never resurrected; only `permanent` children and crashed/running `transient` children restart, matching Erlang/OTP `stdlib/src/supervisor.erl`.
2. **`OTP110-BUG-02` (`certify_intensity_trace` & `certify_hybrid_swarm_run`):** Trailing events after `MAX_RESTART_INTENSITY_EXCEEDED` fail closed with `ERR_EVENT_AFTER_ESCALATION`, and trailing events after terminal `promote` fail closed with `ERR_EVENT_AFTER_PROMOTE`.

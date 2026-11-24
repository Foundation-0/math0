# Erlang/OTP Supervision Tree Semantics — Pure-$\mathbb{Z}/\mathbb{Q}$ State-Machine Certifier

> **Standing:** Offline pure-stdlib certifier and R5 test suite (`honest_novelty_tier: N0` — classical Armstrong 2003 / Erlang/OTP `supervisor.erl` semantics, `Moissanite-Labs/exo#1200`, and self-contained pure-$\mathbb{Z}/\mathbb{Q}$ operational restatement/certifier; no novelty claim above `N0`).
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s, zero external writes).

## 1. Shipped Files (Exact In-PR SHA-256)

| File | SHA-256 | Role |
|---|---|---|
| [`erlang_otp_supervision_oracle.py`](erlang_otp_supervision_oracle.py) | `0fbb3ba94b5968ce275e3df39b9e198d8295f674752b4805b91d57ecb027d4cb` | Pure-$\mathbb{Z}/\mathbb{Q}$ finite-state supervision-tree oracle (5 pillars, `10` dynamic must-fail controls, fail-closed `validate_certificate()`) |
| [`erlang_otp_supervision_certifier.py`](erlang_otp_supervision_certifier.py) | `1f0d378ddb310462c148c81871667b012779c64890e85b5d3b9310f792c4e463` | Strict deterministic CLI (`--json`, `--output`, `--check` rejecting duplicate keys, floats, CRLF, invalid UTF-8, oversized ints `>1000` digits, and byte drift with clean exit `2`) |
| [`test_erlang_otp_supervision_r5.py`](test_erlang_otp_supervision_r5.py) | `86f87ed015abb86c34a98977f537aef3bb2b1bbf5975ce906c0c57357e05fa16` | Assertion-free R5 known-answer, boundary, tamper, and CLI error-handling suite (`8/8` groups OK) |
| [`erlang_otp_supervision_certificate.json`](erlang_otp_supervision_certificate.json) | `f0444050b2927de80000a1ac7de6caf3239263a808037aa6fa0719d9401593a5` | Canonical offline certificate (inner `canonical_sha256: 46415faef56963a3fc9df1601f76c3b6b5b5394a92513c15cb5108f2846b1325`) |
| [`ERLANG_OTP_SUPERVISION_REPORT.md`](ERLANG_OTP_SUPERVISION_REPORT.md) | `4bb62f38c7929b6da8af09d3021e896dffbaf968bc5702246e31d67387a735bd` | Full 5-pillar specification, primary-literature citations, and `exo#1200` / `aletheia v2.1+` extension blueprint |

## 2. Five Certified Pure-$\mathbb{Z}/\mathbb{Q}$ Pillars & `10` Must-Fail Controls

1. **P1 — Exact $3 \times 3$ Restart Policy $\times$ Exit Reason Matrix:** Exact `otp_should_restart` over `{permanent, transient, temporary} × {normal, shutdown, abnormal}` (`4` restart, `5` drop), with must-fail rejection of `temporary` restart (`ERR_TEMPORARY_CHILD_RESTARTED`) and clean `transient` restart (`ERR_TRANSIENT_CLEAN_EXIT_RESTARTED`).
2. **P2 — `one_for_one` / `one_for_all` / `rest_for_one` & Frozen-Snapshot Non-Churn:** Exact reverse-termination / forward-restart traces preserving `temporary` and already-dead `transient` non-resurrection, proving `rest_for_one` yields `0` stale downstream verifiers without restarting upstream `planner`, whereas `one_for_one` fails closed with `ERR_SNAPSHOT_CHURN` (`3` stale children).
3. **P3 — Pure-$\mathbb{Z}/\mathbb{Q}$ Inclusive Sliding-Window Intensity & 2-Level Escalation:** Exact `t_now - t <= W` retention on both integer (`5/1`) and non-dyadic rational (`1/3`) ticks (zero IEEE-754 drift), 2-level `worker -> sub_sup -> root_sup` escalation (`root_terminated_at = "5/1"`), plus fail-closed intensity-bypass, non-monotonic-tick, and post-escalation trailing-event rejections.
4. **P4 — Asymmetric Fault-Isolation (`monitor` vs. `link ± trap_exit`, accurate `kill` vs. `killed` semantics):** Exact BFS signal propagation certifying unidirectional `monitor` gives `0` collateral kills and blocks promotion on both `abnormal` (`monitor_zone_b_isolation`) and external `exit(verifier_1, kill)` $\to$ exit reason `"killed"` (`monitor_zone_b_isolation_on_killed`) without requiring `trap_exit`; certifying Erlang/OTP's distinction that `link + trap_exit=True` **can** trap propagated `"killed"` from an external `exit(verifier_1, kill)` (`link_with_trap_exit_outside_killed`, `0` collateral kills), whereas `link + trap_exit=False` dies on `abnormal`/`killed` (`2` collateral kills) and a **direct** untrappable `"kill"` signal targeting `coordinator` (`exit(coordinator, kill)`) still bypasses `trap_exit=True` (`must_fail_kill_bypasses_trap_exit`, `2` collateral kills).
5. **P5 — `Moissanite-Labs/exo#1200` (`ccdc929a`) $\times$ `aletheia v2.1+` Hybrid Swarm Composition:** Proves sticky-stop and `effect_class != "not_dispatched"` safety gates unconditionally dominate OTP restart rules, with end-to-end clean promotion on `SNAPSHOT_SHA_V2` and fail-closed controls for promotion-while-`DOWN`, stopped-task restart, external-effect restart, and post-promote trailing events.

**Honest Scope Boundary:** Certifies discrete finite-state transition traces and rational inequalities in pure Python; does not verify live OS signals, BEAM scheduler timing, or multi-host network partitions.

## 3. Exact Offline Reproduction (4-Mode Isolated `-I` R4 Parity)

From this directory (`studies/expedition-erlang-otp-supervision-audit110r/`, 100% offline, Python 3 standard library only):

```bash
# 1. Strict byte-for-byte verification against committed certificate (f0444050...):
python3 -I -O -B -W error erlang_otp_supervision_certifier.py --check erlang_otp_supervision_certificate.json

# 2. 4-mode isolated -I deterministic recomputation parity (all match f0444050...):
python3 -I -B erlang_otp_supervision_certifier.py --json | sha256sum
python3 -I -O -B erlang_otp_supervision_certifier.py --json | sha256sum
python3 -I -B -W error erlang_otp_supervision_certifier.py --json | sha256sum
python3 -I -O -B -W error erlang_otp_supervision_certifier.py --json | sha256sum

# 3. Assertion-free R5 known-answer, boundary, tamper & CLI suite (8/8 groups OK):
python3 -I -O -B -W error test_erlang_otp_supervision_r5.py
```

**Reproducible Local Checks:** `8/8` R5 groups pass across `-I -B`, `-I -O -B`, `-I -B -W error`, and `PYTHONHASHSEED=42 -B`; `aletheia mutate --max-mutants 0` kills `110/110` (`104` oracle + `6` certifier, `0` survivors, `truncated=False`).

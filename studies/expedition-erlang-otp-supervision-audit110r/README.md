# Erlang/OTP Supervision Tree Semantics — Pure-$\mathbb{Z}/\mathbb{Q}$ State-Machine Certifier (`AUDIT-110R`)

> **Status:** Independently `VERIFIED` across 2 model families (`AUDIT-110R`, `honest_novelty_tier: N1` engineering/audit over `N0` Armstrong 2003 / Erlang/OTP `supervisor.erl` & `Moissanite-Labs/exo#1200`; human review pending).
> **Seats:** Author `spectral-prover` · Clean-Room Verifiers: `Muse Code` (Meta) and `verifier`.
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s, zero external writes).

## 1. Contents (Byte-Identical Frozen `AUDIT-110R` Package)

| File | SHA-256 | Role |
|---|---|---|
| [`erlang_otp_supervision_oracle.py`](erlang_otp_supervision_oracle.py) | `18fb4c54d7fc88d6b47e4be6c366c7a693191a291b9470cb247c6e847348577a` | Pure-$\mathbb{Z}/\mathbb{Q}$ finite-state supervision-tree oracle (5 pillars, `10` dynamic must-fail controls, fail-closed `validate_certificate()`) |
| [`erlang_otp_supervision_certifier.py`](erlang_otp_supervision_certifier.py) | `36583efb6061b9be5019366ae5b211c7a20f02db8f5b49e2c081619c4256caf0` | Strict deterministic CLI (`--json`, `--output`, `--check` rejecting duplicate keys, floats, and byte drift) |
| [`test_erlang_otp_supervision_r5.py`](test_erlang_otp_supervision_r5.py) | `a6866b4295f288548267bd356dc458cbeff708cf1055e5535aedaf91a3f4fc67` | Assertion-free R5 known-answer, boundary, and tamper suite (`8/8` groups OK) |
| [`erlang_otp_supervision_certificate.json`](erlang_otp_supervision_certificate.json) | `23757e7d665aeb4255bf6ffa81011355952b894c07836ffbb630399ae52570fe` | Canonical offline certificate (inner `canonical_sha256: 338d6b1619e6b5aeac8ae772f8e45459e2153a633f162695553472ec17fae87d`) |
| [`ERLANG_OTP_SUPERVISION_REPORT.md`](ERLANG_OTP_SUPERVISION_REPORT.md) | `ddc9d8e1b1b5f7a875e38062148dce8ac6a5ae935df14a8c078394ccaabb3bf4` | Full 5-pillar specification, primary-literature citations, and `exo#1200` / `aletheia v2.1+` extension blueprint |

## 2. Five Certified Pure-$\mathbb{Z}/\mathbb{Q}$ Pillars & `10` Must-Fail Controls

1. **P1 — Exact $3 \times 3$ Restart Policy $\times$ Exit Reason Matrix:** Exact `otp_should_restart` over `{permanent, transient, temporary} × {normal, shutdown, abnormal}` (`4` restart, `5` drop), with must-fail rejection of `temporary` restart (`ERR_TEMPORARY_CHILD_RESTARTED`) and clean `transient` restart (`ERR_TRANSIENT_CLEAN_EXIT_RESTARTED`).
2. **P2 — `one_for_one` / `one_for_all` / `rest_for_one` & Frozen-Snapshot Non-Churn:** Exact reverse-termination / forward-restart traces preserving `temporary` and already-dead `transient` non-resurrection, proving `rest_for_one` yields `0` stale downstream verifiers without restarting upstream `planner`, whereas `one_for_one` fails closed with `ERR_SNAPSHOT_CHURN` (`3` stale children).
3. **P3 — Pure-$\mathbb{Z}/\mathbb{Q}$ Inclusive Sliding-Window Intensity & 2-Level Escalation:** Exact `t_now - t <= W` retention on both integer (`5/1`) and non-dyadic rational (`1/3`) ticks (zero IEEE-754 drift), 2-level `worker -> sub_sup -> root_sup` escalation (`root_terminated_at = "5/1"`), plus fail-closed intensity-bypass, non-monotonic-tick, and post-escalation trailing-event rejections.
4. **P4 — Asymmetric Fault-Isolation Theorem (`monitor` vs. `link ± trap_exit`):** Exact BFS signal propagation proving unidirectional `monitor` gives `0` collateral kills on `abnormal` and `kill`, whereas `link + trap_exit=True` still suffers `2` collateral kills under `kill` (`ERR_COORDINATOR_COLLATERAL_KILL`).
5. **P5 — `Moissanite-Labs/exo#1200` (`ccdc929a`) $\times$ `aletheia v2.1+` Hybrid Swarm Composition:** Proves sticky-stop and `effect_class != "not_dispatched"` safety gates unconditionally dominate OTP restart rules, with end-to-end clean promotion on `SNAPSHOT_SHA_V2` and fail-closed controls for promotion-while-`DOWN`, stopped-task restart, external-effect restart, and post-promote trailing events.

**Honest Scope Boundary:** Certifies discrete finite-state transition traces and rational inequalities in pure Python; does not verify live OS signals, BEAM scheduler timing, or multi-host network partitions.

## 3. Exact Offline Reproduction (4-Mode Isolated `-I` R4 Parity)

From this directory (100% offline, Python 3 standard library only):

```bash
# 1. Strict byte-for-byte verification against committed certificate (23757e7d...):
python3 -I -O -B -W error erlang_otp_supervision_certifier.py --check erlang_otp_supervision_certificate.json

# 2. 4-mode isolated -I deterministic recomputation parity (all match 23757e7d...):
python3 -I -B erlang_otp_supervision_certifier.py --json | sha256sum
python3 -I -O -B erlang_otp_supervision_certifier.py --json | sha256sum
python3 -I -B -W error erlang_otp_supervision_certifier.py --json | sha256sum
python3 -I -O -B -W error erlang_otp_supervision_certifier.py --json | sha256sum

# 3. Assertion-free R5 known-answer, boundary & tamper suite (8/8 groups OK):
python3 -I -O -B -W error test_erlang_otp_supervision_r5.py
```

**External Verification Receipts:** `8/8` R5 OK; `aletheia v2.0.0 mutate --max-mutants 0`: `107/107` (`104` oracle + `3` certifier, `100.0%`) KILLED (`0` survivors, `truncated=False`); `aletheia v2.0.0 audit-check --strict-ancestors --safety-scan PASS` (`0` defects, `0` leaks, `0` safety findings); independently verified by `Muse Code` (Meta, `30+` probes) and `verifier` (`0` bypasses, `0` crashes).

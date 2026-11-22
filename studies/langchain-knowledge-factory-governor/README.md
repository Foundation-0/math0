# Verified 3-Role Knowledge Factory Curator Governor & Trust-Boundary Tomography (`AUDIT-076R`)

- **Audit Status:** `AUDIT-076R VERIFIED` (`N1`, `0` unresolved defects; `108/108` = `100/100` governor + `8/8` audit `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypass_count = 0` across `14` + `12` adversarial red-team attacks).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** Pinned verbatim LangChain primary essays: *"The five components of building a 'company harness'"* (`https://www.langchain.com/blog/components-building-company-harness`, Oct 24, 2026; HTML `cc6cccb9...`, text `2abd7795...`) and *"How to build a knowledge factory"* (`https://www.langchain.com/blog/knowledge-factory`, Nov 21, 2026; HTML `716c69e3...`, text `ca5f914c...`, `12/12` verbatim line-numbered anchors). No third-party repositories or HTML bundles are vendored here; all exact pure-$\mathbb{Q}$ proofs and the fail-closed 3-role Curator Governor execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [knowledge_factory_governor.py](knowledge_factory_governor.py) | `45da647e7775ab028addef0c415f7444bd6e7b433b24db4b5bdcf0a85bddfb56` — Pure Python 3 stdlib zero-float 3-Role Verified Knowledge Factory Curator Governor (`KF-01..KF-05` + SHA-256 hash-chained ledger; `100/100` R5 mutation killed) |
| [knowledge_factory_audit.py](knowledge_factory_audit.py) | `281416de0dadaf7ab0e071735028845e4aacc3e7be44a62d27d8e96eafd08f81` — Canonical certificate emitter & live 12-anchor source verifier (`--standalone` supported; `8/8` R5 mutation killed) |
| [test_knowledge_factory_r5.py](test_knowledge_factory_r5.py) | `842a1e4514ea43dab878d85aad75b0f946bc90c35155d7a48ed262d054a794b1` — R1–R5 invariant, red-team bypass, and refusal-site test suite (`14/14` OK; `108/108` `100.0%` combined kill) |
| [knowledge_factory_certificate.json](knowledge_factory_certificate.json) | `7f84e852283d072902207ba106f70b3384d00b2fd4041ff12cc21be25e08974b` — Sealed `AUDIT-076R` live-anchored zero-float certificate (`canonical_sha256 = 9485e1ce726b8b0582aaf183dd75c1462dae3bcfa2fe197fefb9ba7da7109f60`) |
| [KNOWLEDGE_FACTORY_AUDIT_REPORT.md](KNOWLEDGE_FACTORY_AUDIT_REPORT.md) | Full isomorphism & trust-boundary tomography report, Law-2 steelman credit, `KF-01..KF-05` proofs, and Law-4 `N0`/`N1` quarantine |

## Quickstart (Zero External Dependencies)

From `studies/langchain-knowledge-factory-governor/`:

```bash
# 1. Run exact pure-Q Curator Governor proofs & certificate emitter in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      a50d62df7dbc34fcb43db95c6c952023b3ed1bfd62d7308e3fa6117c6ce35640
#    (canonical_sha256 = 71c1b53e6f798902da2f6761574a029b5ab1c3ef733db96f627473449200e57d)
python3 -I -B knowledge_factory_audit.py --standalone | sha256sum

# 2. Run the full R5 invariant, red-team, and refusal-site test suite
python3 -I -O -B -W error test_knowledge_factory_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts knowledge_factory_audit.py test_knowledge_factory_r5.py --json
python3 -B -W error -m aletheia mutate knowledge_factory_governor.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_knowledge_factory_r5.py" --json
python3 -B -W error -m aletheia mutate knowledge_factory_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_knowledge_factory_r5.py" --json
```

## Summary of Verified Results (`N1`)

- **`KF-01` (Biba × Bell-LaPadula Lattice & Exact Blast Radius):** Blocks untrusted external-trace elevation into global skills (`Δ_I = +3`), private-DM leakage into global stores (`Δ_C = +2`, blocked even with human admin countersign), and store/tier spoofing via `policy.store_tiers`; proves exact fleet blast radius for `W=10, T=12, p=1/20`: $E[C] = \mathbf{6/1}$ and $1 - (19/20)^{120} = \mathbf{0.997878}$.
- **`KF-02` (Exact Pythagorean Goodhart Drift):** Proves an unverified 4-step Curator accepts `4/4` updates as proxy error drops `175/256` (`68.3594%`) while total error climbs `5/4 -> 657/256` (`+337/320 = +105.3125%`); governed outside-anchor latch halts at step `1` and rejects proxy regressions (`KF02_PROXY_REGRESSION`).
- **`KF-03`–`KF-05` (CAS/Conflict/DAG, Ring-0 & 3-Role Tao Ledger):** Closes multi-worker LWW ARR flip-flop oscillation & stale CAS split-brain, directed skill dependency cycles (3-color DFS), normalized `[.:/- ]` Ring-0 overwrite across `domain_key` + `payload_patch`, scope/endpoint/cron escalation, whitespace/case role-separation spoofing, and forged semantic fields in the SHA-256 hash-chained ledger.

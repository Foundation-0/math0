# Exact Pure-$\mathbb{Q}$ Cost-Break-Even, AST Sandbox & Reasoning-Cache Governance Audit of `arXiv:2611.09891` (`CPU-ARC`, `AUDIT-077R`)

- **Audit Status:** `AUDIT-077R VERIFIED` (`N1`, `0` unresolved defects; `67/67` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypass_count = 0` across `10` incl. 3 RCE escapes + `16` fresh adversarial attacks).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** `arXiv:2611.09891v1` (*CPU-ARC: Agentic Reasoning Caching for on-CPU Reasoning Reuse*, Belcak et al.; `3/3` PDF/text SHA-256s + `24/24` verbatim anchors + `32/32` Tables 3–10 token counts) bridged to `Moissanite-Labs/warp-drive#15` (`warp-sandbox-exec.sh`, `7/7` anchors), `Foundation-0/aletheia v1.4.0`, `sous-labs/songe` (`AUDIT-073R`), and LangChain Knowledge Factory (`AUDIT-076R`). No third-party PDFs or repos are vendored here; all exact pure-$\mathbb{Q}$ cost-break-even proofs, numerical/unit bug reproductions, AST sandbox checks, and fallback contracts execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [cpu_arc_governance_audit.py](cpu_arc_governance_audit.py) | `347ec31f30b6f7c77e86a6e026f880caaa264114ba95a209943108d9829deecc` — Pure Python 3 stdlib zero-float `CPU-ARC` break-even oracle, AST symbol-allowlist sandbox, `do()` SHA-256 callee-pin verifier, canonical worktree guard, and recursive fallback contract (`67/67` R5 mutation killed) |
| [test_cpu_arc_governance_r5.py](test_cpu_arc_governance_r5.py) | `d57e3cf9a714b3adcd2deb04ae69e59cd8f27e749452b6cd906492b00ca90801` — R1–R5 isolated unit, RCE-escape, boundary, and refusal-site test suite (`7/7` OK) |
| [cpu_arc_governance_certificate.json](cpu_arc_governance_certificate.json) | `969cd32a73dbd35183c07adce48fc9031807d6c76538c40dfd4fcb8779098d88` — Sealed `AUDIT-077R` live-anchored zero-float certificate (`canonical_sha256 = 9b2740560b324dac3186037d2cc1c0d9b040d147a9fcc59cb354b185d24ee117`) |
| [CPU_ARC_GOVERNANCE_AUDIT_REPORT.md](CPU_ARC_GOVERNANCE_AUDIT_REPORT.md) | Full forensic report (`CARC-01..CARC-05`), Law-2 steelman credit, generalized pure-$\mathbb{Q}$ break-even & perturbation-bug proofs, 3-Axis Trace-Distillation Triangle bridge, and Law-4 `N0`/`N1` quarantine |

## Quickstart (Zero External Dependencies)

From `studies/cpu-arc-reasoning-cache-governance/`:

```bash
# 1. Run exact pure-Q CPU-ARC break-even & AST sandbox governance oracle in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      12ca8a4cd5c19491fcbce9f67006762710b32337ca527d15a288a68ae9320425
#    (canonical_sha256 = bc06efe74adce1c1af5d8ae5880ac77364591f31f8ca7fa522c95f0b067d9a43)
python3 -I -B cpu_arc_governance_audit.py --standalone --json | sha256sum

# 2. Run the full R5 invariant, AST-RCE-defense, and refusal-site test suite
python3 -I -O -B -W error test_cpu_arc_governance_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts test_cpu_arc_governance_r5.py --json
python3 -B -W error -m aletheia mutate cpu_arc_governance_audit.py \
  --work-root . --max-mutants 500 --add-cwd --test-cmd "python3 -I -O -B -W error test_cpu_arc_governance_r5.py" --json
```

## Summary of Verified Results (`N1`)

- **`CARC-01` (Generalized Exact Pure-$\mathbb{Q}$ Cost-Break-Even & Token Deficit Audit):** Identifies `8/8` negative builder token deficits (`b_A > rep_b > b_D`) across Tables 3–10 and proves generalized break-even collapses `4/8` benchmarks to $N^* = \infty$ at $h = 1/2, L_{\mathrm{err}} = 13S$ (`GSM8K` exact `-1/8000` at `$0.13`).
- **`CARC-02` (Exact Perturbation & Fallback Bugs):** Certifies `+273` Kelvin `3/20 K` error, `"32 F"` `4823/5463 = 88.28%` error, `m^3` vs `dm^3` `1,000x` error, `4/4` negation false positives, and `Fig. 12` `{'work value': None}` breaking `Fig. 1` fallback — closed by recursive nested fallback scanning (`validate_cpu_arc_fallback_contract`).
- **`CARC-03..CARC-05` (AST Symbol-Allowlist Sandbox & 3-Axis Trace-Distillation Triangle):** Closes 20% eval-log leakage, single-family self-judging, and compiled-trace Python RCE / `do()`-hijack via strict AST symbol allowlists, exact `do()` SHA-256 `callee_pins`, and canonical `posixpath` `warp-sandbox-exec.sh` confinement.

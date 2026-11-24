# Exact RFC-1035/7766 DNS-over-TCP Protocol, Security & $\mathcal{L}_{63}$ Channel-Capacity Tomography (`AUDIT-075R`)

- **Audit Status:** `AUDIT-075R VERIFIED` (`N1`, `0` unresolved defects; `150/150` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypass_count = 0` across `6` + `14` adversarial attacks).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** `southpolesteve/workers-dns-tcp @ 9a5f9002079e3418eb77f9a02395ecc9d028a8a0` (`15/15` file SHA-256s + `29/29` verbatim `file:line` anchors) bridged to `Moissanite-Labs/tokenpage#13` (`AUDIT-024`) and `Moissanite-Labs/warp-drive#15` (`src/warp_modeld/server.py`, `6/6` anchors). No third-party repositories are vendored here; all exact pure-$\mathbb{Q}$ combinatorics, wire reproducers, and hardened RPC/DNS gates execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [workers_dns_tcp_audit.py](workers_dns_tcp_audit.py) | `ac14abf2e3725d0088b29e5e6f0c411c6af554e9e572491c16ec85e39d16a9c4` — Pure Python 3 stdlib zero-float upstream wire reproducer, hardened DNS-over-TCP & LLM boundary gate, and exact $\mathcal{L}_{63}$ capacity oracle (`150/150` R5 mutation killed) |
| [test_workers_dns_tcp_r5.py](test_workers_dns_tcp_r5.py) | `5b49e484e9943c0d76cdd949d5362d3cd4761334d70467b7bfa98b944e0e94cd` — R1–R5 isolated unit, boundary, and adversarial red-team test suite (`15/15` OK) |
| [workers_dns_tcp_certificate.json](workers_dns_tcp_certificate.json) | `f629f3e82f7d8cabf5b6238ed88727df2db8b7b8d5619bdc9680eb31491f2554` — Sealed `AUDIT-075R` live-anchored zero-float certificate (`canonical_sha256 = f882efc25019643db0eed5a94af057baa281a8289ca4aa8c9d065923225f4636`) |
| [WORKERS_DNS_TCP_AUDIT_REPORT.md](WORKERS_DNS_TCP_AUDIT_REPORT.md) | Full protocol/security report (`WDT-01..WDT-08`), Law-2 steelman credit, exact pure-$\mathbb{Q}$ channel capacity proofs, `tokenpage#13`/`warp-drive#15` (`WD-RPC-R8-01`) bridges, and Law-4 `N0`/`N1` quarantine |

## Quickstart (Zero External Dependencies)

From `studies/workers-dns-tcp-channel-capacity/`:

```bash
# 1. Run exact pure-Q DNS-over-TCP & channel-capacity oracle in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      c8e473b1e21e47d358edb8cfd8ec815b40d5ed1094b144d25bd329904a54f7a0
#    (canonical_sha256 = 48f685be6ee3f70100fe97427a301fa840c53cc6b00866dfb6349f10658ad062)
python3 -I -B workers_dns_tcp_audit.py --standalone --json | sha256sum

# 2. Run the full R5 invariant and adversarial refusal-site test suite
python3 -I -O -B -W error test_workers_dns_tcp_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts test_workers_dns_tcp_r5.py --json
python3 -B -W error -m aletheia mutate workers_dns_tcp_audit.py \
  --work-root . --max-mutants 500 --add-cwd --test-cmd "python3 -I -O -B -W error test_workers_dns_tcp_r5.py" --json
```

## Summary of Verified Results (`N1`)

- **Protocol & Wire-Framing Forensics (`WDT-01..WDT-08`):** Live-reproduced `65,528`-B `ARCOUNT=5437` RDATA-pointer regex bomb (`1,359,000` calls / `5,452,309` chars / `136.56 ms` V8 CPU), non-root `OPT` `FORMERR` leak, dirty query header bits & meta QTYPEs, `1,489` pipelined queries/64KB burst & `32,767.5x` 2B->65535B pre-body allocation, DNS-0x20 compression defeat, and 63-char QNAME SPF/DMARC smuggling.
- **Exact Pure-$\mathbb{Q}$ Channel Capacity of $\mathcal{L}_{63}$:** Exact 99-digit $N_{\mathrm{valid}}(63)$ recurrence with dominant eigenvalue $\lambda_+ = 18 + 6\sqrt{10}$, `[328.094, 328.095]` bits/label, `38.69%` wire efficiency, and `65,163`-B TCP downlink payload bound.
- **Bidirectional `warp-drive#15` Bridge (`WD-RPC-R8-01`):** Surfaces missing server-side socket read timeout at `src/warp_modeld/server.py:90` alongside hardened DNS-over-TCP / LLM framing gates.

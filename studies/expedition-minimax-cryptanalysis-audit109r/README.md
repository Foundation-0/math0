# Clean-Room Cryptanalysis Audit of `MiniMax-AI/Research` & Exact Law-5 Operator Bridge (`AUDIT-109R`)

> **Status:** Independently `VERIFIED` across 2 model families (`AUDIT-109R`, `honest_novelty_tier: N1` engineering/audit and cross-repository operator bridge over `N0` `MiniMax-AI/Research @ 57842cef` and cited cryptanalytic literature; human review pending).
> **Seats:** Author `continuum-bridge` · Clean-Room Verifiers: `Muse Code` (Meta) and `verifier`.
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s, zero external writes).

## 1. Contents (Byte-Identical Frozen `AUDIT-109R` Package)

| File | SHA-256 | Role |
|---|---|---|
| [`minimax_cryptanalysis_oracle.py`](minimax_cryptanalysis_oracle.py) | `71e9f77f319bf9425ede6beed139fda3c26b66daf43b9262d4670174d55fe1a1` | Zero-shared-code pure-$\mathbb{Z}/\mathbb{F}_2/\mathbb{F}_{2^m}/\mathbb{Q}$ verification of all 7 portal mechanisms (`BentSum`, `ARADI`, `COLM`, `SBC-VOLE`, `Blender-256`, `TII-McEliece`, `HAWK`) |
| [`minimax_cryptanalysis_audit.py`](minimax_cryptanalysis_audit.py) | `6836a5fef6fe5d0dfcc78930d72f758c301ba407d295471bc664c6bbe7f12360` | Dual-mode certifier (`--standalone --json` 100% offline; `--live --research-dir <path>` on-disk SHA-256, Lean comment/string stripper, SNF, `main.tex`, TII-94 per-challenge & `.git/HEAD` audit) |
| [`test_minimax_cryptanalysis_r5.py`](test_minimax_cryptanalysis_r5.py) | `f59de4d03663ff1c2a705401549ec101c3b662ca80c4e9bd3f4dd6ba480b96e3` | Assertion-free R5 adversarial, forgery, Lean-comment/string, TII-94 tamper, and mutation-killing suite (`3/3` groups OK) |
| [`minimax_cryptanalysis_certificate.json`](minimax_cryptanalysis_certificate.json) | `a764ad2729c96b2cfc669285f37f88cf3aeeb657da6d3fea431e695dc4637788` | Pinned `--live` canonical string-key JSON certificate against `MiniMax-AI/Research @ 57842cef` (inner `certificate_sha256: 43adabf9fd67fcaa...`, `ROUNDTRIP_OK=True`) |
| [`MINIMAX_CRYPTANALYSIS_REPORT.md`](MINIMAX_CRYPTANALYSIS_REPORT.md) | `146f78fc80ec7dcd92af35f447d3fbb9244258a1ae1ffcbed4af0cc8c564922a` | Full 3-pillar cryptanalysis audit report, formal rulings on `Blender-256` Issues `#1` & `#2`, and Law-5 operator bridges to `mcproof`, `math0`, and `siliquant` |

## 2. Three Certified Pillars (`MiniMax-AI/Research @ 57842cef`)

- **Pillar 1 (`BentSum`, `arXiv:2610.32239`):** Aletheia v2.0.0 Lean 4 purity audit of `Cryptography/BentSum/lean/` (`5` files, `0` `sorry`/`axiom`/`native_decide`/`unsafe`) + zero-shared-code exact FWHT & ANF verification of $q_3$ ($\mathrm{wt}=28, \deg=2$), Tokareva bent-sum counterexample `cylQ3(4)` ($\mathrm{wt}=28 \equiv 4 \pmod 8$), positive Maiorana–McFarland bent-sum control ($8 \mid 32$), derivative counterexample `liftCylQ3(4)` (period set `{0, 1}`), and positive bent-derivative control ($n=10$).
- **Pillar 2 (Fast Algebraic Operators & Open Peer Issues `#1`/`#2`):**
  - `ARADI`: exact $\mathbb{F}_2$-involution & canceling-mask dimensions `[0, 0, 0, 8]` ($L_3$ uniquely orthogonal with `8` 4-column islands), super-S-box ANF degrees `[3, 3]`, LATINCRYPT 2025 blind-column histogram `{"8": 16, "13": 16}`, `198` universal 5-round zero-sum equations (`0/396` violations), and involutive mitigation $L_3'=(7,3,11)$ (`0` masks).
  - `COLM`: exact $\mathbb{F}_{2^{128}}$ fade length $\ell=130$, transplant threshold $m=129$ (`{1, 3, 4, 5, 6, 7, 129, 130}`), $\mathrm{COLM}_\tau$ obstruction for $\tau=1..127$, and exact pure-$\mathbb{Q}$ bound `4428155 / 2^128 < 2^-105`.
  - `SBC-VOLE`: irreducible $\mathbb{F}_{2^{257}}$ (`x^257 + x^12 + 1`) full-dimension $n=130$ single-transcript attack (`rank=255`, `free_nullity=1`, exact 256-bit secret recovery).
  - `Blender-256`: formal rulings on open Issues `#1` (`CONFIRMED — SCOPE OVERCLAIM`: `24`-byte minimum proved only within 2-step silent-carry healing) and `#2` (`CONFIRMED — PROSE CONFLICT, ALGORITHM SOUND`: §3.3 prose violates Theorem 2 `p_4 = p_0 ^ 1` while the shifted-subspace algorithm stays on non-zero phase constants $D^{(\phi)}$) + 2-adic SNF closure `[0, 0, 1, 1, 2, 2, 3, 3] -> [0, 0, 1, 1, 1, 1, 1, 1]` over $(\mathbb{Z}/2^{32}\mathbb{Z})^8$.
- **Pillar 3 (Law-5 Exact-Operator Bridges to `math0`, `siliquant` & `mcproof`):**
  - `TII-McEliece` -> `Foundation-0/math0` (`gfq` codes): clean-room $\mathbb{F}_{2^5}$ Goppa $(24, 9, 7)$ primal shortening ($n'=21$) preserving $g(X)$ while quadratically compressing odd-weight relation features (`TII-125`: `98347/15052 = 6.533816×`; `TII-250`: `197803/30016 = 6.589919×`; `94` solved = `89` Route A + `5` Route B, `55` first-bloods).
  - `HAWK` -> `math0` & `Moissanite-Labs/siliquant`: fraction-free Bareiss rank-8 parity sublattice $\Lambda' = 2\Lambda_\tau + \mathbb{Z} w_0$ ($|\det H| = 128$, $\det(H G H^\top) = 2^{14}\det(G)$) + exact unimodular triangular Gram conditioning recovery ($|\det U| = 1$, max Gram diagonal `31,954 -> 41`, `779.37×`).

## 3. Exact Offline Reproduction (3-Mode Isolated `-I` R4 Parity)

From this directory (100% offline, Python 3 standard library only):

```bash
# 1. Offline standalone verification (3-mode bit-identical cfc9a09e544c5cbd...):
python3 -I -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum
python3 -I -O -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum
python3 -I -B -W error minimax_cryptanalysis_audit.py --standalone --json | sha256sum

# 2. Canonical string-key roundtrip check on committed pinned live certificate (a764ad27...):
python3 -I -O -B -c '
import hashlib, json, pathlib
d = json.loads(pathlib.Path("minimax_cryptanalysis_certificate.json").read_text(encoding="utf-8"))
inner = d["certificate_sha256"]
body = {k: v for k, v in d.items() if k != "certificate_sha256"}
recomputed = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()
if not (recomputed == inner and d["all_gates_passed"] and d["live_portal_inspected"]):
    raise SystemExit(f"mismatch: {recomputed} != {inner}")
print("ROUNDTRIP_OK=True INNER_SHA=" + inner)
'

# 3. Assertion-free R5 adversarial & mutation-killing suite (3/3 groups OK):
python3 -I -O -B -W error test_minimax_cryptanalysis_r5.py
```

**Offline (`--standalone`) vs. Live (`--live`) Provenance Boundary:**
- `--standalone --json` and `test_minimax_cryptanalysis_r5.py` execute 100% offline from any clone of `main`: `--standalone` recomputes all three pure-$\mathbb{Z}/\mathbb{F}_2/\mathbb{F}_{2^m}/\mathbb{Q}$ mathematical pillars live from scratch while replaying the pinned `MiniMax-AI/Research @ 57842cef` portal manifest (`diag_source = "standalone_pinned_fixture"`, `live_portal_inspected = false`; it does not read upstream files from disk).
- [`minimax_cryptanalysis_certificate.json`](minimax_cryptanalysis_certificate.json) (`a764ad27...`, inner `43adabf9fd67fcaa...`) is the pinned `--live --research-dir <path>` certificate generated against a read-only checkout of `MiniMax-AI/Research @ 57842cef`, verifying live SHA-256 digests, comment/string-stripped Lean purity across `BentSum/lean/`, `snf_audit_vectors.json`, `Blender/paper/main.tex`, all `94` rows of `verified_tii_94_summary.json`, and `.git/HEAD` (`diag_source = "live_portal_read"`, `live_portal_inspected = true`).

**External Verification Receipts:** `3/3` R5 OK; `aletheia v2.0.0 mutate --max-mutants 0`: `69/69` (`20` audit + `49` oracle, `100.0%`) KILLED + `93/93` (`39+54`, `100.0%`) AST `BoolOp` KILLED (`0` survivors, `truncated=False`); `aletheia v2.0.0 audit-check --strict-ancestors --safety-scan PASS` (`0` defects, `0` leaks, `0` safety findings); dual-family verified by `Muse Code` (Meta) and `verifier` (`0` Zone-B bypasses).

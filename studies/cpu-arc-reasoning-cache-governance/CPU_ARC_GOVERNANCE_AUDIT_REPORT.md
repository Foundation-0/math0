# Wave 2 Round 8 — Arm R8-6 (`AUDIT-077`): Mathematical, Cost-Accounting, Perturbation-Robustness & Sandbox-Security Audit of `CPU-ARC` (`arXiv:2611.09891v1`)

> **Owner:** `gravity-probe` | **Audit ID:** `AUDIT-077` | **Oracle Class:** `exact+anchor` | **Honest Novelty:** `N1`  
> **Target Preprint (Strictly Read-Only, `0` External Writes):** Belcak, Heinrich, Muralidharan, Diao & Molchanov, *CPU-ARC: Agentic Reasoning Caching for on-CPU Reasoning Reuse*, [`arXiv:2611.09891v1`](https://arxiv.org/abs/2611.09891) (`28` pp, `2611.09891.pdf` `4d90b5fd...`, `2611.09891.txt` `75fe8eee...`, `2611.09891_layout.txt` `47b904bc...`, `24/24` verbatim newline anchors verified; plus `Moissanite-Labs/warp-drive#15` `blueprints/sandbox/warp-sandbox-exec.sh` `d67b716e...`, `7/7` verbatim anchors verified)  
> **3-Axis Trace-Distillation Triangle:** Context/Skill Layer (LangChain Knowledge Factory, `AUDIT-076R VERIFIED`) ↔ Weight/LoRA Layer (`sous-labs/songe`, `AUDIT-073R VERIFIED` & `Moissanite-Labs/warp-drive#15`, `AUDIT-066R VERIFIED`) ↔ CPU-Executable Code Layer (`CPU-ARC` `arXiv:2611.09891v1`, `AUDIT-077` & `Foundation-0/aletheia v1.4.0`, `AUDIT-067R VERIFIED`)  
> **Artifacts (`symbiosis/round8/arm6-cpu-arc/`):**
> - [`cpu_arc_governance_audit.py`](cpu_arc_governance_audit.py) (`sha256: 347ec31f30b6f7c77e86a6e026f880caaa264114ba95a209943108d9829deecc`; pure Python 3 stdlib, ZERO floats, ZERO bare `assert`s)
> - [`test_cpu_arc_governance_r5.py`](test_cpu_arc_governance_r5.py) (`sha256: d57e3cf9a714b3adcd2deb04ae69e59cd8f27e749452b6cd906492b00ca90801`; `7/7` isolated `-I` test suites, **`67/67` `100.0%` R5 KILLED**, `0` survivors)
> - [`cpu_arc_governance_certificate.json`](cpu_arc_governance_certificate.json) (`sha256: 969cd32a73dbd35183c07adce48fc9031807d6c76538c40dfd4fcb8779098d88`, `canonical_sha256: 9b2740560b324dac3186037d2cc1c0d9b040d147a9fcc59cb354b185d24ee117`, ZERO floats)

---

## 1. Law-2 Steelman: What `CPU-ARC` Gets Genuinely Right

Clean-room verification of `arXiv:2611.09891v1` confirms a genuinely high-leverage architectural thesis:
1. **Decoupling Search from Execution (`O1`/`O2`, `Sec. 1`):** Once an expensive frontier model (`Claude Opus 4.5`) solves a structured reasoning template, executing the arithmetic/algorithmic core in deterministic Python on CPU eliminates multi-thousand-token decoding slips — explaining why `C Acc` exceeds `S Acc` on competition math (`AIME '25`: `93.3%` vs `83.3%`; `AIME '26`: `96.7%` vs `90.0%`, `Table 2`).
2. **Verified Per-Invocation Token Savings (`Tables 2–10`, `Sec. 3.5`):** Exact pure-$\mathbb{Q}$ recomputation of `Source` (`Opus 4.5` `$5/M` in, `$25/M` out) and `Cache` (`Llama 3.2 1B` `$0.023/M` in, `$0.194/M` out summed across `Target + Extractor + Converter`) matches `Table 2`'s `16.3x`–`291.1x` per-invocation savings multipliers across all `8/8` benchmarks (exact unrounded `88.7x`, `262.3x`, `290.9x`, `281.4x`, `38.1x`, `16.2x`, `22.8x`, `82.9x`).
3. **Static Compilation & Auditability (`Sec. 2.2.3`, `Fig. 7` & `Fig. 13`):** Resolving `do()` / `load()` into plain Python calls removes runtime FAISS/EmbeddingGemma dispatch overhead and produces inspectable source modules — making compiled ARCs natural targets for `aletheia v1.4.0` R4/R5 verification and OS-level sandboxing.

---

## 2. Independently Verified Findings (`CARC-01` – `CARC-05`)

### 2.1 `CARC-01` — Exact Pure-$\mathbb{Q}$ Builder Cost Accounting Anomaly & Break-Even Regime Collapse (`Sec. 3.5 L748-752`, `L786-789`, `App. C Tables 3–10`)

Recomputing all `8/8` Appendix C token tables in exact `Fraction` arithmetic exposes **two quantitative flaws** in `CPU-ARC`'s headline cost claims:

1. **8/8 Systematic Builder Token-Conservation & Pricing Anomaly:** Across **every single benchmark (`8/8`)**, `Cache Rd + Cache Wr > Avg In` (negative implied uncached tokens from `-7,888` on `GSM8K` to `-16,321` on `GPQA Diamond`), proving `Avg In` is not the sum of uncached + cached input tokens. Applying the paper's stated `Opus 4.5` rates (`$5/M` in, `$25/M` out, `$6.25/M` cache-write, `$0.50/M` cache-read):
   - Upper model $b_A = (\text{AvgIn}-\text{CacheRd})\cdot \$5/\text{M} + \text{CacheRd}\cdot \$0.50/\text{M} + \text{CacheWr}\cdot \$6.25/\text{M} + \text{AvgOut}\cdot \$25/\text{M}$ **strictly overpredicts** reported Builder cost on **`8/8` benchmarks** by `+$0.0661` to `+$0.1244` (raising `GSM8K` `Build×` from `83.7x` to `90.0x`).
   - Lower floor $b_D = \text{CacheRd}\cdot \$0.50/\text{M} + \text{CacheWr}\cdot \$6.25/\text{M} + \text{AvgOut}\cdot \$25/\text{M}$ (zero uncached input) **strictly underpredicts** reported Builder cost on **`8/8` benchmarks** by `-$0.0524` to `-$0.0949`.
   - Furthermore, `Builder` omits Phase-5 LM Judge $\mathcal{J}$ (`2× Opus 4.5` with extended thinking, `L421, L740`), `Appendix D`'s `10× Opus 4.5` synthetic augmentation + `Llama 3.2 1B` GPU SFT (`L2326`), and `EmbeddingGemma` (300M) CPU retrieval overhead (`L735`).
2. **Exact Generalized Break-Even Law & Silent-Error Collapse (`compute_cpu_arc_breakeven_exact`):** The paper's break-even formula $N_{\text{ideal}} = \lceil B / (S - C) \rceil$ (`L786`: `13` on `AIME '25`, `90` on `GSM8K`, exact match to `L789`) assumes `100%` cache hit rate and `0%` error penalty. Under hit rate $h \in (0, 1]$, explicit fallback rate $e_{\text{fb}}$, silent-error rate $e_{\text{sil}} = 1 - \text{Combined}_{\text{Table 2}}$ (`3.6%`–`9.2%`), and silent-error penalty $L_{\text{err}}$, per-query expected savings are $\Delta = h\,((1 - e_{\text{fb}})S - C - e_{\text{sil}} L_{\text{err}})$ and break-even exists iff $\Delta > 0$ at $N^* = \lceil B_{\text{eff}} / \Delta \rceil$.

| Benchmark | `AvgIn - CR - CW` | `b_D` Floor (`$`) | Reported `B` (`$`) | `b_A` Upper (`$`) | Ideal $N^*$ (`h=1, L=0`) | `h=1/2, L=0` | `e_sil` (`1 - Comb.`) | `h=1/2, L_err = 13S` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `MATH-500` | `-10,654` | `1.1117` | `1.1818` | `1.2664` | `31` | `62` | `21/250` (`8.4%`) | **`∞` (COLLAPSE)** |
| `AIME '24` | `-12,564` | `1.3367` | `1.4198` | `1.5211` | `13` | `26` | `49/1000` (`4.9%`) | `72` (`5.5x` jump) |
| `AIME '25` | `-12,678` | `1.3635` | `1.4517` | `1.5568` | `13` | `25` | `33/500` (`6.6%`) | `175` (`13.5x` jump) |
| `AIME '26` | `-15,193` | `1.4648` | `1.5477` | `1.6555` | `13` | `26` | `23/250` (`9.2%`) | **`∞` (COLLAPSE)** |
| `GPQA Diamond` | `-16,321` | `1.6831` | `1.7781` | `1.9025` | `26` | `52` | `3/50` (`6.0%`) | `261` (`10.0x` jump) |
| `GSM8K` | `-7,888` | `0.7956` | `0.8481` | `0.9142` | `90` | `179` | `3/40` (`7.5%`) | **`∞` (COLLAPSE)** |
| `MMLU-Pro` | `-10,836` | `1.3251` | `1.4084` | `1.5144` | `43` | `86` | `81/1000` (`8.1%`) | **`∞` (COLLAPSE)** |
| `SciBench` | `-13,287` | `1.1864` | `1.2572` | `1.3455` | `30` | `59` | `9/250` (`3.6%`) | `112` (`3.7x` jump) |

On `GSM8K`, a silent-error cost of just `$0.13` (`13/100`) yields exact per-query net savings **`-1/8000` (`-$0.000125/query < 0`)** — the cache **never breaks even**!

### 2.2 `CARC-02` — Live Silent Branch Overfitting, Negation Substring Bugs & Broken Fallback Contract in the Paper's Own Worked Code (`Fig. 1`, `App. A`, `App. B`)
1. **Appendix A (`Fig. 5a L995-996`, `Fig. 6 L1115-1123`):** `if "C" in temp_unit: temp_kelvin = temp_value + 273` drops `3/20 K` (`273` vs `273.15`) and silently treats `"32 F"` as `32 K` instead of `5463/20 K` (**`4823/5463 ≈ 88.28%` relative error**); `pressure_kpa = n * R * T / volume_value` ignores volume units (`4.860 m^3` vs `4.860 dm^3` produces an exact **`1000/1` (`1,000x`)** pressure error with zero refusal); and `gas_model` (`"van der Waals"`) is narrated (`L1070`) without ever branching!
2. **Appendix B (`Fig. 11a L1438-1440`):** `any(kw in volume_constraint.lower() for kw in ["fixed", "constant", "unchanging", "unchanged"])` produces **`4/4` negation false positives** (`"volume is not fixed"`, `"non-constant volume"`, `"unfixed container"`, `"not unchanged volume"`) -> silently returns `w = 0`!
3. **Broken Fallback Contract (`Fig. 1 L168` vs `Fig. 12 L1661`):** `serve(request)` falls back to `llm(request)` ONLY when `result is False` or `CacheInvocationError` is raised (`L168`). Yet `Fig. 12` returns `{'work value': None, 'work with units': 'requires further calculation', ...}` on non-isochoric inputs — a truthy `dict` (`result is not False` is **`True`**), silently returning `None` to the caller instead of invoking `llm(request)`! Closed fail-closed by `validate_cpu_arc_fallback_contract`.

### 2.3 `CARC-03` — Evaluation Log Leakage & Single-Family Self-Judging (`Sec. 3.2 L535`, `Sec. 3.4 L740`, `App. D.1 L2320`)
`Appendix D.1 (L2320)` harvests `~20%` of the Section 3 *evaluation benchmark* invocation logs and amplifies them `10×` via `Opus 4.5` (`L2326`) to fine-tune `Llama 3.2 1B`, without reporting a benchmark-disjoint holdout split (`CS-08` / `AUDIT-063R2` split-leakage class). Moreover, Source $\mathcal{S}$, Builder $\mathcal{B}$, Perturbation Generator $\mathcal{G}$, Generation Judges $\mathcal{J}_G$, and Testing Judges $\mathcal{J}_T$ are **all `Claude Opus 4.5`** (`L739-741`), with perturbation testing survivorship-filtered to golden-passing entries (`L535`).

### 2.4 `CARC-04` — Arbitrary Code Execution (ACE), Dynamic `do()` Registry Hijacking & Unverified Master-Cache Merge (`Sec. 2.1 L247,260-261`, `Sec. 3.4 L743`)
`ast.literal_eval()` (`L260`) guards only `smart_convert`, NOT LLM-synthesized Python bodies executing with `invoke_tool(ctx, name, args)` (`"e.g., terminal"`, `L261`). Dynamic cosine-similarity `do()` dispatch (`L247`) over an immediately merged mutable `master cache` (`L743`) allows a single newly inserted entry to silently hijack existing callers (`Sec. 2.1 L239-242`). Closed fail-closed by `audit_cpu_arc_python_ast` (blocks disallowed/relative/wildcard imports, forbidden builtins, `__dunder__` gadgets, `ctx.invoke_tool` / aliasing / dynamic / Ring-0 tools like `terminal`, and bare `assert`s) + `evaluate_cpu_arc_entry_admission` (requires cross-family verifier, `>= 2` non-`q(o)` perturbation proofs, `100%` R5 mutation kill, 64-hex SHA-256 `callee_pins` on `do()` calls, `0` eval-log overlap, and canonical `warp-sandbox-exec.sh` `--unshare-all --unshare-net --clearenv --seccomp` isolation).

---

## 3. The Round-8 3-Axis Trace-Distillation Triangle (`CARC-05`)

| Axis | Round-8 Exemplar | Distilled Artifact | Primary Unverified Failure Mode | Verified `aletheia v1.4.0` Ring-0 Closure |
|---|---|---|---|---|
| **1. Context / Skill** | LangChain Knowledge Factory (`AUDIT-076R VERIFIED`) | Skills, Domain Knowledge, Data Access Guidance | Biba/BLP poisoning (`KF-01`), Goodhart drift (`+105.31%`, `KF-02`), LWW/DAG races (`KF-03`) | `knowledge_factory_governor.py` (`108/108` R5, 3-role separation, hash-chained ledger) |
| **2. Weight / LoRA** | `sous-labs/songe` (`AUDIT-073R VERIFIED`) & `warp-drive#15` (`AUDIT-066R VERIFIED`) | Idle-compute MLX LoRA / 4-bit fused serving weights | Clipped-KL reversal (`SNG-01`), 1-win bootstrap (`SNG-02`), stale fusion (`SNG-03`) | Bregman KL + clustered Ville supermartingale + Stage 1–4 `warp-modeld` verifier & rollback |
| **3. CPU-Executable Code** | `CPU-ARC` `arXiv:2611.09891v1` (`AUDIT-077`) & `aletheia v1.4.0` (`AUDIT-067R VERIFIED`) | Python semantic functions + compiled CPU modules + 1B SLM | Builder accounting gap & silent-error collapse (`CARC-01`), branch/negation/fallback bugs (`CARC-02`), 20% eval leakage (`CARC-03`), ACE/`do()` hijack (`CARC-04`) | `cpu_arc_governance_audit.py` (`67/67` R5) AST sandbox + `warp-sandbox-exec.sh` + 64-hex `callee_pins` + cross-family R5 gate |

---

## 4. Strict Law-4 `N0` Quarantine & Verification Receipts

- **Quarantined strictly as `N0` (`R8-N0-08`, `R8-N0-09`, `R8-N0-10`, `R8-N0-11`, `R8-N0-12`):** `arXiv:2611.09891v1` (*CPU-ARC*), classical memoization / PAL / Program-of-Thought / DreamCoder, standard amortized break-even algebra, Linux `bwrap`/`seccomp`/`Landlock` sandboxing, and prior verified expedition artifacts (`AUDIT-066R`, `AUDIT-067R`, `AUDIT-073R`, `AUDIT-076R`). Honest novelty classification: **`N1`**.
- **Clean-Room `aletheia v1.4.0` Receipts:**
  - `4/4` isolated `-I` R4 bit-identical (`live --json`: `969cd32a...` == committed cert; `--standalone --json`: `12ca8a4c...`; human: `d49d79c7...`; `test_cpu_arc_governance_r5.py`: `7/7` OK across all 4 modes).
  - `aletheia v1.4.0 mutate cpu_arc_governance_audit.py --work-root . --max-mutants 500 --add-cwd`: **`67/67` (`100.0%`) KILLED, `0` SURVIVORS**.
  - `aletheia v1.4.0 audit-check . --strict-ancestors --scripts cpu_arc_governance_audit.py test_cpu_arc_governance_r5.py`: verified clean (`0` CRLF, `0` `__pycache__`, `0` `/home/` leaks, `0` bare `assert`s, `0` JSON floats/errors, `0` broken relative Markdown links, `0` ancestor permission findings).

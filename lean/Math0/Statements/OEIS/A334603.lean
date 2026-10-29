/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A334603: the period of the decimal expansion of `1/11^n`

Source: https://oeis.org/A334603, _Bernard Schott_, May 07 2020. Verbatim:
> Conjecture proposed by the authors in References page 205: if p is a prime with gcd(p,30) = 1
> and if the period of 1/p is m then the period of 1/p^n is m*p^(n-1).

and (FORMULA section):
> a(n) = 2 * 11^(n-1) [conjectured, see comments].

The reference is J.-M. De Koninck & A. Mercier, *1001 Problèmes en Théorie Classique des
Nombres*, Problème 346, Ellipses 2004. The entry's name is "Period of the fraction 1/11^n for
n >= 1." (offset `1`).

## Encoding

* `period m` is the period of the decimal expansion of `1/m` for `m` coprime to `10`: the least
  `k ≥ 1` with `10 ^ k ≡ 1 [MOD m]`, i.e. the multiplicative order of `10` modulo `m`. For such
  `m` the expansion of `1/m` is purely periodic (`1/m = c / (10^k - 1)` with
  `c = (10^k - 1)/m` exactly when `m ∣ 10^k - 1`), so its minimal period is this order; this is
  also what the entry's programs compute (`MultiplicativeOrder[10, 11^n]`,
  `znorder(Mod(10, 11^n))`). The definition uses `Nat.find`, which needs a witness: Euler's
  theorem gives `10 ^ φ(m) ≡ 1 [MOD m]`. For `m` not coprime to `10` we set `period m = 0`;
  this case never occurs below. (For `m = 1` the definition gives `1`, while A051626 lists `0`
  since `1/1` terminates; `m = 1` never occurs below either.) `period_eq_orderOf` proves
  `period m = orderOf (10 : ZMod m)` for `m` coprime to `10`.
* `a n = period (11 ^ n)` (OEIS offset `1`; `a 0 = period 1 = 1` is not a term).
* `a_data` checks all 20 listed terms `a(1), …, a(20)` in the kernel. A naive search up to
  `a(20) ≈ 1.2·10^20` is infeasible, so it goes through the order certificate
  `orderOf_eq_of_pow_and_pow_div_prime` (`10^L ≡ 1` and `10^(L/q) ≢ 1` for each prime `q ∣ L`),
  with the modular powers computed by binary exponentiation `powMod` (proved equal to
  `b ^ e % m`). `period_data` checks `period` against the 35 terms of A051626 ("Period of decimal
  representation of 1/n") with `3 ≤ n ≤ 90` and `gcd(n, 10) = 1`.
* `statement` is the conjecture of the FORMULA line, the one specific to this sequence:
  `a(n) = 2 * 11^(n-1)` for every index `n ≥ 1` of the sequence.
* `statement_general` is the book conjecture quoted in the COMMENTS line, of which `statement` is
  the case `p = 11` (`period 11 = 2`): for every prime `p` with `gcd(p, 30) = 1` and every
  `n ≥ 1` (the exponent `n - 1` must be a natural number, and `1/p^0 = 1` has no period),
  `period (p ^ n) = period p * p ^ (n - 1)`. Such `p` is coprime to `10`, so `period` is the
  genuine period there.
-/

namespace Math0.Statements.A334603

/-- For `m` coprime to `10` some positive power of `10` is `≡ 1 (mod m)` (Euler's theorem). -/
theorem exists_pow_modEq_one {m : ℕ} (h : Nat.Coprime 10 m) :
    ∃ k, 0 < k ∧ 10 ^ k ≡ 1 [MOD m] := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact absurd (Nat.coprime_zero_right 10 |>.1 h) (by norm_num)
  exact ⟨Nat.totient m, Nat.totient_pos.2 (Nat.pos_of_ne_zero hm), Nat.ModEq.pow_totient h⟩

/-- The period of the decimal expansion of `1/m` for `m` coprime to `10`: the least `k ≥ 1` with
`10 ^ k ≡ 1 (mod m)` (the multiplicative order of `10` modulo `m`). Set to `0` when
`gcd(m, 10) ≠ 1` (never used). -/
def period (m : ℕ) : ℕ :=
  if h : Nat.Coprime 10 m then Nat.find (exists_pow_modEq_one h) else 0

/-- A334603: the period of the fraction `1/11^n` (offset `1`). -/
def a (n : ℕ) : ℕ := period (11 ^ n)

/-! ### Characterizations of `period` -/

theorem period_eq_iff {m L : ℕ} (hm : Nat.Coprime 10 m) :
    period m = L ↔ (0 < L ∧ 10 ^ L ≡ 1 [MOD m]) ∧
      ∀ k, k < L → ¬ (0 < k ∧ 10 ^ k ≡ 1 [MOD m]) := by
  rw [period, dif_pos hm, Nat.find_eq_iff]

theorem pow_eq_one_iff (m k : ℕ) : (10 : ZMod m) ^ k = 1 ↔ 10 ^ k ≡ 1 [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-- For `m` coprime to `10`, `period m` is the multiplicative order of `10` in `ZMod m`. -/
theorem period_eq_orderOf {m : ℕ} (hm : Nat.Coprime 10 m) :
    period m = orderOf (10 : ZMod m) := by
  obtain ⟨k, hk0, hk⟩ := exists_pow_modEq_one hm
  have hpos : 0 < orderOf (10 : ZMod m) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk0, (pow_eq_one_iff m k).2 hk⟩)
  rw [period_eq_iff hm]
  refine ⟨⟨hpos, (pow_eq_one_iff m _).1 (pow_orderOf_eq_one _)⟩, fun j hj ⟨hj0, hj1⟩ => ?_⟩
  exact (orderOf_eq_iff hpos |>.1 rfl).2 j hj hj0 ((pow_eq_one_iff m j).2 hj1)

/-- Order certificate: `10 ^ L ≡ 1` and `10 ^ (L / q) ≢ 1` for every prime `q ∣ L`. -/
theorem period_eq_of_cert {m L : ℕ} (hm : Nat.Coprime 10 m) (hL : 0 < L)
    (h1 : 10 ^ L ≡ 1 [MOD m]) (h2 : ∀ q, q.Prime → q ∣ L → ¬ 10 ^ (L / q) ≡ 1 [MOD m]) :
    period m = L := by
  rw [period_eq_orderOf hm]
  exact orderOf_eq_of_pow_and_pow_div_prime hL ((pow_eq_one_iff m L).2 h1)
    fun q hq hqL h => h2 q hq hqL ((pow_eq_one_iff m _).1 h)

/-! ### Kernel-friendly modular exponentiation -/

/-- Binary exponentiation `b ^ e % m`, with a fuel argument. -/
def powModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | fuel + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then powModAux m fuel (b * b % m) (e / 2) * b % m
    else powModAux m fuel (b * b % m) (e / 2)

/-- `powMod b e m = b ^ e % m` (`powMod_eq`). -/
def powMod (b e m : ℕ) : ℕ := powModAux m e b e

theorem powModAux_eq (m : ℕ) :
    ∀ fuel b e, e < 2 ^ fuel → powModAux m fuel b e = b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this
    simp [powModAux]
  | succ f ih =>
    intro b e he
    have he2 : e / 2 < 2 ^ f := by
      rw [pow_succ] at he
      omega
    rw [powModAux, ih _ _ he2, ← Nat.pow_mod]
    split_ifs with h0 h1
    · simp [h0]
    · rw [Nat.mod_mul_mod, ← pow_two, ← pow_mul, ← pow_succ]
      congr 2
      omega
    · rw [← pow_two, ← pow_mul]
      congr 2
      omega

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m :=
  powModAux_eq m e b e Nat.lt_two_pow_self

theorem modEq_one_iff_powMod (m e : ℕ) : 10 ^ e ≡ 1 [MOD m] ↔ powMod 10 e m = 1 % m := by
  rw [powMod_eq]
  rfl

/-! ### Sanity checks -/

/-- The prime divisors of `2 * 11 ^ i` are `2` and `11`. -/
theorem prime_dvd_two_mul_pow {q i : ℕ} (hq : q.Prime) (h : q ∣ 2 * 11 ^ i) : q = 2 ∨ q = 11 := by
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 (hq.dvd_of_dvd_pow h))

/-- The certificate for the listed terms, checked in the kernel. -/
theorem cert_data : ∀ i < 20,
    powMod 10 (2 * 11 ^ i) (11 ^ (i + 1)) = 1 % 11 ^ (i + 1) ∧
    powMod 10 (2 * 11 ^ i / 2) (11 ^ (i + 1)) ≠ 1 % 11 ^ (i + 1) ∧
    (i = 0 ∨ powMod 10 (2 * 11 ^ i / 11) (11 ^ (i + 1)) ≠ 1 % 11 ^ (i + 1)) := by
  decide +kernel

/-- The definition reproduces all 20 terms `a(1), …, a(20)` listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 20).map (fun i => a (i + 1)) =
    [2, 22, 242, 2662, 29282, 322102, 3543122, 38974342, 428717762, 4715895382,
      51874849202, 570623341222, 6276856753442, 69045424287862, 759499667166482,
      8354496338831302, 91899459727144322, 1010894056998587542, 11119834626984462962,
      122318180896829092582] := by
  have key : ∀ i < 20, a (i + 1) = 2 * 11 ^ i := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := cert_data i hi
    refine period_eq_of_cert (Nat.Coprime.pow_right _ (by norm_num)) (by positivity)
      ((modEq_one_iff_powMod _ _).2 h1) fun q hq hqL h => ?_
    rw [modEq_one_iff_powMod] at h
    rcases prime_dvd_two_mul_pow hq hqL with rfl | rfl
    · exact h2 h
    · rcases h3 with rfl | h3
      · norm_num at hqL
      · exact h3 h
  rw [List.map_congr_left fun i hi => key i (List.mem_range.1 hi)]
  decide +kernel

/-- A decidable check that `period m = L`: `gcd(10, m) = 1`, `L ≥ 1`, `10 ^ L ≡ 1 (mod m)` and
`10 ^ k ≢ 1 (mod m)` for `0 < k < L`. -/
def checkPeriod (m L : ℕ) : Bool :=
  Nat.gcd 10 m == 1 && 0 < L && 10 ^ L % m == 1 % m &&
    (List.range L).all fun k => k == 0 || 10 ^ k % m != 1 % m

theorem period_eq_of_checkPeriod {m L : ℕ} (h : checkPeriod m L = true) : period m = L := by
  simp only [checkPeriod, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hm, hL⟩, h1⟩, h2⟩ := h
  rw [period_eq_iff hm]
  refine ⟨⟨hL, h1⟩, fun k hk ⟨hk0, hk1⟩ => ?_⟩
  rcases h2 k hk with h | h
  · omega
  · exact h hk1

/-- `period` agrees with the 35 terms `A051626(m)` listed in OEIS with `3 ≤ m ≤ 90` and
`gcd(m, 10) = 1` (A051626: period of the decimal representation of `1/m`; kernel-checked). -/
theorem period_data : ∀ p ∈ [(3, 1), (7, 6), (9, 1), (11, 2), (13, 6), (17, 16), (19, 18),
    (21, 6), (23, 22), (27, 3), (29, 28), (31, 15), (33, 2), (37, 3), (39, 6), (41, 5), (43, 21),
    (47, 46), (49, 42), (51, 16), (53, 13), (57, 18), (59, 58), (61, 60), (63, 6), (67, 33),
    (69, 22), (71, 35), (73, 8), (77, 6), (79, 13), (81, 9), (83, 41), (87, 28), (89, 44)],
    period p.1 = p.2 := by
  intro p hp
  exact period_eq_of_checkPeriod (by revert p; decide +kernel)

/-! ### The conjectures -/

/-- Conjecture (A334603, FORMULA, "conjectured, see comments"): the period of the decimal
expansion of `1/11^n` is `2 * 11^(n-1)`, for every `n ≥ 1`. -/
def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = 2 * 11 ^ (n - 1)

/-- The general conjecture of De Koninck & Mercier quoted in the COMMENTS of A334603: if `p` is a
prime with `gcd(p, 30) = 1` and the period of `1/p` is `m`, then for every `n ≥ 1` the period of
`1/p^n` is `m * p^(n-1)`. -/
def statement_general : Prop :=
  ∀ p n : ℕ, p.Prime → Nat.gcd p 30 = 1 → 1 ≤ n → period (p ^ n) = period p * p ^ (n - 1)

end Math0.Statements.A334603

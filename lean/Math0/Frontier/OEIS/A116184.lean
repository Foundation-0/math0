/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A116184
import Math0.Audit

/-!
# A116184: Adamchuk's conjectures on `37^3 ∣ numerator (∑_{k=1}^{36} 1/k^n)`

We prove both claims of the comment in OEIS A116184: (a) `37^3` divides the numerator of
`H(36, n) = ∑_{k=1}^{36} 1/k^n` for every `n = 3 + 36k`, and (b) every prime term `p > 37`
satisfies `p ≡ -1 (mod 37)`.

By `isTerm_iff_check`, `IsTerm n` holds iff `∑_c c^n ≡ 0 (mod 37^3)`, where `c` runs over the
36 residues `36!/k mod 37^3`. Each `c` is prime to `37`, so `c^36 = 1 + 37 a_c` in
`ZMod (37^3)` (Fermat), and the binomial theorem truncated at `37^3` gives, writing
`n = r + 36 t`,
`c^n = c^r (1 + 37 a_c t + 37^2 a_c^2 t (t - 1) / 2)`.
Summing, `∑ c^n = S₀(r) + 37 t S₁(r) + 37^2 (t (t - 1) / 2) S₂(r)` with `S_j(r) = ∑ c^r a_c^j`.

* (a) For `r = 3` one computes `S₀(3) ≡ 0 (mod 37^3)`, `S₁(3) ≡ 0 (mod 37^2)` and
  `S₂(3) ≡ 0 (mod 37)`, so the sum vanishes for every `t`.
* (b) The expression only depends on `r = n mod 36` and `t mod 37^2`. A prime `p > 37` has `r`
  odd and prime to `3` and `p ≢ 0 (mod 37)`; a kernel-checked search over the `12 · 1369` such
  pairs `(r, t mod 37^2)` shows the sum vanishes only when `p ≡ 36 (mod 37)`.
-/

namespace Math0.Frontier.A116184
open Math0.Statements.A116184

/-- `A c = (c^36 mod 37^3 - 1) / 37`, so that `c^36 ≡ 1 + 37 * A c (mod 37^3)`. -/
private def A (c : ℕ) : ℕ := (c ^ 36 % 50653 - 1) / 37

/-- Every coefficient `c` satisfies `c^36 ≡ 1 + 37 * A c (mod 37^3)` (kernel-checked). -/
private theorem A_spec : ∀ c ∈ coeffs, c ^ 36 % 50653 = 1 + 37 * A c := by decide +kernel

/-- `s0 r = ∑ c^r`. -/
private def s0 (r : ℕ) : ℕ := (coeffs.map (fun c => c ^ r)).sum
/-- `s1 r = ∑ c^r * A c`. -/
private def s1 (r : ℕ) : ℕ := (coeffs.map (fun c => c ^ r * A c)).sum
/-- `s2 r = ∑ c^r * (A c)^2`. -/
private def s2 (r : ℕ) : ℕ := (coeffs.map (fun c => c ^ r * A c ^ 2)).sum

/-- `check n` says that `∑ c^n` vanishes in `ZMod (37^3)`. -/
private theorem check_iff (n : ℕ) :
    check n = true ↔ (coeffs.map (fun c : ℕ => (c : ZMod 50653) ^ n)).sum = 0 := by
  rw [check, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_list_sum, List.map_map]
  have hf : ((Nat.cast : ℕ → ZMod 50653) ∘ fun c => c ^ n % 50653) =
      fun c : ℕ => (c : ZMod 50653) ^ n := by
    funext c; simp [ZMod.natCast_mod]
  rw [hf]

/-- If `x^36 = 1 + 37 a` in `ZMod (37^3)`, then
`x^(r + 36 t) = x^r (1 + 37 a t + 37^2 a^2 t (t - 1) / 2)`. -/
private theorem key_pow (x a : ZMod 50653) (hx : x ^ 36 = 1 + 37 * a) (r t : ℕ) :
    x ^ (r + 36 * t) = x ^ r * (1 + 37 * a * t + 1369 * 25327 * a ^ 2 * t * (t - 1)) := by
  rw [pow_add, pow_mul, hx]
  congr 1
  have h : (50653 : ZMod 50653) = 0 := by decide
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (-1369 * a ^ 2 * t + 25327 * a ^ 3 * t * (t - 1)) * h

/-- Distributing a sum over `f c * (1 + α g c + β g c ^ 2)`. -/
private theorem sum_expand (L : List ℕ) (f g : ℕ → ZMod 50653) (α β : ZMod 50653) :
    (L.map (fun c => f c * (1 + α * g c + β * g c ^ 2))).sum =
      (L.map f).sum + α * (L.map (fun c => f c * g c)).sum +
        β * (L.map (fun c => f c * g c ^ 2)).sum := by
  induction L with
  | nil => simp
  | cons c L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `∑ c^(r + 36 t) = s0 r + 37 t s1 r + 37^2 t (t - 1) / 2 s2 r` in `ZMod (37^3)`. -/
private theorem sum_pow (r t : ℕ) :
    (coeffs.map (fun c : ℕ => (c : ZMod 50653) ^ (r + 36 * t))).sum =
      (s0 r : ZMod 50653) + 37 * t * (s1 r : ZMod 50653) +
        1369 * 25327 * t * (t - 1) * (s2 r : ZMod 50653) := by
  have h1 : coeffs.map (fun c : ℕ => (c : ZMod 50653) ^ (r + 36 * t)) =
      coeffs.map (fun c : ℕ => ((c : ZMod 50653) ^ r) * (1 + (37 * t) * (A c : ZMod 50653) +
        (1369 * 25327 * t * (t - 1)) * (A c : ZMod 50653) ^ 2)) := by
    apply List.map_congr_left
    intro c hc
    have hx : (c : ZMod 50653) ^ 36 = 1 + 37 * (A c : ZMod 50653) := by
      have := A_spec c hc
      rw [← Nat.cast_pow, ← ZMod.natCast_mod, this]; push_cast; ring
    rw [key_pow _ _ hx]; ring
  rw [h1, sum_expand]
  simp only [s0, s1, s2, Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_mul,
    Nat.cast_pow]

/-- The value of `∑ c^(r + 36 t)` only depends on `t mod 37^2`. -/
private theorem reduce_t (a0 a1 a2 : ZMod 50653) (t : ℕ) :
    a0 + 37 * (t : ZMod 50653) * a1 + 1369 * 25327 * (t : ZMod 50653) * (t - 1) * a2 =
      a0 + 37 * ((t % 1369 : ℕ) : ZMod 50653) * a1 +
        1369 * 25327 * ((t % 1369 : ℕ) : ZMod 50653) * ((t % 1369 : ℕ) - 1) * a2 := by
  have h : (50653 : ZMod 50653) = 0 := by decide
  have ht : (t : ZMod 50653) =
      ((t % 1369 : ℕ) : ZMod 50653) + 1369 * ((t / 1369 : ℕ) : ZMod 50653) := by
    have := congrArg (Nat.cast : ℕ → ZMod 50653) (Nat.mod_add_div t 1369)
    push_cast at this
    exact this.symm
  rw [ht]
  set u := ((t % 1369 : ℕ) : ZMod 50653)
  set q := ((t / 1369 : ℕ) : ZMod 50653)
  linear_combination (q * a1 + 37 * 25327 * q * (2 * u - 1 + 1369 * q) * a2) * h

/-- Table of `s0 r mod 37^3`. -/
private def T0 : List ℕ :=
  [36, 17797, 22866, 0, 8214, 49284, 19425, 10952, 30007, 2738, 43216, 24642, 37333, 23273, 47064,
    28749, 17353, 19166, 34447, 9583, 42106, 36963, 42143, 21904, 5587, 24642, 20424, 28749, 3404,
    5476, 36926, 19166, 40441, 24642, 6512, 1406]
/-- Table of `s1 r mod 37^3`. -/
private def T1 : List ℕ :=
  [27255, 37851, 5130, 10952, 37185, 925, 47846, 23199, 25461, 42698, 17066, 25900, 12906, 11840,
    35963, 16502, 22617, 13024, 32498, 31598, 46293, 9990, 28931, 18204, 44978, 9953, 46169, 34854,
    17651, 7474, 23664, 18278, 25941, 25086, 32483, 40830]
/-- Table of `s2 r mod 37^3`. -/
private def T2 : List ℕ :=
  [8850, 16404, 22783, 7215, 33961, 31556, 5163, 23268, 45035, 21525, 35844, 23502, 34570, 32968,
    7630, 40875, 4218, 9719, 17569, 4064, 31462, 29196, 41991, 38605, 13321, 30976, 30212, 11949,
    25518, 47635, 43575, 16202, 23121, 47622, 35174, 35312]

/-- `T0` tabulates `s0 r mod 37^3` (kernel-checked). -/
private theorem T0_spec : ∀ r < 36, T0.getD r 0 = s0 r % 50653 := by decide +kernel
/-- `T1` tabulates `s1 r mod 37^3` (kernel-checked). -/
private theorem T1_spec : ∀ r < 36, T1.getD r 0 = s1 r % 50653 := by decide +kernel
/-- `T2` tabulates `s2 r mod 37^3` (kernel-checked). -/
private theorem T2_spec : ∀ r < 36, T2.getD r 0 = s2 r % 50653 := by decide +kernel

/-- The test performed for one pair `(r, u)`. -/
private def okU (r a0 a1 a2 u : ℕ) : Bool :=
  (r + 36 * u) % 37 == 0 ||
    (a0 + 37 * u * a1 + 1369 * 25327 * u * (u + 50652) * a2) % 50653 != 0 ||
    (r + 36 * u) % 37 == 36

/-- The finite check behind part (b) (kernel-checked). -/
private theorem finite_b_aux : ∀ r < 36, r % 2 = 1 → r % 3 ≠ 0 → ∀ u < 1369,
    okU r (T0.getD r 0) (T1.getD r 0) (T2.getD r 0) u = true := by
  decide +kernel

/-- The finite check behind part (b), unpacked. -/
private theorem finite_b (r u : ℕ) (hr : r < 36) (h2 : r % 2 = 1) (h3 : r % 3 ≠ 0)
    (hu : u < 1369) (h37 : (r + 36 * u) % 37 ≠ 0)
    (hz : (T0.getD r 0 + 37 * u * T1.getD r 0 + 1369 * 25327 * u * (u + 50652) * T2.getD r 0)
      % 50653 = 0) :
    (r + 36 * u) % 37 = 36 := by
  have := finite_b_aux r hr h2 h3 u hu
  simp only [okU, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  omega

/-- Part (a): every `3 + 36 k` is a term. -/
private theorem part_a (k : ℕ) : IsTerm (3 + 36 * k) := by
  rw [isTerm_iff_check, check_iff, sum_pow]
  have h0 : (s0 3 : ZMod 50653) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; decide +kernel
  have h1 : ((37 * s1 3 : ℕ) : ZMod 50653) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; decide +kernel
  have h2 : ((1369 * s2 3 : ℕ) : ZMod 50653) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; decide +kernel
  push_cast at h1 h2
  linear_combination h0 + (k : ZMod 50653) * h1 +
    25327 * (k : ZMod 50653) * ((k : ZMod 50653) - 1) * h2

/-- Part (b): every prime term `p > 37` satisfies `p ≡ -1 (mod 37)`. -/
private theorem part_b (p : ℕ) (hp : p.Prime) (h37 : 37 < p) (ht : IsTerm p) :
    ∃ k : ℕ, p = 37 * k - 1 := by
  have h2 : p % 2 ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h); omega
  have h3 : p % 3 ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h); omega
  have h37' : p % 37 ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 37 (Nat.dvd_of_mod_eq_zero h); omega
  rw [isTerm_iff_check, check_iff] at ht
  have hpe : p = p % 36 + 36 * (p / 36) := (Nat.mod_add_div p 36).symm
  rw [hpe, sum_pow, reduce_t] at ht
  have hr : p % 36 < 36 := Nat.mod_lt _ (by norm_num)
  have hu : p / 36 % 1369 < 1369 := Nat.mod_lt _ (by norm_num)
  generalize hR : p % 36 = r at ht hr
  generalize hU : p / 36 % 1369 = u at ht hu
  have hz : (T0.getD r 0 + 37 * u * T1.getD r 0 + 1369 * 25327 * u * (u + 50652) * T2.getD r 0)
      % 50653 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff, T0_spec r hr, T1_spec r hr,
      T2_spec r hr]
    push_cast [ZMod.natCast_mod]
    have h : (50653 : ZMod 50653) = 0 := by decide
    linear_combination ht + (1369 * 25327 * (u : ZMod 50653) * (s2 r : ZMod 50653)) * h
  have key := finite_b r u hr (by omega) (by omega) hu (by omega) hz
  exact ⟨p / 37 + 1, by omega⟩

/-- Adamchuk's conjecture on A116184 holds: (a) `37^3` divides the numerator of `H(36, 3 + 36k)`
for every `k ≥ 0`, and (b) every prime `p > 37` with `37^3 ∣ numerator (H(36, p))` satisfies
`p ≡ -1 (mod 37)`. -/
theorem result : statement := ⟨part_a, part_b⟩

end Math0.Frontier.A116184

#math0_settles Math0.Frontier.A116184.result Math0.Statements.A116184.statement

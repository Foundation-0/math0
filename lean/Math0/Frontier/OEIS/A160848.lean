/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A160848
import Math0.Audit

/-!
# Barker's order-20 recurrence for the lines through an `8 × n` grid holds

We prove Colin Barker's conjecture for A160848: for all `n > 21`,
`a(n) = -a(n-2) + a(n-5) + a(n-6) + 2a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2a(n-13)
- a(n-14) - a(n-15) + a(n-18) + a(n-20)`.

**Column decomposition.** By `a_eq_aFast`, `a(n)` counts pairs `i < j < 8n` with `goodF i j`
(the two smallest grid points of a line). Adding the column `x = n` adds
`D(n) = 1 + ∑_{x<n} C(n, x)`, where `1` is the new vertical line and `C(n, x)` counts the good
pairs with `pt i` in column `x` and `pt j` in column `n`. With `a = n - x` and rows `y, t < 8`
the pair is good iff `gcd(a, |t-y|) = 1` and not (`2a ≤ n` and `t ≤ 2y < 8 + t`). Grouping the
64 row pairs by `b = |t - y|` gives `C(n, x) = G(a) - [n ≤ 2x] Gb(a)` with
`G(a) = ∑_b c_b [gcd(a,b)=1]` (`c = 8,14,12,10,8,6,4,2`) and
`Gb(a) = 8[gcd(a,0)=1] + 12 + 8[gcd(a,2)=1] + 4[gcd(a,3)=1]`.

**Second difference.** Shifting `x ↦ x + 1`, only the term with `n = 2x + 1` changes its
indicator, so `D(n+1) - D(n) = h(n+1)` with `h(m) = G(m) - [m even, m ≥ 2] Gb(m/2)`. Hence
`a(m+2) - 2a(m+1) + a(m) = h(m+1)`.

**Periodicity.** For `1 ≤ b ≤ 7`, `b ∣ 420` and `gcd(a, b) = gcd(a mod b, b)`, while
`gcd(a, 0) = a ≠ 1` for `a ≥ 2`. So `h(m) = h(m mod 420 + 420)` for `m ≥ 3`.

**Recurrence.** The characteristic polynomial factors as `(1 - x)² R(x)` with
`R = 1 + 2x + 4x² + 6x³ + 8x⁴ + 9x⁵ + 9x⁶ + 7x⁷ + 4x⁸ - 4x¹⁰ - 7x¹¹ - 9x¹² - 9x¹³ - 8x¹⁴
- 6x¹⁵ - 4x¹⁶ - 2x¹⁷ - x¹⁸`. So the recurrence at `n` is `∑_j r_j h(n-1-j) = 0`, which by
periodicity reduces to the 420 residues of `n`, checked in the kernel (`key`).
-/

namespace Math0.Frontier.A160848
open Math0.Statements.A160848

/-- One step of `countJ`. -/
private lemma countJ_succ (m : ℕ) : countJ (m + 1) = countJ m + countI m m := rfl

/-- One step of `countI`. -/
private lemma countI_succ (j m : ℕ) : countI j (m + 1) = countI j m + (goodF m j).toNat := by
  show cond (goodF m j) (countI j m + 1) (countI j m) = _
  cases goodF m j <;> rfl

/-- `countI j (m + k)` splits off the last `k` candidates `i`. -/
private lemma countI_add (j m k : ℕ) :
    countI j (m + k) = countI j m + ∑ y ∈ Finset.range k, (goodF (m + y) j).toNat := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, countI_succ, ih, Finset.sum_range_succ, Nat.add_assoc]

/-- `countI j (8n)` as a sum over the columns `x < n` and rows `y < 8`. -/
private lemma countI_mul (j n : ℕ) :
    countI j (8 * n) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range 8, (goodF (8 * x + y) j).toNat := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, countI_add, ih]; exact (Finset.sum_range_succ _ n).symm

/-- `countJ (m + k)` splits off the last `k` values of `j`. -/
private lemma countJ_add (m k : ℕ) :
    countJ (m + k) = countJ m + ∑ t ∈ Finset.range k, countI (m + t) (m + t) := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, countJ_succ, ih, Finset.sum_range_succ, Nat.add_assoc]

/-- The number of good pairs whose larger point lies in column `n`. -/
private def D (n : ℕ) : ℕ := ∑ t ∈ Finset.range 8, countI (8 * n + t) (8 * n + t)

/-- Adding the column `n` adds `D n` lines. -/
private lemma aFast_succ (n : ℕ) : aFast (n + 1) = aFast n + D n := by
  unfold aFast D
  rw [Nat.mul_succ, countJ_add]

/-- The number of good pairs from column `x` to column `n`. -/
private def C (n x : ℕ) : ℕ :=
  ∑ t ∈ Finset.range 8, ∑ y ∈ Finset.range 8, (goodF (8 * x + y) (8 * n + t)).toNat

/-- `goodF` between the points `(x, y)` and `(n, t)` of the grid. -/
private lemma goodF_eq {x y n t : ℕ} (hy : y < 8) (ht : t < 8) :
    goodF (8 * x + y) (8 * n + t) = decide (Nat.gcd (n - x) (t - y + (y - t)) = 1 ∧
      ¬(n ≤ 2 * x ∧ t ≤ 2 * y ∧ 2 * y < 8 + t)) := by
  have h1 : (8 * x + y) / 8 = x := by omega
  have h2 : (8 * x + y) % 8 = y := by omega
  have h3 : (8 * n + t) / 8 = n := by omega
  have h4 : (8 * n + t) % 8 = t := by omega
  rw [goodF, h1, h2, h3, h4]

/-- The pairs inside column `n` contribute exactly one line (the vertical one). -/
private lemma diag_part (n : ℕ) :
    ∑ t ∈ Finset.range 8, ∑ y ∈ Finset.range t, (goodF (8 * n + y) (8 * n + t)).toNat = 1 := by
  have : ∀ t ∈ Finset.range 8,
      ∑ y ∈ Finset.range t, (goodF (8 * n + y) (8 * n + t)).toNat =
      ∑ y ∈ Finset.range t,
        (decide (Nat.gcd 0 (t - y + (y - t)) = 1 ∧ ¬(t ≤ 2 * y ∧ 2 * y < 8 + t))).toNat := by
    intro t ht
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mem_range] at ht hy
    rw [goodF_eq (by omega) ht]
    simp [show n ≤ 2 * n by omega]
  rw [Finset.sum_congr rfl this]
  decide

/-- `D n = ∑_{x<n} C n x + 1`. -/
private lemma D_eq (n : ℕ) : D n = ∑ x ∈ Finset.range n, C n x + 1 := by
  unfold D C
  rw [← diag_part n, Finset.sum_comm (s := Finset.range n), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [countI_add, countI_mul, Finset.sum_comm (s := Finset.range n)]


/-- The indicator of `gcd(a, b) = 1`. -/
private def u (a b : ℕ) : ℕ := (decide (Nat.gcd a b = 1)).toNat

/-- `G a`: the number of row pairs `(t, y)` with `gcd(a, |t-y|) = 1`. -/
private def G (a : ℕ) : ℕ :=
  8 * u a 0 + 14 * u a 1 + 12 * u a 2 + 10 * u a 3 + 8 * u a 4 + 6 * u a 5 + 4 * u a 6 + 2 * u a 7

/-- `Gb a`: the number of row pairs `(t, y)` with `gcd(a, |t-y|) = 1` and
`t ≤ 2y < 8 + t` (the point `2(x,y) - (n,t)` has a valid row). -/
private def Gb (a : ℕ) : ℕ := 8 * u a 0 + 12 * u a 1 + 8 * u a 2 + 4 * u a 3

/-- Closed form of `C n x` in terms of `a = n - x`. -/
private lemma C_eq (n x : ℕ) :
    (C n x : ℤ) = G (n - x) - if n ≤ 2 * x then (Gb (n - x) : ℤ) else 0 := by
  have hC : C n x = ∑ t ∈ Finset.range 8, ∑ y ∈ Finset.range 8,
      (decide (Nat.gcd (n - x) (t - y + (y - t)) = 1 ∧
        ¬(n ≤ 2 * x ∧ t ≤ 2 * y ∧ 2 * y < 8 + t))).toNat := by
    unfold C
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun y hy => ?_
    rw [goodF_eq (Finset.mem_range.1 hy) (Finset.mem_range.1 ht)]
  rw [hC]
  generalize n - x = a
  by_cases hs : n ≤ 2 * x
  · simp [hs, Finset.sum_range_succ, G, Gb, u]
    ring
  · simp [hs, Finset.sum_range_succ, G, u]
    ring


/-- `hcl m = G m - [m even, m ≥ 2] Gb (m/2)`: the second difference of `a`. -/
private def hcl (m : ℕ) : ℤ := (G m : ℤ) - if m % 2 = 0 ∧ 2 ≤ m then (Gb (m / 2) : ℤ) else 0

/-- Shifting both columns by one changes `C` only when `n = 2x + 1`. -/
private lemma C_succ_sub (n x : ℕ) :
    (C (n + 1) (x + 1) : ℤ) - C n x = -(if n = 2 * x + 1 then (Gb (n - x) : ℤ) else 0) := by
  rw [C_eq, C_eq, Nat.add_sub_add_right]
  by_cases h1 : n = 2 * x + 1
  · rw [if_pos (by omega), if_neg (by omega), if_pos h1]; ring
  · rw [if_neg h1]
    by_cases h2 : n ≤ 2 * x
    · rw [if_pos (by omega), if_pos h2]; ring
    · rw [if_neg (by omega), if_neg h2]; ring

/-- The only `x < n` with `n = 2x + 1` is `x = n / 2`, for odd `n`. -/
private lemma sum_odd (n : ℕ) :
    ∑ x ∈ Finset.range n, (if n = 2 * x + 1 then (Gb (n - x) : ℤ) else 0) =
      if (n + 1) % 2 = 0 ∧ 2 ≤ n + 1 then (Gb ((n + 1) / 2) : ℤ) else 0 := by
  by_cases hn : n % 2 = 1
  · rw [if_pos (by omega)]
    rw [Finset.sum_eq_single (n / 2)]
    · rw [if_pos (by omega), show n - n / 2 = (n + 1) / 2 by omega]
    · intro x _ hx
      rw [if_neg (by omega)]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [if_neg (by omega)]
    exact Finset.sum_eq_zero fun x _ => if_neg (by omega)

/-- `D (n + 1) - D n = hcl (n + 1)`. -/
private lemma D_succ (n : ℕ) : (D (n + 1) : ℤ) = D n + hcl (n + 1) := by
  rw [D_eq, D_eq]
  push_cast
  rw [Finset.sum_range_succ']
  have h0 : (C (n + 1) 0 : ℤ) = G (n + 1) := by
    rw [C_eq]; simp
  have hs : ∑ x ∈ Finset.range n, (C (n + 1) (x + 1) : ℤ) =
      ∑ x ∈ Finset.range n, (C n x : ℤ) -
        ∑ x ∈ Finset.range n, (if n = 2 * x + 1 then (Gb (n - x) : ℤ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    linarith [C_succ_sub n x]
  rw [hs, sum_odd, h0, hcl]
  ring

/-- The second difference of `a` is `hcl`. -/
private lemma second_diff (m : ℕ) : (a (m + 2) : ℤ) - 2 * a (m + 1) + a m = hcl (m + 1) := by
  rw [a_eq_aFast, a_eq_aFast, a_eq_aFast, aFast_succ (m + 1), aFast_succ m]
  push_cast
  rw [D_succ]
  ring

/-- `gcd(a mod K + K, b) = gcd(a, b)` when `b ∣ K`. -/
private lemma gcd_mod_add (a b K : ℕ) (hb : b ∣ K) : Nat.gcd (a % K + K) b = Nat.gcd a b := by
  have h1 : Nat.gcd (a % K + K) b = Nat.gcd ((a % K + K) % b) b :=
    (Nat.gcd_comm _ _).trans (Nat.gcd_rec _ _)
  have h2 : Nat.gcd a b = Nat.gcd (a % b) b := (Nat.gcd_comm _ _).trans (Nat.gcd_rec _ _)
  have h3 : (a % K + K) % b = a % b := by
    obtain ⟨c, rfl⟩ := hb
    rw [Nat.add_mul_mod_self_left, Nat.mod_mul_right_mod]
  rw [h1, h2, h3]

/-- `u` is unchanged by `a ↦ a mod K + K` when `b ∣ K`. -/
private lemma u_mod_add (a b K : ℕ) (hb : b ∣ K) : u (a % K + K) b = u a b := by
  simp only [u, gcd_mod_add a b K hb]

/-- `gcd(a, 0) = a ≠ 1` for `a ≥ 2`. -/
private lemma u_zero (a : ℕ) (ha : 2 ≤ a) : u a 0 = 0 := by
  unfold u
  simp only [Nat.gcd_zero_right]
  rw [decide_eq_false (by omega)]
  rfl

/-- `G` has period `420` on `a ≥ 2`. -/
private lemma G_period (a : ℕ) (ha : 2 ≤ a) : G (a % 420 + 420) = G a := by
  unfold G
  rw [u_zero a ha, u_zero _ (by omega)]
  rw [u_mod_add a 1 420 (by norm_num), u_mod_add a 2 420 (by norm_num),
    u_mod_add a 3 420 (by norm_num), u_mod_add a 4 420 (by norm_num),
    u_mod_add a 5 420 (by norm_num), u_mod_add a 6 420 (by norm_num),
    u_mod_add a 7 420 (by norm_num)]

/-- `Gb` has period `210` on `a ≥ 2`. -/
private lemma Gb_period (a : ℕ) (ha : 2 ≤ a) : Gb (a % 210 + 210) = Gb a := by
  unfold Gb
  rw [u_zero a ha, u_zero _ (by omega)]
  rw [u_mod_add a 1 210 (by norm_num), u_mod_add a 2 210 (by norm_num),
    u_mod_add a 3 210 (by norm_num)]

/-- `hcl` has period `420` on `m ≥ 3`. -/
private lemma hcl_period (m : ℕ) (hm : 3 ≤ m) : hcl (m % 420 + 420) = hcl m := by
  unfold hcl
  rw [G_period m (by omega)]
  by_cases he : m % 2 = 0
  · rw [if_pos (by omega), if_pos (by omega),
      show (m % 420 + 420) / 2 = (m / 2) % 210 + 210 by omega, Gb_period _ (by omega)]
  · rw [if_neg (by omega), if_neg (by omega)]

/-- `hcl` evaluated at a canonical representative mod `420`. -/
private def hp (m : ℕ) : ℤ := hcl (m % 420 + 420)

/-- For `k ≥ 3`, `hcl (N + k)` only depends on `N mod 420`. -/
private lemma hcl_eq (N k : ℕ) (hk : 3 ≤ k) : hcl (N + k) = hp (N % 420 + k) := by
  unfold hp
  rw [← hcl_period (N + k) (by omega), show (N + k) % 420 = (N % 420 + k) % 420 by omega]

set_option maxRecDepth 100000 in
/-- Kernel check: `∑_j r_j hcl(m - j) = 0` on every residue class mod `420`. -/
private lemma key : ∀ s < 420, hp (s + 21) + 2 * hp (s + 20) + 4 * hp (s + 19) + 6 * hp (s + 18)
    + 8 * hp (s + 17) + 9 * hp (s + 16) + 9 * hp (s + 15) + 7 * hp (s + 14) + 4 * hp (s + 13)
    - 4 * hp (s + 11) - 7 * hp (s + 10) - 9 * hp (s + 9) - 9 * hp (s + 8) - 8 * hp (s + 7)
    - 6 * hp (s + 6) - 4 * hp (s + 5) - 2 * hp (s + 4) - hp (s + 3) = 0 := by
  decide +kernel

/-- Barker's recurrence for A160848 holds for every `n > 21`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 22 := ⟨n - 22, by omega⟩
  unfold Recurrence
  simp only [show N + 22 - 2 = N + 20 by omega, show N + 22 - 5 = N + 17 by omega,
    show N + 22 - 6 = N + 16 by omega, show N + 22 - 7 = N + 15 by omega,
    show N + 22 - 8 = N + 14 by omega, show N + 22 - 9 = N + 13 by omega,
    show N + 22 - 11 = N + 11 by omega, show N + 22 - 12 = N + 10 by omega,
    show N + 22 - 13 = N + 9 by omega, show N + 22 - 14 = N + 8 by omega,
    show N + 22 - 15 = N + 7 by omega, show N + 22 - 18 = N + 4 by omega,
    show N + 22 - 20 = N + 2 by omega]
  have e : ∀ k, 2 ≤ k → (a (N + k + 2) : ℤ) - 2 * a (N + k + 1) + a (N + k) =
      hp (N % 420 + (k + 1)) := by
    intro k hk
    rw [second_diff, Nat.add_assoc, hcl_eq N (k + 1) (by omega)]
  have e0 := e 20 (by norm_num)
  have e1 := e 19 (by norm_num)
  have e2 := e 18 (by norm_num)
  have e3 := e 17 (by norm_num)
  have e4 := e 16 (by norm_num)
  have e5 := e 15 (by norm_num)
  have e6 := e 14 (by norm_num)
  have e7 := e 13 (by norm_num)
  have e8 := e 12 (by norm_num)
  have e10 := e 10 (by norm_num)
  have e11 := e 9 (by norm_num)
  have e12 := e 8 (by norm_num)
  have e13 := e 7 (by norm_num)
  have e14 := e 6 (by norm_num)
  have e15 := e 5 (by norm_num)
  have e16 := e 4 (by norm_num)
  have e17 := e 3 (by norm_num)
  have e18 := e 2 (by norm_num)
  have hk := key (N % 420) (Nat.mod_lt _ (by norm_num))
  norm_num at e0 e1 e2 e3 e4 e5 e6 e7 e8 e10 e11 e12 e13 e14 e15 e16 e17 e18
  linear_combination e0 + 2 * e1 + 4 * e2 + 6 * e3 + 8 * e4 + 9 * e5 + 9 * e6 + 7 * e7 + 4 * e8
    - 4 * e10 - 7 * e11 - 9 * e12 - 9 * e13 - 8 * e14 - 6 * e15 - 4 * e16 - 2 * e17 - e18 + hk

end Math0.Frontier.A160848

#math0_settles Math0.Frontier.A160848.result Math0.Statements.A160848.statement

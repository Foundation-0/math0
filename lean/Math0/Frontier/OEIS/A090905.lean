/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A090905
import Math0.Audit

/-!
# A090905: each row ends at twice the largest prime of the previous row

We prove Murthy's conjecture: for `n > 4`, group `n - 1` has a largest prime `p`, the last term
of group `n` is `2 p`, and `p` is the Bertrand prime `A006992(n - 1)`.

Write `B k = bertrand k`, so `B (k + 1)` is the largest prime below `2 B k`. We show that for
`n ≥ 10`, row `n` is the block `[2 B (n - 2) + 1, 2 B (n - 1)]`. Rows `1, …, 10` are checked by
computation. For the inductive step let `b < a < c` be three consecutive Bertrand primes, with
row `n` equal to `[2b + 1, 2a]`. Then row `n + 1` starts at `2a + 1`, and:

* The prime `c` lies in row `n`, but none of `2a + 1, …, 2c - 1` is a multiple of `c`. So the
  new row must reach `2c`.
* Ending at `2c` works. The row product `(2a)! / (2b)!` divides `(2c)! / (2a)!`, because
  `(2a)!² ∣ (2b)! (2c)!`. By Legendre's formula this means that for every prime `ℓ`,
  `∑ⱼ (⌊2b/ℓʲ⌋ + ⌊2c/ℓʲ⌋ - 2⌊2a/ℓʲ⌋) ≥ 0`. Each term is `≥ 0`, using `2b > a` and `3c > 5a`,
  except when `c < ℓʲ ≤ 2a`. Then the term is `-1`, `ℓʲ` is not prime because there is no
  prime in `(c, 2a)`, and the term `j = 1` is `≥ 1`.
* The length condition `2c - 2a ≥ 2a - 2b` also follows from `2b > a` and `3c > 5a`.

The inequalities `3c > 5a` (and `3a > 5b`) say that there is a prime between `5x/3` and `2x`
(Nagura's theorem, in the form needed here). We prove it for `x ≥ 83`, in two ranges:

* for `x < 10⁶`, by a ladder of 53 explicit primes `163, 193, …, 1789201`, each less than
  `6/5` times the one before;
* for `x ≥ 10⁶`, with Chebyshev's method. Write `T(N) = log N! = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`. For a
  weight list `W` of pairs `(c_k, k)` with `k ∣ 420` and `∑ c_k / k = 0`, the sum
  `G(N) = ∑ c_k T(N/k) = ∑_{d ≤ N} Λ(d) H(⌊N/d⌋)` with `H(n) = ∑ c_k ⌊n/k⌋` is `420`-periodic.
  Stirling's bounds give `G(420 m) = D m + O(log m)`. Chebyshev's weight
  `(1,1), (-1,2), (-1,3), (-1,5), (1,30)` has `H ≤ 1`, which gives `ψ(N) ≥ 0.92129 N - O(log N)`.
  A 19-term weight with `H ≥ 1` off multiples of `420` gives
  `ψ(N) ≤ 1.06901 N + ψ(N/420) + O(log N)`. Since `2 · 0.92129 > (5/3) · 1.06901 + 0.0056`,
  this leaves a gap of about `0.055 x`, which beats `ψ - θ ≤ 2 √x log x` once `x ≥ 10⁶`.
-/

namespace Math0.Frontier.A090905
open Math0.Statements.A090905
open Finset
open scoped ArithmeticFunction

/-! ### `log N!` as a von Mangoldt sum -/

/-- `log M! = ∑_{d ≤ M} Λ(d) ⌊M/d⌋`. -/
private theorem log_factorial_eq_sum (M : ℕ) :
    Real.log (M.factorial : ℝ) = ∑ d ∈ Ioc 0 M, Λ d * ((M / d : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih]
    have key : ∀ d ∈ Ioc 0 (M + 1), Λ d * (((M + 1) / d : ℕ) : ℝ) =
        Λ d * ((M / d : ℕ) : ℝ) + if d ∣ M + 1 then Λ d else 0 := by
      intro d _
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [sum_congr rfl key, sum_add_distrib, ← sum_filter]
    have h1 : ∑ d ∈ Ioc 0 (M + 1), Λ d * ((M / d : ℕ) : ℝ) =
        ∑ d ∈ Ioc 0 M, Λ d * ((M / d : ℕ) : ℝ) := by
      rw [sum_Ioc_succ_top (by omega), Nat.div_eq_of_lt (by omega)]
      simp
    have h2 : (Ioc 0 (M + 1)).filter (· ∣ M + 1) = (M + 1).divisors := by
      ext d
      simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, _⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), Nat.le_of_dvd (by omega) h⟩, h⟩
    rw [h1, h2, ArithmeticFunction.vonMangoldt_sum]
    push_cast
    ring

/-- `log ⌊N/k⌋! = ∑_{d ≤ N} Λ(d) ⌊⌊N/d⌋/k⌋`. -/
private theorem log_factorial_div_eq_sum (N k : ℕ) (hk : 0 < k) :
    Real.log ((N / k).factorial : ℝ) = ∑ d ∈ Ioc 0 N, Λ d * ((N / d / k : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum]
  have hsub : Ioc 0 (N / k) ⊆ Ioc 0 N := Ioc_subset_Ioc_right (Nat.div_le_self _ _)
  rw [← sum_subset hsub]
  · apply sum_congr rfl
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d k]
  · intro d hd hd'
    simp only [mem_Ioc, not_and, not_le] at hd hd'
    have : N / d / k = 0 := by
      rw [Nat.div_div_eq_div_mul]
      apply Nat.div_eq_of_lt
      have := hd' hd.1
      have h3 : N < k * (N / k + 1) := Nat.lt_mul_div_succ N hk
      nlinarith
    simp [this]

/-! ### Chebyshev weights -/

/-- The step function `H(n) = ∑ c_k ⌊n/k⌋` of a weight list `W` of pairs `(c_k, k)`. -/
private def Hw (W : List (ℤ × ℕ)) (n : ℕ) : ℤ := (W.map (fun p => p.1 * ((n / p.2 : ℕ) : ℤ))).sum

/-- The weighted log-factorial sum `G(N) = ∑ c_k log ⌊N/k⌋!`. -/
private noncomputable def Gw (W : List (ℤ × ℕ)) (N : ℕ) : ℝ :=
  (W.map (fun p => (p.1 : ℝ) * Real.log ((N / p.2).factorial : ℝ))).sum

/-- `G(N) = ∑_{d ≤ N} Λ(d) H(⌊N/d⌋)`. -/
private theorem Gw_eq (W : List (ℤ × ℕ)) (hW : ∀ p ∈ W, 0 < p.2) (N : ℕ) :
    Gw W N = ∑ d ∈ Ioc 0 N, Λ d * (Hw W (N / d) : ℝ) := by
  induction W with
  | nil => simp [Gw, Hw]
  | cons p W ih =>
    have ih' := ih (fun q hq => hW q (List.mem_cons_of_mem _ hq))
    simp only [Gw, Hw, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', log_factorial_div_eq_sum N p.2 (hW p List.mem_cons_self), mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring

/-- `ψ` at a natural number. -/
private theorem psi_nat (N : ℕ) : Chebyshev.psi N = ∑ d ∈ Ioc 0 N, Λ d := by
  simp [Chebyshev.psi]

/-- If `H ≤ 1` everywhere, then `G(N) ≤ ψ(N)`. -/
private theorem Gw_le_psi (W : List (ℤ × ℕ)) (hW : ∀ p ∈ W, 0 < p.2) (hH : ∀ n, Hw W n ≤ 1)
    (N : ℕ) : Gw W N ≤ Chebyshev.psi N := by
  rw [Gw_eq W hW, psi_nat]
  apply sum_le_sum
  intro d _
  have h1 : (Hw W (N / d) : ℝ) ≤ 1 := by exact_mod_cast hH _
  have h2 := ArithmeticFunction.vonMangoldt_nonneg (n := d)
  nlinarith

/-- If `H ≥ 0` everywhere and `H ≥ 1` off multiples of `P`, then `ψ(N) ≤ G(N) + ψ(N/P)`. -/
private theorem psi_le_Gw (W : List (ℤ × ℕ)) (hW : ∀ p ∈ W, 0 < p.2) (P : ℕ) (hP : 0 < P)
    (hH0 : ∀ n, 0 ≤ Hw W n) (hH1 : ∀ n, n % P ≠ 0 → 1 ≤ Hw W n) (N : ℕ) :
    Chebyshev.psi N ≤ Gw W N + Chebyshev.psi (N / P : ℕ) := by
  rw [Gw_eq W hW, psi_nat, psi_nat]
  rw [← sum_filter_add_sum_filter_not (Ioc 0 N) (fun d => N / d % P = 0)]
  have hA : ∑ d ∈ (Ioc 0 N).filter (fun d => N / d % P = 0), Λ d ≤ ∑ d ∈ Ioc 0 (N / P), Λ d := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [mem_filter, mem_Ioc] at hd ⊢
      obtain ⟨⟨hd0, hdN⟩, hm⟩ := hd
      refine ⟨hd0, ?_⟩
      have hpos : 0 < N / d := Nat.div_pos hdN hd0
      have hge : P ≤ N / d := Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hm)
      rw [Nat.le_div_iff_mul_le hP]
      have := Nat.div_mul_le_self N d
      calc d * P ≤ d * (N / d) := Nat.mul_le_mul_left _ hge
        _ = N / d * d := mul_comm _ _
        _ ≤ N := this
    · intro i _ _; exact ArithmeticFunction.vonMangoldt_nonneg
  have hB : ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ N / d % P = 0), Λ d ≤
      ∑ d ∈ Ioc 0 N, Λ d * (Hw W (N / d) : ℝ) := by
    calc ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ N / d % P = 0), Λ d
        ≤ ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ N / d % P = 0), Λ d * (Hw W (N / d) : ℝ) := by
          apply sum_le_sum
          intro d hd
          simp only [mem_filter] at hd
          have h1 : (1 : ℝ) ≤ (Hw W (N / d) : ℝ) := by exact_mod_cast hH1 _ hd.2
          have h2 := ArithmeticFunction.vonMangoldt_nonneg (n := d)
          nlinarith
      _ ≤ ∑ d ∈ Ioc 0 N, Λ d * (Hw W (N / d) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _
          have h1 : (0 : ℝ) ≤ (Hw W (N / d) : ℝ) := by exact_mod_cast hH0 _
          exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h1
  linarith

/-! ### Numerical constants and Stirling bounds -/

/-- Bounds on `log 3`. -/
private theorem log_three_bounds : 1.098612 < Real.log 3 ∧ Real.log 3 < 1.098613 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/4) (by norm_num [abs_of_pos]) 16
  have h4 : Real.log (1 - 1/4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1:ℝ) - 1/4 = 3 / 2^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  rw [h4] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  rw [abs_le] at h
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  constructor <;> nlinarith [h.1, h.2]

/-- Bounds on `log 5`. -/
private theorem log_five_bounds : 1.609437 < Real.log 5 ∧ Real.log 5 < 1.609438 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/5) (by norm_num [abs_of_pos]) 16
  have h4 : Real.log (1 - 1/5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1:ℝ) - 1/5 = 2^2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  rw [h4] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  rw [abs_le] at h
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  constructor <;> nlinarith [h.1, h.2]

/-- Bounds on `log 7`. -/
private theorem log_seven_bounds : 1.945910 < Real.log 7 ∧ Real.log 7 < 1.945911 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/8) (by norm_num [abs_of_pos]) 16
  have h4 : Real.log (1 - 1/8) = Real.log 7 - 3 * Real.log 2 := by
    rw [show (1:ℝ) - 1/8 = 7 / 2^3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  rw [h4] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  rw [abs_le] at h
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  constructor <;> nlinarith [h.1, h.2]

/-- Stirling lower bound: `log M! ≥ M log M - M + (log M)/2 + 1/2`. -/
private theorem log_fact_lower (M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) * Real.log M - M + Real.log M / 2 + 1 / 2 ≤ Real.log (M.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (n := M) (by omega)
  have h2 : 1 ≤ Real.log (2 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have := Real.pi_gt_three
    linarith
  linarith

/-- Stirling upper bound: `log M! ≤ M log M - M + (log M)/2 + 1`. -/
private theorem log_fact_upper (M : ℕ) (hM : 1 ≤ M) :
    Real.log (M.factorial : ℝ) ≤ (M : ℝ) * Real.log M - M + Real.log M / 2 + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le n)
  simp only [Function.comp_apply, Stirling.stirlingSeq_one] at h
  rw [Stirling.log_stirlingSeq_formula] at h
  have e1 : Real.log (Real.exp 1 / √2) = 1 - Real.log 2 / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_sqrt (by norm_num)]
  have e2 : Real.log (2 * ((n + 1 : ℕ) : ℝ)) = Real.log 2 + Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_mul (by norm_num) (by positivity)
  have e3 : Real.log (((n + 1 : ℕ) : ℝ) / Real.exp 1) = Real.log ((n + 1 : ℕ) : ℝ) - 1 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
  rw [e1, e2, e3] at h
  nlinarith

/-! ### Evaluating `G(P m)` -/

/-- `∑ c_k (P/k) log(P/k)`. -/
private noncomputable def D1 (W : List (ℤ × ℕ)) (P : ℕ) : ℝ :=
  (W.map fun p => (p.1 : ℝ) * ((P / p.2 : ℕ) : ℝ) * Real.log ((P / p.2 : ℕ) : ℝ)).sum
/-- `∑ c_k log(P/k)`. -/
private noncomputable def D2 (W : List (ℤ × ℕ)) (P : ℕ) : ℝ :=
  (W.map fun p => (p.1 : ℝ) * Real.log ((P / p.2 : ℕ) : ℝ)).sum
/-- `∑ c_k`. -/
private def Sw (W : List (ℤ × ℕ)) : ℤ := (W.map Prod.fst).sum
/-- Upper error constant from Stirling. -/
private noncomputable def Eu (W : List (ℤ × ℕ)) : ℝ :=
  (W.map fun p => if 0 ≤ p.1 then (p.1 : ℝ) else (p.1 : ℝ) / 2).sum
/-- Lower error constant from Stirling. -/
private noncomputable def El (W : List (ℤ × ℕ)) : ℝ :=
  (W.map fun p => if 0 ≤ p.1 then (p.1 : ℝ) / 2 else (p.1 : ℝ)).sum
/-- `∑ c_k (P/k)` (zero for a balanced weight). -/
private def Rw (W : List (ℤ × ℕ)) (P : ℕ) : ℤ := (W.map fun p => p.1 * ((P / p.2 : ℕ) : ℤ)).sum

/-- Stirling bounds for one term `c log (r m)!`. -/
private theorem term_bounds (c : ℤ) (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (c : ℝ) * Real.log ((r * m).factorial : ℝ) ≤
      ((m : ℝ) * Real.log m - m) * ((c * r : ℤ) : ℝ) + m * ((c : ℝ) * r * Real.log r)
        + (c : ℝ) * Real.log r / 2 + (c : ℝ) / 2 * Real.log m
        + (if 0 ≤ c then (c : ℝ) else (c : ℝ) / 2) ∧
    ((m : ℝ) * Real.log m - m) * ((c * r : ℤ) : ℝ) + m * ((c : ℝ) * r * Real.log r)
        + (c : ℝ) * Real.log r / 2 + (c : ℝ) / 2 * Real.log m
        + (if 0 ≤ c then (c : ℝ) / 2 else (c : ℝ)) ≤
      (c : ℝ) * Real.log ((r * m).factorial : ℝ) := by
  have hrm : 1 ≤ r * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hU := log_fact_upper (r * m) hrm
  have hL := log_fact_lower (r * m) hrm
  have hlog : Real.log ((r * m : ℕ) : ℝ) = Real.log r + Real.log m := by
    push_cast
    exact Real.log_mul (by positivity) (by positivity)
  rw [hlog] at hU hL
  push_cast at hU hL ⊢
  have key : (c : ℝ) * (((r : ℝ) * m) * (Real.log r + Real.log m) - r * m
      + (Real.log r + Real.log m) / 2) =
      ((m : ℝ) * Real.log m - m) * ((c : ℝ) * r) + m * ((c : ℝ) * r * Real.log r)
        + (c : ℝ) * Real.log r / 2 + (c : ℝ) / 2 * Real.log m := by ring
  split_ifs with hc
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    constructor <;> nlinarith
  · have hc' : (c : ℝ) < 0 := by exact_mod_cast not_le.mp hc
    constructor <;> nlinarith

/-- Two-sided bounds for `G(P m)` when every `k` divides `P`. -/
private theorem Gw_bounds (W : List (ℤ × ℕ)) (P m : ℕ) (hm : 1 ≤ m)
    (hW : ∀ p ∈ W, 0 < p.2 ∧ p.2 ∣ P ∧ p.2 ≤ P) :
    Gw W (P * m) ≤ ((m : ℝ) * Real.log m - m) * (Rw W P : ℝ) + m * D1 W P + D2 W P / 2
        + (Sw W : ℝ) / 2 * Real.log m + Eu W ∧
    ((m : ℝ) * Real.log m - m) * (Rw W P : ℝ) + m * D1 W P + D2 W P / 2
        + (Sw W : ℝ) / 2 * Real.log m + El W ≤ Gw W (P * m) := by
  induction W with
  | nil => simp [Gw, Rw, D1, D2, Sw, Eu, El]
  | cons p W ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun q hq => hW q (List.mem_cons_of_mem _ hq))
    obtain ⟨hp0, hpd, hpP⟩ := hW p List.mem_cons_self
    have hr : 1 ≤ P / p.2 := (Nat.one_le_div_iff hp0).mpr hpP
    have hdiv : P * m / p.2 = P / p.2 * m := (Nat.div_mul_right_comm hpd m).symm
    obtain ⟨t1, t2⟩ := term_bounds p.1 (P / p.2) m hr hm
    simp only [Gw, Rw, D1, D2, Sw, Eu, El, List.map_cons, List.sum_cons, hdiv] at ih1 ih2 t1 t2 ⊢
    push_cast at ih1 ih2 t1 t2 ⊢
    constructor <;> linarith

/-- Chebyshev's weight `T(x) - T(x/2) - T(x/3) - T(x/5) + T(x/30)`. -/
private def WL : List (ℤ × ℕ) := [(1, 1), (-1, 2), (-1, 3), (-1, 5), (1, 30)]

/-- A weight with `H ≥ 1` off multiples of `420` and `H ≥ 0` everywhere. -/
private def WU : List (ℤ × ℕ) := [(1, 1), (-1, 2), (-1, 3), (-1, 5), (1, 6), (-1, 7), (1, 10),
  (-1, 12), (1, 14), (-1, 20), (-1, 30), (1, 35), (-1, 42), (1, 60), (-1, 70), (1, 84), (-1, 105),
  (1, 210), (-4, 420)]

/-- `H(n) = H(n mod P) + ⌊n/P⌋ ∑ c_k (P/k)`. -/
private theorem Hw_mod (W : List (ℤ × ℕ)) (P : ℕ) (hW : ∀ p ∈ W, 0 < p.2 ∧ p.2 ∣ P) (n : ℕ) :
    Hw W n = Hw W (n % P) + ((n / P : ℕ) : ℤ) * Rw W P := by
  induction W with
  | nil => simp [Hw, Rw]
  | cons p W ih =>
    have ih' := ih (fun q hq => hW q (List.mem_cons_of_mem _ hq))
    obtain ⟨hp0, k, hk⟩ := hW p List.mem_cons_self
    simp only [Hw, Rw, List.map_cons, List.sum_cons] at ih' ⊢
    have hdiv : n / p.2 = n % P / p.2 + (P / p.2) * (n / P) := by
      subst hk
      rw [Nat.mul_div_cancel_left k hp0]
      conv_lhs => rw [← Nat.mod_add_div n (p.2 * k), mul_assoc]
      exact Nat.add_mul_div_left _ _ hp0
    rw [ih', hdiv]
    push_cast
    ring

/-- Chebyshev's step function is at most `1`. -/
private theorem HL_le (n : ℕ) : Hw WL n ≤ 1 := by
  have hR : Rw WL 30 = 0 := by decide
  rw [Hw_mod WL 30 (by decide) n, hR, mul_zero, add_zero]
  have h : ∀ r, r < 30 → Hw WL r ≤ 1 := by decide
  exact h _ (Nat.mod_lt _ (by norm_num))

/-- The upper step function is `≥ 0`, and `≥ 1` off multiples of `420`. -/
private theorem HU_spec (n : ℕ) : 0 ≤ Hw WU n ∧ (n % 420 ≠ 0 → 1 ≤ Hw WU n) := by
  have hR : Rw WU 420 = 0 := by decide
  rw [Hw_mod WU 420 (by decide) n, hR, mul_zero, add_zero]
  have h : ∀ r, r < 420 → 0 ≤ Hw WU r ∧ (r ≠ 0 → 1 ≤ Hw WU r) := by decide +kernel
  exact h _ (Nat.mod_lt _ (by norm_num))

/-- `log (2^a 3^b 5^c 7^d)`. -/
private theorem log_smooth (a b c d : ℕ) :
    Real.log ((2:ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) =
      a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]

/-- Constants of the lower weight: `D1 = 420 · 0.92129…`. -/
private theorem D_WL : 386.94 ≤ D1 WL 420 ∧ -6.05 ≤ D2 WL 420 := by
  have h420 := log_smooth 2 1 1 1
  have h210 := log_smooth 1 1 1 1
  have h140 := log_smooth 2 0 1 1
  have h84 := log_smooth 2 1 0 1
  have h14 := log_smooth 1 0 0 1
  norm_num at h420 h210 h140 h84 h14
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  have := log_three_bounds
  have := log_five_bounds
  have := log_seven_bounds
  simp only [D1, D2, WL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  constructor <;> linarith

/-- Constants of the upper weight: `D1 = 420 · 1.06900…`. -/
private theorem D_WU : D1 WU 420 ≤ 448.99 ∧ D2 WU 420 ≤ -9.37 := by
  have h420 := log_smooth 2 1 1 1
  have h210 := log_smooth 1 1 1 1
  have h140 := log_smooth 2 0 1 1
  have h84 := log_smooth 2 1 0 1
  have h70 := log_smooth 1 0 1 1
  have h60 := log_smooth 2 1 1 0
  have h42 := log_smooth 1 1 0 1
  have h35 := log_smooth 0 0 1 1
  have h30 := log_smooth 1 1 1 0
  have h21 := log_smooth 0 1 0 1
  have h14 := log_smooth 1 0 0 1
  have h12 := log_smooth 2 1 0 0
  have h10 := log_smooth 1 0 1 0
  have h6 := log_smooth 1 1 0 0
  have h4 := log_smooth 2 0 0 0
  norm_num at h420 h210 h140 h84 h70 h60 h42 h35 h30 h21 h14 h12 h10 h6 h4
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  have := log_three_bounds
  have := log_five_bounds
  have := log_seven_bounds
  simp only [D1, D2, WU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  constructor <;> linarith

/-- The remaining constants of the two weights. -/
private theorem consts : Sw WL = -1 ∧ Sw WU = -6 ∧ El WL = -2 ∧ Eu WU = 1 ∧ Rw WL 420 = 0 ∧
    Rw WU 420 = 0 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide⟩
  · simp only [El, WL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; norm_num
  · simp only [Eu, WU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; norm_num

/-- Lower bound `ψ(420 m) ≥ 386.94 m - O(log m)`. -/
private theorem psi_lower (m : ℕ) (hm : 1 ≤ m) :
    386.94 * (m : ℝ) - 6.05 / 2 - Real.log m / 2 - 2 ≤ Chebyshev.psi ((420 * m : ℕ) : ℝ) := by
  have hW : ∀ p ∈ WL, 0 < p.2 ∧ p.2 ∣ 420 ∧ p.2 ≤ 420 := by decide
  have h1 := Gw_le_psi WL (fun p hp => (hW p hp).1) HL_le (420 * m)
  have h2 := (Gw_bounds WL 420 m hm hW).2
  obtain ⟨hD1, hD2⟩ := D_WL
  obtain ⟨hS, -, hEl, -, hR, -⟩ := consts
  rw [hS, hEl, hR] at h2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : 386.94 * (m : ℝ) ≤ m * D1 WL 420 := by nlinarith
  push_cast at h2
  linarith

/-- Upper bound `ψ(420 m) ≤ 448.99 m + ψ(m) - O(1)`. -/
private theorem psi_upper (m : ℕ) (hm : 1 ≤ m) :
    Chebyshev.psi ((420 * m : ℕ) : ℝ) ≤
      448.99 * (m : ℝ) - 9.37 / 2 - 3 * Real.log m + 1 + Chebyshev.psi (m : ℝ) := by
  have hW : ∀ p ∈ WU, 0 < p.2 ∧ p.2 ∣ 420 ∧ p.2 ≤ 420 := by decide
  have h1 := psi_le_Gw WU (fun p hp => (hW p hp).1) 420 (by norm_num) (fun n => (HU_spec n).1)
    (fun n hn => (HU_spec n).2 hn) (420 * m)
  rw [show 420 * m / 420 = m by omega] at h1
  have h2 := (Gw_bounds WU 420 m hm hW).1
  obtain ⟨hD1, hD2⟩ := D_WU
  obtain ⟨-, hS, -, hEu, -, hR⟩ := consts
  rw [hS, hEu, hR] at h2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : (m : ℝ) * D1 WU 420 ≤ 448.99 * m := by nlinarith
  push_cast at h2
  linarith

/-! ### A prime between `5x/3` and `2x` -/

/-- If `(A, B]` has no prime, then `θ(B) = θ(A)`. -/
private theorem theta_eq_of_no_prime (A B : ℕ) (hAB : A ≤ B)
    (h : ∀ p, A < p → p ≤ B → ¬ p.Prime) :
    Chebyshev.theta (B : ℝ) = Chebyshev.theta (A : ℝ) := by
  simp only [Chebyshev.theta, Nat.floor_natCast]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h0, hB⟩, hp⟩
    refine ⟨⟨h0, ?_⟩, hp⟩
    by_contra hA
    exact h p (by omega) hB hp
  · rintro ⟨⟨h0, hA⟩, hp⟩
    exact ⟨⟨h0, by omega⟩, hp⟩

/-- For `x ≥ 10⁶` there is a prime `p` with `5x < 3p < 6x` (analytic part). -/
private theorem exists_prime_large (a : ℕ) (ha : 1000000 ≤ a) :
    ∃ p, p.Prime ∧ 5 * a < 3 * p ∧ 3 * p < 6 * a := by
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = (2 * a - 1) / 420 := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = (5 * a / 3) / 420 + 1 := ⟨_, rfl⟩
  have hm0' : 1 ≤ m0 := by omega
  have hm1' : 1 ≤ m1 := by omega
  have n1 : 420 * m0 ≤ 2 * a - 1 := by omega
  have n2 : 2 * a ≤ 420 * m0 + 420 := by omega
  have n3 : 5 * a / 3 ≤ 420 * m1 := by omega
  have n4 : 3 * (420 * m1) ≤ 5 * a + 1260 := by omega
  have n5 : m1 * 196 ≤ a := by omega
  have n6 : m0 ≤ a := by omega
  have n7 : m1 ≤ a := by omega
  have n8 : 1 ≤ 2 * a - 1 := by omega
  have n9 : 2 * a - 1 ≤ 2 * a := by omega
  by_contra hne
  have hnp : ∀ p, 5 * a / 3 < p → p ≤ 2 * a - 1 → ¬ p.Prime := by
    intro p h1 h2 hp
    apply hne
    exact ⟨p, hp, by omega, by omega⟩
  have hθ := theta_eq_of_no_prime (5 * a / 3) (2 * a - 1) (by omega) hnp
  clear hne hnp hm0 hm1
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (a : ℝ) := ⟨_, rfl⟩
  have hx6 : (1000000 : ℝ) ≤ x := by rw [hx]; exact_mod_cast ha
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √x := ⟨_, rfl⟩
  have hs2 : s ^ 2 = x := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs1000 : 1000 ≤ s := by
    rw [hs, show (1000 : ℝ) = √1000000 by
      rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx6
  obtain ⟨lx, hlx⟩ : ∃ lx : ℝ, lx = Real.log x := ⟨_, rfl⟩
  have hlx0 : 0 ≤ lx := by rw [hlx]; exact Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl5 := log_five_bounds
  have hlog1000 : Real.log 1000 ≤ 6.9078 := by
    have := log_smooth 3 0 3 0
    norm_num at this
    rw [this]; linarith [hl5.2]
  have hlogs : Real.log s ≤ Real.log 1000 + s / 1000 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < s / 1000 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    linarith
  have hlxs : lx = 2 * Real.log s := by
    rw [hlx, ← hs2, Real.log_pow]; push_cast; ring
  have hL : lx ≤ 11.8157 + s / 500 := by rw [hlxs]; linarith
  have hsL : s * lx ≤ 11.8157 * s + s ^ 2 / 500 := by
    have := mul_le_mul_of_nonneg_left hL (show 0 ≤ s by linarith)
    calc s * lx ≤ s * (11.8157 + s / 500) := this
      _ = 11.8157 * s + s ^ 2 / 500 := by ring
  -- lower bound for `ψ(2a - 1)` and `θ(2a - 1)`
  have hA : (((420 * m0 : ℕ) : ℝ)) ≤ ((2 * a - 1 : ℕ) : ℝ) := by exact_mod_cast n1
  have hψA := Chebyshev.psi_mono hA
  have hlow := psi_lower m0 hm0'
  have hlogm0 : Real.log (m0 : ℝ) ≤ lx := by
    rw [hlx]
    apply Real.log_le_log (by exact_mod_cast hm0')
    rw [hx]; exact_mod_cast n6
  have hm0r : 2 * x ≤ 420 * (m0 : ℝ) + 420 := by rw [hx]; exact_mod_cast n2
  have h2a1 : (1 : ℝ) ≤ ((2 * a - 1 : ℕ) : ℝ) := by exact_mod_cast n8
  have hθA := Chebyshev.psi_sub_theta_le h2a1
  have h2ax : (((2 * a - 1 : ℕ) : ℝ)) ≤ 2 * x := by
    rw [hx]; exact_mod_cast n9
  have hsqA : √(((2 * a - 1 : ℕ) : ℝ)) ≤ 1.4143 * s := by
    rw [show 1.4143 * s = √((1.4143 * s) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have e : (1.4143 * s) ^ 2 = 2.00024449 * x := by rw [mul_pow, hs2]; norm_num
    rw [e]; linarith
  have hlogA : Real.log (((2 * a - 1 : ℕ) : ℝ)) ≤ Real.log 2 + lx := by
    rw [hlx, ← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) h2ax
  have hprodA : √(((2 * a - 1 : ℕ) : ℝ)) * Real.log (((2 * a - 1 : ℕ) : ℝ)) ≤
      1.4143 * s * (Real.log 2 + lx) :=
    mul_le_mul hsqA hlogA (Real.log_nonneg h2a1) (by positivity)
  -- upper bound for `ψ(⌊5a/3⌋)` and `θ(⌊5a/3⌋)`
  have hB : ((5 * a / 3 : ℕ) : ℝ) ≤ ((420 * m1 : ℕ) : ℝ) := by exact_mod_cast n3
  have hψB := Chebyshev.psi_mono hB
  have hθB := Chebyshev.theta_le_psi ((5 * a / 3 : ℕ) : ℝ)
  have hup := psi_upper m1 hm1'
  have hm1r : 3 * (420 * (m1 : ℝ)) ≤ 5 * x + 1260 := by rw [hx]; exact_mod_cast n4
  have hm1one : (1 : ℝ) ≤ m1 := by exact_mod_cast hm1'
  have hψm1 := Chebyshev.psi_le hm1one
  have hlogm1 : Real.log (m1 : ℝ) ≤ lx := by
    rw [hlx]
    apply Real.log_le_log (by linarith)
    rw [hx]; exact_mod_cast n7
  have hlogm1' : 0 ≤ Real.log (m1 : ℝ) := Real.log_nonneg hm1one
  have hsqm1 : √(m1 : ℝ) ≤ s / 14 := by
    rw [show s / 14 = √((s / 14) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have : (m1 : ℝ) * 196 ≤ x := by rw [hx]; exact_mod_cast n5
    have e : (s / 14) ^ 2 = x / 196 := by rw [div_pow, hs2]; norm_num
    rw [e]; linarith
  have hprodm1 : √(m1 : ℝ) * Real.log (m1 : ℝ) ≤ s / 14 * lx :=
    mul_le_mul hsqm1 hlogm1 hlogm1' (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog4] at hψm1
  have hss : 1000 * s ≤ s ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hs1000 (show (0:ℝ) ≤ s by linarith)
    rw [sq]; linarith
  have hl2m1 : Real.log 2 * m1 ≤ 0.6932 * m1 :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hl2s : Real.log 2 * s ≤ 0.6932 * s :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e1 : 1.4143 * s * (Real.log 2 + lx) = 1.4143 * (Real.log 2 * s) + 1.4143 * (s * lx) := by
    ring
  have e2 : s / 14 * lx = (s * lx) / 14 := by ring
  have e3 : 2 * Real.log 2 * (m1 : ℝ) = 2 * (Real.log 2 * m1) := by ring
  have e4 : 2 * √(m1 : ℝ) * Real.log m1 = 2 * (√(m1 : ℝ) * Real.log m1) := by ring
  have e5 : 2 * √(((2 * a - 1 : ℕ) : ℝ)) * Real.log (((2 * a - 1 : ℕ) : ℝ)) =
      2 * (√(((2 * a - 1 : ℕ) : ℝ)) * Real.log (((2 * a - 1 : ℕ) : ℝ))) := by ring
  rw [e3, e4] at hψm1
  rw [e5] at hθA
  rw [e1] at hprodA
  rw [e2] at hprodm1
  linarith

/-- A ladder of primes, each less than `6/5` times the previous one (starting from `138`). -/
private def ladder : List ℕ := [163, 193, 229, 271, 317, 379, 449, 523, 619, 739, 883, 1051, 1259,
  1499, 1789, 2143, 2557, 3067, 3677, 4409, 5281, 6337, 7603, 9109, 10909, 13063, 15671, 18803,
  22549, 27043, 32443, 38923, 46703, 56041, 67247, 80687, 96823, 116177, 139409, 167269, 200713,
  240853, 289021, 346793, 416149, 499363, 599231, 719071, 862879, 1035451, 1242517, 1491013,
  1789201]

/-- `chainOK q L`: each entry of `L` is less than `6/5` times the previous one. -/
private def chainOK : ℕ → List ℕ → Bool
  | _, [] => true
  | q, p :: L => decide (5 * p < 6 * q) && chainOK p L

/-- A ladder of primes covers every `x` in its range. -/
private theorem ladder_aux (L : List ℕ) (hL : ∀ p ∈ L, p.Prime) : ∀ q, chainOK q L = true → ∀ b,
    3 * q ≤ 5 * b → 5 * b < 3 * L.getLastD q → ∃ p, p.Prime ∧ 5 * b < 3 * p ∧ 3 * p < 6 * b := by
  induction L with
  | nil => intro q _ b h1 h2; simp at h2; omega
  | cons p L ih =>
    intro q hq b h1 h2
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hq
    rcases Nat.lt_or_ge (5 * b) (3 * p) with h | h
    · exact ⟨p, hL p List.mem_cons_self, h, by omega⟩
    · rw [List.getLastD_cons] at h2
      exact ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)) p hq.2 b h h2

/-- The ladder consists of primes. -/
private theorem ladder_prime : ∀ p ∈ ladder, p.Prime := by
  simp only [ladder, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  and_intros <;> norm_num

/-- For every `x ≥ 83` there is a prime `p` with `5x < 3p < 6x`. -/
private theorem exists_prime (b : ℕ) (hb : 83 ≤ b) :
    ∃ p, p.Prime ∧ 5 * b < 3 * p ∧ 3 * p < 6 * b := by
  rcases Nat.lt_or_ge b 1000000 with h | h
  · exact ladder_aux ladder ladder_prime 138 (by decide) b (by omega) (by simp [ladder]; omega)
  · exact exists_prime_large b h

/-! ### The divisibility `(2a)!² ∣ (2b)! (2c)!` -/

/-- The floor inequalities behind Legendre's formula, for one prime power `y`. -/
private theorem pointwise (b a c y : ℕ) (hy : 0 < y) (h2 : a < 2 * b) (h3 : 5 * a < 3 * c) :
    2 * (2 * a / y) ≤ 2 * b / y + 2 * c / y + 1 ∧
    (¬ (c < y ∧ y ≤ 2 * a) → 2 * (2 * a / y) ≤ 2 * b / y + 2 * c / y) ∧
    (13 ≤ 2 * a / y → 2 * (2 * a / y) + 1 ≤ 2 * b / y + 2 * c / y) := by
  set k := 2 * a / y with hk
  set q1 := 2 * b / y with hq1
  set q2 := 2 * c / y with hq2
  have ek := Nat.div_mul_le_self (2 * a) y
  have ek' := Nat.lt_div_mul_add (a := 2 * a) hy
  have e1' := Nat.lt_div_mul_add (a := 2 * b) hy
  have e2' := Nat.lt_div_mul_add (a := 2 * c) hy
  rw [← hk] at ek ek'
  rw [← hq1] at e1'
  rw [← hq2] at e2'
  have A : k < 2 * q1 + 2 := by
    have : k * y < (2 * q1 + 2) * y := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  have B : 5 * k < 3 * q2 + 3 := by
    have : (5 * k) * y < (3 * q2 + 3) * y := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  have C : y ≤ c → 2 ≤ q2 := by
    intro hyc
    rw [hq2, Nat.le_div_iff_mul_le hy]; omega
  have D : y ≤ 2 * a → 1 ≤ q2 := by
    intro hya
    rw [hq2, Nat.le_div_iff_mul_le hy]; omega
  have E : 2 * a < y → k = 0 := by
    intro hya
    rw [hk]; exact Nat.div_eq_of_lt hya
  have F : 1 ≤ k → y ≤ 2 * a := by
    intro hk1
    by_contra hcon
    have := E (by omega); omega
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · omega
    · have := D (F h0); omega
  · intro hn
    rcases Nat.lt_or_ge (2 * a) y with hya | hya
    · have := E hya; omega
    · have hyc : y ≤ c := by omega
      have := C hyc
      omega
  · intro h13
    omega

/-- `(2a)!² ∣ (2b)! (2c)!` for consecutive chain primes `b < a < c` (via Legendre). -/
private theorem fact_dvd (b a c : ℕ) (hb : 83 ≤ b) (h1 : 5 * b < 3 * a) (h2 : a < 2 * b)
    (h3 : 5 * a < 3 * c) (h4 : c < 2 * a) (hgap : ∀ q, c < q → q < 2 * a → ¬ q.Prime) :
    (2 * a).factorial * (2 * a).factorial ∣ (2 * b).factorial * (2 * c).factorial := by
  rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)]
  intro p hp
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  have hB : ∀ n, n ≤ 2 * c → Nat.log p n < 2 * c + 1 := fun n hn =>
    lt_of_le_of_lt (Nat.log_le_self p n) (by omega)
  rw [Nat.factorization_factorial hp (hB (2 * a) (by omega)),
    Nat.factorization_factorial hp (hB (2 * b) (by omega)),
    Nat.factorization_factorial hp (hB (2 * c) le_rfl), ← sum_add_distrib, ← sum_add_distrib]
  have hp2 := hp.two_le
  have hpos : ∀ i, 0 < p ^ i := fun i => Nat.pow_pos hp.pos
  by_cases hj : ∃ j ∈ Ico 1 (2 * c + 1), c < p ^ j ∧ p ^ j ≤ 2 * a
  · obtain ⟨j, hjT, hcj, hja⟩ := hj
    have huniq : ∀ i, i ≠ j → ¬ (c < p ^ i ∧ p ^ i ≤ 2 * a) := by
      rintro i hij ⟨hci, hia⟩
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · have e : p ^ (i + 1) ≤ p ^ j := Nat.pow_le_pow_right hp.pos h
        rw [pow_succ] at e
        nlinarith
      · have e : p ^ (j + 1) ≤ p ^ i := Nat.pow_le_pow_right hp.pos h
        rw [pow_succ] at e
        nlinarith
    have hj1 : j ≠ 1 := by
      rintro rfl
      rw [pow_one] at hcj hja
      rcases Nat.lt_or_ge p (2 * a) with hlt | hge
      · exact hgap p hcj hlt hp
      · have : p = 2 * a := by omega
        have h2p : 2 ∣ p := ⟨a, this⟩
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
        omega
    have hj2 : 2 ≤ j := by simp only [mem_Ico] at hjT; omega
    have h13 : 13 ≤ 2 * a / p ^ 1 := by
      rw [pow_one, Nat.le_div_iff_mul_le hp.pos]
      have e : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj2
      rcases Nat.lt_or_ge p 13 with hp13 | hp13
      · omega
      · nlinarith
    have h1T : 1 ∈ (Ico 1 (2 * c + 1)).erase j := by
      simp only [mem_erase, mem_Ico]; omega
    rw [← add_sum_erase _ _ hjT, ← add_sum_erase _ _ hjT, ← add_sum_erase _ _ h1T,
      ← add_sum_erase _ _ h1T]
    have hrest : ∑ x ∈ ((Ico 1 (2 * c + 1)).erase j).erase 1, (2 * a / p ^ x + 2 * a / p ^ x) ≤
        ∑ x ∈ ((Ico 1 (2 * c + 1)).erase j).erase 1, (2 * b / p ^ x + 2 * c / p ^ x) := by
      apply sum_le_sum
      intro i hi
      simp only [mem_erase] at hi
      have := (pointwise b a c (p ^ i) (hpos i) h2 h3).2.1 (huniq i hi.2.1)
      omega
    have hjj := (pointwise b a c (p ^ j) (hpos j) h2 h3).1
    have h11 := (pointwise b a c (p ^ 1) (hpos 1) h2 h3).2.2 h13
    omega
  · push Not at hj
    apply sum_le_sum
    intro i hi
    have := (pointwise b a c (p ^ i) (hpos i) h2 h3).2.1 (by
      rintro ⟨h5, h6⟩; exact absurd h6 (not_le.mpr (hj i hi h5)))
    omega

/-! ### The inductive step on rows -/

/-- `n + i ∣ n (n+1) ⋯ (n+k-1)` for `i < k`. -/
private theorem dvd_ascFactorial_of_lt (n k i : ℕ) (h : i < k) : n + i ∣ n.ascFactorial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Nat.ascFactorial_succ]
    rcases Nat.lt_or_ge i k with h' | h'
    · exact Dvd.dvd.mul_left (ih h') _
    · have : i = k := by omega
      subst this; exact Dvd.intro _ rfl

/-- A prime `c` divides none of `n, …, n + k - 1` when `c < n` and `n + k ≤ 2c`. -/
private theorem not_dvd_ascFactorial (c n k : ℕ) (hc : c.Prime) (hn : c < n) (hk : n + k ≤ 2 * c) :
    ¬ c ∣ n.ascFactorial k := by
  induction k with
  | zero => rw [Nat.ascFactorial_zero]; exact hc.not_dvd_one
  | succ k ih =>
    rw [Nat.ascFactorial_succ]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hc).mp hdvd with h | h
    · obtain ⟨t, ht⟩ := h
      have h1 : c * 1 < c * t := by rw [mul_one]; omega
      have h2 : c * t < c * 2 := by omega
      have := Nat.lt_of_mul_lt_mul_left h1
      have := Nat.lt_of_mul_lt_mul_left h2
      omega
    · exact ih (by omega) h

/-- If row `n` is `[2b+1, 2a]`, the least admissible length of row `n + 1` is `2c - 2a`. -/
private theorem step_core (b a c : ℕ) (hb : 83 ≤ b) (h1 : 5 * b < 3 * a) (h2 : a < 2 * b)
    (h3 : 5 * a < 3 * c) (h4 : c < 2 * a) (hc : c.Prime)
    (hgap : ∀ q, c < q → q < 2 * a → ¬ q.Prime) :
    IsLeast {k | 2 * a - 2 * b ≤ k ∧
      (2 * b + 1).ascFactorial (2 * a - 2 * b) ∣ (2 * a + 1).ascFactorial k} (2 * c - 2 * a) := by
  have hX := Nat.factorial_mul_ascFactorial (2 * b) (2 * a - 2 * b)
  have hY := Nat.factorial_mul_ascFactorial (2 * a) (2 * c - 2 * a)
  rw [show 2 * b + (2 * a - 2 * b) = 2 * a by omega] at hX
  rw [show 2 * a + (2 * c - 2 * a) = 2 * c by omega] at hY
  have hD := fact_dvd b a c hb h1 h2 h3 h4 hgap
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · have hpos : 0 < (2 * b).factorial * (2 * a).factorial := by positivity
    apply Nat.dvd_of_mul_dvd_mul_left hpos
    have e1 : (2 * b).factorial * (2 * a).factorial * (2 * b + 1).ascFactorial (2 * a - 2 * b) =
        (2 * a).factorial * (2 * a).factorial := by rw [← hX]; ring
    have e2 : (2 * b).factorial * (2 * a).factorial * (2 * a + 1).ascFactorial (2 * c - 2 * a) =
        (2 * b).factorial * (2 * c).factorial := by rw [← hY]; ring
    rw [e1, e2]
    exact hD
  · rintro k ⟨_, hk2⟩
    by_contra hlt
    have hcX : c ∣ (2 * b + 1).ascFactorial (2 * a - 2 * b) := by
      have := dvd_ascFactorial_of_lt (2 * b + 1) (2 * a - 2 * b) (c - (2 * b + 1)) (by omega)
      rwa [show 2 * b + 1 + (c - (2 * b + 1)) = c by omega] at this
    exact not_dvd_ascFactorial c (2 * a + 1) k hc (by omega) (by omega) (hcX.trans hk2)

/-- The recursion of the Bertrand primes. -/
private theorem bertrand_succ (n : ℕ) (hn : 1 ≤ n) :
    bertrand (n + 1) = Nat.findGreatest Nat.Prime (2 * bertrand n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [bertrand, Nat.add_sub_cancel]
  exact Function.iterate_succ_apply' _ m 2

/-- The largest prime below `2b` is prime, exceeds `5b/3`, and leaves a prime-free gap. -/
private theorem chain_step (b : ℕ) (hb : 83 ≤ b) :
    (Nat.findGreatest Nat.Prime (2 * b - 1)).Prime ∧
    5 * b < 3 * Nat.findGreatest Nat.Prime (2 * b - 1) ∧
    Nat.findGreatest Nat.Prime (2 * b - 1) < 2 * b ∧
    ∀ q, Nat.findGreatest Nat.Prime (2 * b - 1) < q → q < 2 * b → ¬ q.Prime := by
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime b hb
  have hle : p ≤ 2 * b - 1 := by omega
  have hc := Nat.findGreatest_spec hle hp
  have hpc := Nat.le_findGreatest hle hp
  have hcle := Nat.findGreatest_le (P := Nat.Prime) (2 * b - 1)
  refine ⟨hc, by omega, by omega, ?_⟩
  intro q hq1 hq2
  exact Nat.findGreatest_is_greatest hq1 (by omega)

/-- `B (j + 8) ≥ 83`. -/
private theorem bertrand_ge (j : ℕ) : 83 ≤ bertrand (j + 8) := by
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    rw [show j + 1 + 8 = (j + 8) + 1 by ring, bertrand_succ _ (by omega)]
    have := (chain_step _ ih).2.1
    omega

/-- For `n ≥ 10`, row `n` is `[2 B(n-2) + 1, 2 B(n-1)]`. -/
private theorem rows (j : ℕ) : a (j + 10) = 2 * bertrand (j + 8) + 1 ∧
    len (j + 10) = 2 * bertrand (j + 9) - 2 * bertrand (j + 8) := by
  induction j with
  | zero =>
    have h1 : a 10 = 167 := by decide +kernel
    have h2 : len 10 = 160 := by decide +kernel
    have h3 : bertrand 8 = 83 := by decide +kernel
    have h4 : bertrand 9 = 163 := by decide +kernel
    simp only [zero_add, h1, h2, h3, h4]
    norm_num
  | succ j ih =>
    obtain ⟨iha, ihl⟩ := ih
    have hb := bertrand_ge j
    have hab : bertrand (j + 9) = Nat.findGreatest Nat.Prime (2 * bertrand (j + 8) - 1) :=
      bertrand_succ (j + 8) (by omega)
    have hac : bertrand (j + 10) = Nat.findGreatest Nat.Prime (2 * bertrand (j + 9) - 1) :=
      bertrand_succ (j + 9) (by omega)
    obtain ⟨_, ha1, ha2, _⟩ := chain_step _ hb
    rw [← hab] at ha1 ha2
    have ha83 : 83 ≤ bertrand (j + 9) := by omega
    obtain ⟨hc0, hc1, hc2, hc3⟩ := chain_step _ ha83
    rw [← hac] at hc0 hc1 hc2 hc3
    have hstep := step_core (bertrand (j + 8)) (bertrand (j + 9)) (bertrand (j + 10)) hb ha1 ha2
      hc1 hc2 hc0 hc3
    have hA : a (j + 1 + 10) = 2 * bertrand (j + 9) + 1 := by
      rw [show j + 1 + 10 = (j + 10) + 1 by ring, a_succ _ (by omega), iha, ihl]
      omega
    refine ⟨by rw [hA], ?_⟩
    have hL := len_succ_isLeast (j + 10) (by omega)
    rw [iha, ihl, show j + 10 + 1 = j + 1 + 10 by ring, hA] at hL
    rw [show j + 1 + 9 = j + 10 by ring, show j + 1 + 8 = j + 9 by ring]
    exact hL.unique hstep

/-! ### The statement -/

/-- The conclusion for one concrete small row. -/
private theorem small_case (m lo hi p L : ℕ) (hlo : a m = lo) (hhi : last m = hi)
    (hL : last (m + 1) = L) (hB : bertrand m = p) (hp : p.Prime) (h1 : lo ≤ p) (h2 : p ≤ hi)
    (h3 : L = 2 * p) (hgap : ∀ q, p < q → q ≤ hi → ¬ q.Prime) :
    ∃ p, IsGreatest {q : ℕ | q.Prime ∧ a m ≤ q ∧ q ≤ last m} p ∧
      last (m + 1) = 2 * p ∧ p = bertrand m := by
  refine ⟨p, ⟨⟨hp, by omega, by omega⟩, ?_⟩, by omega, hB.symm⟩
  rintro q ⟨hq, _, hq2⟩
  by_contra hlt
  exact hgap q (by omega) (by omega) hq

/-- Murthy's conjecture (A090905): for `n > 4` the largest prime `p` of group `n - 1` exists,
the last term of group `n` is `2p`, and `p` is the Bertrand prime `A006992(n - 1)`. -/
theorem result : statement := by
  intro n hn
  rcases (show n ≤ 10 ∨ 11 ≤ n by omega) with hs | hb
  · interval_cases n
    · exact small_case 4 5 8 7 14 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun q h1 h2 => by interval_cases q; norm_num)
    · exact small_case 5 9 14 13 26 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun q h1 h2 => by interval_cases q; norm_num)
    · exact small_case 6 15 26 23 46 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun q h1 h2 => by interval_cases q <;> norm_num)
    · exact small_case 7 27 46 43 86 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun q h1 h2 => by interval_cases q <;> norm_num)
    · exact small_case 8 47 86 83 166 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun q h1 h2 => by interval_cases q <;> norm_num)
    · exact small_case 9 87 166 163 326 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun q h1 h2 => by interval_cases q <;> norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 11 := ⟨n - 11, by omega⟩
    rw [show j + 11 - 1 = j + 10 by omega]
    obtain ⟨ha0, hl0⟩ := rows j
    obtain ⟨ha1, hl1⟩ := rows (j + 1)
    have hb := bertrand_ge j
    have hab : bertrand (j + 9) = Nat.findGreatest Nat.Prime (2 * bertrand (j + 8) - 1) :=
      bertrand_succ (j + 8) (by omega)
    have hac : bertrand (j + 10) = Nat.findGreatest Nat.Prime (2 * bertrand (j + 9) - 1) :=
      bertrand_succ (j + 9) (by omega)
    obtain ⟨_, ha1', ha2', _⟩ := chain_step _ hb
    rw [← hab] at ha1' ha2'
    have ha83 : 83 ≤ bertrand (j + 9) := by omega
    obtain ⟨hc0, hc1, hc2, hc3⟩ := chain_step _ ha83
    rw [← hac] at hc0 hc1 hc2 hc3
    simp only [show j + 1 + 10 = j + 11 by ring, show j + 1 + 9 = j + 10 by ring,
      show j + 1 + 8 = j + 9 by ring] at ha1 hl1
    have hlast0 : last (j + 10) = 2 * bertrand (j + 9) := by
      simp only [last, ha0, hl0]; omega
    have hlast1 : last (j + 11) = 2 * bertrand (j + 10) := by
      simp only [last, ha1, hl1]; omega
    refine ⟨bertrand (j + 10), ⟨⟨hc0, ?_, ?_⟩, ?_⟩, hlast1, rfl⟩
    · rw [ha0]; omega
    · rw [hlast0]; omega
    · rintro q ⟨hq, _, hq2⟩
      rw [hlast0] at hq2
      by_contra hlt
      rcases Nat.lt_or_ge q (2 * bertrand (j + 9)) with h | h
      · exact hc3 q (by omega) h hq
      · have hq' : q = 2 * bertrand (j + 9) := by omega
        have h2q : 2 ∣ q := ⟨_, hq'⟩
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q
        omega

end Math0.Frontier.A090905

#math0_settles Math0.Frontier.A090905.result Math0.Statements.A090905.statement

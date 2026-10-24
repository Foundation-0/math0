/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A092054
import Math0.Audit

/-!
# Convergents of `[1; 1/2, 1/3, …]`: numerator plus denominator is a power of two (A092054)

We prove the conjecture in OEIS A092054 (Franklin T. Adams-Watters, 2006): for every `n ≥ 1`,
writing the convergent `[1; 1/2, …, 1/n] = p/q` in lowest terms, `p + q = 2 ^ a(n)` with
`a(n) = v₂(n!) + v₂((n+1)!) = A011371(n) + A011371(n+1) = 2n + 1 - s₂(n) - s₂(n+1)
= Σ_{k=1}^n A001511(⌊(k+1)/2⌋)`.

**Convergents.** With a variable last tail `t > 0`, the continued fraction
`[1; 1/2, …, 1/n, t]` equals `(P n · t + n P (n-1)) / (Q n · t + n Q (n-1))`, where
`P, Q` are the scaled convergent numerators/denominators: `P 0 = 1, P 1 = 1,
P (n+2) = P (n+1) + (n+1)(n+2) P n` and `Q 0 = 0, Q 1 = 1` with the same recursion
(`tailEval_range`). Hence `conv n = P n / Q n` (`conv_eq`).

**Closed forms.** With `D m = (2m-1)!!`: `P (2m) = D(m)² (2m+1)`, `P (2m+1) = D(m+1)²` (so
`P n` is odd), and `T = P + Q` satisfies `T (2m) = 4^m (m!)²`,
`T (2m+1) = 2^(2m+1) m! (m+1)!` (`P_closed`, `T_closed`, by induction).

**Reduction.** Write `m! = 2^v w` with `w` odd. Since `m! m! ∣ (2m)! = 2^m m! D(m)`, `w ∣ D(m)`
(`odd_part`). So `T n = 2^e u` with `u ∣ P n` and `e = v₂(n!) + v₂((n+1)!)` (`key`). As
`P n` is odd, `gcd(P n, Q n) = gcd(P n, T n) = u`, so `p + q = T n / u = 2^e`
(`num_add_den_eq`). Legendre's formula `v₂(m!) = m - s₂(m)` and
`v₂((n+2)!) - v₂(n!) = v₂((n+1)(n+2)) = A001511(⌊(n+2)/2⌋)` give the other three forms.
-/

namespace Math0.Frontier.A092054
open Math0.Statements.A092054
open scoped Nat

/-- Continued fraction with a variable last tail: `tailEval [x₀, …, x_k] t =
x₀ + 1/(x₁ + 1/(⋯ + 1/(x_k + 1/t)))`, and `tailEval [] t = t`. -/
private def tailEval : List ℚ → ℚ → ℚ
  | [], t => t
  | x :: l, t => x + 1 / tailEval l t

/-- `cfEval (l ++ [y])` is `tailEval l y`. -/
private lemma cfEval_append_singleton (l : List ℚ) (y : ℚ) :
    cfEval (l ++ [y]) = tailEval l y := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons z zs =>
      show x + 1 / cfEval ((z :: zs) ++ [y]) = x + 1 / tailEval (z :: zs) y
      rw [ih]

/-- Appending a partial quotient `x` replaces the tail `t` by `x + 1/t`. -/
private lemma tailEval_append (l : List ℚ) (x t : ℚ) :
    tailEval (l ++ [x]) t = tailEval l (x + 1 / t) := by
  induction l with
  | nil => rfl
  | cons z l ih => simp only [List.cons_append, tailEval, ih]

/-- The partial quotients `1/(k+1)`. -/
private def pq (k : ℕ) : ℚ := 1 / ((k : ℚ) + 1)

/-- The numerators (scaled): `P 0 = 1`, `P 1 = 1`, `P (n+2) = P (n+1) + (n+1)(n+2) P n`. -/
private def P : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => P (n + 1) + (n + 1) * (n + 2) * P n

/-- The denominators (scaled): `Q 0 = 0`, `Q 1 = 1`, `Q (n+2) = Q (n+1) + (n+1)(n+2) Q n`. -/
private def Q : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => Q (n + 1) + (n + 1) * (n + 2) * Q n

/-- The denominators are positive from index `1` on. -/
private lemma Q_pos : ∀ n, 0 < Q (n + 1)
  | 0 => by decide
  | n + 1 => by
    have := Q_pos n
    show 0 < Q (n + 1) + (n + 1) * (n + 2) * Q n
    omega

/-- The Möbius form of the truncated continued fraction with a variable tail. -/
private lemma tailEval_range (m : ℕ) (t : ℚ) (ht : 0 < t) :
    tailEval ((List.range (m + 1)).map pq) t =
      ((P (m + 1) : ℚ) * t + (m + 1) * P m) / ((Q (m + 1) : ℚ) * t + (m + 1) * Q m) := by
  induction m generalizing t with
  | zero =>
    simp [tailEval, pq, P, Q]
    field_simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, tailEval_append]
    have hs : 0 < pq (m + 1) + 1 / t := by
      unfold pq; positivity
    rw [ih _ hs]
    have h1 := Q_pos m
    have h2 := Q_pos (m + 1)
    have hP : (P (m + 2) : ℚ) = P (m + 1) + (m + 1) * (m + 2) * P m := by
      simp [P]
    have hQ : (Q (m + 2) : ℚ) = Q (m + 1) + (m + 1) * (m + 2) * Q m := by
      simp [Q]
    rw [hP, hQ]
    unfold pq
    push_cast
    have hd1 : (0 : ℚ) < (Q (m + 1) : ℚ) * (1 / ((m : ℚ) + 1 + 1) + 1 / t) + (m + 1) * Q m := by
      have : (0 : ℚ) < Q (m + 1) := by exact_mod_cast h1
      positivity
    have hd2 : (0 : ℚ) < ((Q (m + 1) : ℚ) + (m + 1) * (m + 2) * Q m) * t + (m + 1 + 1) * Q (m + 1) := by
      have : (0 : ℚ) < Q (m + 1) := by exact_mod_cast h1
      positivity
    rw [div_eq_div_iff hd1.ne' hd2.ne']
    field_simp
    ring

/-- `conv n` is the continued fraction of the list `[pq 0, …, pq (n-1)]`. -/
private lemma conv_eq_pq (n : ℕ) : conv n = cfEval ((List.range n).map pq) := by
  unfold conv
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.bind_eq_flatMap,
      List.flatMap_append] at ih ⊢
    rw [ih]
    simp [pq]

/-- The convergents: `conv n = P n / Q n` for `n ≥ 1`. -/
private lemma conv_eq (n : ℕ) (hn : 1 ≤ n) : conv n = (P n : ℚ) / Q n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [conv_eq_pq, List.range_succ, List.map_append, List.map_singleton]
  rw [cfEval_append_singleton]
  cases m with
  | zero => simp [tailEval, P, Q, pq]
  | succ m =>
    rw [tailEval_range m _ (by unfold pq; positivity)]
    have h1 := Q_pos m
    have hP : (P (m + 2) : ℚ) = P (m + 1) + (m + 1) * (m + 2) * P m := by
      simp [P]
    have hQ : (Q (m + 2) : ℚ) = Q (m + 1) + (m + 1) * (m + 2) * Q m := by
      simp [Q]
    rw [hP, hQ]
    unfold pq
    push_cast
    have : (0 : ℚ) < Q (m + 1) := by exact_mod_cast h1
    field_simp
    ring

/-! ### Closed forms -/

/-- The recursion of `P`. -/
private lemma P_succ_succ (n : ℕ) : P (n + 2) = P (n + 1) + (n + 1) * (n + 2) * P n := rfl

/-- The recursion of `Q`. -/
private lemma Q_succ_succ (n : ℕ) : Q (n + 2) = Q (n + 1) + (n + 1) * (n + 2) * Q n := rfl

/-- The odd double factorial `D m = 1 · 3 ⋯ (2m - 1)`. -/
private def D : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 1) * D m

/-- `(2m-1)!!` is odd. -/
private lemma D_odd (m : ℕ) : Odd (D m) := by
  induction m with
  | zero => decide
  | succ m ih => exact (odd_two_mul_add_one m).mul ih

/-- `(2m-1)!! ∣ (2m+1)!!`. -/
private lemma D_dvd_succ (m : ℕ) : D m ∣ D (m + 1) := Dvd.intro_left _ rfl

/-- `(2m)! = 2^m · m! · (2m-1)!!`. -/
private lemma factorial_two_mul (m : ℕ) : (2 * m)! = 2 ^ m * m ! * D m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, ih,
      Nat.factorial_succ]
    simp only [D, pow_succ]
    ring

/-- Closed form of the numerators: `P (2m) = ((2m-1)!!)² (2m+1)`, `P (2m+1) = ((2m+1)!!)²`. -/
private lemma P_closed (m : ℕ) : P (2 * m) = D m ^ 2 * (2 * m + 1) ∧ P (2 * m + 1) = D (m + 1) ^ 2 := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : P (2 * (m + 1)) = D (m + 1) ^ 2 * (2 * (m + 1) + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, P_succ_succ, h0, h1]
      simp only [D]
      ring
    refine ⟨e0, ?_⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, P_succ_succ,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring, e0, h1]
    simp only [D]
    ring

/-- `T n = P n + Q n` satisfies the same recursion. -/
private lemma T_succ_succ (n : ℕ) :
    P (n + 2) + Q (n + 2) = (P (n + 1) + Q (n + 1)) + (n + 1) * (n + 2) * (P n + Q n) := by
  rw [P_succ_succ, Q_succ_succ]
  ring

/-- Closed form of `T n = P n + Q n`: `T (2m) = 4^m (m!)²`, `T (2m+1) = 2^(2m+1) m! (m+1)!`. -/
private lemma T_closed (m : ℕ) :
    P (2 * m) + Q (2 * m) = 4 ^ m * (m !) ^ 2 ∧
      P (2 * m + 1) + Q (2 * m + 1) = 2 ^ (2 * m + 1) * m ! * (m + 1)! := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : P (2 * (m + 1)) + Q (2 * (m + 1)) = 4 ^ (m + 1) * ((m + 1)!) ^ 2 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, T_succ_succ, h0, h1]
      simp only [Nat.factorial_succ, pow_succ, pow_mul]
      push_cast
      ring
    refine ⟨e0, ?_⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, T_succ_succ,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring, e0, h1]
    simp only [Nat.factorial_succ, pow_succ, pow_mul]
    push_cast
    ring

/-- The scaled numerators are odd. -/
private lemma P_odd (n : ℕ) : Odd (P n) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [(P_closed m).1]
    exact ((D_odd m).pow).mul (odd_two_mul_add_one m)
  · rw [(P_closed m).2]
    exact (D_odd (m + 1)).pow

/-! ### 2-adic valuations -/

/-- `V k = v₂(k!)`. -/
private def V (k : ℕ) : ℕ := padicValNat 2 (k !)

/-- An odd number has `2`-adic valuation `0`. -/
private lemma pv_odd {o : ℕ} (ho : Odd o) : padicValNat 2 o = 0 :=
  padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])

/-- `v₂(2^k · o) = k` for odd `o`. -/
private lemma pv_two_pow_mul_odd (k : ℕ) {o : ℕ} (ho : Odd o) : padicValNat 2 (2 ^ k * o) = k := by
  rw [padicValNat.mul (by positivity) (by rintro rfl; simp at ho), padicValNat.prime_pow,
    pv_odd ho, add_zero]

/-- The odd part `w` of `m!` divides `(2m-1)!!` (because `(2m choose m)` is an integer). -/
private lemma odd_part (m : ℕ) : ∃ v w, m ! = 2 ^ v * w ∧ Odd w ∧ w ∣ D m := by
  obtain ⟨v, w, hw, h⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.factorial_ne_zero m)
  refine ⟨v, w, h, hw, ?_⟩
  have h1 : m ! * m ! ∣ m ! * (2 ^ m * D m) := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add m m
    rw [← two_mul, factorial_two_mul] at this
    rw [show m ! * (2 ^ m * D m) = 2 ^ m * m ! * D m by ring]
    exact this
  have h2 : m ! ∣ 2 ^ m * D m := Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos m) h1
  have h3 : w ∣ 2 ^ m * D m := (Dvd.intro_left _ h.symm).trans h2
  have hc : Nat.Coprime w (2 ^ m) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hw)
  exact hc.dvd_of_dvd_mul_left h3

/-- `v₂((2m)!) = m + v₂(m!)`, given `m! = 2^v w` with `w` odd. -/
private lemma V_two_mul (m v w : ℕ) (h : m ! = 2 ^ v * w) (hw : Odd w) : V (2 * m) = m + v := by
  unfold V
  rw [factorial_two_mul, h, show 2 ^ m * (2 ^ v * w) * D m = 2 ^ (m + v) * (w * D m) by ring,
    pv_two_pow_mul_odd _ (hw.mul (D_odd m))]

/-- `v₂((2m+1)!) = v₂((2m)!)`. -/
private lemma V_two_mul_add_one (m : ℕ) : V (2 * m + 1) = V (2 * m) := by
  unfold V
  rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _),
    pv_odd (odd_two_mul_add_one m), zero_add]

/-- The key factorization: `P n + Q n = 2^e · u` with `u ∣ P n` and `e = v₂(n!) + v₂((n+1)!)`. -/
private lemma key (n : ℕ) : ∃ e u, P n + Q n = 2 ^ e * u ∧ u ∣ P n ∧ e = V n + V (n + 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨v, w, h, hw, hd⟩ := odd_part m
    refine ⟨2 * m + 2 * v, w ^ 2, ?_, ?_, ?_⟩
    · rw [(T_closed m).1, h, show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
      ring
    · rw [(P_closed m).1]
      exact (pow_dvd_pow_of_dvd hd 2).mul_right _
    · rw [V_two_mul_add_one, V_two_mul m v w h hw]
      ring
  · obtain ⟨v, w, h, hw, hd⟩ := odd_part m
    obtain ⟨v', w', h', hw', hd'⟩ := odd_part (m + 1)
    refine ⟨2 * m + 1 + v + v', w * w', ?_, ?_, ?_⟩
    · rw [(T_closed m).2, h, h']
      ring
    · rw [(P_closed m).2, pow_two]
      exact mul_dvd_mul (hd.trans (D_dvd_succ m)) hd'
    · rw [V_two_mul_add_one, V_two_mul m v w h hw, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
        V_two_mul (m + 1) v' w' h' hw']
      ring

/-- If `a + b = 2^e u` with `u ∣ a` and `a` odd, then `a/b` in lowest terms has
numerator plus denominator `2^e`. -/
private lemma num_add_den_eq (a b e u : ℕ) (hb : 0 < b) (hT : a + b = 2 ^ e * u) (hu : u ∣ a)
    (ha : Odd a) : ((a : ℚ) / b).num.natAbs + ((a : ℚ) / b).den = 2 ^ e := by
  have hg : Nat.gcd a b = u := by
    rw [← Nat.gcd_self_add_right a b, hT]
    apply Nat.dvd_antisymm
    · have hc : Nat.Coprime (Nat.gcd a (2 ^ e * u)) (2 ^ e) := by
        apply Nat.Coprime.pow_right
        exact Nat.coprime_two_right.mpr (ha.of_dvd_nat (Nat.gcd_dvd_left _ _))
      exact hc.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
    · exact Nat.dvd_gcd hu (Dvd.intro_left _ rfl)
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · subst h; simp at hT; omega
    · exact h
  have hub : u ∣ b := hg ▸ Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime (a / u) (b / u) := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) (by rw [hg]; exact hu0)
    rwa [hg] at this
  obtain ⟨a', rfl⟩ := hu
  obtain ⟨b', rfl⟩ := hub
  rw [Nat.mul_div_cancel_left _ hu0, Nat.mul_div_cancel_left _ hu0] at hcop
  have hb' : 0 < b' := Nat.pos_of_mul_pos_left hb
  have hq : ((u * a' : ℕ) : ℚ) / ((u * b' : ℕ) : ℚ) = ((a' : ℤ) : ℚ) / ((b' : ℤ) : ℚ) := by
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hu0.ne')]
  have hc' : Nat.Coprime (a' : ℤ).natAbs (b' : ℤ).natAbs := by simpa using hcop
  rw [hq]
  have h1 := Rat.num_div_eq_of_coprime (a := (a' : ℤ)) (b := (b' : ℤ)) (by exact_mod_cast hb') hc'
  have h2 := Rat.den_div_eq_of_coprime (a := (a' : ℤ)) (b := (b' : ℤ)) (by exact_mod_cast hb') hc'
  rw [h1, Int.natAbs_natCast]
  have h3 : (((a' : ℤ) : ℚ) / ((b' : ℤ) : ℚ)).den = b' := by exact_mod_cast h2
  rw [h3]
  have : u * (a' + b') = u * 2 ^ e := by rw [mul_add, hT, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hu0 this

/-! ### The combinatorial identities -/

/-- Legendre: `v₂(m!) = m - s₂(m)`. -/
private lemma V_eq (m : ℕ) : V m = A011371 m := by
  have := sub_one_mul_padicValNat_factorial (p := 2) m
  simpa [V, A011371, binWeight] using this

/-- `v₂(m!) + s₂(m) = m`. -/
private lemma V_add_binWeight (m : ℕ) : V m + binWeight m = m := by
  rw [V_eq, A011371]
  have := Nat.digit_sum_le 2 m
  unfold binWeight
  omega

/-- `v₂((n+2)!) = v₂(n!) + A001511(⌊(n+2)/2⌋)`. -/
private lemma V_add_two (n : ℕ) : V (n + 2) = V n + ruler ((n + 1 + 1) / 2) := by
  unfold V ruler
  rw [Nat.factorial_succ, Nat.factorial_succ, padicValNat.mul (by omega) (by positivity),
    padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega,
      pv_odd (odd_two_mul_add_one j), show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    ring
  · rw [show (2 * j + 1 + 1 + 1) / 2 = j + 1 by omega,
      show 2 * j + 1 + 1 + 1 = 2 * (j + 1) + 1 by ring, pv_odd (odd_two_mul_add_one (j + 1)),
      show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    ring

/-- The ruler-function sum equals `v₂(n!) + v₂((n+1)!)`. -/
private lemma ruler_sum (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, ruler ((k + 1) / 2) = V n + V (n + 1) := by
  induction n with
  | zero => simp [V]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, V_add_two]
    ring

/-- The main theorem. -/
theorem result : statement := by
  intro n hn
  obtain ⟨e, u, hT, hu, he⟩ := key n
  have hsum : num n + den n = 2 ^ e := by
    unfold num den
    rw [conv_eq n hn]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact num_add_den_eq _ _ _ _ (Q_pos k) hT hu (P_odd _)
  have ha : a n = V n + V (n + 1) := by
    unfold a
    rw [hsum, Nat.log_pow (by norm_num), he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsum, ha, ← he]
  · rw [ha, ruler_sum]
  · have h1 := V_add_binWeight n
    have h2 := V_add_binWeight (n + 1)
    rw [ha]
    push_cast
    omega
  · rw [ha, V_eq, V_eq]

end Math0.Frontier.A092054

#math0_settles Math0.Frontier.A092054.result Math0.Statements.A092054.statement

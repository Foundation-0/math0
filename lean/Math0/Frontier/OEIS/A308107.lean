/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A308107
import Math0.Audit

/-!
# A308107: Barker's generating function for smallest sides of scalene triangles

We prove both of Barker's conjectures (the rational generating function and the order-15
recurrence).

*Idea.* A scalene triangle `k < i < j < k + i` with middle side `i ≥ k + 2` is obtained from the
triangle `(k, i - 1, j - 1)` of perimeter `n - 2` with the same smallest side; the ones with
`i = k + 1` are parametrized by `v = j - i ≥ 1`, `w = k - v ≥ 1`, i.e. `(k, i, j) =
(v + w, v + w + 1, 2v + w + 1)`, of perimeter `4v + 3w + 2` and weight `k = v + w`. Shifting
`v ↦ v + 1` and `w ↦ w + 1` in the set `U n` of such pairs gives the relations

* `a(n+2) = a(n) + bv(n+2) + bw(n+2)` with `bv n = ∑_{U n} v`, `bw n = ∑_{U n} w`;
* `bv(n+4) = bv(n) + c(n+4)`, `bw(n+3) = bw(n) + c(n+3)` with `c n = #U n`;
* `c(n+4) = c(n) + e(n+4)` with `e n = #{(v, w) ∈ U n | v = 1}`, and
  `e(n+3) = e(n) + [n + 3 = 9]`.

As power series these say `(1 - X²) A = Bv + Bw`, `(1 - X⁴) Bv = C`, `(1 - X³) Bw = C`,
`(1 - X⁴) C = E`, `(1 - X³) E = X⁹`, so
`(1 - X²)(1 - X³)²(1 - X⁴)² A = X⁹ (2 - X³ - X⁴)`. Since
`(1 - X²)(1 - X³)²(1 - X⁴)² = (1 - X) · den` and `2 - X³ - X⁴ = (1 - X)(2 + 2X + 2X² + X³)`,
cancelling `1 - X` gives `A · den = X⁹ (2 + 2X + 2X² + X³)`, i.e. the generating function, and
comparing coefficients of index `n > 15` gives the recurrence.
-/

namespace Math0.Frontier.A308107
open Math0.Statements.A308107 PowerSeries

/-- The triples `(k, i, j)` with `k < i < j < k + i` and `k + i + j = n` summed in `a n`. -/
private def T (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun t : ℕ × ℕ × ℕ => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < t.1 + t.2.1 ∧
        t.1 + t.2.1 + t.2.2 = n)

/-- The pairs `(v, w)` with `v, w ≥ 1` and `4v + 3w + 2 = n`: the scalene triangles
`(v + w, v + w + 1, 2v + w + 1)` of perimeter `n` whose middle side is one more than the
smallest. -/
private def U (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 4 * p.1 + 3 * p.2 + 2 = n)

/-- `a n` as a sum over `T n`. -/
private theorem a_eq_T (n : ℕ) : a n = ∑ t ∈ T n, t.1 := rfl

/-- Triangles with middle side one more than the smallest side, reparametrized by `U`. -/
private theorem sum_T_filter (n : ℕ) :
    ∑ t ∈ (T n).filter (fun t => t.2.1 = t.1 + 1), t.1 = ∑ p ∈ U n, (p.1 + p.2) := by
  symm
  apply Finset.sum_nbij' (fun p => (p.1 + p.2, p.1 + p.2 + 1, 2 * p.1 + p.2 + 1))
    (fun t => (t.2.2 - t.1 - 1, 2 * t.1 + 1 - t.2.2))
  · rintro ⟨v, w⟩ h
    simp only [U, T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_true] at h ⊢
    omega
  · rintro ⟨k, i, j⟩ h
    simp only [U, T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨v, w⟩ h
    simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨k, i, j⟩ h
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨v, w⟩ _
    rfl

/-- Triangles with middle side at least two more than the smallest side come from perimeter
`n` by adding `1` to the two larger sides. -/
private theorem sum_T_filter_not (n : ℕ) :
    ∑ t ∈ (T (n + 2)).filter (fun t => ¬ t.2.1 = t.1 + 1), t.1 = ∑ t ∈ T n, t.1 := by
  symm
  apply Finset.sum_nbij' (fun t => (t.1, t.2.1 + 1, t.2.2 + 1))
    (fun t => (t.1, t.2.1 - 1, t.2.2 - 1))
  · rintro ⟨k, i, j⟩ h
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨k, i, j⟩ h
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨k, i, j⟩ h
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨k, i, j⟩ h
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨k, i, j⟩ _
    rfl

/-- `a(n+2) = a(n) + ∑_{U(n+2)} (v + w)`. -/
private theorem a_shift (n : ℕ) :
    a (n + 2) = a n + (∑ p ∈ U (n + 2), p.1 + ∑ p ∈ U (n + 2), p.2) := by
  rw [a_eq_T, a_eq_T, ← Finset.sum_filter_add_sum_filter_not (T (n + 2))
    (fun t => t.2.1 = t.1 + 1), sum_T_filter, sum_T_filter_not, Finset.sum_add_distrib, add_comm]

/-- Shifting `v ↦ v + 1` in `U`. -/
private theorem U_shift_v (n : ℕ) (g : ℕ × ℕ → ℕ) :
    ∑ p ∈ U (n + 4), g p =
      ∑ p ∈ U n, g (p.1 + 1, p.2) + ∑ p ∈ U (n + 4), if p.1 = 1 then g p else 0 := by
  have h1 :
      ∑ p ∈ (U (n + 4)).filter (fun p => ¬ p.1 = 1), g p = ∑ p ∈ U n, g (p.1 + 1, p.2) := by
    symm
    apply Finset.sum_nbij' (fun p => (p.1 + 1, p.2)) (fun p => (p.1 - 1, p.2))
    · rintro ⟨v, w⟩ h
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      omega
    · rintro ⟨v, w⟩ h
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      omega
    · rintro ⟨v, w⟩ _
      simp
    · rintro ⟨v, w⟩ h
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      simp only [Prod.mk.injEq, and_true]
      omega
    · rintro ⟨v, w⟩ _
      rfl
  rw [← Finset.sum_filter_add_sum_filter_not (U (n + 4)) (fun p => p.1 = 1), h1,
    Finset.sum_filter, add_comm]

/-- Shifting `w ↦ w + 1` in `U`. -/
private theorem U_shift_w (n : ℕ) (g : ℕ × ℕ → ℕ) :
    ∑ p ∈ U (n + 3), g p =
      ∑ p ∈ U n, g (p.1, p.2 + 1) + ∑ p ∈ U (n + 3), if p.2 = 1 then g p else 0 := by
  have h1 :
      ∑ p ∈ (U (n + 3)).filter (fun p => ¬ p.2 = 1), g p = ∑ p ∈ U n, g (p.1, p.2 + 1) := by
    symm
    apply Finset.sum_nbij' (fun p => (p.1, p.2 + 1)) (fun p => (p.1, p.2 - 1))
    · rintro ⟨v, w⟩ h
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      omega
    · rintro ⟨v, w⟩ h
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      omega
    · rintro ⟨v, w⟩ _
      simp
    · rintro ⟨v, w⟩ h
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · rintro ⟨v, w⟩ _
      rfl
  rw [← Finset.sum_filter_add_sum_filter_not (U (n + 3)) (fun p => p.2 = 1), h1,
    Finset.sum_filter, add_comm]

/-- `U n` is empty for `n < 9`, so every sum over it vanishes. -/
private theorem sum_U_small (n : ℕ) (hn : n < 9) (g : ℕ × ℕ → ℕ) :
    ∑ p ∈ U n, g p = 0 := by
  apply Finset.sum_eq_zero
  rintro ⟨v, w⟩ h
  simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
  omega

/-- `∑_{U n} v`. -/
private def bv (n : ℕ) : ℕ := ∑ p ∈ U n, p.1
/-- `∑_{U n} w`. -/
private def bw (n : ℕ) : ℕ := ∑ p ∈ U n, p.2
/-- `#U n`. -/
private def c (n : ℕ) : ℕ := ∑ _p ∈ U n, 1
/-- `#{(v, w) ∈ U n | v = 1}`. -/
private def e (n : ℕ) : ℕ := ∑ p ∈ U n, if p.1 = 1 then 1 else 0

/-- `bv(n+4) = bv(n) + c(n+4)`. -/
private theorem bv_shift (n : ℕ) : bv (n + 4) = bv n + c (n + 4) := by
  unfold bv c
  rw [U_shift_v n Prod.fst, U_shift_v n (fun _ => 1), Finset.sum_add_distrib]
  have : ∀ p : ℕ × ℕ, (if p.1 = 1 then p.1 else 0) = if p.1 = 1 then 1 else 0 := by
    rintro ⟨v, w⟩; dsimp only; split_ifs with h <;> simp [h]
  simp only [this]
  ring

/-- `bw(n+3) = bw(n) + c(n+3)`. -/
private theorem bw_shift (n : ℕ) : bw (n + 3) = bw n + c (n + 3) := by
  unfold bw c
  rw [U_shift_w n Prod.snd, U_shift_w n (fun _ => 1), Finset.sum_add_distrib]
  have : ∀ p : ℕ × ℕ, (if p.2 = 1 then p.2 else 0) = if p.2 = 1 then 1 else 0 := by
    rintro ⟨v, w⟩; dsimp only; split_ifs with h <;> simp [h]
  simp only [this]
  ring

/-- `c(n+4) = c(n) + e(n+4)`. -/
private theorem c_shift (n : ℕ) : c (n + 4) = c n + e (n + 4) := by
  unfold c e
  rw [U_shift_v n (fun _ => 1)]

/-- `e(n+3) = e(n) + [n + 3 = 9]`: the only pair with `v = w = 1` is at perimeter `9`. -/
private theorem e_shift (n : ℕ) : e (n + 3) = e n + if n + 3 = 9 then 1 else 0 := by
  unfold e
  rw [U_shift_w n (fun p => if p.1 = 1 then 1 else 0)]
  congr 1
  have : ∀ p : ℕ × ℕ, (if p.2 = 1 then (if p.1 = 1 then 1 else 0) else 0) =
      if ((1, 1) : ℕ × ℕ) = p then 1 else 0 := by
    rintro ⟨v, w⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  simp only [this]
  rw [Finset.sum_ite_eq]
  congr 1
  simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range, eq_iff_iff]
  omega

/-- A one-step shift relation is a power series identity. -/
private theorem ps_shift (d : ℕ) (f g : ℕ → ℚ) (h : ∀ n, f (n + d) = f n + g (n + d))
    (h0 : ∀ n < d, f n = g n) : (1 - X ^ d) * mk f = mk g := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul']
  simp only [coeff_mk]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
    rw [Nat.add_sub_cancel, h m]
    ring
  · rw [h0 n (by omega)]
    ring

/-- The first two terms vanish. -/
private theorem a_zero_one : a 0 = 0 ∧ a 1 = 0 := by decide

/-- The shift relations as power series identities, combined:
`A · den = X⁹ (2 + 2X + 2X² + X³)`. -/
private theorem gf_mul :
    mk (fun n => (a n : ℚ)) * den = X ^ 9 * (2 + 2 * X + 2 * X ^ 2 + X ^ 3) := by
  have h1 :
      (1 - X ^ 2) * mk (fun n => (a n : ℚ)) = mk (fun n => ((bv n + bw n : ℕ) : ℚ)) := by
    apply ps_shift
    · intro n
      exact_mod_cast a_shift n
    · intro n hn
      have ha : a n = 0 := by
        interval_cases n
        · exact a_zero_one.1
        · exact a_zero_one.2
      simp only [ha, bv, bw, sum_U_small n (by omega), Nat.cast_zero, add_zero]
  have h2 : mk (fun n => ((bv n + bw n : ℕ) : ℚ)) =
      mk (fun n => (bv n : ℚ)) + mk (fun n => (bw n : ℚ)) := by
    ext n
    simp
  have h3 : (1 - X ^ 4) * mk (fun n => (bv n : ℚ)) = mk (fun n => (c n : ℚ)) := by
    apply ps_shift
    · intro n
      exact_mod_cast bv_shift n
    · intro n hn
      simp only [bv, c, sum_U_small n (by omega)]
  have h4 : (1 - X ^ 3) * mk (fun n => (bw n : ℚ)) = mk (fun n => (c n : ℚ)) := by
    apply ps_shift
    · intro n
      exact_mod_cast bw_shift n
    · intro n hn
      simp only [bw, c, sum_U_small n (by omega)]
  have h5 : (1 - X ^ 4) * mk (fun n => (c n : ℚ)) = mk (fun n => (e n : ℚ)) := by
    apply ps_shift
    · intro n
      exact_mod_cast c_shift n
    · intro n hn
      simp only [c, e, sum_U_small n (by omega)]
  have h6 : (1 - X ^ 3) * mk (fun n => (e n : ℚ)) = X ^ 9 := by
    have : (X ^ 9 : ℚ⟦X⟧) = mk (fun n => ((if n = 9 then 1 else 0 : ℕ) : ℚ)) := by
      ext n
      simp only [coeff_X_pow, coeff_mk]
      split_ifs <;> simp
    rw [this]
    apply ps_shift
    · intro n
      exact_mod_cast e_shift n
    · intro n hn
      simp only [e, sum_U_small n (by omega)]
      rw [if_neg (by omega)]
  have hX : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp at this
  apply mul_left_cancel₀ hX
  unfold den
  linear_combination (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * h1 + (1 - X ^ 3) ^ 2 * (1 - X ^ 4) ^ 2 * h2
    + (1 - X ^ 3) ^ 2 * (1 - X ^ 4) * h3 + (1 - X ^ 3) * (1 - X ^ 4) ^ 2 * h4
    + (1 - X ^ 3) * (2 - X ^ 3 - X ^ 4) * h5 + (2 - X ^ 3 - X ^ 4) * h6

/-- The `n`-th coefficient of `X^k · mk f` for `k ≤ n`. -/
private theorem coeff_shift (f : ℕ → ℚ) {n k : ℕ} (hk : k ≤ n) :
    coeff n (X ^ k * mk f) = f (n - k) := by
  rw [coeff_X_pow_mul', if_pos hk, coeff_mk]

/-- Barker's generating function and recurrence. -/
theorem result : statement := by
  refine ⟨genFun_iff.2 gf_mul, ?_⟩
  intro n hn
  set f : ℕ → ℚ := fun n => (a n : ℚ) with hf
  have hden : mk f * den = X ^ 0 * mk f + X ^ 1 * mk f - C 2 * (X ^ 3 * mk f) -
      C 4 * (X ^ 4 * mk f) - C 2 * (X ^ 5 * mk f) + X ^ 6 * mk f + C 5 * (X ^ 7 * mk f) +
      C 5 * (X ^ 8 * mk f) + X ^ 9 * mk f - C 2 * (X ^ 10 * mk f) - C 4 * (X ^ 11 * mk f) -
      C 2 * (X ^ 12 * mk f) + X ^ 14 * mk f + X ^ 15 * mk f := by
    rw [den_eq]
    simp only [map_ofNat]
    ring
  have hrhs : (X ^ 9 * (2 + 2 * X + 2 * X ^ 2 + X ^ 3) : ℚ⟦X⟧) =
      C 2 * X ^ 9 + C 2 * X ^ 10 + C 2 * X ^ 11 + X ^ 12 := by
    simp only [map_ofNat]
    ring
  have h := congrArg (coeff n) gf_mul
  rw [hden, hrhs] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow] at h
  rw [coeff_shift f (by omega : 0 ≤ n), coeff_shift f (by omega : 1 ≤ n),
    coeff_shift f (by omega : 3 ≤ n), coeff_shift f (by omega : 4 ≤ n),
    coeff_shift f (by omega : 5 ≤ n), coeff_shift f (by omega : 6 ≤ n),
    coeff_shift f (by omega : 7 ≤ n), coeff_shift f (by omega : 8 ≤ n),
    coeff_shift f (by omega : 9 ≤ n), coeff_shift f (by omega : 10 ≤ n),
    coeff_shift f (by omega : 11 ≤ n), coeff_shift f (by omega : 12 ≤ n),
    coeff_shift f (by omega : 14 ≤ n), coeff_shift f (by omega : 15 ≤ n),
    if_neg (by omega : n ≠ 9), if_neg (by omega : n ≠ 10), if_neg (by omega : n ≠ 11),
    if_neg (by omega : n ≠ 12)] at h
  simp only [hf, Nat.sub_zero] at h
  apply Int.cast_injective (α := ℚ)
  push_cast
  linarith

end Math0.Frontier.A308107

#math0_settles Math0.Frontier.A308107.result Math0.Statements.A308107.statement

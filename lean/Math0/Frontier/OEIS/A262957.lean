/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A262957
import Math0.Audit

/-!
# A262957: Israel's `b(n)` and `c(n)` are coprime, so `a(n) = b(n)`

We prove Robert Israel's conjecture from OEIS A262957: the sequences `b`, `c` defined by
`b(1)=2, b(2)=3, c(1)=3, c(2)=5` and
`x(n+1) = (((-1)^n(n-1)+n(n+2)) x(n) - (1+(-1)^n(n+1)) x(n-1)) / (n-(-1)^n)` are coprime
integers, and `a(n) = b(n)`.

**Convergents.** Let `p`, `q : ℕ → ℤ` satisfy `r(k+2) = (k+2) r(k+1) + (-1)^(k+1) r(k)` with
`p(0)=p(1)=1`, `q(0)=0`, `q(1)=1` (these are the shifted convergent numerators/denominators of
the continued fraction). By induction on `k`, for every `t ≥ 1` the fold of
`i, u ↦ i + (-1)^i/u` over `1, …, k+1` with innermost value `t` equals
`(p(k+1) t + (-1)^(k+1) p(k)) / (q(k+1) t + (-1)^(k+1) q(k))` (each step multiplies numerator
and denominator by `t ≠ 0`). With `t = 1`, `cf n = x(n)/y(n)` where
`x(n) = p(n+1) + (-1)^(n+1) p(n)`, `y(n) = q(n+1) + (-1)^(n+1) q(n)`.

**Israel's recurrence.** Writing everything in terms of `r(m+1), r(m+2)` and splitting on the
parity of `m`, `x` and `y` satisfy Israel's recurrence (a polynomial identity), and their
initial values are `2, 3` and `3, 5`. Hence `b = x`, `c = y`.

**Coprimality.** `x(n) q(n) - p(n) y(n) = p(n+1) q(n) - p(n) q(n+1) = ±1` (the determinant
changes by the factor `-(-1)^(k+1)` at each step and starts at `-1`), so `x(n)`, `y(n)` are
coprime. Both are positive for `n ≥ 1` (monotonicity of `p`, `q`), so the reduced numerator of
`cf n` is `x(n) = b(n)`.
-/

namespace Math0.Frontier.A262957
open Math0.Statements.A262957

/-- Shifted convergent sequence: `r 0 = r₀`, `r 1 = r₁`,
`r (k+2) = (k+2) r (k+1) + (-1)^(k+1) r k`. -/
private def seq (r₀ r₁ : ℤ) : ℕ → ℤ
  | 0 => r₀
  | 1 => r₁
  | k + 2 => ((k : ℤ) + 2) * seq r₀ r₁ (k + 1) + (-1) ^ (k + 1) * seq r₀ r₁ k

/-- The defining recurrence of `seq`. -/
private lemma seq_succ_succ (r₀ r₁ : ℤ) (k : ℕ) :
    seq r₀ r₁ (k + 2) = ((k : ℤ) + 2) * seq r₀ r₁ (k + 1) + (-1) ^ (k + 1) * seq r₀ r₁ k := by
  rw [seq]

/-- `z n = r (n+1) + (-1)^(n+1) r n`, the numerator/denominator candidate. -/
private def z (r₀ r₁ : ℤ) (n : ℕ) : ℤ := seq r₀ r₁ (n + 1) + (-1) ^ (n + 1) * seq r₀ r₁ n

/-- `z` satisfies Israel's recurrence. -/
private lemma step_z (r₀ r₁ : ℤ) (m : ℕ) :
    step (m + 2) (z r₀ r₁ (m + 1) : ℚ) (z r₀ r₁ (m + 2) : ℚ) = (z r₀ r₁ (m + 3) : ℚ) := by
  have h4 := seq_succ_succ r₀ r₁ (m + 2)
  have h3 := seq_succ_succ r₀ r₁ (m + 1)
  simp only [step, z]
  rw [show m + 3 + 1 = (m + 2) + 2 by ring, h4, show m + 2 + 1 = (m + 1) + 2 by ring, h3]
  push_cast
  rcases neg_one_pow_eq_or ℚ m with h | h <;> simp only [pow_succ, h]
  · have hne : (m : ℚ) + 2 - 1 * (-1) * (-1) ≠ 0 := by
      have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      intro h'; linarith
    rw [div_eq_iff hne]; ring
  · have hne : (m : ℚ) + 2 - (-1) * (-1) * (-1) ≠ 0 := by
      have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      intro h'; linarith
    rw [div_eq_iff hne]; ring

/-- `israelPair` started from `z 1, z 2` runs through the values of `z`. -/
private lemma israelPair_z (r₀ r₁ : ℤ) (m : ℕ) :
    israelPair (z r₀ r₁ 1 : ℚ) (z r₀ r₁ 2 : ℚ) m =
      ((z r₀ r₁ (m + 1) : ℚ), (z r₀ r₁ (m + 2) : ℚ)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [israelPair, ih]
    simp only [Prod.mk.injEq, true_and]
    exact step_z r₀ r₁ m

/-- Monotonicity and nonnegativity of `seq` when `0 ≤ r₀ ≤ r₁`. -/
private lemma seq_mono (r₀ r₁ : ℤ) (h0 : 0 ≤ r₀) (h1 : r₀ ≤ r₁) (k : ℕ) :
    0 ≤ seq r₀ r₁ k ∧ seq r₀ r₁ k ≤ seq r₀ r₁ (k + 1) := by
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    obtain ⟨ha, hb⟩ := ih
    refine ⟨le_trans ha hb, ?_⟩
    rw [seq_succ_succ]
    have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    have hs : -seq r₀ r₁ k ≤ (-1) ^ (k + 1) * seq r₀ r₁ k := by
      rcases neg_one_pow_eq_or ℤ (k + 1) with h | h <;> rw [h] <;> linarith
    nlinarith

/-- Positivity of `z n` for `n ≥ 1`, given monotonicity and `r k ≥ 1` for `k ≥ 1`. -/
private lemma z_pos (r₀ r₁ : ℤ) (h0 : 0 ≤ r₀) (h1 : r₀ ≤ r₁) (h11 : 1 ≤ r₁) (n : ℕ)
    (hn : 1 ≤ n) : 0 < z r₀ r₁ n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hmono : Monotone (seq r₀ r₁) :=
    monotone_nat_of_le_succ (fun k => (seq_mono r₀ r₁ h0 h1 k).2)
  have hs1 : seq r₀ r₁ 1 = r₁ := by rw [seq]
  have hge : 1 ≤ seq r₀ r₁ (j + 1) := le_trans h11 (hs1 ▸ hmono (show 1 ≤ j + 1 by omega))
  have hj0 := (seq_mono r₀ r₁ h0 h1 j).1
  have hj1 := (seq_mono r₀ r₁ h0 h1 j).2
  have hjn : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  simp only [z]
  rw [seq_succ_succ]
  rcases neg_one_pow_eq_or ℤ j with h | h <;> simp only [pow_succ, h] <;> nlinarith

/-- The determinant `p(k+1) q(k) - p(k) q(k+1)` is `±1`. -/
private lemma det_eq (k : ℕ) :
    seq 1 1 (k + 1) * seq 0 1 k - seq 1 1 k * seq 0 1 (k + 1) = 1 ∨
      seq 1 1 (k + 1) * seq 0 1 k - seq 1 1 k * seq 0 1 (k + 1) = -1 := by
  induction k with
  | zero => right; decide
  | succ k ih =>
    rw [seq_succ_succ 1 1 k, seq_succ_succ 0 1 k]
    have e : (((k : ℤ) + 2) * seq 1 1 (k + 1) + (-1) ^ (k + 1) * seq 1 1 k) * seq 0 1 (k + 1) -
        seq 1 1 (k + 1) * (((k : ℤ) + 2) * seq 0 1 (k + 1) + (-1) ^ (k + 1) * seq 0 1 k) =
        -(-1) ^ (k + 1) * (seq 1 1 (k + 1) * seq 0 1 k - seq 1 1 k * seq 0 1 (k + 1)) := by ring
    rw [e]
    rcases neg_one_pow_eq_or ℤ (k + 1) with h | h <;> rw [h] <;> rcases ih with h' | h' <;>
      rw [h'] <;> norm_num

/-- The fold defining `cf`, over `1, …, k+1` with innermost value `t ≥ 1`, is the Möbius map
given by the convergents. -/
private lemma fold_eq (k : ℕ) : ∀ t : ℚ, 1 ≤ t →
    (List.range' 1 (k + 1)).foldr (fun (i : ℕ) (u : ℚ) => (i : ℚ) + (-1) ^ i / u) t =
      ((seq 1 1 (k + 1) : ℚ) * t + (-1) ^ (k + 1) * (seq 1 1 k : ℚ)) /
        ((seq 0 1 (k + 1) : ℚ) * t + (-1) ^ (k + 1) * (seq 0 1 k : ℚ)) := by
  induction k with
  | zero =>
    intro t ht
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
    simp [seq]
    field_simp
  | succ k ih =>
    intro t ht
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
    rw [List.range'_concat, List.foldr_append, show 1 + 1 * (k + 1) = k + 2 by ring]
    simp only [List.foldr_cons, List.foldr_nil]
    have ht' : 1 ≤ ((k + 2 : ℕ) : ℚ) + (-1) ^ (k + 2) / t := by
      have hinv : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; exact ht
      have hinv0 : 0 ≤ 1 / t := by positivity
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      push_cast
      rcases neg_one_pow_eq_or ℚ (k + 2) with h | h <;> rw [h] <;>
        [skip; rw [neg_div]] <;> linarith
    rw [ih _ ht']
    rw [seq_succ_succ 1 1 k, seq_succ_succ 0 1 k]
    have key : ∀ r₀ r₁ : ℤ,
        (seq r₀ r₁ (k + 1) : ℚ) * (((k + 2 : ℕ) : ℚ) + (-1) ^ (k + 2) / t) +
            (-1) ^ (k + 1) * (seq r₀ r₁ k : ℚ) =
          ((((k : ℤ) + 2) * seq r₀ r₁ (k + 1) + (-1) ^ (k + 1) * seq r₀ r₁ k : ℤ) * t +
            (-1) ^ (k + 1 + 1) * (seq r₀ r₁ (k + 1) : ℚ)) / t := by
      intro r₀ r₁
      rw [eq_div_iff ht0]
      push_cast
      field_simp
      ring
    rw [key 1 1, key 0 1, div_div_div_cancel_right₀ ht0]

/-- `cf n = z_p n / z_q n`. -/
private lemma cf_eq (n : ℕ) : cf n = (z 1 1 n : ℚ) / (z 0 1 n : ℚ) := by
  rw [cf, fold_eq n 1 le_rfl]
  simp only [z]
  push_cast
  ring

/-- Israel's conjecture holds: `b n`, `c n` are coprime integers and `a n = b n`. -/
theorem result : statement := by
  intro n hn
  have hb : b n = (z 1 1 n : ℚ) := by
    have h := israelPair_z 1 1 (n - 1)
    have e1 : ((z 1 1 1 : ℤ) : ℚ) = 2 := by norm_num [z, seq]
    have e2 : ((z 1 1 2 : ℤ) : ℚ) = 3 := by norm_num [z, seq]
    rw [e1, e2] at h
    rw [b, h, Nat.sub_add_cancel hn]
  have hc : c n = (z 0 1 n : ℚ) := by
    have h := israelPair_z 0 1 (n - 1)
    have e1 : ((z 0 1 1 : ℤ) : ℚ) = 3 := by norm_num [z, seq]
    have e2 : ((z 0 1 2 : ℤ) : ℚ) = 5 := by norm_num [z, seq]
    rw [e1, e2] at h
    rw [c, h, Nat.sub_add_cancel hn]
  have hcop : IsCoprime (z 1 1 n) (z 0 1 n) := by
    have hd := det_eq n
    set d := seq 1 1 (n + 1) * seq 0 1 n - seq 1 1 n * seq 0 1 (n + 1) with hd_def
    have hd2 : d * d = 1 := by rcases hd with h | h <;> rw [h] <;> norm_num
    refine ⟨d * seq 0 1 n, -(d * seq 1 1 n), ?_⟩
    simp only [z]
    linear_combination hd2
  have hxpos : 0 < z 1 1 n := z_pos 1 1 (by norm_num) le_rfl le_rfl n hn
  have hypos : 0 < z 0 1 n := z_pos 0 1 le_rfl (by norm_num) le_rfl n hn
  refine ⟨z 1 1 n, z 0 1 n, hb, hc, Int.isCoprime_iff_gcd_eq_one.mp hcop, ?_⟩
  rw [hb, a, cf_eq, Rat.num_div_eq_of_coprime hypos (Int.isCoprime_iff_gcd_eq_one.mp hcop)]
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hxpos)]

end Math0.Frontier.A262957

#math0_settles Math0.Frontier.A262957.result Math0.Statements.A262957.statement

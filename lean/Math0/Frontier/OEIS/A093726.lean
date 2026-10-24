/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A093726
import Math0.Audit

/-!
# Imaginary parts of the convergents of `[1+i; 1+i, 1+i, …]`

We prove Zhuorui He's conjecture: for every `n ≥ 1`,
`a(n)/A093727(n) = A317974(n+1)/A138573(n)`, i.e. the imaginary part of the `n`-th convergent
`c_n` of `(1+i) + 1/((1+i) + ⋯)` equals `A317974(n+1)/A138573(n)`.

**Continuants.** Let `U 0 = 0`, `U 1 = 1`, `U (k+2) = (1+i) U (k+1) + U k` in `ℤ[i]` (stored as
pairs `(re, im)`). Then `c_n = U(n+1)/U(n)`, so with `S n = |U n|²`,
`P n + Q n · i = U (n+1) · conj (U n)` we get `c_n = (P n / S n, Q n / S n)`. This is proved by
induction from `c_{n+1} = (1+i) + 1/c_n`, using the integer identities
`P (n+1) = S (n+1) + P n`, `Q (n+1) = S (n+1) - Q n` and `P n² + Q n² = S n · S (n+1)`.

**Recurrences.** Expanding `U (n+4)`, `U (n+5)` through `U n`, `U (n+1)`, the polynomial
identities `S (n+4) = 2(S (n+3) + S (n+2) + S (n+1)) - S n` (same for `Q`) are checked by `ring`.
Comparing four initial values gives `S n = A138573 n` and `Q n = A317974 (n+1)`.
`A138573` is nondecreasing and `A138573 1 = 1`, so `S n ≠ 0` for `n ≥ 1`.

**Numerators.** Finally `a(n)/A093727(n) = num(y)·(L/den y)/L = y` with
`y = Im c_n` and `L = lcm(den (Re c_n), den y)`, since `den y ∣ L`.
-/

namespace Math0.Frontier.A093726
open Math0.Statements.A093726

/-- One step of the recurrence `U (k+2) = (1+i) U (k+1) + U k` on Gaussian integers written as
pairs `(re, im)`: `step b a = (1+i) b + a`. -/
private def step (b a : ℤ × ℤ) : ℤ × ℤ := (b.1 - b.2 + a.1, b.1 + b.2 + a.2)

/-- The continuants `U 0 = 0`, `U 1 = 1`, `U (k+2) = (1+i) U (k+1) + U k`, as pairs. -/
private def U : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | k + 2 => step (U (k + 1)) (U k)

/-- `S n = |U n|²`. -/
private def S (n : ℕ) : ℤ := (U n).1 ^ 2 + (U n).2 ^ 2

/-- `P n = Re (U (n+1) · conj (U n))`. -/
private def P (n : ℕ) : ℤ := (U (n + 1)).1 * (U n).1 + (U (n + 1)).2 * (U n).2

/-- `Q n = Im (U (n+1) · conj (U n))`. -/
private def Q (n : ℕ) : ℤ := (U (n + 1)).2 * (U n).1 - (U (n + 1)).1 * (U n).2

/-- `S` satisfies the order-4 recurrence of `A138573`. -/
private lemma S_rec (n : ℕ) :
    S (n + 4) = 2 * S (n + 3) + 2 * S (n + 2) + 2 * S (n + 1) - S n := by
  have e4 : U (n + 4) = step (U (n + 3)) (U (n + 2)) := rfl
  have e3 : U (n + 3) = step (U (n + 2)) (U (n + 1)) := rfl
  have e2 : U (n + 2) = step (U (n + 1)) (U n) := rfl
  simp only [S, e4, e3, e2, step]
  ring

/-- `Q` satisfies the same order-4 recurrence (that of `A317974`). -/
private lemma Q_rec (n : ℕ) :
    Q (n + 4) = 2 * Q (n + 3) + 2 * Q (n + 2) + 2 * Q (n + 1) - Q n := by
  have e5 : U (n + 5) = step (U (n + 4)) (U (n + 3)) := rfl
  have e4 : U (n + 4) = step (U (n + 3)) (U (n + 2)) := rfl
  have e3 : U (n + 3) = step (U (n + 2)) (U (n + 1)) := rfl
  have e2 : U (n + 2) = step (U (n + 1)) (U n) := rfl
  simp only [Q, e5, e4, e3, e2, step]
  ring

/-- `S n = A138573 n` and `Q n = A317974 (n+1)`, by induction on four consecutive values. -/
private lemma S_eq_Q_eq (n : ℕ) :
    (S n = A138573 n ∧ S (n + 1) = A138573 (n + 1) ∧ S (n + 2) = A138573 (n + 2) ∧
      S (n + 3) = A138573 (n + 3)) ∧
    (Q n = A317974 (n + 1) ∧ Q (n + 1) = A317974 (n + 2) ∧ Q (n + 2) = A317974 (n + 3) ∧
      Q (n + 3) = A317974 (n + 4)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨⟨h0, h1, h2, h3⟩, ⟨g0, g1, g2, g3⟩⟩ := ih
    refine ⟨⟨h1, h2, h3, ?_⟩, ⟨g1, g2, g3, ?_⟩⟩
    · rw [S_rec, h0, h1, h2, h3]
      show _ = 2 * A138573 (n + 3) + 2 * A138573 (n + 2) + 2 * A138573 (n + 1) - A138573 n
      ring
    · rw [Q_rec, g0, g1, g2, g3]
      show _ = 2 * (A317974 (n + 4) + A317974 (n + 3) + A317974 (n + 2)) - A317974 (n + 1)
      ring

/-- `A138573` is nonnegative and nondecreasing (four consecutive values at a time). -/
private lemma A138573_mono (n : ℕ) :
    0 ≤ A138573 n ∧ A138573 n ≤ A138573 (n + 1) ∧ A138573 (n + 1) ≤ A138573 (n + 2) ∧
      A138573 (n + 2) ≤ A138573 (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨by linarith, h2, h3, ?_⟩
    show A138573 (n + 3) ≤
      2 * A138573 (n + 3) + 2 * A138573 (n + 2) + 2 * A138573 (n + 1) - A138573 n
    linarith

/-- `A138573 (n+1) ≥ 1`. -/
private lemma A138573_pos (n : ℕ) : 1 ≤ A138573 (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => exact ih.trans (A138573_mono (n + 1)).2.1

/-- `|U (n+1)|² ≠ 0`. -/
private lemma S_pos (n : ℕ) : (S (n + 1) : ℚ) ≠ 0 := by
  rw [(S_eq_Q_eq (n + 1)).1.1]
  have := A138573_pos n
  exact_mod_cast (by omega : A138573 (n + 1) ≠ 0)

/-- One step of the continued fraction: if `c = (p/s, q/s)` with `p² + q² = s s'` then
`(1+i) + 1/c = ((s'+p)/s', (s'-q)/s')`. -/
private lemma alg (p q s s' : ℚ) (hs : s ≠ 0) (hs' : s' ≠ 0) (hL : p ^ 2 + q ^ 2 = s * s') :
    gadd (1, 1) (ginv (p / s, q / s)) = ((s' + p) / s', (s' - q) / s') := by
  have hd : p / s * (p / s) + q / s * (q / s) = s' / s := by
    field_simp
    linear_combination hL
  simp only [gadd, ginv, hd, Prod.mk.injEq]
  constructor
  · field_simp
  · field_simp
    ring

/-- The convergents are `conv n = (P n / S n, Q n / S n)` for `n ≥ 1`. -/
private lemma conv_eq (m : ℕ) :
    conv (m + 1) = ((P (m + 1) : ℚ) / S (m + 1), (Q (m + 1) : ℚ) / S (m + 1)) := by
  induction m with
  | zero =>
    rw [show P 1 = 1 by decide, show Q 1 = 1 by decide, show S 1 = 1 by decide]
    simp [conv, cfValue]
  | succ m ih =>
    have hc : conv (m + 2) = gadd (1, 1) (ginv (conv (m + 1))) := rfl
    have hP : P (m + 2) = S (m + 2) + P (m + 1) := by
      have e : U (m + 3) = step (U (m + 2)) (U (m + 1)) := rfl
      simp only [P, S, e, step]
      ring
    have hQ : Q (m + 2) = S (m + 2) - Q (m + 1) := by
      have e : U (m + 3) = step (U (m + 2)) (U (m + 1)) := rfl
      simp only [Q, S, e, step]
      ring
    have hL : (P (m + 1) : ℚ) ^ 2 + (Q (m + 1) : ℚ) ^ 2 = S (m + 1) * S (m + 2) := by
      have : P (m + 1) ^ 2 + Q (m + 1) ^ 2 = S (m + 1) * S (m + 2) := by
        simp only [P, Q, S]
        ring
      exact_mod_cast this
    rw [hc, ih, alg _ _ _ _ (S_pos m) (S_pos (m + 1)) hL, hP, hQ]
    push_cast
    rfl

/-- Zhuorui He's conjecture on A093726: `a(n)/A093727(n) = A317974(n+1)/A138573(n)` for `n ≥ 1`;
both sides are the imaginary part of the `n`-th convergent. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hl : (a (m + 1) : ℚ) / (A093727 (m + 1) : ℚ) = (conv (m + 1)).2 := by
    simp only [a, A093727, gnumIm, gden]
    set z := conv (m + 1)
    have hd : z.2.den ∣ Nat.lcm z.1.den z.2.den := Nat.dvd_lcm_right _ _
    have hL : (Nat.lcm z.1.den z.2.den : ℚ) ≠ 0 := by
      exact_mod_cast Nat.lcm_ne_zero z.1.den_nz z.2.den_nz
    have h2 : (z.2.den : ℚ) ≠ 0 := by exact_mod_cast z.2.den_nz
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hd h2]
    rw [show (z.2.num : ℚ) * ((Nat.lcm z.1.den z.2.den : ℚ) / z.2.den) /
        (Nat.lcm z.1.den z.2.den : ℚ) = z.2.num / z.2.den by field_simp, Rat.num_div_den]
  rw [hl, conv_eq, (S_eq_Q_eq (m + 1)).1.1, (S_eq_Q_eq (m + 1)).2.1]

end Math0.Frontier.A093726

#math0_settles Math0.Frontier.A093726.result Math0.Statements.A093726.statement

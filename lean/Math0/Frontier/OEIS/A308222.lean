/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A308222
import Math0.Audit

/-!
# Perimeters of primitive Heronian isosceles triangles: A308222(n) = 2 · A096033(n + 2)

We prove Kagey's conjecture. Write a primitive Heronian isosceles triangle with perimeter `2m`
as legs `s, s` and base `2(m - s)` (the statement file's `LegOK m s`: `m/2 < s < m`, `s` odd,
`gcd(s, m) = 1`, `m (2s - m)` a square). We show that for `m ≥ 3` such an `s` exists iff `m` is
an odd square or twice a square, i.e. iff `m` lies in A096033 (`IsLegHypDiff`):

* If `m` is odd, then `gcd(m, 2s - m) = gcd(m, 2s) = 1`, so the square `m (2s - m)` forces `m` to
  be a square. If `m = 2m'` is even, then `2s - m = 2f` with `s = m' + f`, `gcd(m', f) = 1`, and
  `m' f` is a square, so `m'` is a square.
* Conversely, for `m = (2u+3)²` take `s = 4(u+1)² + 1` (then `2s - m = (2u+1)²`), and for
  `m = 2(v+2)²` take `s = (v+2)² + (v+1)²` (then `2s - m = 2(v+1)²`); coprimality comes from
  explicit Bezout identities.

Odd numbers are never perimeters, and the differences `1, 2` (the only ones below `3`) give no
triangle. Hence `count IsPerimeter (2n) + 2 = count IsLegHypDiff n` for `n ≥ 3`, and the
`(k+2)`-th difference `d` satisfies `nth IsPerimeter k = 2d` via `Nat.nth_count`.
-/

namespace Math0.Frontier.A308222
open Math0.Statements.A308222

/-- If coprime `a, b` have a square product, then `a` is a square. -/
private theorem sq_of_coprime_mul {a b c : ℕ} (hab : Nat.Coprime a b) (h : a * b = c * c) :
    ∃ k, k * k = a := by
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (a := a) (b := b) (c := c) (k := 2)
    (Nat.isUnit_iff.2 hab) (by rw [h, sq])
  exact ⟨d, by rw [hd, sq]⟩

/-- A valid leg for half-perimeter `m` forces `m` to be a leg-hypotenuse difference. -/
private theorem isLegHypDiff_of_legOK {m s : ℕ} (hl : LegOK m s) : IsLegHypDiff m := by
  obtain ⟨h1, h2, hodd, hg, h, hh⟩ := hl
  rw [isLegHypDiff_iff]
  obtain ⟨e, he⟩ : ∃ e, 2 * s = m + e := ⟨2 * s - m, by omega⟩
  rw [show 2 * s - m = e by omega] at hh
  rcases Nat.even_or_odd m with ⟨m', rfl⟩ | hmo
  · right
    obtain ⟨f, rfl⟩ : ∃ f, e = 2 * f := ⟨e / 2, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', s = f' + m' := ⟨s - m', by omega⟩
    have hf : f' = f := by omega
    subst hf
    have hcs : Nat.Coprime m' (f' + m') :=
      Nat.Coprime.coprime_dvd_left (show m' ∣ m' + m' from ⟨2, by ring⟩) (Nat.Coprime.symm hg)
    have hcop : Nat.Coprime m' f' := Nat.coprime_add_self_right.1 hcs
    have hev : Even (h * h) := ⟨2 * (m' * f'), by rw [hh]; ring⟩
    have hh2 : Even h := by
      rcases Nat.even_mul.1 hev with h' | h' <;> exact h'
    obtain ⟨r, rfl⟩ := hh2
    have hr : m' * f' = r * r := by
      have e1 : (r + r) * (r + r) = 4 * (r * r) := by ring
      have e2 : (m' + m') * (2 * f') = 4 * (m' * f') := by ring
      omega
    obtain ⟨k, hk⟩ := sq_of_coprime_mul hcop hr
    refine ⟨by omega, by omega, k, by omega⟩
  · left
    have hc2 : Nat.Coprime m (2 * s) :=
      Nat.Coprime.mul_right (Nat.coprime_two_right.2 hmo) (Nat.Coprime.symm hg)
    rw [he, add_comm] at hc2
    have hcop : Nat.Coprime m e := Nat.coprime_add_self_right.1 hc2
    obtain ⟨k, hk⟩ := sq_of_coprime_mul hcop hh.symm
    exact ⟨Nat.odd_iff.1 hmo, k, hk⟩

/-- Conversely, every leg-hypotenuse difference `m ≥ 3` has a valid leg. -/
private theorem legOK_of_isLegHypDiff {m : ℕ} (hm : 3 ≤ m) (hL : IsLegHypDiff m) :
    ∃ s, LegOK m s := by
  rw [isLegHypDiff_iff] at hL
  rcases hL with ⟨hmo, k, rfl⟩ | ⟨hme, -, j, hj⟩
  · obtain ⟨u, rfl⟩ : ∃ u, k = 2 * u + 3 := by
      rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exfalso
        have : (r + r) * (r + r) = 2 * (2 * r * r) := by ring
        omega
      · rcases r with _ | r
        · simp at hm
        · exact ⟨r, by ring⟩
    refine ⟨4 * (u + 1) * (u + 1) + 1, by nlinarith, by nlinarith, ?_, ?_, ?_⟩
    · have : 4 * (u + 1) * (u + 1) + 1 = 2 * (2 * (u + 1) * (u + 1)) + 1 := by ring
      omega
    · apply Nat.isCoprime_iff_coprime.1
      exact ⟨(u + 2 : ℤ), -(u + 1 : ℤ), by push_cast; ring⟩
    · refine ⟨(2 * u + 3) * (2 * u + 1), ?_⟩
      rw [show 2 * (4 * (u + 1) * (u + 1) + 1) - (2 * u + 3) * (2 * u + 3) =
        (2 * u + 1) * (2 * u + 1) from Nat.sub_eq_of_eq_add (by ring)]
      ring
  · obtain ⟨v, rfl⟩ : ∃ v, j = v + 2 := by
      rcases j with _ | _ | v
      · omega
      · omega
      · exact ⟨v, rfl⟩
    have hm2 : m = 2 * ((v + 2) * (v + 2)) := by omega
    subst hm2
    refine ⟨(v + 2) * (v + 2) + (v + 1) * (v + 1), by nlinarith, by nlinarith, ?_, ?_, ?_⟩
    · have : (v + 2) * (v + 2) + (v + 1) * (v + 1) = 2 * (v * v + 3 * v + 2) + 1 := by ring
      omega
    · apply Nat.isCoprime_iff_coprime.1
      exact ⟨(2 * v + 5 : ℤ), -(2 * v + 3 : ℤ), by push_cast; ring⟩
    · refine ⟨2 * (v + 1) * (v + 2), ?_⟩
      rw [show 2 * ((v + 2) * (v + 2) + (v + 1) * (v + 1)) - 2 * ((v + 2) * (v + 2)) =
        2 * ((v + 1) * (v + 1)) from Nat.sub_eq_of_eq_add (by ring)]
      ring

/-- For `n ≥ 3`, `2n` is a perimeter iff `n` is a leg-hypotenuse difference. -/
private theorem isPerimeter_two_mul {n : ℕ} (hn : 3 ≤ n) :
    IsPerimeter (2 * n) ↔ IsLegHypDiff n := by
  rw [isPerimeter_iff_legOK, show 2 * n / 2 = n by omega]
  constructor
  · rintro ⟨-, s, hs⟩
    exact isLegHypDiff_of_legOK hs
  · intro h
    exact ⟨by omega, legOK_of_isLegHypDiff hn h⟩

/-- Odd numbers are never perimeters. -/
private theorem not_isPerimeter_odd (n : ℕ) : ¬ IsPerimeter (2 * n + 1) := by
  rw [isPerimeter_iff_legOK]
  rintro ⟨h, -⟩
  omega

/-- Counting relation: below `2n` there are two fewer perimeters than there are differences
below `n` (the differences `1, 2` have no triangle). -/
private theorem count_rel (n : ℕ) (hn : 3 ≤ n) :
    Nat.count IsPerimeter (2 * n) + 2 = Nat.count IsLegHypDiff n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [Nat.count_succ]
    rw [if_neg (not_isPerimeter_odd n), ← ih]
    by_cases h : IsLegHypDiff n
    · rw [if_pos h, if_pos ((isPerimeter_two_mul hn).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((isPerimeter_two_mul hn).1 h'))]

/-- There are infinitely many leg-hypotenuse differences (all `2 j²`). -/
private theorem infinite_L : (Set.ofPred IsLegHypDiff).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ⟨2 * ((N + 1) * (N + 1)), ?_, ?_⟩
  · show IsLegHypDiff _
    rw [isLegHypDiff_iff]
    right
    exact ⟨by omega, by positivity, N + 1, by omega⟩
  · nlinarith

/-- Kagey's conjecture: `a(n) = 2 · A096033(n + 2)`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold a A096033
  rw [show k + 1 + 2 - 1 = k + 2 by omega, show k + 1 - 1 = k by omega]
  have hd : IsLegHypDiff (Nat.nth IsLegHypDiff (k + 2)) := Nat.nth_mem_of_infinite infinite_L _
  have hc : Nat.count IsLegHypDiff (Nat.nth IsLegHypDiff (k + 2)) = k + 2 :=
    Nat.count_nth_of_infinite infinite_L _
  generalize Nat.nth IsLegHypDiff (k + 2) = d at hd hc
  have h3 : 3 ≤ d := by
    by_contra h
    have : Nat.count IsLegHypDiff d ≤ Nat.count IsLegHypDiff 2 :=
      Nat.count_monotone _ (by omega)
    have h2 : Nat.count IsLegHypDiff 2 = 1 := by decide
    omega
  have hcr := count_rel d h3
  have hP : IsPerimeter (2 * d) := (isPerimeter_two_mul h3).2 hd
  rw [← Nat.nth_count hP]
  congr 1
  omega

end Math0.Frontier.A308222

#math0_settles Math0.Frontier.A308222.result Math0.Statements.A308222.statement

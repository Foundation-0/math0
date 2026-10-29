/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A106505
import Math0.Audit

/-!
# A106505: the common sides are periodic modulo 8, so `a(n + 5) = a(n) + 8`

We prove Stephan's conjecture `a(n + 5) = a(n) + 8` for `n > 2` by determining the set of
common sides: for `c ≥ 9`, `IsSide c` holds iff `c` is odd or a multiple of `8`.

* *Necessity* (`isSide_mod`). From `y² = x (x + c)` with `c ≡ 2, 4, 6 (mod 8)`, a check of
  residues mod `8` forces `x` and `y` even (if `x` is odd then `y` is odd, so `x² ≡ y² ≡ 1` and
  `x c ≡ 0 (mod 8)`, i.e. `8 ∣ c`); together with `2 ∣ c` this contradicts primitivity.
* *Sufficiency.* `c = 2m + 1` (`m ≥ 2`) is realised by `(x, y) = (m², m (m + 1))`, and
  `c = 8 (j + 1)` (`j ≥ 1`) by `(x, y) = (n², n (n + 2))` with `n = 2j + 1`.

Hence `IsSide (c + 8) ↔ IsSide c` for `c ≥ 9`, so each window of `8` consecutive integers from
`9` on contains exactly `5` common sides: `count IsSide (N + 8) = count IsSide N + 5` for
`N ≥ 9`. Since `a 3 = 9`, for `n ≥ 3` the common side `c = a n ≥ 9` has `count IsSide c = n - 1`,
so `c + 8` is a common side with `count = n + 4`, i.e. `a (n + 5) = c + 8`.
-/

namespace Math0.Frontier.A106505
open Math0.Statements.A106505

/-- Residue check mod 8: if `y² ≡ x (x + c)` and `c ≡ 2, 4, 6 (mod 8)`, then `x, y` are even. -/
private theorem residue_check : ∀ a b e : Fin 8,
    (b.val * b.val) % 8 = (a.val * ((a.val + e.val) % 8)) % 8 → e.val % 2 = 0 → e.val ≠ 0 →
      a.val % 2 = 0 ∧ b.val % 2 = 0 := by
  decide

/-- A common side is odd or a multiple of `8`. -/
private theorem isSide_mod {c : ℕ} (h : IsSide c) : c % 2 = 1 ∨ c % 8 = 0 := by
  obtain ⟨x, y, h, hg⟩ := h
  obtain ⟨-, -, -, hyy⟩ := (isDoubleAngleTriangle_iff x y c).1 h
  by_contra hc
  have h2 : (c % 8) % 2 = 0 := by omega
  have h8 : c % 8 ≠ 0 := by omega
  have hm : ((y % 8) * (y % 8)) % 8 = ((x % 8) * ((x % 8 + c % 8) % 8)) % 8 := by
    rw [← Nat.add_mod, ← Nat.mul_mod, ← Nat.mul_mod, hyy]
  obtain ⟨hx, hy⟩ := residue_check ⟨x % 8, Nat.mod_lt _ (by norm_num)⟩
    ⟨y % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨c % 8, Nat.mod_lt _ (by norm_num)⟩ hm h2 h8
  simp only at hx hy
  have h2x : 2 ∣ x := by omega
  have h2y : 2 ∣ y := by omega
  have h2c : 2 ∣ c := by omega
  have : 2 ∣ Nat.gcd (Nat.gcd x y) c := Nat.dvd_gcd (Nat.dvd_gcd h2x h2y) h2c
  rw [hg] at this
  omega

/-- Every odd `c = 2m + 1 ≥ 5` is a common side: `(x, y) = (m², m(m+1))`. -/
private theorem isSide_odd (m : ℕ) (hm : 2 ≤ m) : IsSide (2 * m + 1) := by
  refine ⟨m * m, m * (m + 1), (isDoubleAngleTriangle_iff _ _ _).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · ring
  · have h1 : Nat.Coprime m (2 * m + 1) := by
      rw [show 2 * m + 1 = 1 + 2 * m by ring, Nat.coprime_add_mul_right_right]
      exact Nat.coprime_one_right m
    have hcop : Nat.Coprime (m * m) (2 * m + 1) := Nat.Coprime.mul_left h1 h1
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop

/-- Every `c = 8(j + 1) ≥ 16` is a common side: with `n = 2j + 1`, `(x, y) = (n², n(n+2))`. -/
private theorem isSide_eight (j : ℕ) (hj : 1 ≤ j) : IsSide (8 * j + 8) := by
  refine ⟨(2 * j + 1) * (2 * j + 1), (2 * j + 1) * (2 * j + 3),
    (isDoubleAngleTriangle_iff _ _ _).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · ring
  · have h1 : Nat.Coprime (2 * j + 1) (8 * j + 8) := by
      have e : 8 * j + 8 = 4 + 4 * (2 * j + 1) := by ring
      rw [e, Nat.coprime_add_mul_right_right]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    have hcop : Nat.Coprime ((2 * j + 1) * (2 * j + 1)) (8 * j + 8) := Nat.Coprime.mul_left h1 h1
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop

/-- Above `8`, the common sides are exactly the odd numbers and the multiples of `8`. -/
private theorem isSide_iff_large {c : ℕ} (hc : 9 ≤ c) : IsSide c ↔ c % 2 = 1 ∨ c % 8 = 0 := by
  constructor
  · exact isSide_mod
  · rintro (h | h)
    · obtain ⟨m, rfl⟩ : ∃ m, c = 2 * m + 1 := ⟨c / 2, by omega⟩
      exact isSide_odd m (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, c = 8 * j + 8 := ⟨c / 8 - 1, by omega⟩
      exact isSide_eight j (by omega)

/-- Periodicity of `IsSide` above `8`. -/
private theorem isSide_add_eight {c : ℕ} (hc : 9 ≤ c) : IsSide (c + 8) ↔ IsSide c := by
  rw [isSide_iff_large hc, isSide_iff_large (by omega)]
  omega

/-- The set of common sides is infinite. -/
private theorem isSide_infinite : (Set.ofPred IsSide).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  exact ⟨2 * (a + 2) + 1, isSide_odd (a + 2) (by omega), by omega⟩

/-- Counting periodicity: each block of `8` consecutive integers from `9` on contains `5`
common sides. -/
private theorem count_add_eight (N : ℕ) (hN : 9 ≤ N) :
    Nat.count IsSide (N + 8) = Nat.count IsSide N + 5 := by
  induction N, hN using Nat.le_induction with
  | base => decide +kernel
  | succ N hN ih =>
    rw [show N + 1 + 8 = N + 8 + 1 by ring, Nat.count_succ IsSide (N + 8),
      Nat.count_succ IsSide N, ih]
    by_cases h : IsSide N
    · rw [if_pos h, if_pos ((isSide_add_eight hN).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((isSide_add_eight hN).1 h'))]

/-- The third common side is `9`. -/
private theorem nth_two : Nat.nth IsSide 2 = 9 := by
  have h9 : IsSide 9 := by decide +kernel
  have hc : Nat.count IsSide 9 = 2 := by decide +kernel
  have := Nat.nth_count h9
  rwa [hc] at this

/-- Stephan's conjecture for A106505: `a(n + 5) = a(n) + 8` for all `n > 2`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [a, show m + 1 + 5 - 1 = m + 5 by omega, Nat.add_sub_cancel]
  set c := Nat.nth IsSide m with hcdef
  have hpc : IsSide c := Nat.nth_mem_of_infinite isSide_infinite m
  have hcount : Nat.count IsSide c = m := Nat.count_nth_of_infinite isSide_infinite m
  have hc9 : 9 ≤ c := by
    rw [← nth_two, hcdef]
    exact (Nat.nth_le_nth isSide_infinite).2 (by omega)
  have hp8 : IsSide (c + 8) := (isSide_add_eight hc9).2 hpc
  have := Nat.nth_count hp8
  rwa [count_add_eight c hc9, hcount] at this

end Math0.Frontier.A106505

#math0_settles Math0.Frontier.A106505.result Math0.Statements.A106505.statement

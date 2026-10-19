/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A062887
import Math0.Audit

/-!
# Odd descending-by-2 multiples exist exactly when `125 ∤ 2n+1` (A062887)

We prove Irvine's conjecture: `a(n) = 0` if and only if `125 ∣ 2n+1`.

* If `125 ∣ 2n+1` and `N` has the digit property, then `N` is `ofDigits 10 (gen x L)` with
  `x ∈ {1,3,5,7,9}`. For `L ≤ 2` we have `0 < N < 100`, and for `L ≥ 3` the residue of `N`
  modulo `1000` is the three-digit tail `531`, `753`, `975`, `197` or `319`, none divisible by
  `125`. So no multiple of `2n+1` has the property, and `a(n) = 0`.
* If `125 ∤ m = 2n+1`, write `m ∣ 25 m'` with `m'` coprime to `10`. Let
  `S_q = ofDigits 10 (gen 5 (5q))`, the block `31975` repeated `q` times; it has the property
  for `q ≥ 1`. We have `S_{q+1} = 31975 + 10^5 S_q`, hence `25 ∣ S_q` and
  `99999 S_q + 31975 = 31975 · 100000^q`. With `q = φ(99999 m')` Euler's theorem gives
  `100000^q ≡ 1 (mod 99999 m')`, so `99999 m' ∣ 99999 S_q`, i.e. `m' ∣ S_q`, and therefore
  `m ∣ 25 m' ∣ S_q`. So a multiple of `m` with the property exists and `a(n) ≠ 0`.
-/

namespace Math0.Frontier.A062887
open Math0.Statements.A062887

/-- `a n = 0` exactly when no number with the digit property is a multiple of `2n+1`. -/
private theorem a_eq_zero_iff (n : ℕ) : a n = 0 ↔ ¬∃ N, IsDesc2 N ∧ 2 * n + 1 ∣ N := by
  unfold a
  split_ifs with h
  · have hpos := (Nat.find_spec h).1.1
    constructor
    · intro h0; omega
    · intro hn; exact absurd h hn
  · simp [h]

/-- No number with the digit property is divisible by `125`. -/
private theorem not_dvd_125 {N : ℕ} (hN : IsDesc2 N) : ¬125 ∣ N := by
  obtain ⟨x, L, hx, hxo, hL, hd⟩ := exists_gen_of_isDesc2 hN
  have hNe : N = Nat.ofDigits 10 (gen x L) := by rw [← hd, Nat.ofDigits_digits]
  have hx' : x ∈ [1, 3, 5, 7, 9] := by
    have : ∀ y < 10, Odd y → y ∈ [1, 3, 5, 7, 9] := by decide
    exact this x hx hxo
  intro h125
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases L with _ | _ | _ | L
  · omega
  · rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
      simp [gen, Nat.ofDigits_cons] at hNe <;> omega
  · rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
      simp [gen, Nat.ofDigits_cons] at hNe <;> omega
  · rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
      simp [gen, Nat.ofDigits_cons] at hNe <;> omega

/-- The block `31975` repeated `q` times. -/
private def S (q : ℕ) : ℕ := Nat.ofDigits 10 (gen 5 (5 * q))

/-- Appending one more block: `S (q+1) = 31975 + 10^5 S q`. -/
private theorem S_succ (q : ℕ) : S (q + 1) = 31975 + 100000 * S q := by
  unfold S
  rw [show 5 * (q + 1) = 5 * q + 1 + 1 + 1 + 1 + 1 by ring]
  simp [gen, Nat.ofDigits_cons]
  ring

/-- `25 ∣ S q`. -/
private theorem dvd_S_25 (q : ℕ) : 25 ∣ S q := by
  induction q with
  | zero => simp [S, gen]
  | succ q ih =>
    rw [S_succ]
    exact dvd_add (by norm_num) (dvd_mul_of_dvd_right ih _)

/-- The geometric-sum identity `99999 S q + 31975 = 31975 · 100000^q`. -/
private theorem S_geom (q : ℕ) : 99999 * S q + 31975 = 31975 * 100000 ^ q := by
  induction q with
  | zero => simp [S, gen]
  | succ q ih =>
    rw [S_succ, pow_succ]
    nlinarith [ih]

/-- If `m'` is coprime to `10`, then `m'` divides some `S q` with `q ≥ 1`. -/
private theorem exists_dvd_S {m' : ℕ} (h2 : Nat.Coprime m' 2) (h5 : Nat.Coprime m' 5) :
    ∃ q, 1 ≤ q ∧ 25 * m' ∣ S q := by
  set n := 99999 * m' with hn
  have hcop : Nat.Coprime 10 n := by
    rw [hn]
    refine Nat.Coprime.mul_right (by norm_num) ?_
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    exact Nat.Coprime.mul_left (Nat.coprime_comm.mp h2) (Nat.coprime_comm.mp h5)
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · subst h; simp at h2
    · exact h
  have hnpos : 0 < n := by rw [hn]; positivity
  refine ⟨Nat.totient n, Nat.totient_pos.mpr hnpos, ?_⟩
  have h1 : 10 ^ Nat.totient n ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop
  have h2' : 100000 ^ Nat.totient n ≡ 1 [MOD n] := by
    have := h1.pow 5
    rw [one_pow, ← pow_mul, mul_comm, pow_mul] at this
    simpa using this
  have h3 : 99999 * S (Nat.totient n) + 31975 ≡ 0 + 31975 [MOD n] := by
    rw [S_geom]
    simpa using h2'.mul_left 31975
  have h4 : 99999 * S (Nat.totient n) ≡ 0 [MOD n] := Nat.ModEq.add_right_cancel' _ h3
  have h5' : n ∣ 99999 * S (Nat.totient n) := (Nat.modEq_zero_iff_dvd).mp h4
  rw [hn] at h5'
  have hm : m' ∣ S (Nat.totient n) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h5'
  have hc25 : Nat.Coprime 25 m' := by
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_comm.mp h5)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc25 (dvd_S_25 _) hm

/-- An odd `m` with `125 ∤ m` divides `25 m'` for some `m'` coprime to `2` and `5`. -/
private theorem exists_cofactor {m : ℕ} (hodd : ¬2 ∣ m) (h125 : ¬125 ∣ m) :
    ∃ m', Nat.Coprime m' 2 ∧ Nat.Coprime m' 5 ∧ m ∣ 25 * m' := by
  have cop : ∀ k, ¬2 ∣ k → ¬5 ∣ k → Nat.Coprime k 2 ∧ Nat.Coprime k 5 := fun k h2 h5 =>
    ⟨Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2),
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5)⟩
  by_cases h25 : 25 ∣ m
  · obtain ⟨k, rfl⟩ := h25
    have hk2 : ¬2 ∣ k := fun h => hodd (dvd_mul_of_dvd_right h _)
    have hk5 : ¬5 ∣ k := by
      rintro ⟨j, rfl⟩
      exact h125 ⟨j, by ring⟩
    exact ⟨k, (cop k hk2 hk5).1, (cop k hk2 hk5).2, dvd_refl _⟩
  · by_cases h5 : 5 ∣ m
    · obtain ⟨k, rfl⟩ := h5
      have hk2 : ¬2 ∣ k := fun h => hodd (dvd_mul_of_dvd_right h _)
      have hk5 : ¬5 ∣ k := by
        rintro ⟨j, rfl⟩
        exact h25 ⟨j, by ring⟩
      exact ⟨k, (cop k hk2 hk5).1, (cop k hk2 hk5).2, ⟨5, by ring⟩⟩
    · exact ⟨m, (cop m hodd h5).1, (cop m hodd h5).2, dvd_mul_left _ _⟩

/-- Irvine's conjecture for A062887: `a(n) = 0` exactly when `125 ∣ 2n+1`. -/
theorem result : statement := by
  intro n
  rw [a_eq_zero_iff]
  constructor
  · intro hne
    by_contra h125
    obtain ⟨m', h2, h5, hdvd⟩ := exists_cofactor (m := 2 * n + 1) (by omega) h125
    obtain ⟨q, hq, hS⟩ := exists_dvd_S h2 h5
    exact hne ⟨S q, isDesc2_ofDigits_gen 5 (5 * q) (by norm_num) (by decide) (by omega),
      dvd_trans hdvd hS⟩
  · rintro h125 ⟨N, hN, hdvd⟩
    exact not_dvd_125 hN (dvd_trans h125 hdvd)

end Math0.Frontier.A062887

#math0_settles Math0.Frontier.A062887.result Math0.Statements.A062887.statement

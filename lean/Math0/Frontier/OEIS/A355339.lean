/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A355339
import Math0.Audit

/-!
# A355339: the central even run of the knight-move triangle has length 1 iff `n = 2^m - 2`

We prove Rémy Sigrist's conjecture: `a(n) = 1` iff `n > 0` and `n = 2^m - 2`.

**Reduction.** For `n ≥ 1` the central entry `T(n,0)` is even, and the row is symmetric
(`T(n,-k) = T(n,k)`, by induction from the recurrence). So the central even block has length
`2·right - 1` with `right ≥ 1`, and `a(n) = 1` iff `T(n,1)` is odd.

**Parity via polynomials.** Over `𝔽₂` let `F_n` be the row polynomial
`∑_i T(n, i - 2n) X^i`; it satisfies `F_{n+2} = (1+X⁴) F_{n+1} + (X³+X⁵) F_n`. With
`v = 1 + X²` we have `1 + X⁴ = v²` and `X³ + X⁵ = X³ v`, so `G_n = F_n v^n` satisfies
`G_{n+2} = v³ G_{n+1} + v³ X³ G_n`, whose solution is the Fibonacci-type sum
`G_n = ∑_{p+q=n} C(p,q) (v³)^p (X³)^q`. Cancelling `v^n` gives
`F_n = ∑_{p+q=n} C(p,q) X^{3q} v^{2p-q}`, and `[X^j] v^e = C(e, j/2)` for even `j`.

* `[X^{2n}] F_n`: each term is `C(p,q) C(2c, c)` with `2c = 2p - q ≥ 1`, which is even.
* `[X^{2n+1}] F_n`: the term `(p,q)` is `C(p,q) C(2c+1, c)` with `2p - q = 2c + 1`.
  By Lucas' theorem `C(2c+1, c)` is odd iff `c + 1 = 2^t`. If moreover `C(p,q)` is odd, then
  with `D = p - q` we have `C(D+q, q)` odd and `2D + q + 1 = 2^{t+1}`, and Lucas' theorem
  forces `D = 0` (induction on `t`). So only the diagonal term `p = q = n/2` survives, and it
  is odd iff `n/2 = 2c+1` with `c + 1 = 2^t`, i.e. iff `n + 2 = 2^{t+2}`.
-/

namespace Math0.Frontier.A355339
open Math0.Statements.A355339
open Polynomial Finset

/-! ### Binomial parities (Lucas' theorem at `p = 2`) -/

/-- Lucas' theorem at the prime `2`. -/
private lemma lucas2 (n k : ℕ) :
    n.choose k % 2 = ((n % 2).choose (k % 2) * (n / 2).choose (k / 2)) % 2 :=
  @Choose.choose_modEq_choose_mod_mul_choose_div_nat n k 2 ⟨Nat.prime_two⟩

/-- `C(2b+1, b)` is odd iff `b + 1` is a power of two. -/
private lemma oddC : ∀ b : ℕ, (2 * b + 1).choose b % 2 = 1 ↔ ∃ t, b + 1 = 2 ^ t := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rw [lucas2]
    have h1 : (2 * b + 1) % 2 = 1 := by omega
    have h2 : (2 * b + 1) / 2 = b := by omega
    have h3 : (1 : ℕ).choose (b % 2) = 1 := by
      rcases Nat.mod_two_eq_zero_or_one b with h | h <;> rw [h] <;> rfl
    rw [h1, h2, h3, one_mul]
    rcases Nat.even_or_odd' b with ⟨c, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp only [Nat.mul_zero, Nat.zero_div, Nat.choose_zero_right, Nat.zero_add]
        exact ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩
      · have hd := Nat.two_dvd_centralBinom_of_one_le hc
        rw [Nat.centralBinom_eq_two_mul_choose] at hd
        have : 2 * c / 2 = c := by omega
        rw [this, Nat.mod_eq_zero_of_dvd hd]
        constructor
        · intro h; omega
        · rintro ⟨t, ht⟩
          rcases t with _ | t
          · simp at ht; omega
          · rw [pow_succ] at ht; omega
    · have : (2 * c + 1) / 2 = c := by omega
      rw [this, ih c (by omega)]
      constructor
      · rintro ⟨t, ht⟩; exact ⟨t + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨t, ht⟩
        rcases t with _ | t
        · simp at ht
        · exact ⟨t, by rw [pow_succ] at ht; omega⟩

/-- If `C(D+q, q)` is odd and `2D + q + 1` is a power of two, then `D = 0`
(no carries in `2D + q`, and `D ⊆ q` bitwise, force `D = 0`). -/
private lemma dzero : ∀ (t D q : ℕ), (D + q).choose q % 2 = 1 → 2 * D + q + 1 = 2 ^ t → D = 0 := by
  intro t
  induction t with
  | zero => intro D q _ h; simp at h; omega
  | succ t ih =>
    intro D q hc h
    rw [pow_succ] at h
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' + 1 := ⟨q / 2, by omega⟩
    rw [lucas2] at hc
    rcases Nat.even_or_odd' D with ⟨D', rfl | rfl⟩
    · have e1 : (2 * D' + (2 * q' + 1)) % 2 = 1 := by omega
      have e2 : (2 * q' + 1) % 2 = 1 := by omega
      have e3 : (2 * D' + (2 * q' + 1)) / 2 = D' + q' := by omega
      have e4 : (2 * q' + 1) / 2 = q' := by omega
      rw [e1, e2, e3, e4, Nat.choose_self, one_mul] at hc
      have := ih D' q' hc (by omega)
      omega
    · have e1 : (2 * D' + 1 + (2 * q' + 1)) % 2 = 0 := by omega
      have e2 : (2 * q' + 1) % 2 = 1 := by omega
      rw [e1, e2] at hc
      simp at hc

/-- A natural number in `ZMod 2` is its parity bit. -/
private lemma cast_mod2 (x : ℕ) : (x : ZMod 2) = if x % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-! ### The row polynomials over `𝔽₂` -/

/-- The row polynomial `∑_i T(n, i - 2n) X^i`, reduced mod `2`, via the knight-move recurrence. -/
private noncomputable def Fp : ℕ → (ZMod 2)[X]
  | 0 => 1
  | 1 => 1 + X ^ 4
  | n + 2 => (1 + X ^ 4) * Fp (n + 1) + (X ^ 3 + X ^ 5) * Fp n

/-- Row `0` of the triangle. -/
private lemma T0 (k : ℤ) : T 0 k = if k = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; exact T_zero_zero
  · exact T_eq_zero 0 k (by have := abs_pos.mpr h; simpa using this)

/-- Shifting the position by `j` to the left, with zero extension. -/
private lemma T_shift (n j m : ℕ) :
    (T n ((m : ℤ) - 2 * n - j) : ZMod 2) =
      if j ≤ m then (T n (((m - j : ℕ) : ℤ) - 2 * n) : ZMod 2) else 0 := by
  split_ifs with h
  · congr 2; push_cast [h]; ring
  · rw [T_eq_zero n _ (by rw [abs_of_neg (by omega)]; omega), Nat.cast_zero]

/-- The coefficients of `Fp n` are the entries of row `n` mod `2`. -/
private theorem T_coeff : ∀ (n m : ℕ), (T n ((m : ℤ) - 2 * n) : ZMod 2) = (Fp n).coeff m
  | 0, m => by
    rw [T0, Fp, coeff_one]
    split_ifs <;> first | omega | simp
  | 1, m => by
    rw [T_one, T0, T0, Fp, coeff_add, coeff_one, coeff_X_pow]
    split_ifs <;> first | omega | simp
  | n + 2, m => by
    rw [T_add_two, Fp, coeff_add, add_mul, add_mul, coeff_add, coeff_add, one_mul,
      coeff_X_pow_mul', coeff_X_pow_mul', coeff_X_pow_mul', ← T_coeff (n + 1), ← T_coeff (n + 1),
      ← T_coeff n, ← T_coeff n]
    have e1 := T_shift (n + 1) 4 m
    have e3 := T_shift n 5 m
    have e4 := T_shift n 3 m
    push_cast at e1 e3 e4 ⊢
    rw [show (m : ℤ) - 2 * (n + 2) - 2 = m - 2 * (n + 1) - 4 by ring,
      show (m : ℤ) - 2 * (n + 2) + 2 = m - 2 * (n + 1) by ring,
      show (m : ℤ) - 2 * (n + 2) - 1 = m - 2 * n - 5 by ring,
      show (m : ℤ) - 2 * (n + 2) + 1 = m - 2 * n - 3 by ring, e1, e3, e4]
    split_ifs <;> ring

/-- The Fibonacci-type sum `∑_{p+q=n} C(p,q) A^p B^q`. -/
private noncomputable def hsum {R : Type*} [CommSemiring R] (A B : R) (n : ℕ) : R :=
  ∑ p ∈ antidiagonal n, (p.1.choose p.2 : R) * A ^ p.1 * B ^ p.2

/-- `hsum` satisfies `h(n+2) = A h(n+1) + A B h(n)` (Pascal's rule). -/
private lemma hsum_rec {R : Type*} [CommSemiring R] (A B : R) (n : ℕ) :
    hsum A B (n + 2) = A * hsum A B (n + 1) + A * B * hsum A B n := by
  unfold hsum
  rw [Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ']
  rw [Nat.sum_antidiagonal_succ' (n := n)]
  simp only [Nat.choose_succ_succ, Nat.choose_zero_succ, Nat.choose_zero_right, Nat.cast_add,
    Nat.cast_zero, Nat.cast_one, zero_mul, zero_add, Finset.mul_sum]
  rw [mul_add, Finset.mul_sum, add_assoc (A * _), ← Finset.sum_add_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.succ_eq_add_one]
    ring

/-- `2 = 0` in `𝔽₂[X]`. -/
private lemma two_eq_zero : (2 : (ZMod 2)[X]) = 0 := by
  exact_mod_cast CharP.cast_eq_zero (ZMod 2)[X] 2

/-- `1 + X⁴ = (1 + X²)²` in `𝔽₂[X]`. -/
private lemma one_add_X4 : (1 + X ^ 4 : (ZMod 2)[X]) = (1 + X ^ 2) ^ 2 := by
  linear_combination (-(X : (ZMod 2)[X]) ^ 2) * two_eq_zero

/-- `Fp n · v^n = ∑_{p+q=n} C(p,q) (v³)^p (X³)^q` with `v = 1 + X²`. -/
private lemma Fp_mul (n : ℕ) :
    Fp n * (1 + X ^ 2) ^ n = hsum ((1 + X ^ 2 : (ZMod 2)[X]) ^ 3) (X ^ 3) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Fp, hsum]
  | one =>
    rw [Fp, one_add_X4]
    simp [hsum, Nat.sum_antidiagonal_succ]
    ring
  | more n ih0 ih1 =>
    rw [hsum_rec, ← ih0, ← ih1, Fp, one_add_X4]
    ring

/-- `1 + X² ≠ 0`. -/
private lemma vne : (1 + X ^ 2 : (ZMod 2)[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp at this

/-- Closed form `Fp n = ∑_{p+q=n} C(p,q) X^{3q} (1+X²)^{2p-q}`. -/
private lemma Fp_closed (n : ℕ) :
    Fp n = ∑ p ∈ antidiagonal n,
      (p.1.choose p.2 : (ZMod 2)[X]) * (X ^ (3 * p.2) * (1 + X ^ 2) ^ (2 * p.1 - p.2)) := by
  apply mul_right_cancel₀ (pow_ne_zero n vne)
  rw [Fp_mul, hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rcases le_or_gt p.2 p.1 with h | h
  · rw [← pow_mul, ← pow_mul, mul_comm 3 p.2, show 3 * p.1 = 2 * p.1 - p.2 + n by omega, pow_add]
    ring
  · rw [Nat.choose_eq_zero_of_lt h]
    simp

/-- `[X^j] (1 + X²)^e = C(e, j/2)` for even `j`, and `0` for odd `j`. -/
private lemma vpow_coeff (e j : ℕ) :
    ((1 + X ^ 2 : (ZMod 2)[X]) ^ e).coeff j =
      if 2 ∣ j then ((e.choose (j / 2) : ℕ) : ZMod 2) else 0 := by
  have : (1 + X ^ 2 : (ZMod 2)[X]) ^ e = expand (ZMod 2) 2 ((1 + X) ^ e) := by
    simp [map_pow, map_add, expand_X]
  rw [this, coeff_expand two_pos, coeff_one_add_X_pow]

/-- Coefficient formula for `Fp n`. -/
private lemma Fp_coeff (n m : ℕ) :
    (Fp n).coeff m = ∑ p ∈ antidiagonal n, (p.1.choose p.2 : ZMod 2) *
      (if 3 * p.2 ≤ m then (if 2 ∣ (m - 3 * p.2) then
        (((2 * p.1 - p.2).choose ((m - 3 * p.2) / 2) : ℕ) : ZMod 2) else 0) else 0) := by
  rw [Fp_closed, finsetSum_coeff]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_natCast_mul, coeff_X_pow_mul']
  split_ifs <;> simp [vpow_coeff, *]

/-! ### The central coefficients -/

/-- Every term of `[X^{2n}] Fp n` vanishes for `n ≥ 1`. -/
private lemma term_even (n : ℕ) (hn : 1 ≤ n) (p : ℕ × ℕ) (hp : p.1 + p.2 = n) :
    (p.1.choose p.2 : ZMod 2) *
      (if 3 * p.2 ≤ 2 * n then (if 2 ∣ (2 * n - 3 * p.2) then
        (((2 * p.1 - p.2).choose ((2 * n - 3 * p.2) / 2) : ℕ) : ZMod 2) else 0) else 0) = 0 := by
  obtain ⟨a, b⟩ := p
  simp only at hp ⊢
  rcases lt_or_ge a b with hab | hab
  · rw [Nat.choose_eq_zero_of_lt hab, Nat.cast_zero, zero_mul]
  · split_ifs with h1 h2
    · obtain ⟨c, hc⟩ : ∃ c, 2 * a - b = 2 * c := ⟨(2 * a - b) / 2, by omega⟩
      have e1 : (2 * n - 3 * b) / 2 = c := by omega
      have hd := Nat.two_dvd_centralBinom_of_one_le (show 0 < c by omega)
      rw [Nat.centralBinom_eq_two_mul_choose] at hd
      rw [hc, e1, (ZMod.natCast_eq_zero_iff _ 2).mpr hd, mul_zero]
    · rw [mul_zero]
    · rw [mul_zero]

/-- Every off-diagonal term (`p ≠ q`) of `[X^{2n+1}] Fp n` vanishes. -/
private lemma term_off (n : ℕ) (p : ℕ × ℕ) (hp : p.1 + p.2 = n) (hne : p.1 ≠ p.2) :
    (p.1.choose p.2 : ZMod 2) *
      (if 3 * p.2 ≤ 2 * n + 1 then (if 2 ∣ (2 * n + 1 - 3 * p.2) then
        (((2 * p.1 - p.2).choose ((2 * n + 1 - 3 * p.2) / 2) : ℕ) : ZMod 2) else 0) else 0) =
      0 := by
  obtain ⟨a, b⟩ := p
  simp only at hp hne ⊢
  rcases lt_or_ge a b with hab | hab
  · rw [Nat.choose_eq_zero_of_lt hab, Nat.cast_zero, zero_mul]
  · rw [if_pos (by omega)]
    by_cases h2 : 2 ∣ (2 * n + 1 - 3 * b)
    · rw [if_pos h2]
      obtain ⟨c, hc⟩ : ∃ c, 2 * a - b = 2 * c + 1 := ⟨(2 * a - b) / 2, by omega⟩
      have e1 : (2 * n + 1 - 3 * b) / 2 = c + 1 := by omega
      rw [hc, e1, Nat.choose_symm_half, cast_mod2, cast_mod2]
      by_cases hc1 : (2 * c + 1).choose c % 2 = 1
      · obtain ⟨t, ht⟩ := (oddC c).mp hc1
        by_cases hc2 : a.choose b % 2 = 1
        · exfalso
          have h3 : (a - b + b).choose b % 2 = 1 := by rwa [Nat.sub_add_cancel hab]
          have h4 : 2 * (a - b) + b + 1 = 2 ^ (t + 1) := by rw [pow_succ]; omega
          have := dzero (t + 1) (a - b) b h3 h4
          omega
        · rw [if_neg hc2, zero_mul]
      · rw [if_neg hc1, mul_zero]
    · rw [if_neg h2, mul_zero]

/-- For `n ≥ 1`, the central entry `T(n,0)` is even. -/
private lemma T0_even (n : ℕ) (hn : 1 ≤ n) : T n 0 % 2 = 0 := by
  have hT : (T n 0 : ZMod 2) = (Fp n).coeff (2 * n) := by
    rw [← T_coeff]; congr 2; push_cast; ring
  rw [Fp_coeff, Finset.sum_eq_zero
    (fun p hp => term_even n hn p (HasAntidiagonal.mem_antidiagonal.mp hp))] at hT
  have := (ZMod.natCast_eq_zero_iff _ 2).mp hT
  omega

/-- `T(n,1)` is odd iff `n + 2` is a power of two that is at least `4`. -/
private lemma T1_parity (n : ℕ) : T n 1 % 2 = 1 ↔ ∃ t, n + 2 = 2 ^ (t + 2) := by
  have hT : (T n 1 : ZMod 2) = (Fp n).coeff (2 * n + 1) := by
    rw [← T_coeff]; congr 2; push_cast; ring
  rw [Fp_coeff] at hT
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · rw [Finset.sum_eq_single (q, q)] at hT
    · simp only at hT
      rw [Nat.choose_self, Nat.cast_one, one_mul, if_pos (by omega)] at hT
      rcases Nat.even_or_odd' q with ⟨c, rfl | rfl⟩
      · rw [if_neg (by omega)] at hT
        have := (ZMod.natCast_eq_zero_iff _ 2).mp hT
        constructor
        · intro h; omega
        · rintro ⟨t, ht⟩; rw [pow_add] at ht; omega
      · rw [if_pos (by omega)] at hT
        have e1 : (2 * (2 * (2 * c + 1)) + 1 - 3 * (2 * c + 1)) / 2 = c + 1 := by omega
        have e2 : 2 * (2 * c + 1) - (2 * c + 1) = 2 * c + 1 := by omega
        rw [e1, e2, Nat.choose_symm_half, ZMod.natCast_eq_natCast_iff'] at hT
        rw [hT, oddC]
        constructor
        · rintro ⟨t, ht⟩; exact ⟨t, by rw [pow_add]; omega⟩
        · rintro ⟨t, ht⟩; exact ⟨t, by rw [pow_add] at ht; omega⟩
    · intro p hp hne
      apply term_off _ p (HasAntidiagonal.mem_antidiagonal.mp hp)
      intro h
      have := HasAntidiagonal.mem_antidiagonal.mp hp
      exact hne (Prod.ext (by omega) (by omega))
    · intro h
      exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by simp; omega)) h
  · rw [Finset.sum_eq_zero
      (fun p hp => term_off _ p (HasAntidiagonal.mem_antidiagonal.mp hp) (by
        have := HasAntidiagonal.mem_antidiagonal.mp hp; omega))] at hT
    have := (ZMod.natCast_eq_zero_iff _ 2).mp hT
    constructor
    · intro h; omega
    · rintro ⟨t, ht⟩; rw [pow_add] at ht; omega

/-! ### Symmetry and the run length -/

/-- The rows are symmetric: `T(n,-k) = T(n,k)`. -/
private theorem T_symm : ∀ (n : ℕ) (k : ℤ), T n (-k) = T n k
  | 0, k => by rw [T0, T0]; simp [neg_eq_zero]
  | 1, k => by
    rw [T_one, T_one, T0, T0, T0, T0]
    split_ifs <;> omega
  | n + 2, k => by
    rw [T_add_two, T_add_two, show -k - 2 = -(k + 2) by ring, show -k + 2 = -(k - 2) by ring,
      show -k - 1 = -(k + 1) by ring, show -k + 1 = -(k - 1) by ring, T_symm (n + 1),
      T_symm (n + 1), T_symm n, T_symm n]
    ring

/-- The first two entries of `(range (2n+1)).map f` for `n ≥ 1`. -/
private lemma range_map (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℕ) :
    ∃ rest, (List.range (2 * n + 1)).map f = f 0 :: f 1 :: rest := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * n + 1 = k + 1 + 1 := ⟨2 * n - 1, by omega⟩
  rw [hk, List.range_succ_eq_map, List.range_succ_eq_map]
  exact ⟨(List.range k).map (f ∘ Nat.succ ∘ Nat.succ), by simp⟩

/-- The even prefix of `x :: y :: rest` with `x` even has length `≥ 1`, and length `1` iff
`y` is odd. -/
private lemma tw (x y : ℕ) (rest : List ℕ) (hx : x % 2 = 0) :
    1 ≤ ((x :: y :: rest).takeWhile (fun z => z % 2 == 0)).length ∧
    (((x :: y :: rest).takeWhile (fun z => z % 2 == 0)).length = 1 ↔ y % 2 = 1) := by
  rw [List.takeWhile_cons, List.takeWhile_cons]
  simp only [hx, beq_self_eq_true, if_true, List.length_cons]
  split_ifs with h
  · simp only [beq_iff_eq] at h
    simp only [List.length_cons]
    omega
  · simp at h; simp [h]

/-- The run-length expression of `a` equals `1` iff the entry next to the (even) centre is odd. -/
private lemma run_one (x x' y y' : ℕ) (r r' : List ℕ) (hx : x % 2 = 0) (hx' : x' % 2 = 0)
    (hy : y' % 2 = y % 2) :
    (if ((x :: y :: r).takeWhile (fun z => z % 2 == 0)).length = 0 then 0 else
      ((x' :: y' :: r').takeWhile (fun z => z % 2 == 0)).length +
      ((x :: y :: r).takeWhile (fun z => z % 2 == 0)).length - 1) = 1 ↔ y % 2 = 1 := by
  obtain ⟨hR1, hR2⟩ := tw x y r hx
  obtain ⟨hL1, hL2⟩ := tw x' y' r' hx'
  rw [if_neg (by omega)]
  constructor
  · intro h
    exact hR2.mp (by omega)
  · intro h
    have := hR2.mpr h
    have := hL2.mpr (by omega)
    omega

/-- For `n ≥ 1`, `a(n) = 1` iff `T(n,1)` is odd. -/
private lemma a_one_iff (n : ℕ) (hn : 1 ≤ n) : a n = 1 ↔ T n 1 % 2 = 1 := by
  rw [a_eq, if_neg (by omega)]
  dsimp only
  obtain ⟨r1, h1⟩ := range_map n hn (fun k : ℕ => T n k)
  obtain ⟨r2, h2⟩ := range_map n hn (fun k : ℕ => T n (-k))
  rw [h1, h2]
  have h0 := T0_even n hn
  exact run_one _ _ _ _ _ _ (by simpa using h0) (by simpa using h0) (by simp [T_symm])

/-- Sigrist's conjecture holds: `a(n) = 1` iff `n > 0` and `n = 2^m - 2`. -/
theorem result : statement := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a]
  · rw [a_one_iff n hn, T1_parity]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨hn, t + 2, ?_⟩
      have := congrArg (Nat.cast : ℕ → ℤ) ht
      push_cast at this
      linarith
    · rintro ⟨-, m, hm⟩
      rcases m with _ | _ | t
      · norm_num at hm; omega
      · norm_num at hm; omega
      · refine ⟨t, ?_⟩
        have : ((n + 2 : ℕ) : ℤ) = ((2 ^ (t + 2) : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this

end Math0.Frontier.A355339

#math0_settles Math0.Frontier.A355339.result Math0.Statements.A355339.statement

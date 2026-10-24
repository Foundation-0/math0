/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A335012
import Math0.Audit

/-!
# Repunit residues: `a(n) = n - 1` exactly for long period primes

We prove Eu's conjecture on A335012: for `n ≥ 1`, the repunits `R_1, ..., R_n` take exactly
`n - 1` distinct residues modulo `n` iff `n` is a long period prime (A006883).

Write `R_k = (10^k - 1)/9`, so `R_{k+1} = 10 R_k + 1`, `9 R_k + 1 = 10^k` and
`R_{m+k} = 10^k R_m + R_k`.

* **Periodicity.** If `n ∣ R_m` with `m ≥ 1`, then `R_{m+k} ≡ R_k (mod n)`, so every residue is
  already attained by some `R_j` with `1 ≤ j ≤ m`; hence `a(n) ≤ m`.
* **Cancellation.** If `gcd(n, 10) = 1` and `R_i ≡ R_j (mod n)` with `i < j`, then
  `n ∣ 10^i R_{j-i}`, so `n ∣ R_{j-i}`.
* **Small factors.** If `2 ∣ n` (`n ≥ 4`) all residues are odd, if `5 ∣ n` all are `≡ 1 (mod 5)`;
  either way `0` and `2` are missed and `a(n) ≤ n - 2`.
* **Three.** `R_k ≡ k (mod 3)`. If `3 ∣ n`, `gcd(n,10) = 1` and `a(n) = n - 1 < n`, pigeonhole and
  cancellation give `n ∣ R_m` with `1 ≤ m ≤ n - 1`, periodicity forces `m = n - 1`, and then
  `3 ∣ R_{n-1}` gives `3 ∣ n - 1`, impossible.
* **The main case.** If `gcd(n, 30) = 1`, then `n ∣ R_m ↔ 10^m ≡ 1 (mod n)`. Euler gives
  `n ∣ R_{φ(n)}`, so `n - 1 = a(n) ≤ φ(n)`, hence `n` is prime; then with `d = ord_n(10)`,
  `n - 1 ≤ d ∣ n - 1`. Conversely for a long period prime `p ≥ 7`, `R_1, ..., R_{p-1}` are
  pairwise distinct modulo `p` (cancellation and minimality of the order) and `p ∣ R_{p-1}`.
-/

namespace Math0.Frontier.A335012
open Math0.Statements.A335012

/-- The repunit `R_k = 11...1` (`k` ones), defined by `R_0 = 0`, `R_{k+1} = 10 R_k + 1`. -/
private def rep : ℕ → ℕ
  | 0 => 0
  | k + 1 => 10 * rep k + 1

/-- `9 R_k + 1 = 10^k`. -/
private lemma nine_rep (k : ℕ) : 9 * rep k + 1 = 10 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep, pow_succ, ← ih]; ring

/-- The closed form used in the statement agrees with `rep`. -/
private lemma rep_eq (k : ℕ) : (10 ^ k - 1) / 9 = rep k := by
  rw [← nine_rep k]; omega

/-- `R_{m+k} = 10^k R_m + R_k`. -/
private lemma rep_add (m k : ℕ) : rep (m + k) = 10 ^ k * rep m + rep k := by
  induction k with
  | zero => simp [rep]
  | succ k ih => rw [← add_assoc, rep, ih, rep, pow_succ]; ring

/-- `R_k ≡ k (mod 3)`. -/
private lemma rep_mod_three (k : ℕ) : rep k % 3 = k % 3 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep]; omega

/-- Repunits are odd. -/
private lemma rep_mod_two (k : ℕ) (hk : 1 ≤ k) : rep k % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [rep]; omega

/-- Repunits are `≡ 1 (mod 5)`. -/
private lemma rep_mod_five (k : ℕ) (hk : 1 ≤ k) : rep k % 5 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [rep]; omega

/-- `a` in terms of `rep`. -/
private lemma a_eq (n : ℕ) : a n = ((Finset.Icc 1 n).image (fun k => rep k % n)).card := by
  unfold a
  congr 2
  funext k
  rw [rep_eq]

/-- `10^m = 1` in `ZMod n` iff `10^m ≡ 1 (mod n)`. -/
private lemma zmod_pow_iff (n m : ℕ) : (10 : ZMod n) ^ m = 1 ↔ 10 ^ m ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl

/-- If `n` is prime to `3` and `10^m ≡ 1 (mod n)`, then `n ∣ R_m`. -/
private lemma dvd_rep_of_modEq {n m : ℕ} (h3 : Nat.Coprime n 3) (h : 10 ^ m ≡ 1 [MOD n]) :
    n ∣ rep m := by
  rw [← nine_rep] at h
  have h0 : 9 * rep m ≡ 0 [MOD n] := Nat.ModEq.add_right_cancel' 1 (by simpa using h)
  have h9 : Nat.Coprime n 9 := by
    have := Nat.Coprime.pow_right 2 h3
    simpa using this
  exact h9.dvd_of_dvd_mul_left ((Nat.modEq_zero_iff_dvd).1 h0)

/-- If `n ∣ R_m`, then `10^m ≡ 1 (mod n)`. -/
private lemma modEq_of_dvd_rep {n m : ℕ} (h : n ∣ rep m) : 10 ^ m ≡ 1 [MOD n] := by
  rw [← nine_rep]
  have h0 : 9 * rep m ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).2 (dvd_mul_of_dvd_right h 9)
  simpa using h0.add_right 1

/-- Periodicity: if `n ∣ R_m` then every `R_k % n` (`k ≥ 1`) equals some `R_j % n`, `1 ≤ j ≤ m`. -/
private lemma exists_small {n m : ℕ} (hm : 1 ≤ m) (h : n ∣ rep m) :
    ∀ k, 1 ≤ k → ∃ j, 1 ≤ j ∧ j ≤ m ∧ rep j % n = rep k % n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkm : k ≤ m
    · exact ⟨k, hk, hkm, rfl⟩
    · obtain ⟨j, hj1, hjm, hj⟩ := ih (k - m) (by omega) (by omega)
      refine ⟨j, hj1, hjm, ?_⟩
      have hk' : k = m + (k - m) := by omega
      rw [hj, hk', rep_add, Nat.add_sub_cancel_left]
      obtain ⟨c, hc⟩ := h
      rw [hc]
      rw [show 10 ^ (k - m) * (n * c) = n * (10 ^ (k - m) * c) by ring, Nat.mul_add_mod]

/-- Periodicity bound: if `n ∣ R_m` with `m ≥ 1` then `a(n) ≤ m`. -/
private lemma a_le_of_dvd {n m : ℕ} (hm : 1 ≤ m) (h : n ∣ rep m) : a n ≤ m := by
  rw [a_eq]
  calc ((Finset.Icc 1 n).image (fun k => rep k % n)).card
      ≤ ((Finset.Icc 1 m).image (fun k => rep k % n)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image, Finset.mem_Icc] at hx ⊢
        obtain ⟨k, ⟨hk1, -⟩, rfl⟩ := hx
        obtain ⟨j, hj1, hjm, hj⟩ := exists_small hm h k hk1
        exact ⟨j, ⟨hj1, hjm⟩, hj⟩
    _ ≤ (Finset.Icc 1 m).card := Finset.card_image_le
    _ = m := by simp

/-- If no residue `R_k % n` is `0` or `2` (and `n ≥ 3`), then `a(n) ≤ n - 2`. -/
private lemma a_le_sub_two {n : ℕ} (hn : 3 ≤ n)
    (h : ∀ k, 1 ≤ k → rep k % n ≠ 0 ∧ rep k % n ≠ 2) : a n ≤ n - 2 := by
  rw [a_eq]
  calc ((Finset.Icc 1 n).image (fun k => rep k % n)).card
      ≤ (((Finset.range n).erase 0).erase 2).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image, Finset.mem_Icc] at hx
        obtain ⟨k, ⟨hk1, -⟩, rfl⟩ := hx
        obtain ⟨h0, h2⟩ := h k hk1
        simp only [Finset.mem_erase, Finset.mem_range]
        exact ⟨h2, h0, Nat.mod_lt _ (by omega)⟩
    _ = n - 2 := by
        rw [Finset.card_erase_of_mem (by simp; omega), Finset.card_erase_of_mem (by simp; omega)]
        simp; omega

/-- Cancellation: for `n` prime to `10`, `R_i ≡ R_j (mod n)` with `i < j` gives `n ∣ R_{j-i}`. -/
private lemma dvd_rep_sub {n i j : ℕ} (hn : Nat.Coprime n 10) (hij : i < j)
    (h : rep i % n = rep j % n) : n ∣ rep (j - i) := by
  have hj : j = (j - i) + i := by omega
  rw [hj, rep_add] at h
  have h' : 0 + rep i ≡ 10 ^ i * rep (j - i) + rep i [MOD n] := by
    simpa [Nat.ModEq] using h
  have h0 := Nat.ModEq.add_right_cancel' (rep i) h'
  have hd : n ∣ 10 ^ i * rep (j - i) := (Nat.modEq_zero_iff_dvd).1 h0.symm
  exact (Nat.Coprime.pow_right i hn).dvd_of_dvd_mul_left hd

/-- Pigeonhole: if `a(n) < n`, two of `R_1, ..., R_n` agree modulo `n`. -/
private lemma exists_collision {n : ℕ} (h : a n < n) :
    ∃ i j, 1 ≤ i ∧ i < j ∧ j ≤ n ∧ rep i % n = rep j % n := by
  rw [a_eq] at h
  have hninj : ¬ Set.InjOn (fun k => rep k % n) (Finset.Icc 1 n : Set ℕ) := by
    intro hinj
    rw [Finset.card_image_of_injOn hinj] at h
    simp at h
  simp only [Set.InjOn, Finset.coe_Icc, Set.mem_Icc, not_forall] at hninj
  obtain ⟨i, ⟨hi1, hin⟩, j, ⟨hj1, hjn⟩, hij, hne⟩ := hninj
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨i, j, hi1, hlt, hjn, hij⟩
  · exact ⟨j, i, hj1, hlt, hin, hij.symm⟩

/-- `a(1) = 1`. -/
private lemma a_one : a 1 = 1 := by decide +kernel

/-- `a(2) = 1`. -/
private lemma a_two : a 2 = 1 := by decide +kernel

/-- Forward direction: `a(n) = n - 1` forces `n` to be a long period prime. -/
private lemma forward {n : ℕ} (hn : 1 ≤ n) (ha : a n = n - 1) : IsLongPeriodPrime n := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 1 := by omega
    subst this
    rw [a_one] at ha
    simp at ha
  by_cases h2 : 2 ∣ n
  · by_cases hn4 : n = 2
    · subst hn4; exact ⟨Nat.prime_two, Or.inl rfl⟩
    · exfalso
      have hn4' : 4 ≤ n := by obtain ⟨c, hc⟩ := h2; omega
      have := a_le_sub_two (n := n) (by omega) (fun k hk => by
        have hm : rep k % n % 2 = 1 := by rw [Nat.mod_mod_of_dvd _ h2]; exact rep_mod_two k hk
        constructor <;> intro hc <;> rw [hc] at hm <;> simp at hm)
      omega
  by_cases h5 : 5 ∣ n
  · exfalso
    have hn5 : 5 ≤ n := Nat.le_of_dvd (by omega) h5
    have := a_le_sub_two (n := n) (by omega) (fun k hk => by
      have hm : rep k % n % 5 = 1 := by rw [Nat.mod_mod_of_dvd _ h5]; exact rep_mod_five k hk
      constructor <;> intro hc <;> rw [hc] at hm <;> simp at hm)
    omega
  have hc2 : Nat.Coprime n 2 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_two).2 h2))
  have hc5 : Nat.Coprime n 5 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
    (by norm_num : Nat.Prime 5)).2 h5))
  have hc10 : Nat.Coprime n 10 := by
    have := Nat.Coprime.mul_right hc2 hc5
    simpa using this
  by_cases h3 : 3 ∣ n
  · exfalso
    obtain ⟨i, j, hi1, hij, hjn, hr⟩ := exists_collision (n := n) (by omega)
    have hd := dvd_rep_sub hc10 hij hr
    have hle := a_le_of_dvd (by omega) hd
    have hm : j - i = n - 1 := by omega
    rw [hm] at hd
    have h3r : 3 ∣ rep (n - 1) := dvd_trans h3 hd
    have := rep_mod_three (n - 1)
    omega
  have hc3 : Nat.Coprime n 3 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_three).2 h3))
  -- Euler: `n ∣ R_{φ(n)}`, so `n - 1 ≤ φ(n) < n`.
  have heul : 10 ^ n.totient ≡ 1 [MOD n] := Nat.ModEq.pow_totient hc10.symm
  have htpos : 1 ≤ n.totient := Nat.totient_pos.2 (by omega)
  have hle := a_le_of_dvd htpos (dvd_rep_of_modEq hc3 heul)
  have hlt := Nat.totient_lt n (by omega)
  have htot : n.totient = n - 1 := by omega
  have hp : n.Prime := (Nat.totient_eq_iff_prime (by omega)).1 htot
  refine ⟨hp, Or.inr ?_⟩
  rw [htot] at heul
  have hpow : (10 : ZMod n) ^ (n - 1) = 1 := (zmod_pow_iff n (n - 1)).2 heul
  have hdvd : orderOf (10 : ZMod n) ∣ n - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hpos : 0 < orderOf (10 : ZMod n) := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hd : n ∣ rep (orderOf (10 : ZMod n)) :=
    dvd_rep_of_modEq hc3 ((zmod_pow_iff _ _).1 (pow_orderOf_eq_one _))
  have h1 := a_le_of_dvd hpos hd
  have h2 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Backward direction: a long period prime `p` has `a(p) = p - 1`. -/
private lemma backward {p : ℕ} (hp : IsLongPeriodPrime p) : a p = p - 1 := by
  obtain ⟨hpr, h2 | hord⟩ := hp
  · subst h2; exact a_two
  by_cases hp2 : p = 2
  · subst hp2; exact a_two
  have hp3 : 3 ≤ p := by have := hpr.two_le; omega
  have hpow : (10 : ZMod p) ^ (p - 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hmod : 10 ^ (p - 1) ≡ 1 [MOD p] := (zmod_pow_iff _ _).1 hpow
  -- `p` is prime to `10`.
  have hc10 : Nat.Coprime p 10 := by
    have hg := Nat.ModEq.gcd_eq hmod
    have hcop : Nat.Coprime (10 ^ (p - 1)) p := by
      unfold Nat.Coprime; rw [hg]; simp
    exact ((Nat.coprime_pow_left_iff (by omega) _ _).1 hcop).symm
  -- `p ≠ 3`.
  have hne3 : p ≠ 3 := by
    intro h3
    subst h3
    have : (10 : ZMod 3) ^ 1 ≠ 1 := pow_ne_one_of_lt_orderOf one_ne_zero (by rw [hord]; norm_num)
    exact this (by decide)
  have hc3 : Nat.Coprime p 3 := (Nat.coprime_primes hpr Nat.prime_three).2 hne3
  apply le_antisymm
  · exact a_le_of_dvd (by omega) (dvd_rep_of_modEq hc3 hmod)
  · -- `R_1, ..., R_{p-1}` are distinct modulo `p`.
    have hinj : Set.InjOn (fun k => rep k % p) (Finset.Icc 1 (p - 1) : Set ℕ) := by
      have key : ∀ i j, 1 ≤ i → i < j → j ≤ p - 1 → rep i % p ≠ rep j % p := by
        intro i j hi hij hj hr
        have hd := dvd_rep_sub hc10 hij hr
        have hz := (zmod_pow_iff p (j - i)).2 (modEq_of_dvd_rep hd)
        exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega) hz
      intro i hi j hj hr
      simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
      rcases lt_trichotomy i j with hlt | heq | hlt
      · exact absurd hr (key i j hi.1 hlt hj.2)
      · exact heq
      · exact absurd hr.symm (key j i hj.1 hlt hi.2)
    rw [a_eq]
    calc p - 1 = (Finset.Icc 1 (p - 1)).card := by simp
      _ = ((Finset.Icc 1 (p - 1)).image (fun k => rep k % p)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.Icc 1 p).image (fun k => rep k % p)).card := by
          apply Finset.card_le_card
          apply Finset.image_subset_image
          exact Finset.Icc_subset_Icc le_rfl (by omega)

/-- **Eu's conjecture (A335012).** For every `n ≥ 1`, the repunits `R_1, ..., R_n` leave exactly
`n - 1` distinct remainders modulo `n` iff `n` is a long period prime. -/
theorem result : statement := fun _ hn => ⟨forward hn, backward⟩

end Math0.Frontier.A335012

#math0_settles Math0.Frontier.A335012.result Math0.Statements.A335012.statement

/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.OEIS.«51903»
import Math0.Audit

/-!
# No odd n with a(n) > 1 satisfies b^n ≡ b^a(n) (mod n) for all b (OEIS A051903)

Thomas Ordowski (OEIS A051903, Dec 2019) asked whether there are odd numbers `n` with
`a(n) > 1` (where `a(n)` is the largest exponent in the prime factorization of `n`) such that
`b ^ n ≡ b ^ a(n) (mod n)` for every `b`. We prove that there are none, i.e. the negation of the
upstream statement. If `e = a(n) ≥ 2` and `p ^ e ∣ n` (necessarily `p` odd), take `b = p + 1`;
cancelling the unit `(p+1)^e` gives `p ^ e ∣ (p+1)^(n-e) - 1`, and lifting the exponent gives
`v_p((p+1)^(n-e) - 1) = 1 + v_p(n-e)`, so `p^(e-1) ∣ n - e`. Together with `p^(e-1) ∣ n` this
forces `p^(e-1) ∣ e`, impossible since `p^(e-1) ≥ 3^(e-1) > e`.
-/

namespace Math0.OeisA51903

/-- `foldr max 0` of a list of naturals is either `0` or an element of the list. -/
lemma foldr_max_zero_or_mem (L : List ℕ) : L.foldr max 0 = 0 ∨ L.foldr max 0 ∈ L := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rcases max_choice x (L.foldr max 0) with h | h
    · rw [h]; exact Or.inr (Or.inl rfl)
    · rw [h]
      rcases ih with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')

/-- If `a n` is positive, it is the exponent of some prime `p` in `n`. -/
lemma exists_prime_factorization_eq (n : ℕ) (h : 0 < OeisA51903.a n) :
    ∃ p, p.Prime ∧ n.factorization p = OeisA51903.a n := by
  unfold OeisA51903.a at *
  rcases foldr_max_zero_or_mem (n.primeFactorsList.map (n.primeFactorsList.count ·)) with h' | h'
  · omega
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h'
    exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, by rw [← Nat.primeFactorsList_count_eq, hpe]⟩

/-- `k + 1 < 3 ^ k` for `k ≥ 1`. -/
lemma succ_lt_three_pow (k : ℕ) (hk : 1 ≤ k) : k + 1 < 3 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · norm_num
    · have := ih hk'
      rw [pow_succ]; omega

/-- Core: if `p` is an odd prime, `e ≥ 2`, `p ^ e ∣ n` and `(p+1)^n ≡ (p+1)^e [MOD n]`, then we
reach a contradiction. -/
lemma core (n p e : ℕ) (hp : p.Prime) (hpodd : Odd p) (he : 2 ≤ e) (hn : n ≠ 0)
    (hdvd : p ^ e ∣ n) (hb : (p + 1) ^ n ≡ (p + 1) ^ e [MOD n]) : False := by
  have := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  have hpe_le : p ^ e ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have he_lt : e < p ^ e := Nat.lt_pow_self hp1
  obtain ⟨m, rfl⟩ : ∃ m, n = e + m := ⟨n - e, by omega⟩
  have hm : m ≠ 0 := by omega
  have hb' : (p + 1) ^ e * (p + 1) ^ m ≡ (p + 1) ^ e * 1 [MOD p ^ e] := by
    rw [← pow_add, mul_one]; exact hb.of_dvd hdvd
  have hcop : Nat.gcd (p ^ e) ((p + 1) ^ e) = 1 := by
    have : Nat.Coprime p (p + 1) := by simp
    exact Nat.Coprime.pow e e this
  have hc := Nat.ModEq.cancel_left_of_coprime hcop hb'
  have hdiv : p ^ e ∣ (p + 1) ^ m - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp hc.symm
  have hne : (p + 1) ^ m - 1 ≠ 0 := by
    have : 1 < (p + 1) ^ m := Nat.one_lt_pow hm (by omega)
    omega
  have hv := (padicValNat_dvd_iff_le hne).mp hdiv
  have hlte : padicValNat p ((p + 1) ^ m - 1 ^ m) = padicValNat p (p + 1 - 1) + padicValNat p m :=
    padicValNat.pow_sub_pow hpodd (by omega) (by simp) (by
      intro h; have := (Nat.dvd_add_right (dvd_refl p)).mp h
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)) hm
  rw [one_pow] at hlte
  simp only [Nat.add_sub_cancel, padicValNat_self] at hlte
  have hpm : p ^ (e - 1) ∣ m :=
    (padicValNat_dvd_iff_le hm).mpr (by omega)
  have hpn : p ^ (e - 1) ∣ e + m := (pow_dvd_pow p (by omega)).trans hdvd
  have hpe : p ^ (e - 1) ∣ e := (Nat.dvd_add_left hpm).mp hpn
  have h1 : p ^ (e - 1) ≤ e := Nat.le_of_dvd (by omega) hpe
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h; exact absurd hpodd (by decide)
    · have := hp.two_le; rcases h with ⟨k, hk⟩; omega
  have h2 : 3 ^ (e - 1) ≤ p ^ (e - 1) := Nat.pow_le_pow_left h3 _
  have h4 := succ_lt_three_pow (e - 1) (by omega)
  omega

/-- There is no odd `n` with `a n > 1` and `b ^ n ≡ b ^ (a n) [MOD n]` for all `b`. -/
theorem not_conjecture2 : ¬ (type_of% @OeisA51903.conjecture2) := by
  rintro ⟨n, hodd, h1, hb⟩
  obtain ⟨p, hp, hpe⟩ := exists_prime_factorization_eq n (by omega)
  have hn : n ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hdvd : p ^ OeisA51903.a n ∣ n := by
    rw [← hpe]; exact Nat.ordProj_dvd n p
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h
      exfalso
      have : 2 ∣ n := (dvd_pow_self 2 (by omega)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    · exact h
  exact core n p (OeisA51903.a n) hp hpodd h1 hn hdvd (hb (p + 1))

end Math0.OeisA51903

#math0_refutes Math0.OeisA51903.not_conjecture2 OeisA51903.conjecture2

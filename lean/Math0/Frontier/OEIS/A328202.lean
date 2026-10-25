/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A328202
import Math0.Audit

/-!
# The gcd of the interior binomial coefficients is `Λ-exp(n) · Λ-exp(n - 1)`

We prove Jon Maiga's conjecture (A328202): for `n ≥ 4`,
`gcd {C(n, k) : 2 ≤ k ≤ n - 2} = L(n) · L(n - 1)`, where `L(m) = p` if `m = p ^ t` is a prime
power (`t ≥ 1`) and `L(m) = 1` otherwise (A014963).

**`L(n) · L(n-1)` divides the gcd.** If `n = p ^ t` then `p ∣ C(n, k)` for `0 < k < n`. If
`n - 1 = p ^ t` then `C(n, k) = C(n-1, k-1) + C(n-1, k)` and both terms are divisible by `p` for
`2 ≤ k ≤ n - 2`. Since `L(m) ∣ m` and `n`, `n - 1` are coprime, the product divides each
`C(n, k)`.

**The gcd `g` divides `L(n) · L(n-1)`.** Let `p ^ e ∣ g` with `e ≥ 1`. As `g ∣ C(n, 2)` and
`2 · C(n, 2) = n (n - 1)`, `p` divides `n` or `n - 1`.
* `n = p ^ t · m`, `p ∤ m`, `t ≥ 1`. If `m ≥ 2`, Lucas gives `C(p^t m, p^t) ≡ m (mod p)`, so
  `p ∤ g`. If `m = 1`, Kummer for prime powers (`v_p C(p^t, k) = t - v_p k`) gives
  `p² ∤ C(p^t, k₀)` with `k₀ = p^(t-1)` (or `k₀ = 2` when `t = 1`), so `e = 1` and `p = L(n)`.
* `n - 1 = p ^ t · m`, `p ∤ m`, `t ≥ 1`. Use `(N+1) C(N, j) = C(N+1, j+1) (j+1)` with
  `N = n - 1`. If `m ≥ 2`, take `j = p^t`: `p ∤ (N+1) C(N, p^t)`, so `p ∤ C(n, p^t + 1)`.
  If `m = 1`, take `j = p^(t-1)`: `p² ∤ (p^t+1) C(p^t, p^(t-1))`, so `p² ∤ C(n, p^(t-1)+1)`,
  hence `e = 1` and `p = L(n - 1)`.
-/

namespace Math0.Frontier.A328202
open Math0.Statements.A328202

/-- `L(m) ∣ m`. -/
private lemma expMangoldt_dvd_self (m : ℕ) : expMangoldt m ∣ m := by
  unfold expMangoldt
  split_ifs
  · exact Nat.minFac_dvd m
  · exact one_dvd m

/-- `L(p ^ t) = p` for `p` prime and `t ≥ 1`. -/
private lemma expMangoldt_prime_pow {p t : ℕ} (hp : p.Prime) (ht : t ≠ 0) :
    expMangoldt (p ^ t) = p := by
  unfold expMangoldt
  rw [if_pos ((isPrimePow_pow_iff ht).mpr hp.isPrimePow), hp.pow_minFac ht]

/-- `L(n) ∣ C(n, k)` for `0 < k < n`. -/
private lemma expMangoldt_dvd_choose (n k : ℕ) (hk0 : k ≠ 0) (hkn : k ≠ n) :
    expMangoldt n ∣ n.choose k := by
  unfold expMangoldt
  split_ifs with h
  · obtain ⟨p, t, hp, ht, rfl⟩ := (isPrimePow_nat_iff _).mp h
    rw [hp.pow_minFac ht.ne']
    exact hp.dvd_choose_pow hk0 hkn
  · exact one_dvd _

/-- `L(n - 1) ∣ C(n, k)` for `2 ≤ k ≤ n - 2`. -/
private lemma expMangoldt_pred_dvd_choose (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    expMangoldt (n - 1) ∣ n.choose k := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.choose_succ_succ, Nat.add_sub_cancel]
  exact dvd_add (expMangoldt_dvd_choose N j (by omega) (by omega))
    (expMangoldt_dvd_choose N (j + 1) (by omega) (by omega))

/-- Kummer for prime powers: if `v_p(k) ≥ t - 1` then `p² ∤ C(p^t, k)`. -/
private lemma not_sq_dvd_choose {p t k : ℕ} (hp : p.Prime) (hk0 : k ≠ 0) (hk : k ≤ p ^ t)
    (hf : t - 1 ≤ k.factorization p) : ¬ p ^ 2 ∣ (p ^ t).choose k := by
  intro h
  have hc : (p ^ t).choose k ≠ 0 := (Nat.choose_pos hk).ne'
  rw [hp.pow_dvd_iff_le_factorization hc, Nat.factorization_choose_prime_pow hp hk hk0] at h
  omega

/-- Lucas: `C(p^t m, p^t) ≡ m (mod p)`. -/
private lemma choose_pow_mul_modEq {p m : ℕ} (hp : p.Prime) :
    ∀ t : ℕ, (p ^ t * m).choose (p ^ t) ≡ m [MOD p]
  | 0 => by simp [Nat.ModEq]
  | t + 1 => by
    have : Fact p.Prime := ⟨hp⟩
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (t + 1) * m) (p ^ (t + 1))
      p _
    have hp0 : 0 < p := hp.pos
    have e1 : p ^ (t + 1) * m % p = 0 := by
      exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _)
    have e2 : p ^ (t + 1) % p = 0 := by
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self p (by omega))
    have e3 : p ^ (t + 1) * m / p = p ^ t * m := by
      rw [pow_succ, mul_comm (p ^ t) p, mul_assoc, Nat.mul_div_cancel_left _ hp0]
    have e4 : p ^ (t + 1) / p = p ^ t := by
      rw [pow_succ, Nat.mul_div_cancel _ hp0]
    rw [e1, e2, e3, e4, Nat.choose_zero_right, one_mul] at h
    exact h.trans (choose_pow_mul_modEq hp t)

/-- `p ∤ C(p^t m, p^t)` when `p ∤ m`. -/
private lemma not_dvd_choose_pow_mul {p m t : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    ¬ p ∣ (p ^ t * m).choose (p ^ t) := by
  intro h
  exact hm (((choose_pow_mul_modEq hp t).dvd_iff (dvd_refl p)).mp h)

/-- The main theorem: Maiga's conjecture holds for every `n ≥ 4`. -/
theorem result : statement := by
  intro n hn
  set L := expMangoldt n * expMangoldt (n - 1) with hL
  have hcop : Nat.Coprime (expMangoldt n) (expMangoldt (n - 1)) := by
    have h : Nat.Coprime n (n - 1) :=
      (Nat.coprime_self_sub_right (by omega : 1 ≤ n)).mpr (Nat.coprime_one_right n)
    exact (h.coprime_dvd_left (expMangoldt_dvd_self n)).coprime_dvd_right
      (expMangoldt_dvd_self (n - 1))
  have hg : ∀ k, 2 ≤ k → k + 2 ≤ n → a n ∣ n.choose k := fun k h1 h2 =>
    Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨h1, by omega⟩)
  apply Nat.dvd_antisymm
  · -- the gcd divides `L`
    refine (Nat.dvd_iff_prime_pow_dvd_dvd L (a n)).mpr ?_
    intro p e hp hpe
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    have hpg : p ∣ a n := (dvd_pow_self p he.ne').trans hpe
    have hp2 : 2 ≤ p := hp.two_le
    -- `p ^ e ∣ p` as soon as `p² ∤ g`
    have key : ¬ p ^ 2 ∣ a n → p ^ e ∣ p := by
      intro h
      have : e ≤ 1 := by
        by_contra hc
        exact h ((pow_dvd_pow p (by omega)).trans hpe)
      exact (pow_dvd_pow p this).trans (by rw [pow_one])
    have hn2 : p ∣ n * (n - 1) := by
      have h := Nat.add_one_mul_choose_eq (n - 1) 1
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.choose_one_right] at h
      rw [h]
      exact Dvd.dvd.mul_right (hpg.trans (hg 2 le_rfl (by omega))) _
    rcases (Nat.Prime.dvd_mul hp).mp hn2 with hdn | hdn
    · -- `p ∣ n`
      obtain ⟨t, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p
        (by omega)
      have ht : t ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hm (hnm ▸ hdn)
      have hpt : p ≤ p ^ t := Nat.le_self_pow ht p
      have hm0 : m ≠ 0 := by rintro rfl; simp at hnm; omega
      by_cases hm1 : m = 1
      · subst hm1
        rw [mul_one] at hnm
        have hLp : p ∣ L := by
          rw [hL, hnm, expMangoldt_prime_pow hp ht]
          exact dvd_mul_right _ _
        refine (key ?_).trans hLp
        intro h2
        by_cases ht1 : t = 1
        · subst ht1
          rw [pow_one] at hnm
          refine not_sq_dvd_choose hp (by omega : (2 : ℕ) ≠ 0) (by rw [pow_one]; omega)
            (by omega) ?_
          rw [pow_one]
          have := h2.trans (hg 2 le_rfl (by omega))
          rwa [hnm] at this
        · have hk : p ^ (t - 1) * p = p ^ t := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          have hk2 : 2 ≤ p ^ (t - 1) := by
            calc 2 ≤ p := hp2
              _ ≤ p ^ (t - 1) := Nat.le_self_pow (by omega) p
          refine not_sq_dvd_choose hp (t := t) (k := p ^ (t - 1)) (by omega)
            (Nat.pow_le_pow_right hp.pos (by omega)) ?_ ?_
          · rw [hp.factorization_pow, Finsupp.single_eq_same]
          · rw [← hnm]
            refine h2.trans (hg _ hk2 ?_)
            rw [hnm, ← hk]
            nlinarith
      · exfalso
        have hm2 : 2 ≤ m := by omega
        apply not_dvd_choose_pow_mul (t := t) hp hm
        rw [← hnm]
        refine hpg.trans (hg _ (by omega) ?_)
        rw [hnm]
        nlinarith
    · -- `p ∣ n - 1`
      obtain ⟨t, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n - 1 ≠ 0) p
        (by omega)
      have ht : t ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hm (hnm ▸ hdn)
      have hpt : p ≤ p ^ t := Nat.le_self_pow ht p
      have hpdt : p ∣ p ^ t := dvd_pow_self p ht
      have hm0 : m ≠ 0 := by rintro rfl; simp at hnm; omega
      have hn1 : n = (n - 1) + 1 := by omega
      by_cases hm1 : m = 1
      · subst hm1
        rw [mul_one] at hnm
        have hLp : p ∣ L := by
          rw [hL, hnm, expMangoldt_prime_pow hp ht]
          exact dvd_mul_left _ _
        refine (key ?_).trans hLp
        intro h2
        have hk : p ^ (t - 1) * p = p ^ t := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        have hk1 : 1 ≤ p ^ (t - 1) := Nat.one_le_pow _ _ hp.pos
        have hrange : p ^ (t - 1) + 1 + 2 ≤ n := by
          rcases Nat.lt_or_ge t 2 with ht2 | ht2
          · have : t = 1 := by omega
            subst this
            simp only [Nat.sub_self, pow_zero, pow_one] at hnm ⊢
            omega
          · have : 2 ≤ p ^ (t - 1) := by
              calc 2 ≤ p := hp2
                _ ≤ p ^ (t - 1) := Nat.le_self_pow (by omega) p
            have : p ^ (t - 1) * 2 ≤ p ^ t := by rw [← hk]; exact Nat.mul_le_mul_left _ hp2
            omega
        have hid := Nat.add_one_mul_choose_eq (p ^ t) (p ^ (t - 1))
        have hc : p ^ 2 ∣ (p ^ t + 1) * (p ^ t).choose (p ^ (t - 1)) := by
          rw [hid]
          refine Dvd.dvd.mul_right ?_ _
          have := h2.trans (hg _ (by omega) hrange)
          rwa [hn1, hnm] at this
        have hcp : Nat.Coprime (p ^ 2) (p ^ t + 1) := by
          refine Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_)
          intro hd
          have := (Nat.dvd_add_right hpdt).mp hd
          exact hp.one_lt.ne' (Nat.dvd_one.mp this)
        refine not_sq_dvd_choose hp (t := t) (k := p ^ (t - 1)) (by omega)
          (Nat.pow_le_pow_right hp.pos (by omega)) ?_ (hcp.dvd_of_dvd_mul_left hc)
        rw [hp.factorization_pow, Finsupp.single_eq_same]
      · exfalso
        have hm2 : 2 ≤ m := by omega
        have hrange : p ^ t + 1 + 2 ≤ n := by
          rw [hn1, hnm]
          nlinarith
        have hid := Nat.add_one_mul_choose_eq (p ^ t * m) (p ^ t)
        have hc : p ∣ (p ^ t * m + 1) * (p ^ t * m).choose (p ^ t) := by
          rw [hid]
          refine Dvd.dvd.mul_right ?_ _
          have := hpg.trans (hg _ (by omega) hrange)
          rwa [hn1, hnm] at this
        rcases (Nat.Prime.dvd_mul hp).mp hc with hd | hd
        · have := (Nat.dvd_add_right (Dvd.dvd.mul_right hpdt m)).mp hd
          exact hp.one_lt.ne' (Nat.dvd_one.mp this)
        · exact not_dvd_choose_pow_mul hp hm hd
  · -- `L` divides the gcd
    refine Finset.dvd_gcd ?_
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact hcop.mul_dvd_of_dvd_of_dvd (expMangoldt_dvd_choose n k (by omega) (by omega))
      (expMangoldt_pred_dvd_choose n k hk.1 (by omega))

end Math0.Frontier.A328202

#math0_settles Math0.Frontier.A328202.result Math0.Statements.A328202.statement

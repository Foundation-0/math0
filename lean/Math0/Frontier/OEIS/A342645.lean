/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A342645
import Math0.Audit

/-!
# A342645: the diagonals of the eventual Mahonian-column polynomials

We prove both conjectures of A342645 (Kagey).

*Diagonals.* For `x ≥ n` the Mahonian number `mahonian x n` equals
`P_n(x) = ∑_{a ≤ n} e_a binom(x+n-a-1, n-a)`, where `∏_{i ≥ 1} (1 - q^i) = ∑ e_a q^a`
(from `∏_{i<x} (1 + ⋯ + q^i) · (1-q)^x = ∏_{i ≤ x} (1 - q^i)`). Newton interpolation then shows that
row `n` of the triangle is the coefficient list of `n! P_n(x)`, so
`T(n,k) = ∑_a e_a n(n-1)⋯(n-a+1) c(n-a,k)` with `c` the unsigned Stirling numbers of the first
kind. Since `c(N, N-r)` is a polynomial in `N` of degree `2r` with leading coefficient `1/(2^r r!)`
(discrete integration of `c(N+1, N+1-r) - c(N, N-r) = N c(N, N-r+1)`), `T(n, n-m)` is a polynomial
in `n` of degree `2m` with leading coefficient `1/(2^m m!)`; the four FORMULA identities follow
from `e_0, …, e_3 = 1, -1, -1, 0` and closed forms of `c(N, N-r)`, `r ≤ 3`.

*Leading coefficients.* We show `|A290030(m) / A053657(m+1)| = 1/(2^m m!)`. Writing
`B_m^(x) = m! f_m(x)` with `f_m(x) = [t^m] exp(x h(t))`, `h = log(t/(e^t-1))`, the list `norlund m` is
the coefficient list of `m! f_m` and its top entry is `(-1/2)^m`; so the claim is that the least
common denominator `L` of `B_m^(x)` satisfies `L · m! = A053657(m+1)`. Prime by prime this says that
the `p`-content of `f_m` is `p^(V_p(m))`, `V_p(m) = q + v_p(q!)`, `q = ⌊m/(p-1)⌋`:
* upper bound: by von Staudt–Clausen and Adams' theorem (proved here from a Voronoi-type
  congruence and Faulhaber's formula), `|h_i|_p ≤ p^(w_p(i))`; expanding `exp(x h)` part size by
  part size and using `m w_p(i) + v_p(m!) ≤ V_p(i m)` and superadditivity of `V_p` bounds every
  coefficient;
* lower bound: for `p = 2` the top coefficient `(-1/2)^m/m!` has the right size; for odd `p` the
  coefficient `[x^q] f_{(p-1)q} = [t^((p-2)q)] g^q / q!` (`g = h/t`) is dominated by
  `h_{p-1}^q / q!` (a weighted ultrametric argument), and `x f_{n} = (x-n-1) f_{n+1} - x f_{n+1}(x+1)`
  shows that the `p`-content of `f_n` is nondecreasing in `n`.
-/

namespace Math0.Frontier.A342645
open Math0.Statements.A342645

section VonStaudt
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- A natural number not divisible by `p` has `p`-adic norm `1`. -/
private lemma padicNorm_natCast_eq_one {q : ℕ} (h : ¬ p ∣ q) : padicNorm p (q : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff q).2 h

/-- For a prime `q ≠ p`, `|1/q|_p = 1`. -/
private lemma padicNorm_one_div_prime {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    padicNorm p (1 / (q : ℚ)) = 1 := by
  rw [padicNorm.div, padicNorm.one, padicNorm_natCast_eq_one]
  · simp
  · intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).1 hd).symm

/-- `|1/2|_p ≤ p`. -/
private lemma padicNorm_two_inv_le : padicNorm p ((2 : ℚ)⁻¹) ≤ p := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one]
  by_cases h2 : p = 2
  · subst h2
    have : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := by
      have := @padicNorm.padicNorm_p_of_prime 2 _
      simpa using this
    rw [this]; norm_num
  · have : padicNorm p ((2 : ℕ) : ℚ) = 1 := by
      apply padicNorm_natCast_eq_one
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hd
      exact h2 this
    simp only [Nat.cast_ofNat] at this
    rw [this]; simp; exact_mod_cast hp.out.one_lt.le

/-- For odd `p`, `|1/2|_p = 1`. -/
private lemma padicNorm_two_inv_odd (h2 : p ≠ 2) : padicNorm p ((2 : ℚ)⁻¹) = 1 := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one]
  have : padicNorm p ((2 : ℕ) : ℚ) = 1 := by
    apply padicNorm_natCast_eq_one
    intro hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hd)
  simp only [Nat.cast_ofNat] at this
  rw [this]; simp

/-- The von Staudt–Clausen theorem, localized at `p`: `B_{2k} = z - [p-1 ∣ 2k]/p` with `z` `p`-integral. -/
private lemma vsc_decomp (k : ℕ) (hk : 0 < k) :
    ∃ z : ℚ, padicNorm p z ≤ 1 ∧
      bernoulli (2 * k) = z - (if (p - 1) ∣ 2 * k then 1 / (p : ℚ) else 0) := by
  obtain ⟨m, hm⟩ := Bernoulli.vonStaudt_clausen k
  set S := (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) with hS
  have hsplit : (∑ q ∈ S, (1 : ℚ) / q) =
      (if (p - 1) ∣ 2 * k then 1 / (p : ℚ) else 0) + ∑ q ∈ S.erase p, (1 : ℚ) / q := by
    by_cases hd : (p - 1) ∣ 2 * k
    · have hpS : p ∈ S := by
        rw [hS, mem_filter, mem_range]
        refine ⟨?_, hp.out, hd⟩
        have := Nat.le_of_dvd (by omega) hd
        omega
      rw [if_pos hd, ← add_sum_erase _ _ hpS]
    · have hpS : p ∉ S := by
        rw [hS, mem_filter]; tauto
      rw [if_neg hd, erase_eq_of_notMem hpS, zero_add]
  refine ⟨(m : ℚ) - ∑ q ∈ S.erase p, (1 : ℚ) / q, ?_, ?_⟩
  · refine le_trans (padicNorm.sub) (max_le (padicNorm.of_int m) ?_)
    refine padicNorm.sum_le' (fun q hq => ?_) zero_le_one
    rw [mem_erase, hS, mem_filter] at hq
    rw [padicNorm_one_div_prime hq.2.2.1 hq.1]
  · have : bernoulli (2 * k) = (m : ℚ) - ∑ q ∈ S, (1 : ℚ) / q := by
      rw [hm]; ring
    rw [this, hsplit]; ring

/-- `|B_n|_p ≤ p` for every `n` (von Staudt–Clausen). -/
private lemma bern_norm_le_p (n : ℕ) : padicNorm p (bernoulli n) ≤ p := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp at hk; subst hk; simp [bernoulli_zero, hp1]
    · obtain ⟨z, hz, hb⟩ := vsc_decomp (p := p) k hkpos
      rw [show n = 2 * k by omega, hb]
      refine le_trans padicNorm.sub (max_le (hz.trans hp1) ?_)
      split_ifs
      · rw [padicNorm.div, padicNorm.one, padicNorm.padicNorm_p_of_prime]; simp
      · simp
  · rcases Nat.eq_or_lt_of_le hodd.pos with h1 | h1
    · subst h1; rw [bernoulli_one, show (-1 / 2 : ℚ) = -(2 : ℚ)⁻¹ by ring, padicNorm.neg]
      exact padicNorm_two_inv_le
    · rw [bernoulli_eq_zero_of_odd hodd h1]; simp

/-- If `p - 1 ∤ n` then `B_n` is `p`-integral (von Staudt–Clausen). -/
private lemma bern_norm_le_one (n : ℕ) (h : ¬ (p - 1) ∣ n) : padicNorm p (bernoulli n) ≤ 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp at hk; subst hk; exact absurd (dvd_zero _) h
    · obtain ⟨z, hz, hb⟩ := vsc_decomp (p := p) k hkpos
      rw [show n = 2 * k by omega] at h ⊢
      rw [hb, if_neg h, sub_zero]; exact hz
  · rcases Nat.eq_or_lt_of_le hodd.pos with h1 | h1
    · subst h1
      have h2 : p ≠ 2 := by rintro rfl; exact h (by simp)
      rw [bernoulli_one, show (-1 / 2 : ℚ) = -(2 : ℚ)⁻¹ by ring, padicNorm.neg,
        padicNorm_two_inv_odd h2]
    · rw [bernoulli_eq_zero_of_odd hodd h1]; simp

/-- If `p - 1 ∣ n` with `n > 0` even, then `|B_n|_p = p` (von Staudt–Clausen). -/
private lemma bern_norm_eq_p (n : ℕ) (h : (p - 1) ∣ n) (he : Even n) (hn : 0 < n) :
    padicNorm p (bernoulli n) = p := by
  obtain ⟨k, hk⟩ := he
  have hkpos : 0 < k := by omega
  obtain ⟨z, hz, hb⟩ := vsc_decomp (p := p) k hkpos
  rw [show n = 2 * k by omega] at h ⊢
  rw [hb, if_pos h]
  have h1p : padicNorm p (1 / (p : ℚ)) = p := by
    rw [padicNorm.div, padicNorm.one, padicNorm.padicNorm_p_of_prime]; simp
  have hlt : padicNorm p z < padicNorm p (1 / (p : ℚ)) := by
    rw [h1p]; exact lt_of_le_of_lt hz (by exact_mod_cast hp.out.one_lt)
  rw [sub_eq_add_neg, padicNorm.add_eq_max_of_ne, padicNorm.neg, h1p, max_eq_right]
  · rw [← h1p]; exact hlt.le
  · rw [padicNorm.neg]; exact hlt.ne

end VonStaudt

section PowerSums
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- A primitive root modulo `p`: `a^n ≡ 1 (mod p)` forces `p - 1 ∣ n`. -/
private lemma exists_prim_root : ∃ a : ℕ, ¬ p ∣ a ∧
    ∀ n : ℕ, (p : ℤ) ∣ (a : ℤ) ^ n - 1 → (p - 1) ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  refine ⟨(g : ZMod p).val, ?_, ?_⟩
  · intro hd
    have : (((g : ZMod p).val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [ZMod.natCast_zmod_val] at this
    exact g.ne_zero this
  · intro n hn
    have h1 : (g : ZMod p) ^ n = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hn
      push_cast at this
      rw [ZMod.natCast_zmod_val] at this
      exact sub_eq_zero.1 this
    have : g ^ n = 1 := Units.ext (by simpa using h1)
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one this

/-- The power sum `∑ j^n` over `0 ≤ j < p^e` with `p ∤ j`. -/
private def psT (n e : ℕ) : ℤ := ∑ j ∈ (range (p ^ e)).filter (fun j => ¬ p ∣ j), (j : ℤ) ^ n

/-- The power sum `∑ j^n` over `0 ≤ j < p^e`. -/
private def psS (n e : ℕ) : ℤ := ∑ j ∈ range (p ^ e), (j : ℤ) ^ n

/-- Multiplication by `a` with `p ∤ a` permutes the residues prime to `p` modulo `p^e`. -/
private lemma psT_perm (a n e : ℕ) (ha : ¬ p ∣ a) :
    ∑ j ∈ (range (p ^ e)).filter (fun j => ¬ p ∣ j), (((a * j) % p ^ e : ℕ) : ℤ) ^ n =
      psT (p := p) n e := by
  set U := (range (p ^ e)).filter (fun j => ¬ p ∣ j)
  have hN : 0 < p ^ e := pow_pos hp.out.pos e
  have hcop : Nat.gcd (p ^ e) a = 1 := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 ha
  have hmaps : Set.MapsTo (fun j => (a * j) % p ^ e) (U : Set ℕ) (U : Set ℕ) := by
    intro j hj
    simp only [U, coe_filter, mem_range, Set.mem_ofPred_eq] at hj ⊢
    refine ⟨Nat.mod_lt _ hN, ?_⟩
    intro hd
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; rw [pow_zero] at hj
      have : j = 0 := by omega
      subst this; exact absurd (dvd_zero p) hj.2
    have h1 : p ∣ p ^ e := dvd_pow_self p he.ne'
    have h2 : p ∣ a * j := by
      have := Nat.mod_add_div (a * j) (p ^ e)
      rw [← this]; exact dvd_add hd (dvd_mul_of_dvd_left h1 _)
    rcases (Nat.Prime.dvd_mul hp.out).1 h2 with h | h
    · exact ha h
    · exact hj.2 h
  have hinj : Set.InjOn (fun j => (a * j) % p ^ e) (U : Set ℕ) := by
    intro j hj k hk hjk
    simp only [U, coe_filter, mem_range, Set.mem_ofPred_eq] at hj hk
    have := Nat.ModEq.cancel_left_of_coprime hcop hjk
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hj.1, Nat.mod_eq_of_lt hk.1] at this
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj le_rfl
  unfold psT
  exact Finset.sum_nbij _ (fun j hj => hmaps hj) hinj hsurj (fun _ _ => rfl)

/-- Voronoi-type congruence: `p^(e + min(v_p(n), e))` divides the reduced power sum when `a^n ≢ 1 (mod p)`. -/
private lemma psT_dvd (a n e : ℕ) (ha : ¬ p ∣ a) (hprim : ¬ (p : ℤ) ∣ (a : ℤ) ^ n - 1) :
    (p : ℤ) ^ (e + min (padicValNat p n) e) ∣ psT (p := p) n e := by
  set D : ℤ := (p : ℤ) ^ (e + min (padicValNat p n) e)
  set N : ℕ := p ^ e
  have hDN : D ∣ (N : ℤ) * n := by
    simp only [D, N, pow_add, Nat.cast_pow]
    apply mul_dvd_mul_left
    have : (p : ℤ) ^ (padicValNat p n) ∣ (n : ℤ) := by exact_mod_cast pow_padicValNat_dvd
    exact (pow_dvd_pow _ (min_le_left _ _)).trans this
  have hDN2 : D ∣ (N : ℤ) ^ 2 := by
    simp only [D, N, Nat.cast_pow, ← pow_mul]
    apply pow_dvd_pow; omega
  have key : D ∣ ((a : ℤ) ^ n - 1) * psT (p := p) n e := by
    have hsum : ((a : ℤ) ^ n - 1) * psT (p := p) n e =
        ∑ j ∈ (range (p ^ e)).filter (fun j => ¬ p ∣ j),
          (((a * j : ℕ) : ℤ) ^ n - (((a * j) % p ^ e : ℕ) : ℤ) ^ n) := by
      rw [sum_sub_distrib, psT_perm a n e ha, sub_mul, one_mul, psT, mul_sum]
      congr 1
      refine sum_congr rfl (fun j _ => ?_)
      push_cast; ring
    rw [hsum]
    refine dvd_sum (fun j _ => ?_)
    set r : ℤ := (((a * j) % p ^ e : ℕ) : ℤ)
    set q : ℤ := (((a * j) / p ^ e : ℕ) : ℤ)
    have hdecomp : ((a * j : ℕ) : ℤ) = r + (N : ℤ) * q := by
      simp only [r, q, N]
      exact_mod_cast (Nat.mod_add_div (a * j) (p ^ e)).symm
    rw [hdecomp]
    have h2 := sq_dvd_add_pow_sub_sub ((N : ℤ) * q) r n
    have : (r + N * q) ^ n - r ^ n =
        ((r + N * q) ^ n - r ^ (n - 1) * (N * q) * n - r ^ n) + r ^ (n - 1) * (N * q) * n := by
      ring
    rw [this]
    refine dvd_add ?_ ?_
    · exact hDN2.trans ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) 2).trans h2)
    · have : r ^ (n - 1) * (N * q) * n = ((N : ℤ) * n) * (r ^ (n - 1) * q) := by ring
      rw [this]; exact dvd_mul_of_dvd_left hDN _
  have hcop : IsCoprime D ((a : ℤ) ^ n - 1) := by
    apply IsCoprime.pow_left
    exact (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp.out).irreducible).2 hprim
  exact hcop.dvd_of_dvd_mul_left key

/-- Splitting the full power sum according to divisibility by `p`. -/
private lemma psS_succ (n e : ℕ) (_hn : 0 < n) :
    psS (p := p) n (e + 1) = psT (p := p) n (e + 1) + (p : ℤ) ^ n * psS (p := p) n e := by
  unfold psS psT
  rw [← sum_filter_add_sum_filter_not (range (p ^ (e + 1))) (fun j => p ∣ j), add_comm]
  congr 1
  rw [mul_sum]
  have : (range (p ^ (e + 1))).filter (fun j => p ∣ j) = (range (p ^ e)).map
      ⟨fun i => p * i, fun x y h => Nat.eq_of_mul_eq_mul_left hp.out.pos h⟩ := by
    ext j
    simp only [mem_filter, mem_range, mem_map]
    constructor
    · rintro ⟨hj, ⟨i, rfl⟩⟩
      refine ⟨i, ?_, rfl⟩
      rw [pow_succ'] at hj
      exact Nat.lt_of_mul_lt_mul_left hj
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_left hi hp.out.pos
  rw [this, sum_map]
  refine sum_congr rfl (fun i _ => ?_)
  show (((p * i : ℕ) : ℤ)) ^ n = _
  push_cast; ring

/-- `p^(e + min(v_p(n), e))` divides `∑_{j < p^e} j^n` when `a^n ≢ 1 (mod p)`. -/
private lemma psS_dvd (a n : ℕ) (hn : 0 < n) (ha : ¬ p ∣ a) (hprim : ¬ (p : ℤ) ∣ (a : ℤ) ^ n - 1) (e : ℕ) :
    (p : ℤ) ^ (e + min (padicValNat p n) e) ∣ psS (p := p) n e := by
  induction e with
  | zero => simp [psS, zero_pow hn.ne']
  | succ e ih =>
    rw [psS_succ n e hn]
    refine dvd_add (psT_dvd a n (e + 1) ha hprim) ?_
    have hle : e + 1 + min (padicValNat p n) (e + 1) ≤ n + (e + min (padicValNat p n) e) := by
      rcases le_or_gt (padicValNat p n) e with h | h
      · rw [min_eq_left h, min_eq_left (by omega)]; omega
      · rw [min_eq_right h.le, min_eq_right (by omega)]
        have : 2 ≤ n := by
          have h1 : 1 ≤ padicValNat p n := by omega
          have h2 : p ∣ n := dvd_of_one_le_padicValNat h1
          have := Nat.le_of_dvd hn h2
          have := hp.out.two_le
          omega
        omega
    exact (pow_dvd_pow _ hle).trans (by rw [pow_add]; exact mul_dvd_mul_left _ ih)

end PowerSums

section Adams
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- `|m|_p = p^(-v_p(m))` for `m > 0`. -/
private lemma padicNorm_natCast_eq (m : ℕ) (hm : 0 < m) :
    padicNorm p (m : ℚ) = ((p : ℚ) ^ (padicValNat p m))⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm.ne'), padicValRat.of_nat, zpow_neg,
    zpow_natCast]

/-- `|p^e|_p = p^(-e)`. -/
private lemma padicNorm_prime_pow (e : ℕ) : padicNorm p ((p : ℚ) ^ e) = ((p : ℚ) ^ e)⁻¹ := by
  have := padicNorm_natCast_eq (p := p) (p ^ e) (pow_pos hp.out.pos e)
  rw [padicValNat.prime_pow] at this
  exact_mod_cast this

/-- `|1/m|_p ≤ m` for `m > 0`. -/
private lemma padicNorm_one_div_nat_le (m : ℕ) (hm : 0 < m) : padicNorm p (1 / (m : ℚ)) ≤ m := by
  rw [padicNorm.div, padicNorm.one, padicNorm_natCast_eq m hm, one_div, inv_inv]
  exact_mod_cast Nat.le_of_dvd hm pow_padicValNat_dvd

/-- If `p^k ∣ z` then `|z|_p ≤ p^(-k)`. -/
private lemma padicNorm_int_le_of_dvd (z : ℤ) (k : ℕ) (h : (p : ℤ) ^ k ∣ z) :
    padicNorm p (z : ℚ) ≤ ((p : ℚ) ^ k)⁻¹ := by
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := k) (z := z)).1 (by exact_mod_cast h)
  rwa [zpow_neg, zpow_natCast] at this

/-- An elementary size estimate used in the proof of Adams' theorem. -/
private lemma aux_big (n q : ℕ) (hq : 2 ≤ q) : n * (n + 1) * q ≤ q ^ (n * (n + 1) + 1) := by
  rw [pow_succ]
  apply Nat.mul_le_mul_right
  have h2 : n * (n + 1) < 2 ^ (n * (n + 1)) := Nat.lt_two_pow_self
  have h3 : 2 ^ (n * (n + 1)) ≤ q ^ (n * (n + 1)) := Nat.pow_le_pow_left hq _
  omega

/-- **Adams' theorem** (the case needed here): if `p - 1 ∤ n` then `B_n / n` is `p`-integral. Proof: a Voronoi-type congruence for power sums modulo `p^e` and Faulhaber's formula. -/
private theorem adams (n : ℕ) (h : ¬ (p - 1) ∣ n) : padicNorm p (bernoulli n / n) ≤ 1 := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h'
    · exact absurd (dvd_zero _) h
    · exact h'
  obtain ⟨a, ha, hprim⟩ := exists_prim_root (p := p)
  have hprim' : ¬ (p : ℤ) ∣ (a : ℤ) ^ n - 1 := fun hd => h (hprim n hd)
  set e := n * (n + 1) + 1 with he
  set ν := padicValNat p n with hν
  have hνe : ν ≤ e := by
    have h1 := padicValNat_le_nat_log (p := p) n
    have h2 : Nat.log p n ≤ n := (Nat.log_lt_self p hn.ne').le
    have : n ≤ e := by rw [he]; nlinarith
    omega
  have hS := psS_dvd (p := p) a n hn ha hprim' e
  rw [min_eq_left hνe] at hS
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  set N : ℚ := (p : ℚ) ^ e with hN
  have hN0 : N ≠ 0 := by positivity
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hSQ : ((psS (p := p) n e : ℤ) : ℚ) = ∑ k ∈ range (p ^ e), (k : ℚ) ^ n := by
    unfold psS; push_cast; rfl
  have hF := sum_range_pow (p ^ e) n
  rw [← hSQ, sum_range_succ, Nat.choose_succ_self_right, Nat.add_sub_cancel_left] at hF
  push_cast at hF
  have key : bernoulli n / n = (psS (p := p) n e : ℚ) / (n * N) -
      ∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * N ^ (n - i) * (1 / (n * (n + 1))) := by
    rw [hF, add_div, sum_div]
    have hsum : ∑ i ∈ range n,
        bernoulli i * ((n + 1).choose i : ℚ) * N ^ (n + 1 - i) / (n + 1) / (n * N) =
        ∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * N ^ (n - i) * (1 / (n * (n + 1))) := by
      refine sum_congr rfl (fun i hi => ?_)
      have hi' : i < n := mem_range.1 hi
      rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
      field_simp
    rw [hsum]
    field_simp
    ring
  rw [key]
  refine le_trans padicNorm.sub (max_le ?_ ?_)
  · rw [padicNorm.div, padicNorm.mul, padicNorm_natCast_eq n hn, hN, padicNorm_prime_pow]
    have h1 := padicNorm_int_le_of_dvd (p := p) _ _ hS
    rw [div_le_one (by positivity)]
    calc padicNorm p (psS (p := p) n e : ℚ) ≤ ((p : ℚ) ^ (e + ν))⁻¹ := h1
      _ = ((p : ℚ) ^ ν)⁻¹ * ((p : ℚ) ^ e)⁻¹ := by rw [pow_add, mul_inv, mul_comm]
  · refine padicNorm.sum_le' (fun i hi => ?_) zero_le_one
    have hi' : i < n := mem_range.1 hi
    rw [padicNorm.mul, padicNorm.mul, padicNorm.mul]
    have hB := bern_norm_le_p (p := p) i
    have hC := padicNorm.of_nat (p := p) ((n + 1).choose i)
    have hNp : padicNorm p (N ^ (n - i)) ≤ ((p : ℚ) ^ e)⁻¹ := by
      rw [hN, ← pow_mul, padicNorm_prime_pow]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ (by exact_mod_cast hp.out.one_lt.le)
      have : 1 ≤ n - i := by omega
      nlinarith
    have hD : padicNorm p (1 / ((n : ℚ) * (n + 1))) ≤ (n * (n + 1) : ℕ) := by
      have := padicNorm_one_div_nat_le (p := p) (n * (n + 1)) (by positivity)
      push_cast at this ⊢; exact this
    have hbig : ((n * (n + 1) : ℕ) : ℚ) * p ≤ (p : ℚ) ^ e := by
      have := aux_big n p hp.out.two_le
      rw [← he] at this
      exact_mod_cast this
    have hpe : (0 : ℚ) < (p : ℚ) ^ e := by positivity
    calc padicNorm p (bernoulli i) * padicNorm p ((n + 1).choose i : ℚ) *
          padicNorm p (N ^ (n - i)) * padicNorm p (1 / ((n : ℚ) * (n + 1)))
        ≤ (p : ℚ) * 1 * ((p : ℚ) ^ e)⁻¹ * ((n * (n + 1) : ℕ) : ℚ) := by
          have hp0' : (0 : ℚ) ≤ p := hp0.le
          refine mul_le_mul (mul_le_mul (mul_le_mul hB hC (padicNorm.nonneg _) hp0') hNp
            (padicNorm.nonneg _) (by positivity)) hD (padicNorm.nonneg _) (by positivity)
      _ ≤ 1 := by
          rw [mul_one, mul_comm _ (((n * (n + 1) : ℕ) : ℚ)), ← mul_assoc,
            ← div_eq_mul_inv, div_le_one hpe]
          exact hbig

end Adams

section Series
open PowerSeries Finset

/-- `G k = B_k / k!`, the coefficients of `t / (e^t - 1)`. -/
private noncomputable def G (k : ℕ) : ℚ := bernoulli k / k.factorial
/-- The power series `G = t/(e^t - 1) = ∑ B_k t^k / k!`. -/
private noncomputable def Gs : ℚ⟦X⟧ := PowerSeries.mk G
/-- The power series `(e^t - 1)/t = ∑ t^k/(k+1)!`. -/
private noncomputable def Es : ℚ⟦X⟧ := PowerSeries.mk (fun k => 1 / ((k + 1).factorial : ℚ))
/-- The coefficients `h_k` of `h = log(t/(e^t - 1))`: `h_1 = -1/2` and `h_k = -B_k/(k·k!)` otherwise. -/
private noncomputable def hcoef (k : ℕ) : ℚ := if k = 1 then -1 / 2 else -G k / k
/-- The power series `h = log(t/(e^t - 1))`. -/
private noncomputable def hs : ℚ⟦X⟧ := PowerSeries.mk hcoef

/-- `Gs` is Mathlib's `bernoulliPowerSeries`. -/
private lemma Gs_eq : Gs = bernoulliPowerSeries ℚ := by
  ext n; simp [Gs, bernoulliPowerSeries, G]

/-- `e^t - 1 = t · Es`. -/
private lemma exp_sub_one_eq : exp ℚ - 1 = X * Es := by
  ext n
  cases n with
  | zero => simp [Es]
  | succ n =>
    rw [coeff_succ_X_mul]
    simp [Es, coeff_exp]

/-- `G · Es = 1`. -/
private lemma Gs_mul_Es : Gs * Es = 1 := by
  have h := bernoulliPowerSeries_mul_exp_sub_one ℚ
  rw [← Gs_eq, exp_sub_one_eq] at h
  have hX : (X : ℚ⟦X⟧) ≠ 0 := X_ne_zero
  apply mul_left_cancel₀ hX
  calc X * (Gs * Es) = Gs * (X * Es) := by ring
    _ = X := h
    _ = X * 1 := (mul_one _).symm

/-- `t Es' = 1 + t Es - Es`. -/
private lemma X_Es' : X * d⁄dX ℚ Es = 1 + X * Es - Es := by
  ext n
  rcases n with _ | n
  · simp [Es]
  · rw [coeff_succ_X_mul, coeff_derivative, map_sub, map_add, coeff_succ_X_mul]
    simp only [Es, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false, zero_add]
    rw [Nat.factorial_succ (n + 1)]
    have h1 : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- `t G' = G - t G - G²` for `G = t/(e^t - 1)`. -/
private lemma X_Gs' : X * d⁄dX ℚ Gs = Gs - X * Gs - Gs ^ 2 := by
  have h1 := Gs_mul_Es
  have h2 : Gs * d⁄dX ℚ Es + Es * d⁄dX ℚ Gs = 0 := by
    have := (d⁄dX ℚ).leibniz Gs Es
    rw [h1, derivative_one] at this
    simpa [smul_eq_mul] using this.symm
  have h3 := X_Es'
  linear_combination (-(X * d⁄dX ℚ Gs - Gs + X * Gs)) * h1 + (X * Gs) * h2 + (-Gs ^ 2) * h3

/-- `G_0 = 1`. -/
private lemma G_zero : G 0 = 1 := by simp [G]
/-- `G_1 = -1/2`. -/
private lemma G_one : G 1 = -1 / 2 := by simp [G, bernoulli_one]

/-- `t h' = 1 - t - G`. -/
private lemma X_hs' : X * d⁄dX ℚ hs = 1 - X - Gs := by
  ext n
  rcases n with _ | n
  · simp [Gs, G_zero]
  · rw [coeff_succ_X_mul, coeff_derivative]
    rcases n with _ | n
    · simp [hs, hcoef, Gs, G_one, coeff_X]; norm_num
    · simp only [hs, Gs, coeff_mk, map_sub, coeff_one, coeff_X, hcoef]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        show n + 1 + 1 ≠ 1 by omega, zero_sub]
      have : ((n + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      push_cast at this ⊢
      field_simp
      ring

/-- `G' = h' G`, i.e. `h = log G`. -/
private lemma Gs'_eq : d⁄dX ℚ Gs = d⁄dX ℚ hs * Gs := by
  have hX : (X : ℚ⟦X⟧) ≠ 0 := X_ne_zero
  apply mul_left_cancel₀ hX
  rw [X_Gs', ← mul_assoc, X_hs']; ring

/-- `(G^N)' = N h' G^N`. -/
private lemma Gs_pow_deriv (N : ℕ) : d⁄dX ℚ (Gs ^ N) = (N : ℚ⟦X⟧) * d⁄dX ℚ hs * Gs ^ N := by
  rw [derivative_pow, Gs'_eq]
  rcases N with _ | N
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]; push_cast; ring

/-- Uniqueness for the linear differential equation `Y' = c Y` over `ℚ`. -/
private lemma ode_unique (A B c : ℚ⟦X⟧) (h0 : constantCoeff A = constantCoeff B)
    (hA : d⁄dX ℚ A = c * A) (hB : d⁄dX ℚ B = c * B) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa using h0
    · have eA := coeff_derivative A n
      have eB := coeff_derivative B n
      rw [hA, coeff_mul] at eA
      rw [hB, coeff_mul] at eB
      have hsum : ∑ x ∈ antidiagonal n, coeff x.1 c * coeff x.2 A =
          ∑ x ∈ antidiagonal n, coeff x.1 c * coeff x.2 B := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [ih x.2 (by have := mem_antidiagonal.1 hx; omega)]
      have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
      have := eA.symm.trans (hsum.trans eB)
      exact mul_right_cancel₀ hn this

/-- `h(0) = 0`. -/
private lemma constantCoeff_hs : constantCoeff hs = 0 := by
  simp [hs, hcoef, G_zero]

/-- `[t^n] h^k = 0` for `n < k`. -/
private lemma coeff_hs_pow_eq_zero (k n : ℕ) (h : n < k) : coeff n (hs ^ k) = 0 := by
  have h1 : (X : ℚ⟦X⟧) ∣ hs := X_dvd_iff.2 constantCoeff_hs
  have h2 : (X : ℚ⟦X⟧) ^ k ∣ hs ^ k := pow_dvd_pow_of_dvd h1 k
  exact X_pow_dvd_iff.1 h2 n h

/-- The power series `exp(c h) = ∑_k c^k h^k / k!`. -/
private noncomputable def Ys (c : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n => ∑ k ∈ range (n + 1), c ^ k * coeff n (hs ^ k) / k.factorial)

/-- The truncation `∑_{k ≤ M} c^k h^k / k!` of `exp(c h)`. -/
private noncomputable def Zs (c : ℚ) (M : ℕ) : ℚ⟦X⟧ :=
  ∑ k ∈ range (M + 1), PowerSeries.C (c ^ k / k.factorial) * hs ^ k

/-- The truncations of `exp(c h)` agree with `exp(c h)` in low degree. -/
private lemma coeff_Zs (c : ℚ) (M n : ℕ) (h : n ≤ M) : coeff n (Zs c M) = coeff n (Ys c) := by
  simp only [Zs, Ys, map_sum, coeff_C_mul, coeff_mk]
  have : range (M + 1) = range (n + 1) ∪ Ico (n + 1) (M + 1) := by
    ext k; simp only [mem_range, mem_union, mem_Ico]; omega
  rw [this, sum_union (by
    rw [range_eq_Ico]; exact Ico_disjoint_Ico_consecutive _ _ _)]
  rw [sum_eq_zero (s := Ico (n + 1) (M + 1)), add_zero]
  · refine sum_congr rfl (fun k _ => by ring)
  · intro k hk
    rw [coeff_hs_pow_eq_zero k n (by simp at hk; omega), mul_zero]

/-- Derivative of the truncated exponential. -/
private lemma Zs_deriv (c : ℚ) (M : ℕ) :
    d⁄dX ℚ (Zs c (M + 1)) = PowerSeries.C c * d⁄dX ℚ hs * Zs c M := by
  simp only [Zs, map_sum, Derivation.leibniz, derivative_C, smul_eq_mul, derivative_pow]
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  refine sum_congr rfl (fun k _ => ?_)
  have hk : ((k + 1).factorial : ℚ) = (k + 1) * k.factorial := by
    push_cast [Nat.factorial_succ]; ring
  rw [hk]
  have : PowerSeries.C (c ^ (k + 1) / ((k + 1) * (k.factorial : ℚ))) * ((k + 1 : ℕ) : ℚ⟦X⟧) =
      PowerSeries.C c * PowerSeries.C (c ^ k / k.factorial) := by
    rw [← map_mul, ← map_natCast (PowerSeries.C (R := ℚ)), ← map_mul]
    congr 1
    have : (k.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  calc PowerSeries.C (c ^ (k + 1) / ((k + 1) * (k.factorial : ℚ))) *
        (((k + 1 : ℕ) : ℚ⟦X⟧) * hs ^ k * d⁄dX ℚ hs)
      = (PowerSeries.C (c ^ (k + 1) / ((k + 1) * (k.factorial : ℚ))) * ((k + 1 : ℕ) : ℚ⟦X⟧)) *
          hs ^ k * d⁄dX ℚ hs := by ring
    _ = _ := by rw [this]; ring

/-- `exp(c h)' = c h' exp(c h)`. -/
private lemma Ys_deriv (c : ℚ) : d⁄dX ℚ (Ys c) = PowerSeries.C c * d⁄dX ℚ hs * Ys c := by
  ext n
  rw [coeff_derivative, ← coeff_Zs c (n + 1) (n + 1) le_rfl, ← coeff_derivative, Zs_deriv,
    coeff_mul, coeff_mul]
  refine sum_congr rfl (fun x hx => ?_)
  rw [coeff_Zs c n x.2 (by have := mem_antidiagonal.1 hx; omega)]

/-- `exp(c h)(0) = 1`. -/
private lemma constantCoeff_Ys (c : ℚ) : constantCoeff (Ys c) = 1 := by
  simp [Ys]

/-- `exp(N h) = G^N` for natural `N`. -/
private lemma Ys_nat (N : ℕ) : Ys N = Gs ^ N := by
  apply ode_unique _ _ (PowerSeries.C (N : ℚ) * d⁄dX ℚ hs)
  · rw [constantCoeff_Ys, map_pow]; simp [Gs, G_zero]
  · exact Ys_deriv N
  · rw [Gs_pow_deriv]; simp

end Series

section Valuations
open Finset

/-- `V_p(n) = q + v_p(q!)` with `q = ⌊n/(p-1)⌋`: the exponent of `p` in `A053657(n+1)`. -/
private def Vp (p n : ℕ) : ℕ := n / (p - 1) + padicValNat p (n / (p - 1)).factorial

/-- The bound `w_p(i) = v_p(i!) + [p-1 ∣ i](1 + v_p(i))` for `-v_p(h_i)`. -/
private def wp (p i : ℕ) : ℕ := padicValNat p i.factorial + if (p - 1) ∣ i then 1 + padicValNat p i else 0

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p` is monotone along divisibility. -/
private lemma padicValNat_mono {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) : padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).1 ((pow_padicValNat_dvd).trans hab)

/-- `v_p(a!) ≤ v_p(b!)` for `a ≤ b`. -/
private lemma padicValNat_fact_mono {a b : ℕ} (hab : a ≤ b) :
    padicValNat p a.factorial ≤ padicValNat p b.factorial :=
  padicValNat_mono (Nat.factorial_dvd_factorial hab) (Nat.factorial_ne_zero _)

/-- `v_p(a!) + v_p(b!) ≤ v_p((a+b)!)`. -/
private lemma padicValNat_fact_add (a b : ℕ) :
    padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p (a + b).factorial := by
  rw [← padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  exact padicValNat_mono (Nat.factorial_mul_factorial_dvd_factorial_add a b) (Nat.factorial_ne_zero _)

/-- `V_p` is monotone. -/
private lemma Vp_mono {a b : ℕ} (h : a ≤ b) : Vp p a ≤ Vp p b := by
  unfold Vp
  have : a / (p - 1) ≤ b / (p - 1) := Nat.div_le_div_right h
  have := padicValNat_fact_mono (p := p) this
  omega

/-- `V_p` is superadditive. -/
private lemma Vp_add (a b : ℕ) : Vp p a + Vp p b ≤ Vp p (a + b) := by
  unfold Vp
  have h1 := (Nat.div_add_div_le_add_div (x := a) (y := b) (z := p - 1))
  have h2 := padicValNat_fact_add (p := p) (a / (p - 1)) (b / (p - 1))
  have h3 := padicValNat_fact_mono (p := p) h1
  omega

/-- `(Q!)^m m! ∣ (mQ)!` for `Q > 0`. -/
private lemma fact_pow_mul_dvd (Q m : ℕ) (hQ : 0 < Q) :
    Q.factorial ^ m * m.factorial ∣ (m * Q).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (m * Q).factorial * Q.factorial * ((m + 1) * Q).choose Q = ((m + 1) * Q).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (n := (m + 1) * Q) (k := Q) (by nlinarith)
      rw [show (m + 1) * Q - Q = m * Q by rw [add_mul, one_mul, Nat.add_sub_cancel]] at this
      rw [← this]; ring
    have h2 : (m + 1) ∣ ((m + 1) * Q).choose Q := by
      have := Nat.add_one_mul_choose_eq ((m + 1) * Q - 1) (Q - 1)
      rw [show (m + 1) * Q - 1 + 1 = (m + 1) * Q by
        have : 1 ≤ (m + 1) * Q := by nlinarith
        omega, show Q - 1 + 1 = Q by omega] at this
      -- this : (m+1)*Q * choose ((m+1)Q-1) (Q-1) = choose ((m+1)Q) Q * Q
      have h3 : (m + 1) * (((m + 1) * Q - 1).choose (Q - 1)) * Q = ((m + 1) * Q).choose Q * Q := by
        rw [← this]; ring
      exact ⟨_, (Nat.eq_of_mul_eq_mul_right hQ h3).symm⟩
    obtain ⟨c, hc⟩ := h2
    rw [← h1, hc, Nat.factorial_succ, pow_succ]
    obtain ⟨d, hd⟩ := ih
    rw [hd]
    exact ⟨d * c, by ring⟩

/-- `m V_p(i) + v_p(m!) ≤ V_p(i m)`. -/
private lemma Vp_mul (i m : ℕ) (hi : 0 < i) :
    m * Vp p i + padicValNat p m.factorial ≤ Vp p (i * m) := by
  unfold Vp
  set Q := i / (p - 1)
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQ
  · rw [hQ0]
    simp only [Nat.factorial_zero, padicValNat_one_right, add_zero, mul_zero, zero_add]
    have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
    have h1 := sub_one_mul_padicValNat_factorial (p := p) m
    have h2 : padicValNat p m.factorial ≤ i * m / (p - 1) := by
      rw [Nat.le_div_iff_mul_le hp1, mul_comm, h1]
      have : m ≤ i * m := Nat.le_mul_of_pos_left m hi
      omega
    omega
  have h1 : m * Q ≤ i * m / (p - 1) := by
    rcases Nat.eq_zero_or_pos (p - 1) with h0 | h0
    · simp [Q, h0]
    rw [Nat.le_div_iff_mul_le h0]
    have : Q * (p - 1) ≤ i := Nat.div_mul_le_self i (p - 1)
    nlinarith
  have h2 : m * padicValNat p Q.factorial + padicValNat p m.factorial ≤
      padicValNat p (m * Q).factorial := by
    have := padicValNat_mono (p := p) (fact_pow_mul_dvd Q m hQ) (Nat.factorial_ne_zero _)
    rw [padicValNat.mul (pow_ne_zero _ (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      padicValNat.pow] at this
    exact this
  have h3 := padicValNat_fact_mono (p := p) h1
  nlinarith

/-- The base-`p` digit sum of a positive number is positive. -/
private lemma digits_sum_pos {i : ℕ} (hi : i ≠ 0) : 0 < (p.digits i).sum := by
  have h1 := sub_one_mul_padicValNat_factorial (p := p) i
  have h2 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hi
  omega

/-- If `p - 1 ∣ i > 0` then the base-`p` digit sum of `i` is at least `p - 1`. -/
private lemma digits_sum_ge {i : ℕ} (hi : i ≠ 0) (hd : (p - 1) ∣ i) : p - 1 ≤ (p.digits i).sum := by
  have hpos := digits_sum_pos (p := p) hi
  rcases Nat.lt_or_ge p 3 with h3 | h3
  · have := hp.out.two_le; omega
  · have hmod : i ≡ (p.digits i).sum [MOD (p - 1)] :=
      Nat.modEq_digits_sum (p - 1) p (by
        have h1 : 1 ≡ p [MOD p - 1] := (Nat.modEq_iff_dvd' (by omega)).2 (by
          rw [show p - 1 = p - 1 from rfl])
        unfold Nat.ModEq at h1
        rw [← h1]; exact Nat.mod_eq_of_lt (by omega)) i
    have : (p - 1) ∣ (p.digits i).sum := (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans
      (Nat.modEq_zero_iff_dvd.2 hd)))
    exact Nat.le_of_dvd hpos this

/-- `v_p(((p-1)Q)!) ≤ Q - 1` for `Q > 0`. -/
private lemma padicValNat_fact_mul_le (Q : ℕ) (hQ : 0 < Q) :
    padicValNat p ((p - 1) * Q).factorial + 1 ≤ Q := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have h1 := sub_one_mul_padicValNat_factorial (p := p) ((p - 1) * Q)
  have h2 := digits_sum_ge (p := p) (i := (p - 1) * Q) (by positivity) (dvd_mul_right _ _)
  have h3 : (p - 1) * padicValNat p ((p - 1) * Q).factorial ≤ (p - 1) * (Q - 1) := by
    rw [h1, Nat.mul_sub, mul_one]; omega
  have := Nat.le_of_mul_le_mul_left h3 hp1
  omega

/-- `v_p((p-1)Q) = v_p(Q)`. -/
private lemma padicValNat_sub_one_mul (Q : ℕ) (hQ : 0 < Q) :
    padicValNat p ((p - 1) * Q) = padicValNat p Q := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  rw [padicValNat.mul hp1 hQ.ne', padicValNat.eq_zero_of_not_dvd, zero_add]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- `w_p(i) ≤ V_p(i)`. -/
private lemma wp_le_Vp (i : ℕ) (hi : 0 < i) : wp p i ≤ Vp p i := by
  unfold wp Vp
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  split_ifs with hd
  · obtain ⟨Q, rfl⟩ := hd
    have hQ : 0 < Q := by
      rcases Nat.eq_zero_or_pos Q with h | h
      · simp [h] at hi
      · exact h
    rw [Nat.mul_div_cancel_left _ hp1, padicValNat_sub_one_mul Q hQ]
    have h1 := padicValNat_fact_mul_le (p := p) Q hQ
    have h2 : padicValNat p Q ≤ padicValNat p Q.factorial :=
      padicValNat_mono (Nat.dvd_factorial hQ le_rfl) (Nat.factorial_ne_zero _)
    omega
  · have h1 := sub_one_mul_padicValNat_factorial (p := p) i
    have : padicValNat p i.factorial ≤ i / (p - 1) := by
      rw [Nat.le_div_iff_mul_le hp1, mul_comm, h1]; omega
    omega

/-- `w_p(1) = 0` for odd `p`. -/
private lemma wp_one (h2 : p ≠ 2) : wp p 1 = 0 := by
  unfold wp
  have : ¬ (p - 1) ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd one_pos hd
    have := hp.out.two_le
    omega
  simp [this]

/-- `w_p(p-1) = 1` for odd `p`. -/
private lemma wp_sub_one (h2 : p ≠ 2) : wp p (p - 1) = 1 := by
  unfold wp
  have h3 : 3 ≤ p := by have := hp.out.two_le; omega
  rw [if_pos dvd_rfl, padicValNat.eq_zero_of_not_dvd (n := p - 1), padicValNat.eq_zero_of_not_dvd]
  · intro hd
    exact (Nat.Prime.dvd_factorial hp.out).not.mpr (by omega) hd
  · intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega

omit hp in
/-- `(p-2) v < p^v - 1` for `v > 0` and `p ≥ 3`. -/
private lemma pow_bound (v : ℕ) (hv : 0 < v) (hp3 : 3 ≤ p) : (p - 2) * v < p ^ v - 1 := by
  have := one_add_mul_le_pow (a := ((p : ℤ) - 1)) (by omega) v
  have h : (1 : ℤ) + v * ((p : ℤ) - 1) ≤ (p : ℤ) ^ v := by simpa using this
  have h2 : (p - 2) * v + 1 < p ^ v := by
    zify [show 2 ≤ p by omega]
    nlinarith
  omega

/-- For odd `p` and `i ≥ 2`, `i ≠ p - 1`: `(p-2) w_p(i) < i - 1` (strictness for the lower bound). -/
private lemma wp_strict (h2 : p ≠ 2) (i : ℕ) (hi : 2 ≤ i) (hne : i ≠ p - 1) :
    (p - 2) * wp p i < i - 1 := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hp1 : 0 < p - 1 := by omega
  unfold wp
  split_ifs with hd
  · obtain ⟨Q, rfl⟩ := hd
    have hQ : 2 ≤ Q := by
      rcases Nat.lt_or_ge Q 2 with h | h
      · interval_cases Q
        · simp at hi
        · simp at hne
      · exact h
    rw [padicValNat_sub_one_mul Q (by omega)]
    have h1 := padicValNat_fact_mul_le (p := p) Q (by omega)
    -- need (p-2) * (v + 1 + vQ) < (p-1)Q - 1 where v + 1 ≤ Q
    have h3 : (p - 2) * padicValNat p Q < Q - 1 := by
      rcases Nat.eq_zero_or_pos (padicValNat p Q) with h0 | h0
      · rw [h0]; omega
      · have h4 := pow_bound (p := p) _ h0 hp3
        have h5 : p ^ padicValNat p Q ≤ Q := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
        omega
    have e1 : (p - 2) * (padicValNat p ((p - 1) * Q).factorial + (1 + padicValNat p Q)) ≤
        (p - 2) * (Q + padicValNat p Q) := Nat.mul_le_mul_left _ (by omega)
    have e2 : (p - 2) * (Q + padicValNat p Q) = (p - 2) * Q + (p - 2) * padicValNat p Q := by ring
    have e3 : (p - 1) * Q = (p - 2) * Q + Q := by
      rw [show p - 1 = (p - 2) + 1 by omega]; ring
    omega
  · have h1 := sub_one_mul_padicValNat_factorial (p := p) i
    have h2' := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : i ≠ 0)
    simp only [add_zero]
    set v := padicValNat p i.factorial
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · rw [h0]; omega
    · have e3 : (p - 1) * v = (p - 2) * v + v := by
        rw [show p - 1 = (p - 2) + 1 by omega]; ring
      omega

end Valuations

section UpperBound
open PowerSeries Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `|1/m!|_p = p^(v_p(m!))`. -/
private lemma padicNorm_one_div_fact (m : ℕ) :
    padicNorm p (1 / (m.factorial : ℚ)) = (p : ℚ) ^ padicValNat p m.factorial := by
  rw [padicNorm.div, padicNorm.one, padicNorm_natCast_eq _ (Nat.factorial_pos m), one_div, inv_inv]

/-- `|1/m|_p = p^(v_p(m))`. -/
private lemma padicNorm_one_div_nat (m : ℕ) (hm : 0 < m) :
    padicNorm p (1 / (m : ℚ)) = (p : ℚ) ^ padicValNat p m := by
  rw [padicNorm.div, padicNorm.one, padicNorm_natCast_eq _ hm, one_div, inv_inv]

/-- `|a^n|_p = |a|_p^n`. -/
private lemma padicNorm_pow (a : ℚ) (n : ℕ) : padicNorm p (a ^ n) = padicNorm p a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

/-- `|h_i|_p ≤ p^(w_p(i))`, from von Staudt–Clausen and Adams' theorem. -/
private lemma hcoef_norm_le (i : ℕ) (hi : 0 < i) : padicNorm p (hcoef i) ≤ (p : ℚ) ^ wp p i := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rcases Nat.eq_or_lt_of_le hi with h1 | h2
  · subst h1
    simp only [hcoef, if_true]
    rw [show (-1 / 2 : ℚ) = -(2 : ℚ)⁻¹ by ring, padicNorm.neg]
    by_cases hp2 : p = 2
    · subst hp2
      have : wp 2 1 = 1 := by simp [wp]
      rw [this, pow_one]; exact padicNorm_two_inv_le
    · rw [padicNorm_two_inv_odd hp2]; exact one_le_pow₀ hp1
  · have hne : i ≠ 1 := by omega
    have heq : hcoef i = -(bernoulli i / i) * (1 / (i.factorial : ℚ)) := by
      simp only [hcoef, hne, if_false, G]; ring
    rw [heq, padicNorm.mul, padicNorm.neg, padicNorm_one_div_fact]
    unfold wp
    split_ifs with hd
    · rw [div_eq_mul_one_div, padicNorm.mul, padicNorm_one_div_nat i hi, pow_add, pow_add,
        pow_one]
      have hB := bern_norm_le_p (p := p) i
      have : padicNorm p (bernoulli i) * (p : ℚ) ^ padicValNat p i * (p : ℚ) ^ padicValNat p i.factorial
          ≤ (p : ℚ) * (p : ℚ) ^ padicValNat p i * (p : ℚ) ^ padicValNat p i.factorial := by
        gcongr
      linarith
    · have hA := adams (p := p) i hd
      rw [add_zero]
      calc padicNorm p (bernoulli i / i) * (p : ℚ) ^ padicValNat p i.factorial
          ≤ 1 * (p : ℚ) ^ padicValNat p i.factorial := by gcongr
        _ = _ := one_mul _

/-- `|h_{p-1}|_p = p` for odd `p`. -/
private lemma hcoef_norm_pm1 (h2 : p ≠ 2) : padicNorm p (hcoef (p - 1)) = p := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hne : p - 1 ≠ 1 := by omega
  have heq : hcoef (p - 1) = -(bernoulli (p - 1)) * (1 / ((p - 1 : ℕ) : ℚ)) *
      (1 / ((p - 1).factorial : ℚ)) := by
    simp only [hcoef, hne, if_false, G]; ring
  have hev : Even (p - 1) := by
    rcases hp.out.eq_two_or_odd' with h | h
    · exact absurd h h2
    · exact Nat.Odd.sub_odd h odd_one
  rw [heq, padicNorm.mul, padicNorm.mul, padicNorm.neg,
    bern_norm_eq_p (p - 1) dvd_rfl hev (by omega), padicNorm_one_div_fact,
    padicNorm_one_div_nat _ (by omega)]
  rw [padicValNat.eq_zero_of_not_dvd (n := p - 1), padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro hd
    exact (Nat.Prime.dvd_factorial hp.out).not.mpr (by omega) hd
  · intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- The truncation `∑_{i ≤ j} h_i t^i`. -/
private noncomputable def hsT (j : ℕ) : ℚ⟦X⟧ := PowerSeries.mk (fun i => if i ≤ j then hcoef i else 0)

/-- `h_0 = 0`. -/
private lemma hcoef_zero : hcoef 0 = 0 := by simp [hcoef]

/-- The truncation `h_{≤ 0}` is `0`. -/
private lemma hsT_zero : hsT 0 = 0 := by
  ext i; simp only [hsT, coeff_mk, map_zero]
  split_ifs with h
  · have : i = 0 := by omega
    subst this; exact hcoef_zero
  · rfl

/-- Adding one more term to the truncation. -/
private lemma hsT_succ (j : ℕ) :
    hsT (j + 1) = hsT j + PowerSeries.C (hcoef (j + 1)) * X ^ (j + 1) := by
  ext i
  simp only [hsT, coeff_mk, map_add, coeff_C_mul_X_pow]
  split_ifs <;> first | omega | simp_all

/-- Upper bound `|[t^n] (h_{≤ j})^k / k!|_p ≤ p^(V_p(n))`, by induction on the largest part `j` (multinomial expansion). -/
private lemma upper_hsT (j : ℕ) : ∀ n k : ℕ,
    padicNorm p (coeff n (hsT j ^ k) / k.factorial) ≤ (p : ℚ) ^ Vp p n := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  induction j with
  | zero =>
    intro n k
    rw [hsT_zero]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, coeff_one]
      split_ifs
      · rw [padicNorm.one]; exact one_le_pow₀ hp1
      · rw [padicNorm.zero]; positivity
    · rw [zero_pow hk.ne']; simp
  | succ j ih =>
    intro n k
    rw [hsT_succ, add_pow, map_sum, sum_div]
    refine padicNorm.sum_le' (fun m hm => ?_) (by positivity)
    have hm' : m ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hm)
    set J := (j + 1) * (k - m)
    have hy : (PowerSeries.C (hcoef (j + 1)) * X ^ (j + 1)) ^ (k - m) =
        PowerSeries.C (hcoef (j + 1) ^ (k - m)) * X ^ J := by
      rw [mul_pow, ← map_pow, ← pow_mul]
    rw [hy]
    have hcho : ((k.choose m : ℕ) : ℚ) / k.factorial = 1 / (m.factorial * (k - m).factorial) := by
      rw [Nat.choose_eq_factorial_div_factorial hm', Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hm')
        (by positivity)]
      push_cast
      field_simp
    have hcoeff : coeff n (hsT j ^ m * (PowerSeries.C (hcoef (j + 1) ^ (k - m)) * X ^ J) *
        ((k.choose m : ℕ) : ℚ⟦X⟧)) / k.factorial =
        (if J ≤ n then (coeff (n - J) (hsT j ^ m) / m.factorial) *
          (hcoef (j + 1) ^ (k - m) * (1 / ((k - m).factorial : ℚ))) else 0) := by
      rw [show ((k.choose m : ℕ) : ℚ⟦X⟧) = PowerSeries.C ((k.choose m : ℕ) : ℚ) by simp,
        mul_comm _ (PowerSeries.C _), coeff_C_mul, ← mul_assoc, mul_comm (hsT j ^ m),
        mul_assoc, coeff_C_mul, coeff_mul_X_pow']
      split_ifs
      · calc ((k.choose m : ℕ) : ℚ) * (hcoef (j + 1) ^ (k - m) * coeff (n - J) (hsT j ^ m)) /
              k.factorial
            = (hcoef (j + 1) ^ (k - m) * coeff (n - J) (hsT j ^ m)) *
                (((k.choose m : ℕ) : ℚ) / k.factorial) := by ring
          _ = _ := by rw [hcho]; ring
      · simp
    rw [hcoeff]
    split_ifs with hJ
    · rw [padicNorm.mul, padicNorm.mul, padicNorm_one_div_fact]
      have h1 := ih (n - J) m
      have h2 : padicNorm p (hcoef (j + 1) ^ (k - m)) ≤ (p : ℚ) ^ ((k - m) * wp p (j + 1)) := by
        rw [padicNorm_pow, mul_comm, pow_mul]
        exact pow_le_pow_left₀ (padicNorm.nonneg _) (hcoef_norm_le (j + 1) (by omega)) _
      have h3 : (k - m) * wp p (j + 1) + padicValNat p (k - m).factorial ≤ Vp p J := by
        have hJdef : J = (j + 1) * (k - m) := rfl
        have := Vp_mul (p := p) (j + 1) (k - m) (by omega)
        rw [← hJdef] at this
        have := wp_le_Vp (p := p) (j + 1) (by omega)
        have : (k - m) * wp p (j + 1) ≤ (k - m) * Vp p (j + 1) := Nat.mul_le_mul_left _ this
        omega
      have h4 : Vp p (n - J) + Vp p J ≤ Vp p n := by
        have := Vp_add (p := p) (n - J) J
        rwa [Nat.sub_add_cancel hJ] at this
      calc padicNorm p (coeff (n - J) (hsT j ^ m) / m.factorial) *
            (padicNorm p (hcoef (j + 1) ^ (k - m)) * (p : ℚ) ^ padicValNat p (k - m).factorial)
          ≤ (p : ℚ) ^ Vp p (n - J) * ((p : ℚ) ^ ((k - m) * wp p (j + 1)) *
              (p : ℚ) ^ padicValNat p (k - m).factorial) := by
            gcongr
            exact mul_nonneg (padicNorm.nonneg _) (by positivity)
          _ = (p : ℚ) ^ (Vp p (n - J) + ((k - m) * wp p (j + 1) + padicValNat p (k - m).factorial)) := by
            rw [pow_add, pow_add]
          _ ≤ (p : ℚ) ^ Vp p n := pow_le_pow_right₀ hp1 (by omega)
    · rw [padicNorm.zero]; positivity

end UpperBound

section Content
open PowerSeries Finset

/-- `a(n,k) = [t^n] h^k / k!`, the coefficient of `x^k` in `f_n(x) = [t^n] (t/(e^t-1))^x`. -/
private noncomputable def aco (n k : ℕ) : ℚ := coeff n (hs ^ k) / k.factorial

/-- `[t^n] h^k` only depends on `h_{≤ n}`. -/
private lemma coeff_hs_pow_eq_hsT (n k : ℕ) : coeff n (hs ^ k) = coeff n (hsT n ^ k) := by
  have h1 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ hs - hsT n := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [hs, hsT, show m ≤ n by omega]
  have h2 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ hs ^ k - hsT n ^ k := h1.trans (sub_dvd_pow_sub_pow _ _ _)
  have := X_pow_dvd_iff.1 h2 n (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

variable {p : ℕ} [hp : Fact p.Prime]

/-- Upper bound `|a(n,k)|_p ≤ p^(V_p(n))`. -/
private theorem aco_upper (n k : ℕ) : padicNorm p (aco n k) ≤ (p : ℚ) ^ Vp p n := by
  unfold aco; rw [coeff_hs_pow_eq_hsT]; exact upper_hsT n n k

/-- The power series `g = h / t`. -/
private noncomputable def gs : ℚ⟦X⟧ := PowerSeries.mk (fun i => hcoef (i + 1))

/-- `h = t g`. -/
private lemma hs_eq : hs = X * gs := by
  ext i
  rcases i with _ | i
  · simp [hs, hcoef_zero]
  · rw [coeff_succ_X_mul]; simp [hs, gs]

/-- `[t^n] h^n = h_1^n`. -/
private lemma coeff_hs_pow_self (n : ℕ) : coeff n (hs ^ n) = hcoef 1 ^ n := by
  rw [hs_eq, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff,
    map_pow]
  simp [gs]

/-- The top coefficient `a(n,n) = (-1/2)^n / n!`. -/
private lemma aco_self (n : ℕ) : aco n n = (-1 / 2 : ℚ) ^ n / n.factorial := by
  rw [aco, coeff_hs_pow_self]; simp [hcoef]

/-- `|a(n,n)|_2 = 2^(V_2(n))`. -/
private lemma aco_lower_two (n : ℕ) : padicNorm 2 (aco n n) = (2 : ℚ) ^ Vp 2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [aco_self, div_eq_mul_one_div, padicNorm.mul, padicNorm_one_div_fact, padicNorm_pow,
    show (-1 / 2 : ℚ) = -(2 : ℚ)⁻¹ by ring, padicNorm.neg, inv_eq_one_div, padicNorm.div,
    padicNorm.one]
  have h2 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := by
    have := @padicNorm.padicNorm_p_of_prime 2 _
    simpa using this
  rw [h2]
  simp [Vp, pow_add]

end Content

section LowerBoundOdd
open PowerSeries Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- Ultrametric bound for `|∑ F|_p^d`. -/
private lemma norm_sum_pow_le {ι : Type*} (s : Finset ι) (F : ι → ℚ) (d : ℕ) (C : ℚ) (hC : 0 ≤ C)
    (hd : 0 < d) (h : ∀ x ∈ s, padicNorm p (F x) ^ d ≤ C) :
    padicNorm p (∑ x ∈ s, F x) ^ d ≤ C := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [zero_pow hd.ne', hC]
  · obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image s (fun x => padicNorm p (F x)) hne
    have h1 : padicNorm p (∑ x ∈ s, F x) ≤ padicNorm p (F y) :=
      padicNorm.sum_le hne (fun i hi => hmax i hi)
    exact (pow_le_pow_left₀ (padicNorm.nonneg _) h1 d).trans (h y hy)

/-- Strict ultrametric bound for `|∑ F|_p^d`. -/
private lemma norm_sum_pow_lt {ι : Type*} (s : Finset ι) (F : ι → ℚ) (d : ℕ) (C : ℚ) (hC : 0 < C)
    (hd : 0 < d) (h : ∀ x ∈ s, padicNorm p (F x) ^ d < C) :
    padicNorm p (∑ x ∈ s, F x) ^ d < C := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [zero_pow hd.ne', hC]
  · obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image s (fun x => padicNorm p (F x)) hne
    have h1 : padicNorm p (∑ x ∈ s, F x) ≤ padicNorm p (F y) :=
      padicNorm.sum_le hne (fun i hi => hmax i hi)
    exact lt_of_le_of_lt (pow_le_pow_left₀ (padicNorm.nonneg _) h1 d) (h y hy)

/-- Strict ultrametric bound for `|a + b|_p^d`. -/
private lemma norm_add_pow_lt (a b : ℚ) (d : ℕ) (C : ℚ) (_hd : 0 < d)
    (ha : padicNorm p a ^ d < C) (hb : padicNorm p b ^ d < C) :
    padicNorm p (a + b) ^ d < C := by
  have h1 := padicNorm.nonarchimedean (p := p) (q := a) (r := b)
  rcases le_total (padicNorm p a) (padicNorm p b) with h | h
  · rw [max_eq_right h] at h1
    exact lt_of_le_of_lt (pow_le_pow_left₀ (padicNorm.nonneg _) h1 d) hb
  · rw [max_eq_left h] at h1
    exact lt_of_le_of_lt (pow_le_pow_left₀ (padicNorm.nonneg _) h1 d) ha

section odd

variable (h2 : p ≠ 2)
include h2

/-- An odd prime is at least `3`. -/
private lemma p3 : 3 ≤ p := by have := hp.out.two_le; omega

/-- `|g_i|_p^(p-2) ≤ p^i`. -/
private lemma gs_bound (i : ℕ) : padicNorm p (coeff i gs) ^ (p - 2) ≤ (p : ℚ) ^ i := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have h := hcoef_norm_le (p := p) (i + 1) (by omega)
  simp only [gs, coeff_mk]
  have hw : (p - 2) * wp p (i + 1) ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [wp_one h2]; simp
    by_cases he : i + 1 = p - 1
    · rw [he, wp_sub_one h2]; omega
    · have := wp_strict h2 (i + 1) (by omega) he; omega
  calc padicNorm p (hcoef (i + 1)) ^ (p - 2) ≤ ((p : ℚ) ^ wp p (i + 1)) ^ (p - 2) :=
        pow_le_pow_left₀ (padicNorm.nonneg _) h _
    _ = (p : ℚ) ^ ((p - 2) * wp p (i + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ (p : ℚ) ^ i := pow_le_pow_right₀ hp1 hw

/-- `|g_i|_p^(p-2) < p^i` unless `i ∈ {0, p-2}`. -/
private lemma gs_strict (i : ℕ) (hi0 : i ≠ 0) (hid : i ≠ p - 2) :
    padicNorm p (coeff i gs) ^ (p - 2) < (p : ℚ) ^ i := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have h := hcoef_norm_le (p := p) (i + 1) (by omega)
  simp only [gs, coeff_mk]
  have hw : (p - 2) * wp p (i + 1) < i := by
    have := wp_strict h2 (i + 1) (by omega) (by have := p3 h2; omega); omega
  calc padicNorm p (hcoef (i + 1)) ^ (p - 2) ≤ ((p : ℚ) ^ wp p (i + 1)) ^ (p - 2) :=
        pow_le_pow_left₀ (padicNorm.nonneg _) h _
    _ = (p : ℚ) ^ ((p - 2) * wp p (i + 1)) := by rw [← pow_mul, mul_comm]
    _ < (p : ℚ) ^ i := pow_lt_pow_right₀ hp1 hw

/-- `|g_0|_p ≤ 1` for odd `p`. -/
private lemma gs_zero : padicNorm p (coeff 0 gs) ≤ 1 := by
  simp only [gs, coeff_mk, zero_add, hcoef, if_true]
  rw [show (-1 / 2 : ℚ) = -(2 : ℚ)⁻¹ by ring, padicNorm.neg, padicNorm_two_inv_odd h2]

/-- `|g_{p-2}|_p = p` for odd `p`. -/
private lemma gs_d : padicNorm p (coeff (p - 2) gs) = p := by
  simp only [gs, coeff_mk]
  rw [show p - 2 + 1 = p - 1 by have := p3 h2; omega]
  exact hcoef_norm_pm1 h2

/-- Weighted `p`-adic bounds for the powers `g^q`, with the dominant term `g_{p-2}^q` of `[t^((p-2)q)] g^q` isolated. -/
private lemma gs_pow_props (q : ℕ) :
    (∀ i, padicNorm p (coeff i (gs ^ q)) ^ (p - 2) ≤ (p : ℚ) ^ i) ∧
    (∀ i, (p - 2) * q < i → padicNorm p (coeff i (gs ^ q)) ^ (p - 2) < (p : ℚ) ^ i) ∧
    padicNorm p (coeff ((p - 2) * q) (gs ^ q) - coeff (p - 2) gs ^ q) ^ (p - 2) <
      (p : ℚ) ^ ((p - 2) * q) := by
  have hp3 := p3 h2
  have hd : 0 < p - 2 := by omega
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  induction q with
  | zero =>
    refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
    · rw [pow_zero, coeff_one]
      split_ifs with h
      · subst h; simp
      · simp [zero_pow hd.ne']
    · rw [pow_zero, coeff_one, if_neg (by omega)]; simp [zero_pow hd.ne']; positivity
    · simp [zero_pow hd.ne']
  | succ q ih =>
    obtain ⟨P1, P2, P3⟩ := ih
    have hterm : ∀ (a b : ℕ), padicNorm p (coeff a gs * coeff b (gs ^ q)) ^ (p - 2) ≤
        (p : ℚ) ^ (a + b) := by
      intro a b
      rw [padicNorm.mul, mul_pow, pow_add]
      exact mul_le_mul (gs_bound h2 a) (P1 b) (pow_nonneg (padicNorm.nonneg _) _) (by positivity)
    have hterm_lt : ∀ (a b : ℕ), (a ≠ 0 ∧ a ≠ p - 2) ∨ (p - 2) * q < b →
        padicNorm p (coeff a gs * coeff b (gs ^ q)) ^ (p - 2) < (p : ℚ) ^ (a + b) := by
      intro a b hab
      rw [padicNorm.mul, mul_pow, pow_add]
      rcases hab with ⟨ha0, had⟩ | hb
      · calc padicNorm p (coeff a gs) ^ (p - 2) * padicNorm p (coeff b (gs ^ q)) ^ (p - 2)
            ≤ padicNorm p (coeff a gs) ^ (p - 2) * (p : ℚ) ^ b :=
              mul_le_mul_of_nonneg_left (P1 b) (pow_nonneg (padicNorm.nonneg _) _)
          _ < (p : ℚ) ^ a * (p : ℚ) ^ b :=
              mul_lt_mul_of_pos_right (gs_strict h2 a ha0 had) (by positivity)
      · calc padicNorm p (coeff a gs) ^ (p - 2) * padicNorm p (coeff b (gs ^ q)) ^ (p - 2)
            ≤ (p : ℚ) ^ a * padicNorm p (coeff b (gs ^ q)) ^ (p - 2) :=
              mul_le_mul_of_nonneg_right (gs_bound h2 a) (pow_nonneg (padicNorm.nonneg _) _)
          _ < (p : ℚ) ^ a * (p : ℚ) ^ b :=
              mul_lt_mul_of_pos_left (P2 b hb) (by positivity)
    refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
    · rw [pow_succ', coeff_mul]
      refine norm_sum_pow_le _ _ _ _ (by positivity) hd (fun x hx => ?_)
      have := hterm x.1 x.2
      rwa [(HasAntidiagonal.mem_antidiagonal.1 hx)] at this
    · rw [pow_succ', coeff_mul]
      refine norm_sum_pow_lt _ _ _ _ (by positivity) hd (fun x hx => ?_)
      have hx' := HasAntidiagonal.mem_antidiagonal.1 hx
      have := hterm_lt x.1 x.2 (by
        by_cases ha0 : x.1 = 0
        · right; rw [mul_add, mul_one] at hi; omega
        · by_cases had : x.1 = p - 2
          · right; rw [mul_add, mul_one] at hi; omega
          · left; exact ⟨ha0, had⟩)
      rwa [hx'] at this
    · rw [pow_succ', coeff_mul]
      have hmem : (p - 2, (p - 2) * q) ∈ antidiagonal ((p - 2) * (q + 1)) := by
        rw [HasAntidiagonal.mem_antidiagonal]; ring
      rw [← add_sum_erase _ _ hmem]
      have : coeff (p - 2) gs * coeff ((p - 2) * q) (gs ^ q) +
          ∑ x ∈ (antidiagonal ((p - 2) * (q + 1))).erase (p - 2, (p - 2) * q),
            coeff x.1 gs * coeff x.2 (gs ^ q) - coeff (p - 2) gs ^ (q + 1) =
          coeff (p - 2) gs * (coeff ((p - 2) * q) (gs ^ q) - coeff (p - 2) gs ^ q) +
          ∑ x ∈ (antidiagonal ((p - 2) * (q + 1))).erase (p - 2, (p - 2) * q),
            coeff x.1 gs * coeff x.2 (gs ^ q) := by ring
      rw [this]
      apply norm_add_pow_lt _ _ _ _ hd
      · rw [padicNorm.mul, mul_pow, gs_d h2]
        rw [show (p - 2) * (q + 1) = (p - 2) + (p - 2) * q by ring, pow_add]
        exact mul_lt_mul_of_pos_left P3 (by positivity)
      · refine norm_sum_pow_lt _ _ _ _ (by positivity) hd (fun x hx => ?_)
        have hne := Finset.ne_of_mem_erase hx
        have hx' := HasAntidiagonal.mem_antidiagonal.1 (Finset.mem_of_mem_erase hx)
        have := hterm_lt x.1 x.2 (by
          by_cases ha0 : x.1 = 0
          · right; rw [mul_add, mul_one] at hx'; omega
          · by_cases had : x.1 = p - 2
            · exfalso; apply hne
              ext
              · exact had
              · simp only; rw [mul_add, mul_one] at hx'; omega
            · left; exact ⟨ha0, had⟩)
        rwa [hx'] at this

/-- `|[t^((p-2)q)] g^q|_p = p^q` for odd `p`. -/
private lemma coeff_gs_pow_norm (q : ℕ) :
    padicNorm p (coeff ((p - 2) * q) (gs ^ q)) = (p : ℚ) ^ q := by
  have hp3 := p3 h2
  have hd : 0 < p - 2 := by omega
  have P3 := (gs_pow_props h2 q).2.2
  set err := coeff ((p - 2) * q) (gs ^ q) - coeff (p - 2) gs ^ q
  have hmain : padicNorm p (coeff (p - 2) gs ^ q) = (p : ℚ) ^ q := by
    rw [padicNorm_pow, gs_d h2]
  have herr : padicNorm p err < (p : ℚ) ^ q := by
    rw [mul_comm, pow_mul] at P3
    exact lt_of_pow_lt_pow_left₀ _ (by positivity) P3
  have : coeff ((p - 2) * q) (gs ^ q) = coeff (p - 2) gs ^ q + err := by simp [err]
  rw [this, padicNorm.add_eq_max_of_ne, hmain, max_eq_left (by rw [← hmain] at herr; linarith)]
  rw [hmain]; exact herr.ne'

/-- `|a((p-1)q, q)|_p = p^(V_p((p-1)q))` for odd `p`. -/
private theorem aco_lower_odd (q : ℕ) :
    padicNorm p (aco ((p - 1) * q) q) = (p : ℚ) ^ Vp p ((p - 1) * q) := by
  have hp3 := p3 h2
  have hcoeff : coeff ((p - 1) * q) (hs ^ q) = coeff ((p - 2) * q) (gs ^ q) := by
    rw [hs_eq, mul_pow, coeff_X_pow_mul', if_pos (Nat.le_mul_of_pos_left q (by omega))]
    congr 1
    rw [show p - 1 = (p - 2) + 1 by omega, add_mul, one_mul, Nat.add_sub_cancel]
  rw [aco, hcoeff, div_eq_mul_one_div, padicNorm.mul, coeff_gs_pow_norm h2,
    padicNorm_one_div_fact, ← pow_add]
  unfold Vp
  rw [Nat.mul_div_cancel_left _ (by omega)]

end odd

end LowerBoundOdd

section Monotone
open PowerSeries Finset

/-- The polynomial `f_n(x) = [t^n] (t/(e^t-1))^x = B_n^(x) / n!`. -/
private noncomputable def fpoly (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ range (n + 1), Polynomial.C (aco n k) * Polynomial.X ^ k

/-- `a(n,k) = 0` for `k > n`. -/
private lemma aco_eq_zero (n k : ℕ) (h : n < k) : aco n k = 0 := by
  rw [aco, coeff_hs_pow_eq_zero k n h, zero_div]

/-- The coefficients of `f_n` are the `a(n,k)`. -/
private lemma coeff_fpoly (n k : ℕ) : (fpoly n).coeff k = aco n k := by
  simp only [fpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hk; simp at hk; simp [aco_eq_zero n k (by omega)]

/-- `f_n(N) = [t^n] G^N` for natural `N`. -/
private lemma eval_fpoly (n N : ℕ) : (fpoly n).eval (N : ℚ) = coeff n (Gs ^ N) := by
  rw [← Ys_nat]
  simp only [fpoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Ys, coeff_mk, aco]
  refine sum_congr rfl (fun k _ => by ring)

/-- `t (G^N)' = N (G^N - t G^N - G^(N+1))`. -/
private lemma X_Gs_pow_deriv (N : ℕ) :
    X * d⁄dX ℚ (Gs ^ N) = (N : ℚ⟦X⟧) * (Gs ^ N - X * Gs ^ N - Gs ^ (N + 1)) := by
  rw [Gs_pow_deriv]
  have := X_hs'
  calc X * ((N : ℚ⟦X⟧) * d⁄dX ℚ hs * Gs ^ N) = (N : ℚ⟦X⟧) * (X * d⁄dX ℚ hs) * Gs ^ N := by ring
    _ = _ := by rw [this]; ring

/-- Coefficient form of `X_Gs_pow_deriv`. -/
private lemma f_rel (n N : ℕ) :
    coeff (n + 1) (Gs ^ N) * (n + 1) =
      N * (coeff (n + 1) (Gs ^ N) - coeff n (Gs ^ N) - coeff (n + 1) (Gs ^ (N + 1))) := by
  have h := congrArg (coeff (n + 1)) (X_Gs_pow_deriv N)
  rw [coeff_succ_X_mul, coeff_derivative] at h
  rw [h]
  rw [show ((N : ℚ⟦X⟧)) = PowerSeries.C (N : ℚ) by simp, coeff_C_mul, map_sub, map_sub,
    coeff_succ_X_mul]

/-- `x f_n(x) = (x - n - 1) f_{n+1}(x) - x f_{n+1}(x+1)`. -/
private lemma fpoly_rel (n : ℕ) :
    Polynomial.X * fpoly n = (Polynomial.X - Polynomial.C ((n : ℚ) + 1)) * fpoly (n + 1) -
      Polynomial.X * (fpoly (n + 1)).comp (Polynomial.X + 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun N : ℕ => (N : ℚ)))
  · rintro _ ⟨N, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one]
    rw [show (N : ℚ) + 1 = ((N + 1 : ℕ) : ℚ) by push_cast; ring, eval_fpoly, eval_fpoly,
      eval_fpoly]
    linear_combination (f_rel n N)
  · exact Set.infinite_range_of_injective Nat.cast_injective

variable {p : ℕ} [hp : Fact p.Prime]

/-- Substituting `x ↦ x + 1` preserves strict `p`-adic bounds on all coefficients. -/
private lemma comp_coeff_lt (P : Polynomial ℚ) (C : ℚ) (hC : 0 < C)
    (h : ∀ j, padicNorm p (P.coeff j) < C) (k : ℕ) :
    padicNorm p ((P.comp (Polynomial.X + 1)).coeff k) < C := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  refine padicNorm.sum_lt' (fun j _ => ?_) hC
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow, padicNorm.mul]
  calc padicNorm p (P.coeff j) * padicNorm p ((j.choose k : ℕ) : ℚ)
      ≤ padicNorm p (P.coeff j) * 1 :=
        mul_le_mul_of_nonneg_left (padicNorm.of_nat _) (padicNorm.nonneg _)
    _ < C := by rw [mul_one]; exact h j

/-- If all coefficients of `f_{n+1}` have `p`-adic norm `< C`, so do those of `f_n`. -/
private lemma aco_mono (n : ℕ) (C : ℚ) (hC : 0 < C) (h : ∀ k, padicNorm p (aco (n + 1) k) < C) (k : ℕ) :
    padicNorm p (aco n k) < C := by
  have hrel := congrArg (fun P => Polynomial.coeff P (k + 1)) (fpoly_rel n)
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, sub_mul,
    Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, coeff_fpoly,
    coeff_fpoly, coeff_fpoly] at hrel
  rw [hrel]
  have h3 := comp_coeff_lt (p := p) (fpoly (n + 1)) C hC (fun j => by rw [coeff_fpoly]; exact h j) k
  refine lt_of_le_of_lt padicNorm.sub (max_lt (lt_of_le_of_lt padicNorm.sub (max_lt (h k) ?_)) h3)
  rw [padicNorm.mul]
  calc padicNorm p ((n : ℚ) + 1) * padicNorm p (aco (n + 1) (k + 1))
      ≤ 1 * padicNorm p (aco (n + 1) (k + 1)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast padicNorm.of_nat (p := p) (n + 1))
          (padicNorm.nonneg _)
    _ < C := by rw [one_mul]; exact h (k + 1)

/-- The `p`-content of `f_n` is exactly `p^(V_p(n))`. -/
private theorem aco_content (n : ℕ) :
    (∀ k, padicNorm p (aco n k) ≤ (p : ℚ) ^ Vp p n) ∧
    ∃ k, (p : ℚ) ^ Vp p n ≤ padicNorm p (aco n k) := by
  refine ⟨fun k => aco_upper n k, ?_⟩
  by_cases h2 : p = 2
  · subst h2; exact ⟨n, (aco_lower_two n).ge⟩
  by_contra hcon
  push Not at hcon
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set q := n / (p - 1)
  set m := (p - 1) * q
  have hm : m ≤ n := by simp only [m, q]; exact Nat.mul_div_le n (p - 1)
  have hV : Vp p m = Vp p n := by
    simp only [Vp, m, q]
    rw [Nat.mul_div_cancel_left _ (by omega)]
  have hdown : ∀ j, j ≤ n - m → ∀ k, padicNorm p (aco (n - j) k) < (p : ℚ) ^ Vp p n := by
    intro j
    induction j with
    | zero => intro _ k; simpa using hcon k
    | succ j ih =>
      intro hj k
      have := ih (by omega)
      have e : n - j = (n - (j + 1)) + 1 := by omega
      rw [e] at this
      exact aco_mono _ _ (by positivity) this k
  have := hdown (n - m) le_rfl q
  rw [show n - (n - m) = m by omega, aco_lower_odd h2 q, hV] at this
  exact lt_irrefl _ this

end Monotone

section NorlundLists
open Finset Math0.Statements.A342645

/-- The polynomial with rational coefficient list `l` (lowest degree first). -/
private noncomputable def toPolyQ : List ℚ → Polynomial ℚ
  | [] => 0
  | a :: l => Polynomial.C a + Polynomial.X * toPolyQ l

/-- Coefficients of `toPolyQ`. -/
private lemma coeff_toPolyQ (l : List ℚ) (k : ℕ) : (toPolyQ l).coeff k = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [toPolyQ]
  | cons a l ih =>
    cases k with
    | zero => simp [toPolyQ]
    | succ k => simp [toPolyQ, Polynomial.coeff_X_mul, ih]

/-- `addQ` is polynomial addition. -/
private lemma toPolyQ_addQ (a b : List ℚ) : toPolyQ (addQ a b) = toPolyQ a + toPolyQ b := by
  induction a generalizing b with
  | nil => simp [addQ, toPolyQ]
  | cons x a ih =>
    cases b with
    | nil => simp [addQ, toPolyQ]
    | cons y b => simp only [addQ, toPolyQ, ih, map_add]; ring

/-- Scaling a coefficient list. -/
private lemma toPolyQ_map_mul (c : ℚ) (l : List ℚ) :
    toPolyQ (l.map (fun a => c * a)) = Polynomial.C c * toPolyQ l := by
  induction l with
  | nil => simp [toPolyQ]
  | cons x l ih => simp only [List.map_cons, toPolyQ, ih, map_mul]; ring

/-- `mulQ` is polynomial multiplication. -/
private lemma toPolyQ_mulQ (a b : List ℚ) : toPolyQ (mulQ a b) = toPolyQ a * toPolyQ b := by
  induction a with
  | nil => simp [mulQ, toPolyQ]
  | cons x a ih =>
    have : mulQ (x :: a) b = addQ (b.map (x * ·)) (0 :: mulQ a b) := rfl
    rw [this, toPolyQ_addQ, toPolyQ_map_mul, toPolyQ, toPolyQ, ih, map_zero]
    ring

/-- Entries of a truncated list. -/
private lemma getD_take (l : List ℚ) (m i : ℕ) :
    (l.take m).getD i 0 = if i < m then l.getD i 0 else 0 := by
  induction l generalizing m i with
  | nil => simp
  | cons a l ih =>
    cases m with
    | zero => simp
    | succ m =>
      cases i with
      | zero => simp
      | succ i => simp only [List.take_succ_cons, List.getD_cons_succ, ih]; split_ifs <;> first | rfl | omega

/-- Truncating above degree `n` does not change the degree-`n` coefficient of a product. -/
private lemma coeff_take_mul (l : List ℚ) (B : Polynomial ℚ) (n : ℕ) :
    (toPolyQ (l.take (n + 1)) * B).coeff n = (toPolyQ l * B).coeff n := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine sum_congr rfl (fun x hx => ?_)
  have := HasAntidiagonal.mem_antidiagonal.1 hx
  rw [coeff_toPolyQ, coeff_toPolyQ, getD_take, if_pos (by omega)]

/-- Length of `powsH`. -/
private lemma powsH_length (n : ℕ) (H : List ℚ) (k : ℕ) (P : List ℚ) : (powsH n H k P).length = k := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih => simp [powsH, ih]

/-- `powsH` lists the coefficients `[t^n] P H^j`. -/
private lemma powsH_getD (n : ℕ) (H : List ℚ) (k : ℕ) (P : List ℚ) (j : ℕ) :
    (powsH n H k P).getD j 0 =
      if j < k then (toPolyQ P * toPolyQ H ^ j).coeff n else 0 := by
  induction k generalizing P j with
  | zero => simp [powsH]
  | succ k ih =>
    cases j with
    | zero => simp [powsH, coeff_toPolyQ]
    | succ j =>
      simp only [powsH, List.getD_cons_succ, ih]
      split_ifs with h1 h2 h2
      · rw [coeff_take_mul, toPolyQ_mulQ, pow_succ]; ring_nf
      · omega
      · omega
      · rfl

/-- `descQ j` is the falling factorial `x(x-1)⋯(x-j+1)`. -/
private lemma toPolyQ_descQ (j : ℕ) : toPolyQ (descQ j) = descPochhammer ℚ j := by
  induction j with
  | zero => simp [descQ, toPolyQ]
  | succ j ih =>
    simp only [descQ]
    rw [toPolyQ_addQ, toPolyQ, toPolyQ_map_mul, ih, descPochhammer_succ_right, map_zero, zero_add]
    rw [show ((j : Polynomial ℚ)) = Polynomial.C (j : ℚ) by simp]
    rw [map_neg]; ring

/-- The polynomial computed by `norlundAux`. -/
private lemma toPolyQ_norlundAux (n j : ℕ) (cs : List ℚ) :
    toPolyQ (norlundAux n j cs) = ∑ i ∈ range cs.length,
      Polynomial.C ((n.factorial : ℚ) * cs.getD i 0 / ((j + i).factorial : ℚ)) *
        descPochhammer ℚ (j + i) := by
  induction cs generalizing j with
  | nil => simp [norlundAux, toPolyQ]
  | cons c cs ih =>
    simp only [norlundAux]
    rw [toPolyQ_addQ, toPolyQ_map_mul, toPolyQ_descQ, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl (fun i _ => ?_)
    rw [show j + 1 + i = j + (i + 1) by ring]

end NorlundLists

section BernoulliLists
open Finset Math0.Statements.A342645 PowerSeries

/-- List sums over `List.range` are `Finset` sums. -/
private lemma list_sum_map_range (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The recursion defining `revG`, satisfied by `G_k = B_k/k!`. -/
private lemma G_rec (k : ℕ) :
    G (k + 1) = -∑ i ∈ range (k + 1), G (k - i) / ((i + 2).factorial : ℚ) := by
  have h := congrArg (coeff (k + 1)) Gs_mul_Es
  rw [coeff_mul, coeff_one, if_neg (by omega), ← Finset.Nat.sum_antidiagonal_swap] at h
  simp only [Prod.fst_swap, Prod.snd_swap] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun b a => coeff a Gs * coeff b Es),
    sum_range_succ'] at h
  simp only [Gs, Es, coeff_mk, Nat.sub_zero, zero_add, Nat.factorial_one, Nat.cast_one,
    div_one, mul_one] at h
  have h2 : ∑ i ∈ range (k + 1), G (k + 1 - (i + 1)) * (1 / ((i + 1 + 1).factorial : ℚ)) =
      ∑ i ∈ range (k + 1), G (k - i) / ((i + 2).factorial : ℚ) := by
    refine sum_congr rfl (fun i _ => ?_)
    rw [show k + 1 - (i + 1) = k - i by omega]; ring
  rw [h2] at h
  linarith

/-- `revG k = [G_k, …, G_0]`. -/
private lemma revG_eq (k : ℕ) : revG k = (List.range (k + 1)).map (fun i => G (k - i)) := by
  induction k with
  | zero => simp [revG, G_zero]
  | succ k ih =>
    rw [revG, ih, List.zipWith_map_left, List.zipWith_self, list_sum_map_range,
      List.range_succ_eq_map (n := k + 1), List.map_cons, List.map_map]
    congr 1
    · rw [Nat.sub_zero, G_rec]
    · refine List.map_congr_left (fun i _ => ?_)
      simp

/-- `bernG n = [G_0, …, G_n]`. -/
private lemma bernG_getD (n i : ℕ) : (bernG n).getD i 0 = if i ≤ n then G i else 0 := by
  rw [bernG, revG_eq, List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_reverse (by simp; omega)]
    simp only [List.length_map, List.length_range, List.getElem?_map]
    rw [List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 1; omega
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- `Hser n = [0, G_1, …, G_n]`. -/
private lemma Hser_getD (n i : ℕ) : (Hser n).getD i 0 = if 1 ≤ i ∧ i ≤ n then G i else 0 := by
  rcases i with _ | i
  · simp [Hser]
  · simp only [Hser, List.getD_cons_succ]
    rw [show (bernG n).tail.getD i 0 = (bernG n).getD (i + 1) 0 by
      rcases h : bernG n with _ | ⟨a, l⟩
      · simp
      · simp]
    rw [bernG_getD]
    split_ifs <;> first | rfl | omega

end BernoulliLists

section NorlundPoly
open Finset Math0.Statements.A342645 PowerSeries

/-- `G - 1` has no constant term. -/
private lemma constantCoeff_Gs_sub_one : constantCoeff (Gs - 1) = 0 := by
  simp [Gs, G_zero]

/-- `[t^n] (G-1)^i = 0` for `n < i`. -/
private lemma coeff_Gs_sub_one_pow_eq_zero (i n : ℕ) (h : n < i) : coeff n ((Gs - 1) ^ i) = 0 := by
  have h1 : (X : ℚ⟦X⟧) ∣ Gs - 1 := X_dvd_iff.2 constantCoeff_Gs_sub_one
  exact X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd h1 i) n h

/-- Degree-`n` coefficients of powers of the truncation `Hser n` agree with those of `G - 1`. -/
private lemma coeff_Hpoly_pow (n j : ℕ) :
    (toPolyQ (Hser n) ^ j).coeff n = coeff n ((Gs - 1) ^ j) := by
  have h1 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ (toPolyQ (Hser n) : ℚ⟦X⟧) - (Gs - 1) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, coeff_toPolyQ, Hser_getD, map_sub, coeff_one]
    simp only [Gs, coeff_mk]
    rcases m with _ | m
    · simp [G_zero]
    · rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega)]; ring
  have h2 := X_pow_dvd_iff.1 (h1.trans (sub_dvd_pow_sub_pow _ _ j)) n (by omega)
  rw [map_sub, ← Polynomial.coe_pow, Polynomial.coeff_coe] at h2
  exact sub_eq_zero.1 h2

/-- The list `powsH n (Hser n) (n+1) [1]` is `[t^n] (G-1)^j`, `j ≤ n`. -/
private lemma norlund_cs (n i : ℕ) :
    (powsH n (Hser n) (n + 1) [1]).getD i 0 =
      if i < n + 1 then coeff n ((Gs - 1) ^ i) else 0 := by
  rw [powsH_getD]
  split_ifs
  · rw [show toPolyQ [1] = 1 by simp [toPolyQ], one_mul, coeff_Hpoly_pow]
  · rfl

/-- `norlund n = ∑_j (n!/j!) [t^n](G-1)^j x(x-1)⋯(x-j+1)`. -/
private lemma toPolyQ_norlund (n : ℕ) : toPolyQ (norlund n) = ∑ i ∈ range (n + 1),
    Polynomial.C ((n.factorial : ℚ) * coeff n ((Gs - 1) ^ i) / (i.factorial : ℚ)) *
      descPochhammer ℚ i := by
  rw [norlund, toPolyQ_norlundAux, powsH_length]
  refine sum_congr rfl (fun i hi => ?_)
  rw [norlund_cs, if_pos (mem_range.1 hi), zero_add]

/-- `norlund n` evaluated at `N` is `n! [t^n] G^N`. -/
private lemma eval_norlund (n N : ℕ) :
    (toPolyQ (norlund n)).eval (N : ℚ) = n.factorial * coeff n (Gs ^ N) := by
  rw [toPolyQ_norlund, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hpow : Gs ^ N = ∑ i ∈ range (N + 1), (Gs - 1) ^ i * (N.choose i : ℚ⟦X⟧) := by
    have := add_pow (Gs - 1) 1 N
    simp only [one_pow, mul_one] at this
    rw [← this]; ring
  rw [hpow, map_sum, mul_sum]
  have e1 : ∀ i ∈ range (n + 1), (n.factorial : ℚ) * coeff n ((Gs - 1) ^ i) / (i.factorial : ℚ) *
      (((i.factorial * N.choose i : ℕ)) : ℚ) =
      n.factorial * (coeff n ((Gs - 1) ^ i) * (N.choose i : ℚ)) := by
    intro i _
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    push_cast; field_simp
  have e2 : ∀ i ∈ range (N + 1), (n.factorial : ℚ) * coeff n ((Gs - 1) ^ i * (N.choose i : ℚ⟦X⟧)) =
      n.factorial * (coeff n ((Gs - 1) ^ i) * (N.choose i : ℚ)) := by
    intro i _
    rw [show ((N.choose i : ℕ) : ℚ⟦X⟧) = PowerSeries.C ((N.choose i : ℕ) : ℚ) by simp,
      coeff_mul_C]
  rw [sum_congr rfl e1, sum_congr rfl e2, ← mul_sum, ← mul_sum]
  congr 1
  have hsub1 : range (n + 1) ⊆ range (n + N + 1) := range_subset_range.2 (by omega)
  have hsub2 : range (N + 1) ⊆ range (n + N + 1) := range_subset_range.2 (by omega)
  rw [sum_subset hsub1, sum_subset hsub2]
  · intro i hi hi'
    simp only [mem_range] at hi hi'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro i hi hi'
    simp only [mem_range] at hi hi'
    rw [coeff_Gs_sub_one_pow_eq_zero i n (by omega)]; simp

/-- `norlund n` is the coefficient list of `n! f_n`. -/
private lemma toPolyQ_norlund_eq (n : ℕ) :
    toPolyQ (norlund n) = Polynomial.C (n.factorial : ℚ) * fpoly n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun N : ℕ => (N : ℚ)))
  · rintro _ ⟨N, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_C]
    rw [eval_norlund, eval_fpoly]
  · exact Set.infinite_range_of_injective Nat.cast_injective

/-- The `k`-th entry of `norlund n` is `n! a(n,k)`. -/
private theorem norlund_getD (n k : ℕ) : (norlund n).getD k 0 = n.factorial * aco n k := by
  rw [← coeff_toPolyQ, toPolyQ_norlund_eq, Polynomial.coeff_C_mul, coeff_fpoly]

end NorlundPoly

section LcmDen
open Finset Math0.Statements.A342645 PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(den c) ≤ e ↔ |c|_p ≤ p^e`. -/
private lemma den_val_le_iff (c : ℚ) (e : ℕ) :
    padicValNat p c.den ≤ e ↔ padicNorm p c ≤ (p : ℚ) ^ e := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  by_cases hc : c = 0
  · subst hc; simp
  rw [padicNorm.eq_zpow_of_nonzero hc, padicValRat_def]
  by_cases hd : p ∣ c.den
  · have hnum : padicValInt p c.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hn
      have hcop := c.reduced
      have h1 : p ∣ c.num.natAbs := by
        rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs]; exact (dvd_abs _ _).2 hn
      exact hp.out.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_gcd h1 hd).trans
        (by rw [hcop.gcd_eq_one])))
    rw [hnum]
    simp only [Nat.cast_zero, zero_sub, neg_neg, zpow_natCast]
    exact (pow_le_pow_iff_right₀ hp1).symm
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    simp only [Nat.cast_zero, sub_zero, zero_le, true_iff]
    refine le_trans (zpow_le_one_of_nonpos₀ hp1.le ?_) (one_le_pow₀ hp1.le)
    simp

/-- `lcmDen` is positive. -/
private lemma lcmDen_ne_zero (l : List ℚ) : lcmDen l ≠ 0 := by
  induction l with
  | nil => simp [lcmDen]
  | cons c l ih =>
    simp only [lcmDen, List.map_cons, List.foldr_cons] at ih ⊢
    exact Nat.lcm_ne_zero c.den_nz ih

/-- `v_p(lcmDen l) ≤ e` iff every entry `c` has `v_p(den c) ≤ e`. -/
private lemma val_lcmDen_le_iff (l : List ℚ) (e : ℕ) :
    padicValNat p (lcmDen l) ≤ e ↔ ∀ c ∈ l, padicValNat p c.den ≤ e := by
  induction l with
  | nil => simp [lcmDen]
  | cons c l ih =>
    have hne := lcmDen_ne_zero l
    simp only [lcmDen, List.map_cons, List.foldr_cons] at ih hne ⊢
    rw [← Nat.factorization_def _ hp.out, Nat.factorization_lcm c.den_nz hne,
      Finsupp.sup_apply, Nat.factorization_def _ hp.out, Nat.factorization_def _ hp.out,
      sup_le_iff, ih]
    simp

/-- Each denominator divides `lcmDen`. -/
private lemma den_dvd_lcmDen (l : List ℚ) (c : ℚ) (hc : c ∈ l) : c.den ∣ lcmDen l := by
  induction l with
  | nil => simp at hc
  | cons a l ih =>
    simp only [lcmDen, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hc with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (ih h).trans (Nat.dvd_lcm_right _ _)

/-- A nonzero `getD` entry belongs to the list. -/
private lemma mem_of_getD_ne_zero (l : List ℚ) (k : ℕ) (h : l.getD k 0 ≠ 0) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h ⊢
  rcases hk : l[k]? with _ | c
  · rw [hk] at h; simp at h
  · simp only [Option.getD_some]
    exact List.mem_of_getElem? hk

/-- Every element of a list is a `getD` entry. -/
private lemma getD_of_mem (l : List ℚ) (c : ℚ) (hc : c ∈ l) : ∃ k, l.getD k 0 = c := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  exact ⟨k, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl⟩

/-- `v_p(n!) ≤ V_p(n)`. -/
private lemma fact_val_le_Vp (n : ℕ) : padicValNat p n.factorial ≤ Vp p n := by
  unfold Vp
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have h1 := sub_one_mul_padicValNat_factorial (p := p) n
  have : padicValNat p n.factorial ≤ n / (p - 1) := by
    rw [Nat.le_div_iff_mul_le hp1, mul_comm, h1]; omega
  omega

omit hp in
/-- `|n!|_p = p^(-v_p(n!))`. -/
private lemma padicNorm_fact (n : ℕ) :
    padicNorm p (n.factorial : ℚ) = ((p : ℚ) ^ padicValNat p n.factorial)⁻¹ :=
  padicNorm_natCast_eq _ (Nat.factorial_pos n)

/-- `v_p(lcmDen (norlund n)) = V_p(n) - v_p(n!)`. -/
private theorem val_lcmDen_norlund (n : ℕ) :
    padicValNat p (lcmDen (norlund n)) = Vp p n - padicValNat p n.factorial := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℚ) < p := by positivity
  obtain ⟨hup, k, hlow⟩ := aco_content (p := p) n
  have hF := fact_val_le_Vp (p := p) n
  set e := Vp p n - padicValNat p n.factorial
  have hnorm : ∀ k, padicNorm p ((norlund n).getD k 0) =
      ((p : ℚ) ^ padicValNat p n.factorial)⁻¹ * padicNorm p (aco n k) := by
    intro k; rw [norlund_getD, padicNorm.mul, padicNorm_fact]
  have hsplit : (p : ℚ) ^ Vp p n = (p : ℚ) ^ padicValNat p n.factorial * (p : ℚ) ^ e := by
    rw [← pow_add]; congr 1; omega
  apply le_antisymm
  · rw [val_lcmDen_le_iff]
    intro c hc
    obtain ⟨j, rfl⟩ := getD_of_mem _ c hc
    rw [den_val_le_iff, hnorm, inv_mul_le_iff₀ (by positivity), ← hsplit]
    exact hup j
  · by_contra hlt
    push Not at hlt
    have hc : padicNorm p ((norlund n).getD k 0) ≥ (p : ℚ) ^ e := by
      rw [hnorm, ge_iff_le, le_inv_mul_iff₀ (by positivity), ← hsplit]; exact hlow
    have hne : (norlund n).getD k 0 ≠ 0 := by
      intro h0; rw [h0, padicNorm.zero] at hc
      exact absurd hc (not_le.2 (by positivity))
    have hmem := mem_of_getD_ne_zero _ k hne
    have h1 := (val_lcmDen_le_iff (p := p) (norlund n) (e - 1)).1 (by omega) _ hmem
    rw [den_val_le_iff] at h1
    have : (p : ℚ) ^ e ≤ (p : ℚ) ^ (e - 1) := le_trans hc h1
    have := (pow_le_pow_iff_right₀ hp1).1 this
    omega

end LcmDen

section LeadingCoefficient
open Finset Math0.Statements.A342645 PowerSeries

/-- The exponent of `p` in the product defining `A053657(n+1)` is `V_p(n)`. -/
private lemma exp_eq_Vp (p n : ℕ) [hp : Fact p.Prime] :
    ∑ k ∈ range (n + 1), n / ((p - 1) * p ^ k) = Vp p n := by
  have h1 : ∀ k, n / ((p - 1) * p ^ k) = n / (p - 1) / p ^ k := fun k =>
    (Nat.div_div_eq_div_mul n (p - 1) (p ^ k)).symm
  simp only [h1]
  rw [sum_range_succ', pow_zero, Nat.div_one, Vp, add_comm]
  congr 1
  rw [padicValNat_factorial (b := n + 1)]
  · rw [sum_Ico_eq_sum_range]
    refine sum_congr (by simp) (fun k _ => ?_)
    rw [add_comm]
  · have : n / (p - 1) ≤ n := Nat.div_le_self _ _
    have := Nat.log_le_self p (n / (p - 1))
    omega

/-- `v_p(A053657(n+1)) = V_p(n)`. -/
private lemma factorization_A053657 (n p : ℕ) (hp : p.Prime) :
    (A053657 (n + 1)).factorization p = Vp p n := by
  have : Fact p.Prime := ⟨hp⟩
  unfold A053657
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.Prime.ne_zero (mem_filter.1 hq).2))]
  rw [Finset.sum_apply']
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.add_sub_cancel]
  by_cases hpS : p ∈ (range (n + 1 + 1)).filter Nat.Prime
  · rw [sum_eq_single p]
    · rw [hp.factorization_self, mul_one, exp_eq_Vp]
    · intro q hq hqp
      rw [(mem_filter.1 hq).2.factorization, Finsupp.single_eq_of_ne hqp.symm, mul_zero]
    · intro h; exact absurd hpS h
  · rw [sum_eq_zero]
    · have : n + 1 < p := by
        simp only [mem_filter, mem_range, not_and] at hpS
        by_contra h; exact hpS (by omega) hp
      simp [Vp, Nat.div_eq_of_lt (show n < p - 1 by omega)]
    · intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      rw [(mem_filter.1 hq).2.factorization, Finsupp.single_eq_of_ne hqp.symm, mul_zero]

/-- `lcmDen (norlund n) · n! = A053657(n+1)`. -/
private theorem lcmDen_mul_fact (n : ℕ) : lcmDen (norlund n) * n.factorial = A053657 (n + 1) := by
  have hA : A053657 (n + 1) ≠ 0 := by
    unfold A053657
    exact prod_ne_zero_iff.2 (fun q hq => pow_ne_zero _ (Nat.Prime.ne_zero (mem_filter.1 hq).2))
  apply Nat.eq_of_factorization_eq (mul_ne_zero (lcmDen_ne_zero _) (Nat.factorial_ne_zero _)) hA
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [factorization_A053657 n p hp, Nat.factorization_mul (lcmDen_ne_zero _)
      (Nat.factorial_ne_zero _), Finsupp.add_apply, Nat.factorization_def _ hp,
      Nat.factorization_def _ hp, val_lcmDen_norlund]
    have := fact_val_le_Vp (p := p) n
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The leading coefficient of `B_n^(x)` is `(-1/2)^n`. -/
private lemma norlund_getD_self (n : ℕ) : (norlund n).getD n 0 = (-1 / 2 : ℚ) ^ n := by
  rw [norlund_getD, aco_self]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- `|A290030(n) / A053657(n+1)| = 1/(2^n n!)`. -/
private theorem A290030_ratio (n : ℕ) :
    |(A290030 n : ℚ) / (A053657 (n + 1) : ℚ)| = 1 / (2 ^ n * (n.factorial : ℚ)) := by
  set L := lcmDen (norlund n) with hL
  have hmem : (-1 / 2 : ℚ) ^ n ∈ norlund n := by
    rw [← norlund_getD_self]
    exact mem_of_getD_ne_zero _ _ (by rw [norlund_getD_self]; positivity)
  have hden : ((-1 / 2 : ℚ) ^ n).den = 2 ^ n := by
    rw [Rat.den_pow]; congr 1; norm_num
  have hdvd : 2 ^ n ∣ L := hden ▸ den_dvd_lcmDen _ _ hmem
  obtain ⟨M, hM⟩ := hdvd
  have hL0 : L ≠ 0 := lcmDen_ne_zero _
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM; exact hL0 hM
  have hA : A290030 n = (-1) ^ n * (M : ℤ) := by
    unfold A290030
    rw [← hL, norlund_getD_self, hM]
    have : ((2 ^ n * M : ℕ) : ℚ) * (-1 / 2 : ℚ) ^ n = (((-1) ^ n * (M : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [div_pow, mul_div_assoc']
      field_simp
    rw [this, Rat.num_intCast]
  rw [hA, ← lcmDen_mul_fact, ← hL, hM]
  push_cast
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hM' : (0 : ℚ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
  rw [abs_of_pos hM', abs_of_pos (by positivity)]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

end LeadingCoefficient

section TriangleLists
open Finset Math0.Statements.A342645

/-- The rational polynomial with integer coefficient list `l` (lowest degree first). -/
private noncomputable def toPolyZ : List ℤ → Polynomial ℚ
  | [] => 0
  | a :: l => Polynomial.C (a : ℚ) + Polynomial.X * toPolyZ l

/-- Coefficients of `toPolyZ`. -/
private lemma coeff_toPolyZ (l : List ℤ) (k : ℕ) : (toPolyZ l).coeff k = ((l.getD k 0 : ℤ) : ℚ) := by
  induction l generalizing k with
  | nil => simp [toPolyZ]
  | cons a l ih =>
    cases k with
    | zero => simp [toPolyZ]
    | succ k =>
      simp only [toPolyZ, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih,
        List.getD_cons_succ]
      simp

/-- `addZ` is polynomial addition. -/
private lemma toPolyZ_addZ (a b : List ℤ) : toPolyZ (addZ a b) = toPolyZ a + toPolyZ b := by
  induction a generalizing b with
  | nil => simp [addZ, toPolyZ]
  | cons x a ih =>
    cases b with
    | nil => simp [addZ, toPolyZ]
    | cons y b => simp only [addZ, toPolyZ, ih, Int.cast_add, map_add]; ring

/-- Scaling a coefficient list. -/
private lemma toPolyZ_map_mul (c : ℤ) (l : List ℤ) :
    toPolyZ (l.map (fun a => c * a)) = Polynomial.C (c : ℚ) * toPolyZ l := by
  induction l with
  | nil => simp [toPolyZ]
  | cons x l ih => simp only [List.map_cons, toPolyZ, ih, Int.cast_mul, map_mul]; ring

/-- `mulXsub c` multiplies by `x - c`. -/
private lemma toPolyZ_mulXsub (c : ℤ) (l : List ℤ) :
    toPolyZ (mulXsub c l) = (Polynomial.X - Polynomial.C (c : ℚ)) * toPolyZ l := by
  unfold mulXsub
  rw [toPolyZ_addZ, toPolyZ, toPolyZ_map_mul]
  simp only [Int.cast_zero, map_zero, zero_add, Int.cast_neg, map_neg]
  ring

/-- `fallingFrom c j` is `(x-c)(x-c-1)⋯(x-c-j+1)`. -/
private lemma toPolyZ_fallingFrom (c j : ℕ) :
    toPolyZ (fallingFrom c j) =
      (descPochhammer ℚ j).comp (Polynomial.X - Polynomial.C (c : ℚ)) := by
  induction j with
  | zero => simp [fallingFrom, toPolyZ]
  | succ j ih =>
    rw [fallingFrom, toPolyZ_mulXsub, ih, descPochhammer_succ_right, Polynomial.mul_comp,
      Polynomial.sub_comp, Polynomial.X_comp]
    rw [show ((j : Polynomial ℚ)) = Polynomial.C (j : ℚ) by simp, Polynomial.C_comp]
    push_cast
    rw [map_add]; ring

/-- The polynomial computed by `newton`. -/
private lemma toPolyZ_newton (n j : ℕ) (ds : List ℤ) :
    toPolyZ (newton n j ds) = ∑ i ∈ range ds.length,
      Polynomial.C (((ds.getD i 0 : ℤ) : ℚ) * ((n.factorial / (j + i).factorial : ℕ) : ℚ)) *
        (descPochhammer ℚ (j + i)).comp (Polynomial.X - Polynomial.C (n : ℚ)) := by
  induction ds generalizing j with
  | nil => simp [newton, toPolyZ]
  | cons d ds ih =>
    rw [newton, toPolyZ_addZ, toPolyZ_map_mul, toPolyZ_fallingFrom, ih, List.length_cons,
      sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    · refine sum_congr rfl (fun i _ => ?_)
      rw [show j + 1 + i = j + (i + 1) by ring]
    · rw [mul_comm, Int.cast_mul, Int.cast_natCast]; ring

/-- Length of `diffHeads`. -/
private lemma diffHeads_length (k : ℕ) (v : List ℤ) : (diffHeads k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [diffHeads, ih]

/-- Entries of the difference list. -/
private lemma getD_zipWith_sub (v : List ℤ) (m : ℕ) (hm : m + 1 < v.length) :
    (List.zipWith (· - ·) v.tail v).getD m 0 = v.getD (m + 1) 0 - v.getD m 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_zipWith, List.getElem?_tail, List.getElem?_eq_getElem hm,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-- `diffHeads` lists the iterated forward differences at `0`. -/
private lemma diffHeads_getD (k : ℕ) (v : List ℤ) (i : ℕ) (hi : i < k) (hk : k ≤ v.length) :
    (diffHeads k v).getD i 0 = (fwdDiff 1)^[i] (fun m : ℕ => v.getD m 0) 0 := by
  induction k generalizing v i with
  | zero => omega
  | succ k ih =>
    rcases i with _ | i
    · simp only [diffHeads, List.getD_cons_zero, Function.iterate_zero, id]
      cases v <;> simp
    · simp only [diffHeads, List.getD_cons_succ]
      have hlen : k ≤ (List.zipWith (· - ·) v.tail v).length := by
        simp [List.length_zipWith, List.length_tail]; omega
      rw [ih _ i (by omega) hlen, Function.iterate_succ_apply, fwdDiff_iter_eq_sum_shift,
        fwdDiff_iter_eq_sum_shift]
      refine sum_congr rfl (fun m hm => ?_)
      have hm' := mem_range.1 hm
      congr 1
      simp only [smul_eq_mul, mul_one, zero_add, fwdDiff]
      rw [getD_zipWith_sub v m (by omega)]

end TriangleLists

section Mahonian
open Finset Math0.Statements.A342645

/-- `∏_{i=1}^{x} (1 - q^i)`. -/
private noncomputable def Pprod (x : ℕ) : Polynomial ℤ :=
  ∏ i ∈ range x, (1 - Polynomial.X ^ (i + 1))

/-- `e_a = [q^a] ∏_{i ≥ 1} (1 - q^i)`. -/
private noncomputable def ecoef (a : ℕ) : ℤ := (Pprod a).coeff a

/-- `binom(x + m - 1, m) = x(x+1)⋯(x+m-1)/m!` as a polynomial in `x`. -/
private noncomputable def Rpoly (m : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / (m.factorial : ℚ)) * ascPochhammer ℚ m

/-- The column polynomial `P_n(x) = ∑_{a ≤ n} e_a binom(x+n-a-1, n-a)`. -/
private noncomputable def Mcol (n : ℕ) : Polynomial ℚ :=
  ∑ a ∈ range (n + 1), Polynomial.C (ecoef a : ℚ) * Rpoly (n - a)

/-- `[q^a] ∏_{i ≤ x} (1 - q^i) = e_a` once `x ≥ a`. -/
private lemma Pprod_coeff_stable (a x : ℕ) (h : a ≤ x) : (Pprod x).coeff a = ecoef a := by
  induction x, h using Nat.le_induction with
  | base => rfl
  | succ x hx ih =>
    rw [Pprod, prod_range_succ, ← Pprod, mul_sub, mul_one, Polynomial.coeff_sub,
      Polynomial.coeff_mul_X_pow', if_neg (by omega), sub_zero, ih]

/-- `(∏_{i<x} (1 + q + ⋯ + q^i)) (1-q)^x = ∏_{i=1}^{x} (1 - q^i)`. -/
private lemma mahonianPoly_map_mul (x : ℕ) :
    (mahonianPoly x).map (Nat.castRingHom ℤ) * (1 - Polynomial.X) ^ x = Pprod x := by
  unfold mahonianPoly Pprod
  rw [Polynomial.map_prod, ← card_range x, ← prod_const, card_range, ← prod_mul_distrib]
  refine prod_congr rfl (fun i _ => ?_)
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_pow, Polynomial.map_X]
  exact geom_sum_mul_neg _ _

/-- `[q^b] (1-q)^(-x) = x(x+1)⋯(x+b-1)/b!`. -/
private lemma coeff_invOneSubPow (x b : ℕ) :
    ((PowerSeries.coeff b (PowerSeries.invOneSubPow ℤ x).val : ℤ) : ℚ) =
      (ascPochhammer ℚ b).eval (x : ℚ) / (b.factorial : ℚ) := by
  rcases x with _ | d
  · rw [PowerSeries.invOneSubPow_zero, Units.val_one, PowerSeries.coeff_one, Nat.cast_zero,
      ascPochhammer_eval_zero]
    split_ifs <;> simp_all
  · rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose, Nat.choose_symm_add]
    have : (b.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp

/-- For `x ≥ n`, the Mahonian number `mahonian x n` equals `P_n(x)`. -/
private theorem mahonian_eq_Mcol (x n : ℕ) (h : n ≤ x) :
    (mahonian x n : ℚ) = (Mcol n).eval (x : ℚ) := by
  -- power series identity
  set u := PowerSeries.invOneSubPow ℤ x
  have hP : (((mahonianPoly x).map (Nat.castRingHom ℤ) : Polynomial ℤ) : PowerSeries ℤ) =
      (Pprod x : PowerSeries ℤ) * u.val := by
    have h1 : (((mahonianPoly x).map (Nat.castRingHom ℤ) : Polynomial ℤ) : PowerSeries ℤ) *
        (1 - PowerSeries.X) ^ x = (Pprod x : PowerSeries ℤ) := by
      rw [← mahonianPoly_map_mul x, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
        Polynomial.coe_one, Polynomial.coe_X]
    have h2 : (1 - PowerSeries.X : PowerSeries ℤ) ^ x * u.val = 1 := by
      rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]; exact u.inv_val
    rw [← h1, mul_assoc, h2, mul_one]
  have hc := congrArg (PowerSeries.coeff n) hP
  rw [Polynomial.coeff_coe, Polynomial.coeff_map, coeff_mahonianPoly, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (Pprod x : PowerSeries ℤ) *
      PowerSeries.coeff b u.val)] at hc
  have hc' : (mahonian x n : ℚ) = ((∑ a ∈ range (n + 1), PowerSeries.coeff a (Pprod x : PowerSeries ℤ) *
      PowerSeries.coeff (n - a) u.val : ℤ) : ℚ) := by
    rw [← hc]; simp
  rw [hc', Mcol, Polynomial.eval_finsetSum]
  push_cast
  refine sum_congr rfl (fun a ha => ?_)
  have ha' := mem_range.1 ha
  rw [Pprod_coeff_stable a x (by omega), coeff_invOneSubPow, Rpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

end Mahonian

section Interpolation
open Finset Math0.Statements.A342645

/-- `deg binom(x+m-1, m) ≤ m`. -/
private lemma natDegree_Rpoly_le (m : ℕ) : (Rpoly m).natDegree ≤ m := by
  unfold Rpoly
  exact (Polynomial.natDegree_C_mul_le _ _).trans (ascPochhammer_natDegree ℚ m).le

/-- `deg P_n ≤ n`. -/
private lemma natDegree_Mcol_le (n : ℕ) : (Mcol n).natDegree ≤ n := by
  unfold Mcol
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  exact (Polynomial.natDegree_C_mul_le _ _).trans ((natDegree_Rpoly_le _).trans (Nat.sub_le _ _))

/-- The interpolation data has `n + 1` entries. -/
private lemma column_length (n : ℕ) : (column n).length = n + 1 := by simp [column]

/-- The interpolation data are Mahonian numbers. -/
private lemma column_getD (n m : ℕ) (hm : m ≤ n) : (column n).getD m 0 = (mahonian (n + m) n : ℤ) := by
  rw [column, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- The forward differences of the interpolation data are those of `P_n` at `x = n`. -/
private lemma diff_eq (n i : ℕ) (hi : i ≤ n) :
    (((diffHeads (n + 1) (column n)).getD i 0 : ℤ) : ℚ) =
      (fwdDiff 1)^[i] (fun x : ℚ => (Mcol n).eval x) (n : ℚ) := by
  rw [diffHeads_getD (n + 1) (column n) i (by omega) (by rw [column_length]),
    fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  refine sum_congr rfl (fun k hk => ?_)
  have hk' := mem_range.1 hk
  simp only [zsmul_eq_mul, smul_eq_mul, mul_one, zero_add, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  congr 1
  rw [column_getD n k (by omega), Int.cast_natCast, mahonian_eq_Mcol (n + k) n (by omega)]
  push_cast; ring_nf

/-- Row `n` of the triangle is the coefficient list of `n! P_n(x)` (Newton interpolation of a polynomial of degree `≤ n`). -/
private lemma Trow_poly (n : ℕ) :
    toPolyZ (Trow n) = Polynomial.C (n.factorial : ℚ) * Mcol n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun y : ℕ => (n : ℚ) + y))
  · rintro _ ⟨y, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [Trow, toPolyZ_newton, diffHeads_length, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    have hnewton := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ)) (fun x : ℚ => (Mcol n).eval x) y (n : ℚ)
    simp only [nsmul_eq_mul, mul_one] at hnewton
    rw [hnewton, mul_sum]
    have hsub1 : range (n + 1) ⊆ range (n + y + 1) := range_subset_range.2 (by omega)
    have hsub2 : range (y + 1) ⊆ range (n + y + 1) := range_subset_range.2 (by omega)
    rw [sum_subset hsub1, sum_subset hsub2]
    · refine sum_congr rfl (fun i hi => ?_)
      by_cases hin : i ≤ n
      · simp only [zero_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
          Polynomial.eval_sub, Polynomial.eval_X, add_sub_cancel_left,
          descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
        rw [diff_eq n i hin, Nat.cast_div (Nat.factorial_dvd_factorial hin) (by positivity)]
        have : (i.factorial : ℚ) ≠ 0 := by positivity
        push_cast
        field_simp
      · have hz : (fwdDiff 1)^[i] (fun x : ℚ => (Mcol n).eval x) = 0 :=
          Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (lt_of_le_of_lt (natDegree_Mcol_le n) (by omega))
        rw [hz]
        have hz2 : (diffHeads (n + 1) (column n)).getD i 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [diffHeads_length]; omega)]
          rfl
        rw [hz2]; simp
    · intro i hi hi'
      simp only [mem_range] at hi hi'
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    · intro i hi hi'
      simp only [mem_range] at hi hi'
      have hz2 : (diffHeads (n + 1) (column n)).getD i 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [diffHeads_length]; omega)]
        rfl
      rw [hz2]; simp
  · exact Set.infinite_range_of_injective (fun a b h => by simpa using h)

/-- `T(n,k) = n! [x^k] P_n(x)`. -/
private theorem T_eq (n k : ℕ) : (T n k : ℚ) = (n.factorial : ℚ) * (Mcol n).coeff k := by
  rw [T, ← coeff_toPolyZ, Trow_poly, Polynomial.coeff_C_mul]

end Interpolation

section Stirling
open Finset Math0.Statements.A342645 Polynomial

/-- Unsigned Stirling numbers of the first kind: `x(x+1)⋯(x+m-1) = ∑_k c(m,k) x^k`. -/
private noncomputable def cst (m k : ℕ) : ℕ := (ascPochhammer ℕ m).coeff k

/-- `c(m+1,k+1) = c(m,k) + m c(m,k+1)`. -/
private lemma cst_succ_succ (m k : ℕ) : cst (m + 1) (k + 1) = cst m k + m * cst m (k + 1) := by
  unfold cst
  rw [ascPochhammer_succ_right, mul_add, coeff_add, coeff_mul_X,
    show ((m : ℕ[X])) = C m by simp, coeff_mul_C]
  ring

/-- `c(m,k) = 0` for `k > m`. -/
private lemma cst_eq_zero (m k : ℕ) (h : m < k) : cst m k = 0 := by
  unfold cst
  apply coeff_eq_zero_of_natDegree_lt
  rw [ascPochhammer_natDegree]; exact h

/-- `c(m,m) = 1`. -/
private lemma cst_self (m : ℕ) : cst m m = 1 := by
  unfold cst
  have := monic_ascPochhammer ℕ m
  rw [Monic, leadingCoeff, ascPochhammer_natDegree] at this
  exact this

/-- `c(m,0) = 0` for `m > 0`. -/
private lemma cst_zero_right (m : ℕ) (hm : 0 < m) : cst m 0 = 0 := by
  unfold cst
  rw [coeff_zero_eq_eval_zero, ascPochhammer_eval_zero, if_neg (by omega)]

/-- Coefficients of `binom(x+m-1, m)`. -/
private lemma coeff_Rpoly (m k : ℕ) : (Rpoly m).coeff k = (cst m k : ℚ) / (m.factorial : ℚ) := by
  unfold Rpoly cst
  rw [coeff_C_mul, ← ascPochhammer_map (Nat.castRingHom ℚ), coeff_map]
  simp; ring

/-- `e_0 = 1`. -/
private lemma ecoef_zero : ecoef 0 = 1 := by simp [ecoef, Pprod]

/-- `T(n,k) = ∑_a e_a n(n-1)⋯(n-a+1) c(n-a,k)`. -/
private theorem T_formula (n k : ℕ) : (T n k : ℚ) =
    ∑ a ∈ range (n + 1), (ecoef a : ℚ) * (n.descFactorial a : ℚ) * (cst (n - a) k : ℚ) := by
  rw [T_eq, Mcol, finsetSum_coeff, mul_sum]
  refine sum_congr rfl (fun a ha => ?_)
  have ha' : a ≤ n := Nat.lt_succ_iff.1 (mem_range.1 ha)
  rw [coeff_C_mul, coeff_Rpoly]
  have h1 := Nat.factorial_mul_descFactorial ha'
  have h2 : ((n - a).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) = (n - a).factorial * n.descFactorial a := by exact_mod_cast h1.symm
  rw [h3]
  field_simp

/-- Discrete antiderivative: for `deg P ≤ d` there is `Q` with `Q(x+1) - Q(x) = P(x)`, `deg Q ≤ d + 1` and `[x^(d+1)] Q = [x^d] P / (d+1)`. -/
private lemma antidiff (d : ℕ) : ∀ P : ℚ[X], P.natDegree ≤ d →
    ∃ Q : ℚ[X], Q.comp (X + 1) - Q = P ∧ Q.natDegree ≤ d + 1 ∧
      Q.coeff (d + 1) = P.coeff d / (d + 1) := by
  induction d with
  | zero =>
    intro P hP
    rw [Nat.le_zero, natDegree_eq_zero] at hP
    obtain ⟨c, rfl⟩ := hP
    refine ⟨C c * X, ?_, ?_, ?_⟩
    · simp [mul_add]
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  | succ d ih =>
    intro P hP
    set a := P.coeff (d + 1)
    set Q0 : ℚ[X] := C (a / (d + 2)) * X ^ (d + 2)
    set R := Q0.comp (X + 1) - Q0
    have hR : ∀ j, R.coeff j = a / (d + 2) * (((d + 2).choose j : ℚ) - if j = d + 2 then 1 else 0) := by
      intro j
      simp only [R, Q0, mul_comp, C_comp, X_pow_comp, coeff_sub, coeff_C_mul, coeff_X_add_one_pow,
        coeff_X_pow]
      ring
    have hP' : (P - R).natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [coeff_sub, hR]
      have hj' : d < j := by exact_mod_cast hj
      rcases Nat.lt_trichotomy j (d + 2) with h | h | h
      · have : j = d + 1 := by omega
        subst this
        rw [Nat.choose_succ_self_right, if_neg (by omega)]
        have : (d : ℚ) + 2 ≠ 0 := by positivity
        push_cast; field_simp; ring
      · subst h; rw [Nat.choose_self, if_pos rfl, coeff_eq_zero_of_natDegree_lt (by omega)]; simp
      · rw [Nat.choose_eq_zero_of_lt h, if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    obtain ⟨Q', hQ'1, hQ'2, _⟩ := ih (P - R) hP'
    refine ⟨Q0 + Q', ?_, ?_, ?_⟩
    · rw [add_comp]
      have : R = Q0.comp (X + 1) - Q0 := rfl
      linear_combination hQ'1 - this
    · refine (natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact (natDegree_C_mul_le _ _).trans (by simp)
    · rw [coeff_add, coeff_eq_zero_of_natDegree_lt (show Q'.natDegree < d + 1 + 1 by omega)]
      simp only [Q0, coeff_C_mul, coeff_X_pow]
      push_cast; ring

end Stirling

section Diagonals
open Finset Math0.Statements.A342645 Polynomial

/-- `c(N, N-r)` is a polynomial in `N ≥ r` of degree `2r` with leading coefficient `1/(2^r r!)`. -/
private lemma Ddiag (r : ℕ) : ∃ D : ℚ[X], (∀ N : ℕ, r ≤ N → D.eval (N : ℚ) = (cst N (N - r) : ℚ)) ∧
    D.natDegree = 2 * r ∧ D.leadingCoeff = 1 / (2 ^ r * (r.factorial : ℚ)) := by
  induction r with
  | zero =>
    refine ⟨1, fun N _ => ?_, by simp, by simp⟩
    simp [cst_self]
  | succ r ih =>
    obtain ⟨D', hD'1, hD'2, hD'3⟩ := ih
    have hD'0 : D' ≠ 0 := by
      intro h; rw [h, leadingCoeff_zero] at hD'3
      have : (0 : ℚ) < 1 / (2 ^ r * (r.factorial : ℚ)) := by positivity
      linarith
    set P := X * D'
    have hPdeg : P.natDegree = 2 * r + 1 := by
      simp only [P]; rw [natDegree_X_mul hD'0, hD'2]
    have hPc : P.coeff (2 * r + 1) = 1 / (2 ^ r * (r.factorial : ℚ)) := by
      simp only [P]; rw [coeff_X_mul, ← hD'2]; exact hD'3
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := antidiff (2 * r + 1) P hPdeg.le
    set D := Q - C (Q.eval ((r + 1 : ℕ) : ℚ))
    have hstep : ∀ x : ℚ, Q.eval (x + 1) - Q.eval x = x * D'.eval x := by
      intro x
      have := congrArg (eval x) hQ1
      simpa [eval_comp, P] using this
    have hcoef : Q.coeff (2 * r + 1 + 1) ≠ 0 := by
      rw [hQ3, hPc]; positivity
    have hQdeg : Q.natDegree = 2 * (r + 1) := by
      have := natDegree_eq_of_le_of_coeff_ne_zero hQ2 hcoef
      rw [this]; ring
    refine ⟨D, ?_, ?_, ?_⟩
    · intro N hN
      induction N, hN using Nat.le_induction with
      | base =>
        simp only [D, eval_sub, eval_C, sub_self, Nat.sub_self]
        rw [cst_zero_right _ (by omega)]; simp
      | succ N hN ihN =>
        have h1 : D.eval ((N + 1 : ℕ) : ℚ) = D.eval (N : ℚ) + N * D'.eval (N : ℚ) := by
          simp only [D, eval_sub, eval_C]
          have := hstep (N : ℚ)
          push_cast
          linarith
        rw [h1, ihN, hD'1 N (by omega)]
        have h2 := cst_succ_succ N (N - (r + 1))
        rw [show N - (r + 1) + 1 = N - r by omega] at h2
        rw [show N + 1 - (r + 1) = N - (r + 1) + 1 by omega, show N - (r + 1) + 1 = N - r by omega,
          h2]
        push_cast; ring
    · simp only [D]; rw [natDegree_sub_C, hQdeg]
    · rw [leadingCoeff, show D.natDegree = 2 * (r + 1) by simp only [D]; rw [natDegree_sub_C, hQdeg]]
      simp only [D, coeff_sub, coeff_C, if_neg (show 2 * (r + 1) ≠ 0 by omega), sub_zero]
      rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring, hQ3, hPc]
      push_cast [Nat.factorial_succ]
      have : (r.factorial : ℚ) ≠ 0 := by positivity
      field_simp
      ring

/-- `T(n, n-m)` is a polynomial in `n ≥ m` of degree `2m` with leading coefficient `1/(2^m m!)`. -/
private theorem diag (m : ℕ) : ∃ Q : ℚ[X], Q.natDegree = 2 * m ∧
    Q.leadingCoeff = 1 / (2 ^ m * (m.factorial : ℚ)) ∧
    ∀ n : ℕ, m ≤ n → (T n (n - m) : ℚ) = Q.eval (n : ℚ) := by
  choose D hD using Ddiag
  set f : ℕ → ℚ[X] := fun j => C (ecoef j : ℚ) * descPochhammer ℚ j *
    (D (m - j)).comp (X - C (j : ℚ))
  set Q := ∑ j ∈ range (m + 1), f j
  have hf0 : f 0 = D m := by
    simp [f, ecoef_zero]
  have hrest : ∀ j ∈ range m, (f (j + 1)).natDegree ≤ 2 * m - 1 := by
    intro j hj
    have hj' := mem_range.1 hj
    simp only [f]
    refine (natDegree_mul_le).trans ?_
    have h1 : (C (ecoef (j + 1) : ℚ) * descPochhammer ℚ (j + 1)).natDegree ≤ j + 1 :=
      (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree ℚ (j + 1)).le
    have h2 : ((D (m - (j + 1))).comp (X - C ((j + 1 : ℕ) : ℚ))).natDegree ≤ 2 * (m - (j + 1)) := by
      rw [natDegree_comp, (hD _).2.1, natDegree_X_sub_C, mul_one]
    omega
  have hQ : Q = D m + ∑ j ∈ range m, f (j + 1) := by
    simp only [Q]; rw [sum_range_succ', hf0, add_comm]
  have hDm := hD m
  have hdeg : Q.natDegree = 2 * m ∧ Q.leadingCoeff = 1 / (2 ^ m * (m.factorial : ℚ)) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [hQ, h0, range_zero, sum_empty, add_zero]
      exact ⟨by rw [(hD 0).2.1], by rw [(hD 0).2.2]⟩
    · have hlt : (∑ j ∈ range m, f (j + 1)).natDegree < (D m).natDegree := by
        rw [hDm.2.1]
        exact lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ hrest) (by omega)
      refine ⟨?_, ?_⟩
      · rw [hQ, natDegree_add_eq_left_of_natDegree_lt hlt, hDm.2.1]
      · rw [hQ, leadingCoeff_add_of_degree_lt' (degree_lt_degree hlt), hDm.2.2]
  refine ⟨Q, hdeg.1, hdeg.2, ?_⟩
  · intro n hn
    rw [T_formula]
    simp only [Q, f, eval_finsetSum, eval_mul, eval_C, eval_comp, eval_sub, eval_X,
      descPochhammer_eval_eq_descFactorial]
    have hsub : range (m + 1) ⊆ range (n + 1) := range_subset_range.2 (by omega)
    rw [← sum_subset hsub]
    · refine sum_congr rfl (fun j hj => ?_)
      have hj' := Nat.lt_succ_iff.1 (mem_range.1 hj)
      rw [show (n : ℚ) - (j : ℚ) = ((n - j : ℕ) : ℚ) by push_cast [Nat.cast_sub (by omega : j ≤ n)]; ring,
        (hD (m - j)).1 (n - j) (by omega), show n - j - (m - j) = n - m by omega]
    · intro a ha ha'
      simp only [mem_range] at ha ha'
      rw [cst_eq_zero (n - a) (n - m) (by omega)]; simp

end Diagonals

section Formulas
open Finset Math0.Statements.A342645 Polynomial

/-- `T(n, n-m) = ∑_{a ≤ m} e_a n(n-1)⋯(n-a+1) c(n-a, n-m)`. -/
private lemma T_diag_sum (n m : ℕ) (h : m ≤ n) : (T n (n - m) : ℚ) =
    ∑ a ∈ range (m + 1), (ecoef a : ℚ) * (n.descFactorial a : ℚ) * (cst (n - a) (n - m) : ℚ) := by
  rw [T_formula]
  symm
  apply sum_subset (range_subset_range.2 (by omega))
  intro a ha ha'
  simp only [mem_range] at ha ha'
  rw [cst_eq_zero (n - a) (n - m) (by omega)]; simp

/-- `e_1 = -1`. -/
private lemma ecoef_one : ecoef 1 = -1 := by
  simp [ecoef, Pprod, coeff_one]

/-- `e_2 = -1`. -/
private lemma ecoef_two : ecoef 2 = -1 := by
  have : Pprod 2 = 1 - X - X ^ 2 + X ^ 3 := by
    simp [Pprod, prod_range_succ]; ring
  rw [ecoef, this]
  simp [coeff_X_pow, coeff_one, coeff_X]

/-- `e_3 = 0`. -/
private lemma ecoef_three : ecoef 3 = 0 := by
  have : Pprod 3 = 1 - X - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by
    simp [Pprod, prod_range_succ]; ring
  rw [ecoef, this]
  simp [coeff_X_pow, coeff_one, coeff_X]

/-- `c(k+1, k) = (k+1)k/2`. -/
private lemma cst1 (k : ℕ) : (cst (k + 1) k : ℚ) = (k + 1) * k / 2 := by
  induction k with
  | zero => simp [cst_zero_right]
  | succ k ih =>
    rw [cst_succ_succ, cst_self]; push_cast; rw [ih]; ring

/-- `c(k+2, k) = (k+2)(k+1)k(3k+5)/24`. -/
private lemma cst2 (k : ℕ) : (cst (k + 2) k : ℚ) = (k + 2) * (k + 1) * k * (3 * k + 5) / 24 := by
  induction k with
  | zero => simp [cst_zero_right]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, cst_succ_succ]
    push_cast
    rw [ih, show k + 2 = (k + 1) + 1 by ring, cst1]
    push_cast; ring

/-- `c(k+3, k) = (k+3)²(k+2)²(k+1)k/48`. -/
private lemma cst3 (k : ℕ) :
    (cst (k + 3) k : ℚ) = (k + 3) ^ 2 * (k + 2) ^ 2 * (k + 1) * k / 48 := by
  induction k with
  | zero => simp [cst_zero_right]
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, cst_succ_succ]
    push_cast
    rw [ih, show k + 3 = (k + 1) + 2 by ring, cst2]
    push_cast; ring

/-- `T(n,n) = 1`. -/
private theorem formula0 (n : ℕ) : T n n = 1 := by
  have h := T_diag_sum n 0 (Nat.zero_le n)
  simp only [Nat.sub_zero, zero_add, range_one, sum_singleton, ecoef_zero,
    Nat.descFactorial_zero, cst_self] at h
  have h' : (T n n : ℚ) = 1 := by rw [h]; norm_num
  exact_mod_cast h'

/-- `T(n,n-1) = (n² - 3n)/2`. -/
private theorem formula1 (n : ℕ) (hn : 1 ≤ n) :
    (T n (n - 1) : ℚ) = (-3 * (n : ℚ) + (n : ℚ) ^ 2) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [T_diag_sum _ 1 hn]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, Nat.add_sub_cancel,
    Nat.sub_zero, ecoef_zero, ecoef_one, Nat.descFactorial_zero, Nat.descFactorial_one, cst_self]
  rw [cst1]
  push_cast; ring

/-- `T(n,n-2) = (3n⁴ - 22n³ + 21n² - 2n)/24`. -/
private theorem formula2 (n : ℕ) (hn : 2 ≤ n) :
    (T n (n - 2) : ℚ) =
      (-2 * (n : ℚ) + 21 * (n : ℚ) ^ 2 - 22 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 4) / 24 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [T_diag_sum _ 2 hn]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, Nat.add_sub_cancel,
    Nat.sub_zero, ecoef_zero, ecoef_one, ecoef_two, Nat.descFactorial_zero, Nat.descFactorial_one,
    cst_self]
  rw [show k + 2 - 1 = k + 1 by omega, cst2, cst1]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  push_cast
  ring

/-- `T(n,n-3) = (n⁶ - 13n⁵ + 37n⁴ + 13n³ - 134n² + 96n)/48`. -/
private theorem formula3 (n : ℕ) (hn : 3 ≤ n) :
    (T n (n - 3) : ℚ) =
      (96 * (n : ℚ) - 134 * (n : ℚ) ^ 2 + 13 * (n : ℚ) ^ 3 + 37 * (n : ℚ) ^ 4
        - 13 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) / 48 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [T_diag_sum _ 3 hn]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, Nat.add_sub_cancel,
    Nat.sub_zero, ecoef_zero, ecoef_one, ecoef_two, ecoef_three, Nat.descFactorial_zero,
    Nat.descFactorial_one, cst_self]
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, cst3, cst2, cst1]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  push_cast
  ring

end Formulas

/-- Both conjectures of A342645 hold: every diagonal `n ↦ T(n, n-m)` is a polynomial of degree `2m`
with leading coefficient `|A290030(m)/A053657(m+1)| = 1/(2^m m!)`, and the four FORMULA identities
hold. -/
theorem result : statement := by
  refine ⟨fun m => ?_, formula0, formula1, formula2, formula3⟩
  obtain ⟨Q, hdeg, hlc, hT⟩ := diag m
  refine ⟨Q, ?_, ?_, hT⟩
  · have hQ0 : Q ≠ 0 := by
      intro h
      rw [h, Polynomial.leadingCoeff_zero] at hlc
      have : (0 : ℚ) < 1 / (2 ^ m * (m.factorial : ℚ)) := by positivity
      linarith
    rw [Polynomial.degree_eq_natDegree hQ0, hdeg]
  · rw [hlc, A290030_ratio]

end Math0.Frontier.A342645

#math0_settles Math0.Frontier.A342645.result Math0.Statements.A342645.statement

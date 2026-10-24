/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A362086
import Math0.Audit

/-!
# OEIS A362086: every denominator except 9 is 1 or a prime

We prove Bouras' conjecture: for every `n ≥ 3`, the denominator `a n` of
`1/(2-3/(3-4/(…(n-1)-n/(-3))))` is `1` or a prime, unless it equals `9` (which happens at `n = 5`).

*Closed form.* The convergents of the continued fraction have numerators `k+1` and denominators
`(k+1)·!k/2`, where `!k = 0! + ⋯ + (k-1)!` is the left factorial. Feeding in `-3` gives, with
`x = n-3` and `N = n^2+n-3 = x^2+7x+9`,
`cf n = (N·!x + 3(x+2)·x!) / (2N)`. Every intermediate tail is positive (each tail `t_k` with
`k ≤ n-1` is at least `k-2`), so Lean's `x/0 = 0` convention never intervenes. Since `N` is odd
and `N·!x + 3(x+2)·x!` is even, `a n = N / gcd(N, M)` with `M = 3(x+2)·x!`.

*Number theory* (for `x ≥ 33`). Let `d = N / gcd(N, M)` and let `p` be its least prime factor
(odd, as `N` is odd). If `p ∣ d` then `p^(j+1) ∣ N` whenever `p^j ∣ M`. Note
`(x+3)^2 < N < (x+4)^2`.
* `2p ≤ x`: then `p^(x/p) ∣ x! ∣ M`, so `p^(x/p+1) ≤ N < (x+4)^2 ≤ (p(x/p+1)+4)^2 < p^(x/p+1)`,
  which is impossible.
* `x < 2p ≤ 2x`: then `p ∣ M`, so `N = m p^2` with `m < 5`; parity and `(x+3)^2 < N < (x+4)^2`
  force `N = 3p^2`, and then `3p ∣ gcd(N, M)`, so `d ∣ p`.
* `p > x`: `N` is not divisible by `x+1, x+2, x+3` (as `N = (x+1)(x+6)+3 = (x+2)(x+5)-1 =
  (x+3)(x+4)-3`), so every prime factor of `d` is at least `x+4`; two of them would give
  `d ≥ (x+4)^2 > N`, so `d = p`.
The cases `n < 36` are read off from the kernel-checked data `a_data`.
-/

namespace Math0.Frontier.A362086
open Math0.Statements.A362086

/-- Left factorial `!m = 0! + 1! + ⋯ + (m-1)!`. -/
private def lf (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, i.factorial

/-- Recursion for the left factorial: `!(m+1) = !m + m!`. -/
private lemma lf_succ (m : ℕ) : lf (m+1) = lf m + m.factorial := by
  simp [lf, Finset.sum_range_succ]

/-- Peeling off the innermost level of the continued fraction: the fold over
`[2, …, m+2]` starting from `t` is the fold over `[2, …, m+1]` starting from `step (m+2) t`. -/
private lemma fold_concat (m : ℕ) (t : ℚ) :
    (List.range' 2 (m+1)).foldr step t = (List.range' 2 m).foldr step (step (m+2) t) := by
  rw [List.range'_concat, List.foldr_append]
  simp [add_comm]

/-- The value of `step 2 (step 3 (… (step (m+2) t)))` predicted by the convergents of the
continued fraction: numerators `k+1` and denominators `(k+1)·!k/2`. -/
private def F (m : ℕ) (t : ℚ) : ℚ :=
  2 * ((m+2) * t - (m+3) * (m+1)) / ((m+2) * (lf (m+1) : ℚ) * t - (m+3) * (m+1) * (lf m : ℚ))

/-- One more level of the continued fraction moves the convergent formula from `m` to `m+1`
(valid for every nonzero innermost value `t`). -/
private lemma F_step (m : ℕ) (t : ℚ) (ht : t ≠ 0) : F m (step (m+3) t) = F (m+1) t := by
  have h1 : (lf (m+1) : ℚ) = lf m + m.factorial := by rw [lf_succ]; push_cast; ring
  have h2 : (lf (m+1+1) : ℚ) = lf m + m.factorial + (m+1) * m.factorial := by
    rw [lf_succ, lf_succ, Nat.factorial_succ]; push_cast; ring
  calc F m (step (m+3) t)
      = (2 * ((m+3) * t - (m+4) * (m+2)) / t) /
        (((m+3) * (lf m + m.factorial + (m+1) * m.factorial) * t
          - (m+4) * (m+2) * (lf m + m.factorial)) / t) := by
        simp only [F, step, h1]
        push_cast
        congr 1
        · field_simp; ring
        · field_simp; ring
    _ = (2 * ((m+3) * t - (m+4) * (m+2))) /
        ((m+3) * (lf m + m.factorial + (m+1) * m.factorial) * t
          - (m+4) * (m+2) * (lf m + m.factorial)) := div_div_div_cancel_right₀ ht _ _
    _ = F (m+1) t := by
        simp only [F, h1, h2]
        push_cast
        ring_nf

/-- The fold equals the convergent formula as long as the innermost value is large enough;
this keeps every intermediate tail positive, so no division by zero ever occurs. -/
private lemma fold_eq_F (m : ℕ) : ∀ t : ℚ, (m + 1 : ℚ) ≤ t →
    (List.range' 2 (m+1)).foldr step t = F m t := by
  induction m with
  | zero =>
    intro t ht
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
    simp [F, step, lf]
    field_simp
    ring
  | succ m ih =>
    intro t ht
    push_cast at ht
    have htpos : 0 < t := by linarith
    rw [fold_concat]
    have hs : ((m + 1 : ℕ) : ℚ) + 0 ≤ step (m+3) t := by
      unfold step; push_cast
      have : ((m:ℚ)+3+1)/t ≤ 2 := by rw [div_le_iff₀ htpos]; linarith
      linarith
    rw [show m + 1 + 2 = m + 3 from rfl, ih _ (by simpa using hs)]
    exact F_step m t htpos.ne'

/-- Closed form: with `x = y+1`, `N = x^2+7x+9` (that is `n^2+n-3` for `n = x+3`),
`cf (x+3) = (N·!x + 3(x+2)·x!) / (2N)`. -/
private lemma cf_closed (y : ℕ) :
    cf (y+4) = (((y+1)^2+7*(y+1)+9) * lf (y+1) + 3*(y+3)*(y+1).factorial : ℕ) /
      (2*((y+1)^2+7*(y+1)+9) : ℕ) := by
  have hs : ((y + 1 : ℕ) : ℚ) ≤ step (y+3) (-3) := by
    unfold step; push_cast
    have : ((y:ℚ)+3+1)/(-3) = -(((y:ℚ)+4)/3) := by ring
    rw [this]
    have : (0:ℚ) ≤ ((y:ℚ)+4)/3 := by positivity
    linarith
  have hfold : (List.range' 2 (y+4-2)).foldr step (-3) = F (y+1) (-3) := by
    rw [show y+4-2 = (y+1)+1 by omega, fold_concat, show y+1+2 = y+3 from rfl,
      fold_eq_F y _ (by simpa using hs), F_step y (-3) (by norm_num)]
  unfold cf
  rw [hfold]
  unfold F
  rw [one_div_div]
  have hN : (0:ℚ) < (y:ℚ)^2 + 9*y + 17 := by positivity
  rw [div_eq_div_iff]
  · rw [lf_succ (y+1), lf_succ y, Nat.factorial_succ]
    push_cast
    ring
  · push_cast; nlinarith
  · push_cast; nlinarith

/-- `!x = 0! + 1! + ⋯ + (x-1)!` is even for `x ≥ 2`. -/
private lemma two_dvd_lf (x : ℕ) (hx : 2 ≤ x) : 2 ∣ lf x := by
  induction x, hx using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    rw [lf_succ]
    exact dvd_add ih (Nat.dvd_factorial (by norm_num) hx)

/-- `N = x^2+7x+9` is odd. -/
private lemma N_odd (x : ℕ) : ¬ 2 ∣ x^2 + 7*x + 9 := by
  intro h
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h0 <;>
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h0] at h

/-- The sequence in closed form: `a (x+3) = N / gcd(N, 3(x+2)·x!)` with `N = x^2+7x+9`. -/
private lemma a_eq (x : ℕ) (hx : 3 ≤ x) :
    a (x+3) = (x^2+7*x+9) / Nat.gcd (x^2+7*x+9) (3*(x+2)*x.factorial) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  set N := (y+1)^2+7*(y+1)+9 with hN
  set M := 3*((y+1)+2)*(y+1).factorial with hM
  have hW : 2 ∣ N * lf (y+1) + M := by
    refine dvd_add (dvd_mul_of_dvd_right (two_dvd_lf _ (by omega)) _) ?_
    exact dvd_mul_of_dvd_right (Nat.dvd_factorial (by norm_num) (by omega)) _
  obtain ⟨X, hX⟩ := hW
  have hcf : cf (y+1+3) = (X : ℚ) / (N : ℚ) := by
    rw [show y+1+3 = y+4 from rfl, cf_closed y]
    have : N * lf (y+1) + 3*(y+3)*(y+1).factorial = 2 * X := by rw [← hX]
    rw [this, show (2*((y+1)^2+7*(y+1)+9) : ℕ) = 2 * N from rfl]
    push_cast
    have hN0 : (N:ℚ) ≠ 0 := by positivity
    field_simp
  have hden : a (y+1+3) = N / Nat.gcd N X := by
    unfold a
    rw [hcf, show (X : ℚ) / (N : ℚ) = ((X : ℤ) : ℚ) / ((N : ℤ) : ℚ) by push_cast; rfl,
      ← Rat.divInt_eq_div, Rat.den_divInt]
    have hN0 : (N : ℤ) ≠ 0 := by positivity
    rw [if_neg hN0]
    simp [Int.gcd]
  rw [hden]
  congr 1
  have hcop : Nat.Coprime 2 N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (N_odd _)
  rw [← Nat.gcd_add_mul_right_right N M (lf (y+1)), show M + lf (y+1) * N = 2 * X by rw [← hX]; ring,
    Nat.gcd_comm N (2 * X), Nat.Coprime.gcd_mul_left_cancel X hcop, Nat.gcd_comm]

/-- `q^k ∣ (qk)!`, since `q, 2q, …, kq` all occur in the product. -/
private lemma pow_dvd_fact (q k : ℕ) (hq : 0 < q) : q^k ∣ (q*k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : q * (k+1) = (q*k + (q-1)) + 1 := by rw [Nat.mul_succ]; omega
    rw [h, Nat.factorial_succ, pow_succ, mul_comm (q^k)]
    apply mul_dvd_mul
    · rw [← h]; exact Dvd.intro (k+1) rfl
    · exact ih.trans (Nat.factorial_dvd_factorial (by omega))

/-- If `q` divides `N / gcd(N, M)`, then `q^(j+1) ∣ N` whenever `q^j ∣ M`. -/
private lemma pow_step {N M q : ℕ} (hq : q ∣ N / Nat.gcd N M) :
    ∀ j, q^j ∣ M → q^(j+1) ∣ N := by
  have hg : Nat.gcd N M ∣ N := Nat.gcd_dvd_left N M
  have hNe : N = Nat.gcd N M * (N / Nat.gcd N M) := (Nat.mul_div_cancel' hg).symm
  intro j
  induction j with
  | zero => intro _; simpa using hq.trans (Nat.div_dvd_of_dvd hg)
  | succ j ih =>
    intro hj
    have h1 : q^j ∣ M := (pow_dvd_pow q (Nat.le_succ j)).trans hj
    have h2 : q^(j+1) ∣ Nat.gcd N M := Nat.dvd_gcd (ih h1) hj
    rw [hNe, pow_succ]
    exact mul_dvd_mul h2 hq

/-- `(qj+4)^2 < q^j` for `q ≥ 3`, `j ≥ 6`. -/
private lemma bound6 (q : ℕ) (hq : 3 ≤ q) : ∀ j, 6 ≤ j → (q*j+4)^2 < q^j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have h1 : q^6 = q^4 * q^2 := by ring
    have h2 : 81 ≤ q^4 := by
      calc 81 = 3^4 := by norm_num
        _ ≤ q^4 := Nat.pow_le_pow_left hq 4
    rw [h1]; nlinarith
  | succ j hj ih =>
    rw [pow_succ]
    have h3 : (q*(j+1)+4)^2 ≤ 3*(q*j+4)^2 := by nlinarith
    calc (q*(j+1)+4)^2 ≤ 3*(q*j+4)^2 := h3
      _ < 3 * q^j := by omega
      _ ≤ q^j * q := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hq

/-- `(qj+4)^2 < q^j` for `q, j ≥ 3` and `qj ≥ 34`. -/
private lemma bound (q j : ℕ) (hq : 3 ≤ q) (hj : 3 ≤ j) (hqj : 34 ≤ q*j) :
    (q*j+4)^2 < q^j := by
  rcases (show j = 3 ∨ j = 4 ∨ j = 5 ∨ 6 ≤ j by omega) with rfl | rfl | rfl | h6
  · have : 12 ≤ q := by omega
    nlinarith
  · have : 9 ≤ q := by omega
    have h1 : q^4 = q^2 * q^2 := by ring
    have h2 : 81 ≤ q^2 := by nlinarith
    rw [h1]; nlinarith
  · have : 7 ≤ q := by omega
    have h1 : q^5 = q^3 * q^2 := by ring
    have h2 : 343 ≤ q^3 := by
      calc 343 = 7^3 := by norm_num
        _ ≤ q^3 := Nat.pow_le_pow_left this 3
    rw [h1]; nlinarith
  · exact bound6 q hq j h6

/-- `x + k` divides `N + c` for small shifts, so it cannot divide `N` when `x` is large. -/
private lemma not_dvd_aux (x k c : ℕ) (hk : x + k ∣ x^2 + 7*x + 9 + c) (hc : c < x + k)
    (hc' : 0 < c) : ¬ x + k ∣ x^2 + 7*x + 9 := by
  intro h
  have := (Nat.dvd_add_right h).mp hk
  have := Nat.le_of_dvd hc' this
  omega

/-- The number-theoretic core: for `x ≥ 33`, `N / gcd(N, 3(x+2)·x!)` is `1` or a prime,
where `N = x^2+7x+9`. -/
private lemma main (x : ℕ) (hx : 33 ≤ x) :
    (x^2+7*x+9) / Nat.gcd (x^2+7*x+9) (3*(x+2)*x.factorial) = 1 ∨
    ((x^2+7*x+9) / Nat.gcd (x^2+7*x+9) (3*(x+2)*x.factorial)).Prime := by
  set N := x^2+7*x+9 with hN
  set M := 3*(x+2)*x.factorial with hM
  set g := Nat.gcd N M with hg
  set d := N / g with hd
  have hNpos : 0 < N := by positivity
  have hgN : g ∣ N := Nat.gcd_dvd_left N M
  have hdN : d ∣ N := Nat.div_dvd_of_dvd hgN
  have hNgd : N = g * d := (Nat.mul_div_cancel' hgN).symm
  have hodd : ¬ 2 ∣ N := N_odd x
  have hfM : x.factorial ∣ M := Dvd.intro_left _ rfl
  have hN4 : N < (x+4)^2 := by rw [hN]; nlinarith
  by_cases hd1 : d = 1
  · left; exact hd1
  have hpp : d.minFac.Prime := Nat.minFac_prime hd1
  set p := d.minFac with hp
  have hpd : p ∣ d := Nat.minFac_dvd d
  have hpN : p ∣ N := hpd.trans hdN
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    rcases (show p = 2 ∨ 3 ≤ p by omega) with h | h
    · rw [h] at hpN; exact absurd hpN hodd
    · exact h
  by_cases hpx : p ≤ x
  · by_cases h2p : 2*p ≤ x
    · exfalso
      have hk2 : 2 ≤ x / p := (Nat.le_div_iff_mul_le hpp.pos).mpr (by linarith)
      have hdvdM : p^(x/p) ∣ M :=
        (pow_dvd_fact p (x/p) hpp.pos).trans
          ((Nat.factorial_dvd_factorial (Nat.mul_div_le x p)).trans hfM)
      have h1 := pow_step hpd (x/p) hdvdM
      have h2 : p^(x/p+1) ≤ N := Nat.le_of_dvd hNpos h1
      have h3 : x < p*(x/p+1) := Nat.lt_mul_div_succ x hpp.pos
      have h4 := bound p (x/p+1) hp3 (by omega) (by omega)
      have h6 : (x+4)^2 ≤ (p*(x/p+1)+4)^2 := Nat.pow_le_pow_left (by omega) 2
      omega
    · push Not at h2p
      have hpM : p ∣ M := (Nat.dvd_factorial hpp.pos hpx).trans hfM
      have hp2 : p^2 ∣ N := pow_step hpd 1 (by simpa using hpM)
      obtain ⟨m, hm⟩ := hp2
      have hm5 : m < 5 := by
        by_contra hcon
        push Not at hcon
        have h1 : (x+1)^2 ≤ (2*p)^2 := Nat.pow_le_pow_left (by omega) 2
        have h2 : 5 * p^2 ≤ p^2 * m := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hcon
        nlinarith
      interval_cases m
      · omega
      · exfalso
        rw [mul_one] at hm
        have h1 : x + 3 < p := by
          by_contra hc; push Not at hc
          have : p^2 ≤ (x+3)^2 := Nat.pow_le_pow_left hc 2
          nlinarith
        have h2 : p < x + 4 := by
          by_contra hc; push Not at hc
          have : (x+4)^2 ≤ p^2 := Nat.pow_le_pow_left hc 2
          omega
        omega
      · exfalso; exact hodd ⟨p^2, by rw [hm]; ring⟩
      · have hp_ne3 : p ≠ 3 := by omega
        have h3M : 3 ∣ M := ⟨(x+2)*x.factorial, by rw [hM]; ring⟩
        have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hpp).mpr (Ne.symm hp_ne3)
        have h3pM : 3*p ∣ M := hcop.mul_dvd_of_dvd_of_dvd h3M hpM
        have h3pN : 3*p ∣ N := ⟨p, by rw [hm]; ring⟩
        have h3pg : 3*p ∣ g := Nat.dvd_gcd h3pN h3pM
        obtain ⟨h, hh⟩ := h3pg
        have hpe : p = h * d := by
          have : 3*p*p = 3*p*(h*d) := by rw [← mul_assoc, ← hh, ← hNgd, hm]; ring
          exact Nat.eq_of_mul_eq_mul_left (by positivity) this
        rcases hpp.eq_one_or_self_of_dvd d ⟨h, by rw [hpe, mul_comm]⟩ with h' | h'
        · left; exact h'
        · right; rw [h']; exact hpp
      · exfalso; exact hodd ⟨2*p^2, by rw [hm]; ring⟩
  · push Not at hpx
    have h1 : ¬ x + 1 ∣ N := by
      intro h
      have h' : x + 1 ∣ (x+1)*(x+6) + 3 := by
        rw [show (x+1)*(x+6) + 3 = N by rw [hN]; ring]; exact h
      have := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h')
      omega
    have h2 : ¬ x + 2 ∣ N := not_dvd_aux x 2 1 ⟨x+5, by ring⟩ (by omega) (by norm_num)
    have h3 : ¬ x + 3 ∣ N := not_dvd_aux x 3 3 ⟨x+4, by ring⟩ (by omega) (by norm_num)
    have hB : ∀ q, q ∣ N → x < q → x + 4 ≤ q := by
      intro q hq hxq
      by_contra hcon
      push Not at hcon
      rcases (show q = x+1 ∨ q = x+2 ∨ q = x+3 by omega) with rfl | rfl | rfl
      · exact h1 hq
      · exact h2 hq
      · exact h3 hq
    have hp4 : x + 4 ≤ p := hB p hpN hpx
    by_cases hdp : d = p
    · right; rw [hdp]; exact hpp
    exfalso
    have hdr : d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
    have hr1 : d / p ≠ 1 := by intro h; apply hdp; rw [hdr, h, mul_one]
    have hr0 : d / p ≠ 0 := by
      intro h; rw [h, mul_zero] at hdr; rw [hdr] at hNgd; omega
    have hrp : (d / p).minFac.Prime := Nat.minFac_prime hr1
    have hrd : (d / p).minFac ∣ d := (Nat.minFac_dvd _).trans (Dvd.intro_left p hdr.symm)
    have hpr : p ≤ (d / p).minFac := Nat.minFac_le_of_dvd hrp.two_le hrd
    have hr4 : x + 4 ≤ d / p := le_trans hp4 (hpr.trans (Nat.minFac_le (Nat.pos_of_ne_zero hr0)))
    have hdle : d ≤ N := Nat.le_of_dvd hNpos hdN
    have : (x+4)^2 ≤ d := by rw [hdr, sq]; exact Nat.mul_le_mul hp4 hr4
    omega

/-- The cases `3 ≤ n < 60`, read off from the 57 kernel-checked terms `a_data`. -/
private lemma small (n : ℕ) (hn : 3 ≤ n) (hn' : n < 60) (h9 : a n ≠ 9) :
    a n = 1 ∨ (a n).Prime := by
  have key : ∀ v ∈ (List.range 57).map (fun i => a (i + 3)), v ≠ 9 → v = 1 ∨ v.Prime := by
    rw [a_data]
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    norm_num
  refine key (a n) (List.mem_map.mpr ⟨n - 3, List.mem_range.mpr (by omega), ?_⟩) h9
  show a (n - 3 + 3) = a n
  congr 1
  omega

/-- Bouras' conjecture for A362086: except for `9`, every term `a n` (`n ≥ 3`) is `1` or a prime. -/
theorem result : statement := by
  intro n hn h9
  by_cases hsmall : n < 36
  · exact small n hn (by omega) h9
  · obtain ⟨x, rfl⟩ : ∃ x, n = x + 3 := ⟨n - 3, by omega⟩
    rw [a_eq x (by omega)]
    exact main x (by omega)

end Math0.Frontier.A362086

#math0_settles Math0.Frontier.A362086.result Math0.Statements.A362086.statement

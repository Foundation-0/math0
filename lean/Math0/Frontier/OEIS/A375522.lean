/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A375522
import Math0.Audit

/-!
# A375522: `S2(n) - S1(n) = 1` fails at `n = 42`

The Sigrist–Sloane conjecture says that `S2(n) - S1(n) = 1` for all `n ≥ 1` except `n = 4, 6`.
We refute it: `S2(42) - S1(42) = 5`.

Idea. Write the remainder `1 - s n = u n / D n` in lowest terms; then `S2(n) - S1(n) = u n`.
With `p` the next prime and `b = ⌊D / (u p)⌋ + 1`, the next remainder is `num / (D p b)` with
`num = u p - D % (u p)`, reduced by `g = gcd(num, D p b)`. The denominators `D n` grow doubly
exponentially (more than `10^11` digits at `n = 42`), so we never compute them. Instead we track
`D` modulo a modulus `X` (starting from `X = (190!)^2`): `D % (u p)` is known when `u p ∣ X`,
`⌊D / (u p)⌋` is then known modulo `X / (u p)`, `D p b` modulo `X / u`, and `g` is known when
`num ∣ X / u`; after dividing by `g` the new `D` is known modulo `X / u / g`. We prove that
this modular step is faithful under these checks (`mstep_spec`), and the kernel runs the 42 steps
and checks them (`mrun_42`), finding `u 42 = 5`: at `n = 42` (`p = 181`) the unreduced numerator
is `125` but only `25` cancels.
-/

namespace Math0.Frontier.A375522
open Math0.Statements.A375522

/-- One exact step of the process on the remainder `R = 1 - s = u / D`, as a pair `(u, D)`:
with `b = D / (u p) + 1`, the new remainder is `num / den` where `num = u p b - D = u p - D % (u p)`
and `den = D p b`, reduced by `g = gcd num den`. -/
private def tstep (p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  let num := x.1 * p - x.2 % (x.1 * p)
  let den := x.2 * (p * (x.2 / (x.1 * p) + 1))
  (num / Nat.gcd num den, den / Nat.gcd num den)

/-- The exact pairs `(u n, D n)` with `1 - s n = u n / D n` in lowest terms. -/
private def T : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => tstep (prime (n + 1)) (T n)

/-- The `k`-th prime is positive. -/
private theorem prime_pos (k : ℕ) : 0 < prime k := by
  unfold prime; rw [primeAt_eq_nth]; exact (Nat.prime_nth_prime _).pos

/-- If `R = u / D` with `u, D, p > 0`, then the greedy update
`R - 1 / (p * (1 + ⌊1 / (R p)⌋))` has numerator and denominator (in lowest terms) given by
`tstep p (u, D)`, and its numerator is positive. -/
private theorem rat_step (R : ℚ) (u D p : ℕ) (hu : 0 < u) (hD : 0 < D) (hp : 0 < p)
    (hR : R = (u : ℚ) / D) :
    (R - 1 / ((p : ℚ) * ((1 + ⌊1 / (R * p)⌋ : ℤ) : ℚ))).num = (tstep p (u, D)).1 ∧
    (R - 1 / ((p : ℚ) * ((1 + ⌊1 / (R * p)⌋ : ℤ) : ℚ))).den = (tstep p (u, D)).2 ∧
    0 < (tstep p (u, D)).1 := by
  have hup : 0 < u * p := Nat.mul_pos hu hp
  have hrlt : D % (u * p) < u * p := Nat.mod_lt _ hup
  have hDqr : u * p * (D / (u * p)) + D % (u * p) = D := Nat.div_add_mod D (u * p)
  have e1 : (tstep p (u, D)).1 = (u * p - D % (u * p)) /
      Nat.gcd (u * p - D % (u * p)) (D * (p * (D / (u * p) + 1))) := rfl
  have e2 : (tstep p (u, D)).2 = (D * (p * (D / (u * p) + 1))) /
      Nat.gcd (u * p - D % (u * p)) (D * (p * (D / (u * p) + 1))) := rfl
  rw [e1, e2]
  generalize hq : D / (u * p) = q at hDqr ⊢
  generalize hr : D % (u * p) = r at hDqr hrlt ⊢
  have hnum_pos : 0 < u * p - r := by omega
  have hden_pos : 0 < D * (p * (q + 1)) := by positivity
  have hfloor : ⌊1 / (R * p)⌋ = (q : ℤ) := by
    have : 1 / (R * p) = ((D : ℕ) : ℚ) / ((u * p : ℕ) : ℚ) := by
      rw [hR]; push_cast; field_simp
    rw [this, Rat.floor_natCast_div_natCast, ← hq]; rfl
  have hR' : R - 1 / ((p : ℚ) * ((1 + ⌊1 / (R * p)⌋ : ℤ) : ℚ)) =
      mkRat ((u * p - r : ℕ) : ℤ) (D * (p * (q + 1))) := by
    rw [Rat.mkRat_eq_div, hfloor, hR]
    have hnumQ : (((u * p - r : ℕ) : ℤ) : ℚ) = (u : ℚ) * p - r := by
      rw [Int.cast_natCast, Nat.cast_sub hrlt.le]; push_cast; ring
    have hDQ : (D : ℚ) = u * p * q + r := by rw [← hDqr]; push_cast; ring
    rw [hnumQ]
    have hD' : (D : ℚ) ≠ 0 := by positivity
    have hp' : (p : ℚ) ≠ 0 := by positivity
    have hq' : (q : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    linear_combination (-(q : ℚ) - 1) * hDQ
  rw [hR', Rat.num_mkRat, Rat.den_mkRat, if_neg hden_pos.ne', if_neg hden_pos.ne',
    Int.natAbs_natCast, Nat.gcd_comm]
  refine ⟨rfl, rfl, Nat.div_pos (Nat.gcd_le_left _ hnum_pos) (Nat.gcd_pos_of_pos_left _ hnum_pos)⟩

/-- `T n` is the reduced numerator/denominator pair of the remainder `1 - s n`. -/
private theorem T_spec (n : ℕ) :
    (1 - s n).num = (T n).1 ∧ (1 - s n).den = (T n).2 ∧ 0 < (T n).1 := by
  induction n with
  | zero => simp [s, T]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hrec : 1 - s (n + 1) = (1 - s n) - 1 / ((prime (n + 1) : ℚ) *
        ((1 + ⌊1 / ((1 - s n) * (prime (n + 1) : ℚ))⌋ : ℤ) : ℚ)) := by
      rw [s]; ring
    have hR : 1 - s n = ((T n).1 : ℚ) / ((T n).2 : ℚ) := by
      rw [← Rat.num_div_den (1 - s n), h1, h2]; rfl
    have hD : 0 < (T n).2 := h2 ▸ (1 - s n).den_pos
    rw [hrec]
    exact rat_step (1 - s n) _ _ _ h3 hD (prime_pos _) hR

/-- `a n - S1 n` equals the numerator of the remainder `1 - s n`. -/
private theorem diff_eq (n : ℕ) : (a n : ℤ) - S1 n = (1 - s n).num := by
  have hden : (1 - s n).den = (s n).den := by
    have := Rat.intCast_sub_den 1 (s n)
    simp only [Int.cast_one] at this
    exact this
  have key : ((s n).num : ℚ) = ((1 - s n).den : ℚ) - (1 - s n).num := by
    rw [← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num, hden]; ring
  have key' : (s n).num = ((1 - s n).den : ℤ) - (1 - s n).num := by exact_mod_cast key
  unfold a S1
  rw [key', hden]; ring

/-- The same step computed from `(u, Dm, X)` where `Dm` is a residue of the true `D` modulo `X`:
it returns the new `u`, a residue of the new `D`, and the new modulus `X / u / g`. -/
private def mstep (p : ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let num := st.1 * p - st.2.1 % (st.1 * p)
  let den := st.2.1 * (p * (st.2.1 / (st.1 * p) + 1))
  let g := Nat.gcd num den
  (num / g, den / g % (st.2.2 / st.1 / g), st.2.2 / st.1 / g)

/-- The side conditions under which `mstep` is faithful: `u p > 0`, `u p ∣ X`, and the new
unreduced numerator `u p - Dm % (u p)` divides `X / u`. -/
private def mok (p : ℕ) (st : ℕ × ℕ × ℕ) : Bool :=
  0 < st.1 * p && st.2.2 % (st.1 * p) == 0 &&
    st.2.2 / st.1 % (st.1 * p - st.2.1 % (st.1 * p)) == 0

/-- Run `mstep` from `(1, 1, X0)`, checking `mok` at every step (`none` if a check fails). -/
private def mrun (X0 : ℕ) : ℕ → Option (ℕ × ℕ × ℕ)
  | 0 => some (1, 1, X0)
  | n + 1 => (mrun X0 n).bind fun st =>
      if mok (prime (n + 1)) st then some (mstep (prime (n + 1)) st) else none

/-- Faithfulness of one modular step: if `D ≡ Dm [MOD X]` and the checks pass, the modular step
returns the true new `u` and a residue of the true new `D` modulo the new modulus. -/
private theorem mstep_spec (p u D Dm X : ℕ) (hok : mok p (u, Dm, X) = true)
    (hmod : D ≡ Dm [MOD X]) :
    (tstep p (u, D)).1 = (mstep p (u, Dm, X)).1 ∧
    (tstep p (u, D)).2 ≡ (mstep p (u, Dm, X)).2.1 [MOD (mstep p (u, Dm, X)).2.2] := by
  simp only [mok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hup, hX⟩, hnum⟩ := hok
  have hu : 0 < u := Nat.pos_of_mul_pos_right hup
  obtain ⟨k, rfl⟩ : u * p ∣ X := Nat.dvd_of_mod_eq_zero hX
  have hXu : u * p * k / u = p * k := by rw [mul_assoc, Nat.mul_div_cancel_left _ hu]
  have hr : D % (u * p) = Dm % (u * p) := Nat.ModEq.of_dvd (Dvd.intro k rfl) hmod
  have hD1 := Nat.div_add_mod D (u * p)
  have hD2 := Nat.div_add_mod Dm (u * p)
  have hX' := Nat.modEq_iff_dvd.mp hmod
  have e1 : (tstep p (u, D)).1 = (u * p - D % (u * p)) /
      Nat.gcd (u * p - D % (u * p)) (D * (p * (D / (u * p) + 1))) := rfl
  have e2 : (tstep p (u, D)).2 = (D * (p * (D / (u * p) + 1))) /
      Nat.gcd (u * p - D % (u * p)) (D * (p * (D / (u * p) + 1))) := rfl
  have e3 : mstep p (u, Dm, u * p * k) = ((u * p - Dm % (u * p)) /
      Nat.gcd (u * p - Dm % (u * p)) (Dm * (p * (Dm / (u * p) + 1))),
      (Dm * (p * (Dm / (u * p) + 1))) /
      Nat.gcd (u * p - Dm % (u * p)) (Dm * (p * (Dm / (u * p) + 1))) %
        (u * p * k / u / Nat.gcd (u * p - Dm % (u * p)) (Dm * (p * (Dm / (u * p) + 1)))),
      u * p * k / u / Nat.gcd (u * p - Dm % (u * p)) (Dm * (p * (Dm / (u * p) + 1)))) := rfl
  rw [e1, e2, e3, hr, hXu]
  simp only [hXu] at hnum
  rw [hr] at hD1
  have hrlt : Dm % (u * p) < u * p := Nat.mod_lt _ hup
  generalize D / (u * p) = q1 at hD1 ⊢
  generalize Dm / (u * p) = q2 at hD2 ⊢
  generalize Dm % (u * p) = r at hD1 hD2 hnum hrlt ⊢
  generalize hnumdef : u * p - r = num at hnum ⊢
  have hnumd : num ∣ p * k := Nat.dvd_of_mod_eq_zero hnum
  have hq : (k : ℤ) ∣ (q2 : ℤ) - q1 := by
    have e : (Dm : ℤ) - D = ((u * p : ℕ) : ℤ) * ((q2 : ℤ) - q1) := by
      rw [← hD1, ← hD2]; push_cast; ring
    have : ((u * p : ℕ) : ℤ) * k ∣ ((u * p : ℕ) : ℤ) * ((q2 : ℤ) - q1) := by
      rw [← e]; exact_mod_cast hX'
    exact (mul_dvd_mul_iff_left (by positivity)).mp this
  have hd : ((p * k : ℕ) : ℤ) ∣ ((Dm * (p * (q2 + 1)) : ℕ) : ℤ) - ((D * (p * (q1 + 1)) : ℕ) : ℤ) := by
    obtain ⟨c, hc⟩ := hX'
    obtain ⟨e, he⟩ := hq
    refine ⟨u * p * c * (q2 + 1) + D * e, ?_⟩
    push_cast at hc ⊢
    linear_combination (p : ℤ) * (q2 + 1) * hc + (p : ℤ) * D * he
  have hdm : D * (p * (q1 + 1)) ≡ Dm * (p * (q2 + 1)) [MOD p * k] := Nat.modEq_iff_dvd.mpr hd
  have hg : Nat.gcd num (D * (p * (q1 + 1))) = Nat.gcd num (Dm * (p * (q2 + 1))) := by
    have := (hdm.of_dvd hnumd).gcd_eq
    rw [Nat.gcd_comm, this, Nat.gcd_comm]
  rw [hg]
  refine ⟨rfl, ?_⟩
  generalize hgdef : Nat.gcd num (Dm * (p * (q2 + 1))) = g
  have hg1 : g ∣ D * (p * (q1 + 1)) := hgdef ▸ hg ▸ Nat.gcd_dvd_right _ _
  have hg2 : g ∣ Dm * (p * (q2 + 1)) := hgdef ▸ Nat.gcd_dvd_right _ _
  have hg3 : g ∣ p * k := (hgdef ▸ Nat.gcd_dvd_left _ _ : g ∣ num).trans hnumd
  have hgpos : 0 < g := by
    rw [← hgdef]; apply Nat.gcd_pos_of_pos_left; omega
  refine Nat.ModEq.trans ?_ (Nat.mod_modEq _ _).symm
  obtain ⟨x1, hx1⟩ := hg1
  obtain ⟨x2, hx2⟩ := hg2
  obtain ⟨x3, hx3⟩ := hg3
  rw [hx1, hx2, hx3] at hdm
  rw [hx1, hx2, hx3, Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos,
    Nat.mul_div_cancel_left _ hgpos]
  exact Nat.ModEq.mul_left_cancel' hgpos.ne' hdm

/-- Faithfulness of the whole modular run. -/
private theorem mrun_spec (X0 : ℕ) (n : ℕ) :
    ∀ st, mrun X0 n = some st → (T n).1 = st.1 ∧ (T n).2 ≡ st.2.1 [MOD st.2.2] := by
  induction n with
  | zero =>
    intro st h
    simp only [mrun, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro st h
    simp only [mrun] at h
    cases hm : mrun X0 n with
    | none => rw [hm] at h; simp at h
    | some st0 =>
      rw [hm] at h
      simp only [Option.bind_some] at h
      split_ifs at h with hok
      cases h
      obtain ⟨h1, h2⟩ := ih st0 hm
      obtain ⟨u, Dm, X⟩ := st0
      have key := mstep_spec (prime (n + 1)) u (T n).2 Dm X hok h2
      have hT : T n = (u, (T n).2) := Prod.ext h1 rfl
      show (tstep (prime (n + 1)) (T n)).1 = _ ∧ (tstep (prime (n + 1)) (T n)).2 ≡ _ [MOD _]
      rw [hT]
      exact key

/-- The starting modulus `(190!)^2`. -/
private def X0 : ℕ := Nat.factorial 190 ^ 2

/-- Kernel computation: the modular run from `X0 = (190!)^2` passes all 42 checks and gives
`u 42 = 5`. -/
private theorem mrun_42 : (mrun X0 42).map (·.1) = some 5 := by
  decide +kernel

/-- The conjecture fails at `n = 42`: there `S2(42) - S1(42) = 5`. -/
theorem result : ¬ statement := by
  intro h
  have h42 := h 42 (by norm_num) (by norm_num) (by norm_num)
  rw [diff_eq, (T_spec 42).1] at h42
  obtain ⟨st, hst, h5⟩ : ∃ st, mrun X0 42 = some st ∧ st.1 = 5 := by
    have := mrun_42
    cases hm : mrun X0 42 with
    | none => rw [hm] at this; simp at this
    | some st => rw [hm] at this; simp at this; exact ⟨st, rfl, this⟩
  rw [(mrun_spec X0 42 st hst).1, h5] at h42
  norm_num at h42

end Math0.Frontier.A375522

#math0_settles Math0.Frontier.A375522.result Math0.Statements.A375522.statement

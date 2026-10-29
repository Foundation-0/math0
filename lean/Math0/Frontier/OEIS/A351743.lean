/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A351743
import Math0.Audit

/-!
# A351743: the eventual affine 42-block structure

We prove all four conjectures in `Math0.Statements.A351743.statement`: Sycamore's conjecture that
`1` and `2` occur infinitely often in A351743, Sigrist's two conjectures on the odd- and
even-indexed terms, and the A355149 conjecture on the partial sums.

The idea. Put `Y 0 = 0`, `Y (m + 1) = 3645 * Y m + 1` (so `Y m = (3645^m - 1)/3644`). For each
`i < 42` there are explicit naturals `(P_i, Q_i, R_i, U_i)` (the table `rows`) such that for all
`m`, `a(139 + 42 m + i) = P_i * Y m + Q_i` and `s(139 + 42 m + i) = R_i * Y m + U_i`.
This is proved by induction: the base `m = 0, i = 0` is a kernel computation, and each step of
the recursion maps the affine pair of row `i` to the affine pair of row `i + 1` *for every value*
`W` of the parameter (row `41` maps to row `0` evaluated at `3645 W + 1`). Such a step is a
statement `coprimePart (R W + U) (P W + Q) = P' W + Q'`, which follows from a factorisation
`R W + U = d * e` with `d` prime to `P W + Q` and `e ∣ (P W + Q)^k` (`cp_eq`). There are two
shapes:
* when `P = 0` (so `a(n) = Q ∈ {1, …, 5}` is constant), `e` is a constant dividing `Q^k` and
  `d = P' W + Q'` is prime to `Q` because some `g` with `Q ∣ g^k` divides `P'` and is prime to
  `Q'`;
* when `P' = 0` (then `s(n) = c * a(n)` with `c ∈ {2, 4, 5, 6, 9}`), `d = Q'` is a constant and
  `e = f * (P W + Q)`, where `f ∣ h^k` for a common divisor `h` of `P` and `Q`.
All the finitely many arithmetic side conditions on the table (`Good`) are checked by the kernel.
The conjectures then follow: rows `4` and `8` are `a = 1` and `a = 2`, the rows of odd index
`139 + i` are constant, and since `Y (m + 1) = 3645 * Y m + 1`, the quantities
`a(n + 42) - 3645 a(n)` and `s(n + 42) - 3645 s(n)` only depend on `i`.
-/

namespace Math0.Frontier.A351743
open Math0.Statements.A351743

/-- The block parameter: `Y 0 = 0`, `Y (m + 1) = 3645 * Y m + 1`,
i.e. `Y m = (3645^m - 1)/3644`. -/
private def Y : ℕ → ℕ
  | 0 => 0
  | m + 1 => 3645 * Y m + 1

/-- The pair `(P * W + Q, R * W + U)` described by a row `(P, Q, R, U)` at parameter `W`. -/
private def F (r : ℕ × ℕ × ℕ × ℕ) (W : ℕ) : ℕ × ℕ :=
  (r.1 * W + r.2.1, r.2.2.1 * W + r.2.2.2)

/-- The rows `(P_i, Q_i, R_i, U_i)`, `i < 42`: `a(139 + 42 m + i) = P_i * Y m + Q_i` and
`s(139 + 42 m + i) = R_i * Y m + U_i`. -/
private def rows : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 3, 1150034580, 315591),
    (383344860, 105197, 1533379440, 420788),
    (0, 4, 1533379440, 420792),
    (191672430, 52599, 1725051870, 473391),
    (0, 1, 1725051870, 473392),
    (1725051870, 473392, 3450103740, 946784),
    (0, 1, 3450103740, 946785),
    (3450103740, 946785, 6900207480, 1893570),
    (0, 2, 6900207480, 1893572),
    (1725051870, 473393, 8625259350, 2366965),
    (0, 5, 8625259350, 2366970),
    (1725051870, 473394, 10350311220, 2840364),
    (0, 1, 10350311220, 2840365),
    (10350311220, 2840365, 20700622440, 5680730),
    (0, 2, 20700622440, 5680732),
    (5175155610, 1420183, 25875778050, 7100915),
    (0, 5, 25875778050, 7100920),
    (5175155610, 1420184, 31050933660, 8521104),
    (0, 3, 31050933660, 8521107),
    (10350311220, 2840369, 41401244880, 11361476),
    (0, 4, 41401244880, 11361480),
    (5175155610, 1420185, 46576400490, 12781665),
    (0, 1, 46576400490, 12781666),
    (46576400490, 12781666, 93152800980, 25563332),
    (0, 1, 93152800980, 25563333),
    (93152800980, 25563333, 186305601960, 51126666),
    (0, 2, 186305601960, 51126668),
    (46576400490, 12781667, 232882002450, 63908335),
    (0, 5, 232882002450, 63908340),
    (46576400490, 12781668, 279458402940, 76690008),
    (0, 1, 279458402940, 76690009),
    (279458402940, 76690009, 558916805880, 153380018),
    (0, 2, 558916805880, 153380020),
    (139729201470, 38345005, 698646007350, 191725025),
    (0, 1, 698646007350, 191725026),
    (698646007350, 191725026, 1397292014700, 383450052),
    (0, 1, 1397292014700, 383450053),
    (1397292014700, 383450053, 2794584029400, 766900106),
    (0, 2, 2794584029400, 766900108),
    (698646007350, 191725027, 3493230036750, 958625135),
    (0, 5, 3493230036750, 958625140),
    (698646007350, 191725028, 4191876044100, 1150350168)]

/-- Row `i` of the table. -/
private def row (i : ℕ) : ℕ × ℕ × ℕ × ℕ := rows.getD i (0, 0, 0, 0)

/-- Certificates for the steps: `(e, g, k, 0, 0)` for a step of the first shape (`GoodSmall`),
`(c, f, g, h, k)` for a step of the second shape (`GoodBig`). -/
private def certs : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(3, 3, 4, 0, 0),
    (4, 1, 2, 1, 4),
    (8, 2, 4, 0, 0),
    (9, 9, 1, 3, 4),
    (1, 1, 4, 0, 0),
    (2, 2, 1, 2, 4),
    (1, 1, 4, 0, 0),
    (2, 1, 2, 15, 4),
    (4, 2, 4, 0, 0),
    (5, 1, 5, 1, 4),
    (5, 5, 4, 0, 0),
    (6, 6, 1, 6, 4),
    (1, 1, 4, 0, 0),
    (2, 1, 2, 5, 4),
    (4, 2, 4, 0, 0),
    (5, 1, 5, 1, 4),
    (5, 5, 4, 0, 0),
    (6, 2, 3, 2, 4),
    (3, 3, 4, 0, 0),
    (4, 1, 2, 1, 4),
    (8, 2, 4, 0, 0),
    (9, 9, 1, 15, 4),
    (1, 1, 4, 0, 0),
    (2, 2, 1, 2, 4),
    (1, 1, 4, 0, 0),
    (2, 1, 2, 3, 4),
    (4, 2, 4, 0, 0),
    (5, 1, 5, 1, 4),
    (5, 5, 4, 0, 0),
    (6, 6, 1, 6, 4),
    (1, 1, 4, 0, 0),
    (2, 1, 2, 1, 4),
    (4, 2, 4, 0, 0),
    (5, 5, 1, 5, 4),
    (1, 1, 4, 0, 0),
    (2, 2, 1, 6, 4),
    (1, 1, 4, 0, 0),
    (2, 1, 2, 1, 4),
    (4, 2, 4, 0, 0),
    (5, 1, 5, 1, 4),
    (5, 5, 4, 0, 0),
    (6, 2, 3, 2, 4)]

/-- Certificate `i`. -/
private def cert (i : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ := certs.getD i (0, 0, 0, 0, 0)

/-- The row describing block `m + 1` in terms of the parameter `Y m` of block `m`
(see `F_shift`). -/
private def shift (r : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (3645 * r.1, r.1 + r.2.1, 3645 * r.2.2.1, r.2.2.1 + r.2.2.2)

/-- The row following row `i`: row `i + 1`, or the shifted row `0` after row `41`. -/
private def nextRow (i : ℕ) : ℕ × ℕ × ℕ × ℕ := if i = 41 then shift (row 0) else row (i + 1)

/-- Side conditions for a step from `r` to `r'` when `a(n) = Q` is constant (`P = 0`):
`R W + U = e * (P' W + Q')` with `e ∣ Q^k`, and `P' W + Q'` prime to `Q`. -/
private abbrev GoodSmall (r r' : ℕ × ℕ × ℕ × ℕ) (e g k : ℕ) : Prop :=
  r.1 = 0 ∧ r.2.2.1 = e * r'.1 ∧ r.2.2.2 = e * r'.2.1 ∧ e ∣ r.2.1 ^ k ∧ g ∣ r'.1 ∧
    Nat.Coprime r'.2.1 g ∧ r.2.1 ∣ g ^ k ∧ 0 < e ∧ 0 < r'.2.1 ∧
    r'.2.2.1 = r.2.2.1 + r'.1 ∧ r'.2.2.2 = r.2.2.2 + r'.2.1

/-- Side conditions for a step from `r` to `r'` when `s(n) = c * a(n)` and `a(n + 1) = Q'` is
constant (`P' = 0`): `c = Q' * f` with `f ∣ (P W + Q)^k` and `Q'` prime to `P W + Q`. -/
private abbrev GoodBig (r r' : ℕ × ℕ × ℕ × ℕ) (c f g h k : ℕ) : Prop :=
  r'.1 = 0 ∧ r.2.2.1 = c * r.1 ∧ r.2.2.2 = c * r.2.1 ∧ c = r'.2.1 * f ∧ h ∣ r.1 ∧ h ∣ r.2.1 ∧
    f ∣ h ^ k ∧ g ∣ r.1 ∧ Nat.Coprime r.2.1 g ∧ r'.2.1 ∣ g ^ k ∧ 0 < r'.2.1 ∧ 0 < r.2.1 ∧
    0 < f ∧ r'.2.2.1 = r.2.2.1 ∧ r'.2.2.2 = r.2.2.2 + r'.2.1

/-- A certified step from row `r` to row `r'`. -/
private abbrev Good (r r' : ℕ × ℕ × ℕ × ℕ) (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  GoodSmall r r' x.1 x.2.1 x.2.2.1 ∨ GoodBig r r' x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- If `w = d * e` with `d` prime to `v` and `e ∣ v^k`, then the greatest divisor of `w` prime
to `v` is `d`. -/
private theorem cp_eq (d e v k : ℕ) (hd : 0 < d) (he : 0 < e) (hc : Nat.Coprime d v)
    (hk : e ∣ v ^ k) : coprimePart (d * e) v = d := by
  have h1 := coprimePart_isGreatest (d * e) v (Nat.mul_pos hd he)
  have h2 : IsGreatest {x | x ∣ d * e ∧ Nat.Coprime x v} d := by
    refine ⟨⟨dvd_mul_right d e, hc⟩, ?_⟩
    rintro x ⟨hx, hxv⟩
    have hxe : Nat.Coprime x e := Nat.Coprime.coprime_dvd_right hk (Nat.Coprime.pow_right k hxv)
    exact Nat.le_of_dvd hd (hxe.dvd_of_dvd_mul_right hx)
  exact h1.unique h2

/-- `L W + M` is prime to `K` as soon as some `g ∣ L` is prime to `M` and `K ∣ g^k`. -/
private theorem cop_lin (L M g K k W : ℕ) (hg : g ∣ L) (hM : Nat.Coprime M g)
    (hK : K ∣ g ^ k) : Nat.Coprime (L * W + M) K := by
  obtain ⟨t, rfl⟩ := hg
  have h1 : Nat.Coprime (M + (t * W) * g) g := (Nat.coprime_add_mul_right_left M g (t * W)).2 hM
  have h2 : g * t * W + M = M + (t * W) * g := by ring
  rw [h2]
  exact Nat.Coprime.coprime_dvd_right hK (Nat.Coprime.pow_right k h1)

/-- One step of the recursion on an explicit pair. -/
private theorem step_F (P Q R U W : ℕ) :
    step (F (P, Q, R, U) W) =
      (coprimePart (R * W + U) (P * W + Q), R * W + U + coprimePart (R * W + U) (P * W + Q)) :=
  rfl

/-- Soundness of the first shape of step. -/
private theorem step_small (P Q R U P' Q' R' U' e g k W : ℕ)
    (H : GoodSmall (P, Q, R, U) (P', Q', R', U') e g k) :
    step (F (P, Q, R, U) W) = F (P', Q', R', U') W := by
  obtain ⟨hP, hR, hU, he, hg, hQ', hQg, he0, hQ'0, hR', hU'⟩ := H
  dsimp only at hP hR hU he hg hQ' hQg he0 hQ'0 hR' hU'
  have hw : R * W + U = (P' * W + Q') * e := by rw [hR, hU]; ring
  have hv : P * W + Q = Q := by rw [hP]; ring
  have hpos : 0 < P' * W + Q' := Nat.lt_of_lt_of_le hQ'0 (Nat.le_add_left _ _)
  have hcp : coprimePart (R * W + U) (P * W + Q) = P' * W + Q' := by
    rw [hw, hv]
    exact cp_eq _ _ _ k hpos he0 (cop_lin P' Q' g Q k W hg hQ' hQg) he
  rw [step_F, hcp, hw]
  simp only [F, Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  rw [hR', hU', hR, hU]
  ring

/-- Soundness of the second shape of step. -/
private theorem step_big (P Q R U P' Q' R' U' c f g h k W : ℕ)
    (H : GoodBig (P, Q, R, U) (P', Q', R', U') c f g h k) :
    step (F (P, Q, R, U) W) = F (P', Q', R', U') W := by
  obtain ⟨hP', hR, hU, hc, hhP, hhQ, hf, hgP, hQg, hQ'g, hQ'0, hQ0, hf0, hR', hU'⟩ := H
  dsimp only at hP' hR hU hc hhP hhQ hf hgP hQg hQ'g hQ'0 hQ0 hf0 hR' hU'
  have hw : R * W + U = Q' * (f * (P * W + Q)) := by rw [hR, hU, hc]; ring
  have hvpos : 0 < P * W + Q := Nat.lt_of_lt_of_le hQ0 (Nat.le_add_left _ _)
  have hhv : h ∣ P * W + Q := Dvd.dvd.add (Dvd.dvd.mul_right hhP W) hhQ
  have hcp : coprimePart (R * W + U) (P * W + Q) = Q' := by
    rw [hw]
    refine cp_eq _ _ _ (k + 1) hQ'0 (Nat.mul_pos hf0 hvpos)
      (cop_lin P Q g Q' k W hgP hQg hQ'g).symm ?_
    rw [pow_succ]
    exact mul_dvd_mul_right (dvd_trans hf (pow_dvd_pow_of_dvd hhv k)) _
  rw [step_F, hcp]
  simp only [F, Prod.mk.injEq]
  refine ⟨by rw [hP']; ring, ?_⟩
  rw [hR', hU']
  ring

/-- Soundness of a certified step: it holds for every value `W` of the parameter. -/
private theorem step_good (r r' : ℕ × ℕ × ℕ × ℕ) (x : ℕ × ℕ × ℕ × ℕ × ℕ) (H : Good r r' x)
    (W : ℕ) : step (F r W) = F r' W := by
  obtain ⟨P, Q, R, U⟩ := r
  obtain ⟨P', Q', R', U'⟩ := r'
  obtain ⟨x1, x2, x3, x4, x5⟩ := x
  rcases H with H | H
  · exact step_small P Q R U P' Q' R' U' x1 x2 x3 W H
  · exact step_big P Q R U P' Q' R' U' x1 x2 x3 x4 x5 W H

/-- All 42 steps of the table are certified (kernel computation). -/
private theorem good_all : ∀ i, i < 42 → Good (row i) (nextRow i) (cert i) := by
  decide +kernel

/-- Each row steps to the next row, for every value of the parameter. -/
private theorem step_row (i : ℕ) (hi : i < 42) (W : ℕ) : step (F (row i) W) = F (nextRow i) W :=
  step_good _ _ _ (good_all i hi) W

/-- The shifted row at `W` is the row at `3645 W + 1`. -/
private theorem F_shift (r : ℕ × ℕ × ℕ × ℕ) (W : ℕ) : F (shift r) W = F r (3645 * W + 1) := by
  obtain ⟨P, Q, R, U⟩ := r
  simp only [F, shift, Prod.mk.injEq]
  constructor <;> ring

private theorem state_succ' (n : ℕ) : state (n + 1) = step (state n) := by
  unfold state
  rw [Function.iterate_succ_apply']

/-- The base of the induction: `(a 139, s 139) = (3, 315591)` (kernel computation). -/
private theorem state_base : state 138 = F (row 0) (Y 0) := by
  decide +kernel

/-- The block structure: `state (138 + 42 m + i) = F (row i) (Y m)` for `i < 42`. -/
private theorem key (m : ℕ) : ∀ i, i < 42 → state (138 + 42 * m + i) = F (row i) (Y m) := by
  induction m with
  | zero =>
    intro i hi
    induction i with
    | zero => exact state_base
    | succ i ih =>
      rw [show 138 + 42 * 0 + (i + 1) = (138 + 42 * 0 + i) + 1 by ring, state_succ',
        ih (by omega), step_row i (by omega), nextRow, if_neg (by omega)]
  | succ m ihm =>
    intro i hi
    induction i with
    | zero =>
      rw [show 138 + 42 * (m + 1) + 0 = (138 + 42 * m + 41) + 1 by ring, state_succ',
        ihm 41 (by norm_num), step_row 41 (by norm_num), nextRow, if_pos rfl, F_shift]
      rfl
    | succ i ih =>
      rw [show 138 + 42 * (m + 1) + (i + 1) = (138 + 42 * (m + 1) + i) + 1 by ring, state_succ',
        ih (by omega), step_row i (by omega), nextRow, if_neg (by omega)]

/-- `a(139 + 42 m + i) = P_i * Y m + Q_i`. -/
private theorem a_form (m i : ℕ) (hi : i < 42) :
    a (139 + 42 * m + i) = (row i).1 * Y m + (row i).2.1 := by
  rw [show 139 + 42 * m + i = (138 + 42 * m + i) + 1 by ring]
  show (state _).1 = _
  rw [key m i hi]
  rfl

/-- `s(139 + 42 m + i) = R_i * Y m + U_i`. -/
private theorem s_form (m i : ℕ) (hi : i < 42) :
    s (139 + 42 * m + i) = (row i).2.2.1 * Y m + (row i).2.2.2 := by
  rw [show 139 + 42 * m + i = (138 + 42 * m + i) + 1 by ring, ← state_snd, key m i hi]
  rfl

/-- `1` occurs infinitely often: `a(143 + 42 m) = 1`. -/
private theorem one_inf : {n : ℕ | a n = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => 139 + 42 * m + 4) ?_ ?_
  · intro x y hxy
    simp only at hxy
    omega
  · intro m
    show a (139 + 42 * m + 4) = 1
    rw [a_form m 4 (by norm_num), show row 4 = (0, 1, 1725051870, 473392) from rfl]
    simp

/-- `2` occurs infinitely often: `a(147 + 42 m) = 2`. -/
private theorem two_inf : {n : ℕ | a n = 2}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => 139 + 42 * m + 8) ?_ ?_
  · intro x y hxy
    simp only at hxy
    omega
  · intro m
    show a (139 + 42 * m + 8) = 2
    rw [a_form m 8 (by norm_num), show row 8 = (0, 2, 6900207480, 1893572) from rfl]
    simp

/-- The rows at odd indices `139 + i` are constant. -/
private theorem row_even_const : ∀ i, i < 42 → i % 2 = 0 → (row i).1 = 0 := by
  decide

/-- Sigrist's first conjecture. -/
private theorem odd_part : sigristOdd := by
  unfold sigristOdd
  intro n hn
  obtain ⟨m, i, hi, hk⟩ : ∃ m i, i < 42 ∧ 2 * n - 1 = 139 + 42 * m + i :=
    ⟨(2 * n - 1 - 139) / 42, (2 * n - 1 - 139) % 42, Nat.mod_lt _ (by norm_num), by omega⟩
  have hk' : 2 * (n + 21) - 1 = 139 + 42 * (m + 1) + i := by omega
  have hev : i % 2 = 0 := by omega
  rw [hk, hk', a_form _ _ hi, a_form _ _ hi, row_even_const i hi hev]
  simp

/-- `a(n + 42) - 3645 a(n)` for `n = 139 + 42 m + i`. -/
private def dA (j : ℕ) : ℤ := ((row j).1 : ℤ) + (row j).2.1 - 3645 * (row j).2.1

/-- Sigrist's second conjecture. -/
private theorem even_part : sigristEven := by
  unfold sigristEven
  refine ⟨fun n => dA ((2 * (n % 21) + 29) % 42), ?_, ?_⟩
  · intro n
    simp only [Nat.add_mod_right]
  · intro n hn
    obtain ⟨m, i, hi, hk⟩ : ∃ m i, i < 42 ∧ 2 * n = 139 + 42 * m + i :=
      ⟨(2 * n - 139) / 42, (2 * n - 139) % 42, Nat.mod_lt _ (by norm_num), by omega⟩
    have hk' : 2 * (n + 21) = 139 + 42 * (m + 1) + i := by omega
    have hj : (2 * (n % 21) + 29) % 42 = i := by omega
    simp only
    rw [hj, hk', hk, a_form _ _ hi, a_form _ _ hi]
    simp only [Y, dA]
    push_cast
    ring

/-- `s(n + 42) - 3645 s(n)` for `n = 139 + 42 m + i`. -/
private def dS (j : ℕ) : ℤ := ((row j).2.2.1 : ℤ) + (row j).2.2.2 - 3645 * (row j).2.2.2

/-- The A355149 conjecture. -/
private theorem sums_part : partialSums := by
  unfold partialSums
  refine ⟨fun n => dS ((n + 29) % 42), ?_, ?_⟩
  · intro n
    simp only [show n + 42 + 29 = (n + 29) + 42 by ring, Nat.add_mod_right]
  · intro n hn
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h
      have h1 : s 180 = 1150350168 := by
        rw [show 180 = 139 + 42 * 0 + 41 by rfl, s_form 0 41 (by norm_num)]
        rfl
      have h2 : s 139 = 315591 := by
        rw [show 139 = 139 + 42 * 0 + 0 by rfl, s_form 0 0 (by norm_num)]
        rfl
      have h3 : a 139 = 3 := by
        rw [show 139 = 139 + 42 * 0 + 0 by rfl, a_form 0 0 (by norm_num)]
        rfl
      have h4 : s 138 = 315588 := by
        have := s_succ 138
        rw [show (138 + 1 : ℕ) = 139 from rfl, h2, h3] at this
        omega
      simp only
      rw [show 138 + 42 = 180 by rfl, h1, h4]
      decide
    · obtain ⟨m, i, hi, hk⟩ : ∃ m i, i < 42 ∧ n = 139 + 42 * m + i :=
        ⟨(n - 139) / 42, (n - 139) % 42, Nat.mod_lt _ (by norm_num), by omega⟩
      have hj : (n + 29) % 42 = i := by omega
      simp only
      rw [hj]
      subst hk
      rw [show 139 + 42 * m + i + 42 = 139 + 42 * (m + 1) + i by ring, s_form _ _ hi,
        s_form _ _ hi]
      simp only [Y, dS]
      push_cast
      ring

/-- All four conjectures on A351743 and A355149 hold. -/
theorem result : statement :=
  And.intro (And.intro one_inf two_inf) (And.intro odd_part (And.intro even_part sums_part))

end Math0.Frontier.A351743

#math0_settles Math0.Frontier.A351743.result Math0.Statements.A351743.statement

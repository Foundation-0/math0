/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A121750
import Math0.Audit

/-!
# Mathar's recurrence for A121750 (even columns in deco polyominoes)

We prove R. J. Mathar's conjectured order-6 D-finite recurrence for A121750 for every `n ≥ 7`.

**Translation invariance.** Shifting every column of a list in `tails r b` up by one cell gives
exactly `tails (r + 1) (b + 1)` (`tails_shift`), and keeps column lengths. Hence the table entry
`(tab r).getD b` (count, total even columns) only depends on `r - b`: it equals
`(cnt (r - b), tot (r - b))`, where `cnt m`, `tot m` are the entries at bottom `0`, and
`tot m = a (m + 1)`.

**Recurrences.** The recursion of `tab` at bottom `0` becomes
`cnt (r+1) = 1 + gS cnt r` and `tot (r+1) = [r+1 odd] + hS cnt r + gS tot r`, with
`gS f r = ∑_{t ≤ r} ∑_{j ≤ t} f (r - j)` and `hS f r` the same sum restricted to odd `t`.
Peeling off `j = 0` gives `gS f (r+1) = gS f r + (r + 2) f (r + 1)` and
`hS f (r+1) + hS f r = gS f r + f (r + 1) ⌊(r + 2)/2⌋`.

**Algebra.** For `n = r + 8`, write `r = 2s + p` (`p ∈ {0,1}`). Starting from the free values
`gS tot r`, `hS cnt r`, `gS cnt r`, seven steps of these recurrences express
`a(n-6), …, a(n)` as polynomials in `s` and the three free values; substituting into Mathar's
left-hand side gives `0` identically (`alg0`, `alg1`, by `ring`). The case `n = 7` is the
kernel-checked `recurrence_data`.
-/

namespace Math0.Frontier.A121750
open Math0.Statements.A121750

/-- Shift every cell of a column list up by one. -/
private def sh (cs : List (ℕ × ℕ)) : List (ℕ × ℕ) := cs.map fun c => (c.1 + 1, c.2 + 1)

/-- `range' (b + 1) n` is `range' b n` shifted by one. -/
private lemma range'_succ_left (b n : ℕ) :
    List.range' (b + 1) n = (List.range' b n).map (· + 1) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih => rw [List.range'_succ, List.range'_succ, List.map_cons, ih]

/-- Translation invariance: `tails (r + 1) (b + 1)` is `tails r b` shifted up by one. -/
private lemma tails_shift (r b : ℕ) : tails (r + 1) (b + 1) = (tails r b).map sh := by
  induction r generalizing b with
  | zero =>
    rcases b with _ | b
    · simp [tails, sh]
    · simp [tails]
  | succ r ih =>
    rw [tails, tails, List.map_append]
    congr 1
    · by_cases h : b ≤ r + 1
      · rw [if_pos (by omega), if_pos h]; simp [sh]
      · rw [if_neg (by omega), if_neg h]; simp
    · rw [show r + 1 + 1 - (b + 1) = r + 1 - b by omega, range'_succ_left]
      simp only [List.flatMap_map, List.map_flatMap]
      congr 1
      funext t
      rw [show t + 1 + 1 - (b + 1) = t + 1 - b by omega, range'_succ_left]
      simp only [List.flatMap_map, ih, List.map_map]
      congr 1

/-- Shifting does not change column lengths. -/
private lemma evenCols_sh (cs : List (ℕ × ℕ)) : evenCols (sh cs) = evenCols cs := by
  simp only [evenCols, sh, List.countP_map]
  congr 1
  funext c
  simp

/-- Translation invariance of the table entries. -/
private lemma tab_shift (r b : ℕ) : (tab (r + 1)).getD (b + 1) (0, 0) = (tab r).getD b (0, 0) := by
  rw [tab_getD, tab_getD, tails_shift, List.length_map, List.map_map]
  simp only [Function.comp_def, evenCols_sh]

/-- Table entries depend only on `r - b`. -/
private lemma tab_sub (r b : ℕ) (h : b ≤ r) :
    (tab r).getD b (0, 0) = (tab (r - b)).getD 0 (0, 0) := by
  induction b generalizing r with
  | zero => rfl
  | succ b ih =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [tab_shift, ih r (by omega), Nat.add_sub_add_right]

/-- `cnt m = |tails m 0|`, the number of deco polyominoes of height `m + 1`. -/
private def cnt (m : ℕ) : ℕ := ((tab m).getD 0 (0, 0)).1

/-- `tot m = a (m + 1)`, the total number of even columns over `tails m 0`. -/
private def tot (m : ℕ) : ℕ := ((tab m).getD 0 (0, 0)).2

/-- `gS f r = ∑_{t ≤ r} ∑_{j ≤ t} f (r - j)`. -/
private def gS (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (t + 1), f (r - j)

/-- `hS f r = ∑_{t ≤ r, t odd} ∑_{j ≤ t} f (r - j)`. -/
private def hS (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (r + 1), eo 0 t * ∑ j ∈ Finset.range (t + 1), f (r - j)

/-- `oddCnt k` is the number of odd `t < k`. -/
private def oddCnt (k : ℕ) : ℕ := ∑ t ∈ Finset.range k, eo 0 t

/-- A list sum over `range' 0 n` as a `Finset` sum. -/
private lemma lsum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range' 0 n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.range_eq_range']
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

/-- The recursion of `tab` at bottom `0`, using translation invariance. -/
private lemma row0 (r : ℕ) : (tab (r + 1)).getD 0 (0, 0) =
    (1 + gS cnt r, eo 0 (r + 1) + hS cnt r + gS tot r) := by
  have key : ∀ t ∈ Finset.range (r + 1), ∀ j ∈ Finset.range (t + 1),
      (tab r).getD j (0, 0) = (cnt (r - j), tot (r - j)) := by
    intro t ht j hj
    simp only [Finset.mem_range] at ht hj
    rw [tab_sub r j (by omega)]
    rfl
  have e1 : ∀ t ∈ Finset.range (r + 1),
      ∑ j ∈ Finset.range (t + 1), ((tab r).getD j (0, 0)).1 =
        ∑ j ∈ Finset.range (t + 1), cnt (r - j) := fun t ht =>
    Finset.sum_congr rfl fun j hj => by rw [key t ht j hj]
  have e2 : ∀ t ∈ Finset.range (r + 1),
      ∑ j ∈ Finset.range (t + 1), ((tab r).getD j (0, 0)).2 =
        ∑ j ∈ Finset.range (t + 1), tot (r - j) := fun t ht =>
    Finset.sum_congr rfl fun j hj => by rw [key t ht j hj]
  rw [tab, nextRow, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, Nat.sub_zero, List.sum_map_add, lsum]
  refine Prod.ext ?_ ?_
  · show 1 + _ = 1 + _
    rw [gS]
    congr 1
    exact Finset.sum_congr rfl e1
  · show eo 0 (r + 1) + (_ + _) = eo 0 (r + 1) + hS cnt r + gS tot r
    rw [hS, gS, add_assoc]
    congr 2
    · exact Finset.sum_congr rfl fun t ht => by rw [e1 t ht]
    · exact Finset.sum_congr rfl e2

/-- Peeling `j = 0` off the inner sum. -/
private lemma inner_succ (f : ℕ → ℕ) (r t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), f (r + 1 - j) = ∑ j ∈ Finset.range t, f (r - j) + f (r + 1) := by
  rw [Finset.sum_range_succ']
  simp

/-- `gS f (r + 1) = gS f r + (r + 2) f (r + 1)`. -/
private lemma gS_succ (f : ℕ → ℕ) (r : ℕ) : gS f (r + 1) = gS f r + (r + 2) * f (r + 1) := by
  rw [gS, gS]
  simp_rw [inner_succ]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_range_succ' (fun t => ∑ j ∈ Finset.range t, f (r - j))]
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]

/-- Consecutive parities add up to one. -/
private lemma eo_add (t : ℕ) : eo 0 (t + 1) + eo 0 t = 1 := by
  unfold eo; split_ifs <;> omega

/-- `hS f (r + 1) + hS f r = gS f r + f (r + 1) · oddCnt (r + 2)`. -/
private lemma hS_succ (f : ℕ → ℕ) (r : ℕ) :
    hS f (r + 1) + hS f r = gS f r + f (r + 1) * oddCnt (r + 2) := by
  rw [hS, hS, gS, oddCnt]
  simp_rw [inner_succ, mul_add]
  rw [Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun t => eo 0 t * ∑ j ∈ Finset.range t, f (r - j))]
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
  rw [← Finset.sum_mul, mul_comm (∑ t ∈ Finset.range (r + 1 + 1), eo 0 t), add_right_comm,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← add_mul, eo_add, one_mul]

/-- `oddCnt k = ⌊k / 2⌋`. -/
private lemma oddCnt_eq (k : ℕ) : oddCnt k = k / 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [oddCnt, Finset.sum_range_succ, ← oddCnt, ih]
    unfold eo; split_ifs <;> omega

/-- The first recurrence, in `ℤ`. -/
private lemma Z1 (r : ℕ) :
    (tot (r + 1) : ℤ) = (((r + 1) % 2 : ℕ) : ℤ) + hS cnt r + gS tot r := by
  have h : tot (r + 1) = eo 0 (r + 1) + hS cnt r + gS tot r := by rw [tot, row0]
  have he : eo 0 (r + 1) = (r + 1) % 2 := by unfold eo; split_ifs <;> omega
  rw [h, he]
  push_cast
  ring

/-- `gS tot (r + 1) = gS tot r + (r + 2) tot (r + 1)` in `ℤ`. -/
private lemma Z2 (r : ℕ) : (gS tot (r + 1) : ℤ) = gS tot r + ((r : ℤ) + 2) * tot (r + 1) := by
  rw [gS_succ]; push_cast; ring

/-- The `hS` recurrence in `ℤ`. -/
private lemma Z3 (r : ℕ) : (hS cnt (r + 1) : ℤ) =
    gS cnt r + cnt (r + 1) * (((r + 2) / 2 : ℕ) : ℤ) - hS cnt r := by
  have h := hS_succ cnt r
  rw [oddCnt_eq] at h
  have h' : ((hS cnt (r + 1) + hS cnt r : ℕ) : ℤ) =
      ((gS cnt r + cnt (r + 1) * ((r + 2) / 2) : ℕ) : ℤ) := by rw [h]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h'
  linarith

/-- `cnt (r + 1) = 1 + gS cnt r` in `ℤ`. -/
private lemma Z4 (r : ℕ) : (cnt (r + 1) : ℤ) = 1 + gS cnt r := by
  have h : cnt (r + 1) = 1 + gS cnt r := by rw [cnt, row0]
  rw [h]; push_cast; ring

/-- `gS cnt (r + 1) = gS cnt r + (r + 2) cnt (r + 1)` in `ℤ`. -/
private lemma Z5 (r : ℕ) : (gS cnt (r + 1) : ℤ) = gS cnt r + ((r : ℤ) + 2) * cnt (r + 1) := by
  rw [gS_succ]; push_cast; ring

/-- `a (k + 1) = tot k`. -/
private lemma a_tot (k : ℕ) : (a (k + 1) : ℤ) = tot k := by
  rw [a_eq_aDP]; rfl

/-- The algebraic core for a base index `x = 2s + 0`: seven steps of the recurrences,
then Mathar's identity, as a polynomial identity. -/
private lemma alg0 (s x : ℤ) {v1 v2 v3 v4 v5 v6 v7 gv0 gv1 gv2 gv3 gv4 gv5 gv6 hu0 hu1 hu2 hu3 hu4 hu5 hu6 gu0 gu1 gu2 gu3 gu4 gu5 u1 u2 u3 u4 u5 u6 e1 e2 e3 e4 e5 e6 e7 c2 c3 c4 c5 c6 c7 k0 k1 k2 k3 k4 k5 : ℤ}
    (hv1 : v1 = e1 + hu0 + gv0)
    (hv2 : v2 = e2 + hu1 + gv1)
    (hv3 : v3 = e3 + hu2 + gv2)
    (hv4 : v4 = e4 + hu3 + gv3)
    (hv5 : v5 = e5 + hu4 + gv4)
    (hv6 : v6 = e6 + hu5 + gv5)
    (hv7 : v7 = e7 + hu6 + gv6)
    (hg1 : gv1 = gv0 + (k0 + 2) * v1)
    (hg2 : gv2 = gv1 + (k1 + 2) * v2)
    (hg3 : gv3 = gv2 + (k2 + 2) * v3)
    (hg4 : gv4 = gv3 + (k3 + 2) * v4)
    (hg5 : gv5 = gv4 + (k4 + 2) * v5)
    (hg6 : gv6 = gv5 + (k5 + 2) * v6)
    (hh1 : hu1 = gu0 + u1 * c2 - hu0)
    (hh2 : hu2 = gu1 + u2 * c3 - hu1)
    (hh3 : hu3 = gu2 + u3 * c4 - hu2)
    (hh4 : hu4 = gu3 + u4 * c5 - hu3)
    (hh5 : hu5 = gu4 + u5 * c6 - hu4)
    (hh6 : hu6 = gu5 + u6 * c7 - hu5)
    (hu1' : u1 = 1 + gu0)
    (hu2' : u2 = 1 + gu1)
    (hu3' : u3 = 1 + gu2)
    (hu4' : u4 = 1 + gu3)
    (hu5' : u5 = 1 + gu4)
    (hu6' : u6 = 1 + gu5)
    (hgu1 : gu1 = gu0 + (k0 + 2) * u1)
    (hgu2 : gu2 = gu1 + (k1 + 2) * u2)
    (hgu3 : gu3 = gu2 + (k2 + 2) * u3)
    (hgu4 : gu4 = gu3 + (k3 + 2) * u4)
    (hgu5 : gu5 = gu4 + (k4 + 2) * u5)
    (he1 : e1 = 1)
    (he2 : e2 = 0)
    (he3 : e3 = 1)
    (he4 : e4 = 0)
    (he5 : e5 = 1)
    (he6 : e6 = 0)
    (he7 : e7 = 1)
    (hc2 : c2 = s + 1)
    (hc3 : c3 = s + 1)
    (hc4 : c4 = s + 2)
    (hc5 : c5 = s + 2)
    (hc6 : c6 = s + 3)
    (hc7 : c7 = s + 3)
    (hk0 : k0 = 2 * s + 0)
    (hk1 : k1 = 2 * s + 1)
    (hk2 : k2 = 2 * s + 2)
    (hk3 : k3 = 2 * s + 3)
    (hk4 : k4 = 2 * s + 4)
    (hk5 : k5 = 2 * s + 5)
    (hx : x = 2 * s + 0)
    : v7 + (-(x + 8) - 2) * v6 + (-(x + 8) ^ 2 + 4 * (x + 8) - 2) * v5 + ((x + 8) ^ 3 - 3 * (x + 8) ^ 2 - 4 * (x + 8) + 11) * v4 - ((x + 8) - 1) * ((x + 8) ^ 2 - 11 * (x + 8) + 26) * v3 + (-(x + 8) ^ 3 + 5 * (x + 8) ^ 2 + 7 * (x + 8) - 43) * v2 + ((x + 8) - 3) * ((x + 8) - 5) ^ 2 * v1 = 0 := by
  subst_vars
  ring

/-- The algebraic core for a base index `x = 2s + 1`: seven steps of the recurrences,
then Mathar's identity, as a polynomial identity. -/
private lemma alg1 (s x : ℤ) {v1 v2 v3 v4 v5 v6 v7 gv0 gv1 gv2 gv3 gv4 gv5 gv6 hu0 hu1 hu2 hu3 hu4 hu5 hu6 gu0 gu1 gu2 gu3 gu4 gu5 u1 u2 u3 u4 u5 u6 e1 e2 e3 e4 e5 e6 e7 c2 c3 c4 c5 c6 c7 k0 k1 k2 k3 k4 k5 : ℤ}
    (hv1 : v1 = e1 + hu0 + gv0)
    (hv2 : v2 = e2 + hu1 + gv1)
    (hv3 : v3 = e3 + hu2 + gv2)
    (hv4 : v4 = e4 + hu3 + gv3)
    (hv5 : v5 = e5 + hu4 + gv4)
    (hv6 : v6 = e6 + hu5 + gv5)
    (hv7 : v7 = e7 + hu6 + gv6)
    (hg1 : gv1 = gv0 + (k0 + 2) * v1)
    (hg2 : gv2 = gv1 + (k1 + 2) * v2)
    (hg3 : gv3 = gv2 + (k2 + 2) * v3)
    (hg4 : gv4 = gv3 + (k3 + 2) * v4)
    (hg5 : gv5 = gv4 + (k4 + 2) * v5)
    (hg6 : gv6 = gv5 + (k5 + 2) * v6)
    (hh1 : hu1 = gu0 + u1 * c2 - hu0)
    (hh2 : hu2 = gu1 + u2 * c3 - hu1)
    (hh3 : hu3 = gu2 + u3 * c4 - hu2)
    (hh4 : hu4 = gu3 + u4 * c5 - hu3)
    (hh5 : hu5 = gu4 + u5 * c6 - hu4)
    (hh6 : hu6 = gu5 + u6 * c7 - hu5)
    (hu1' : u1 = 1 + gu0)
    (hu2' : u2 = 1 + gu1)
    (hu3' : u3 = 1 + gu2)
    (hu4' : u4 = 1 + gu3)
    (hu5' : u5 = 1 + gu4)
    (hu6' : u6 = 1 + gu5)
    (hgu1 : gu1 = gu0 + (k0 + 2) * u1)
    (hgu2 : gu2 = gu1 + (k1 + 2) * u2)
    (hgu3 : gu3 = gu2 + (k2 + 2) * u3)
    (hgu4 : gu4 = gu3 + (k3 + 2) * u4)
    (hgu5 : gu5 = gu4 + (k4 + 2) * u5)
    (he1 : e1 = 0)
    (he2 : e2 = 1)
    (he3 : e3 = 0)
    (he4 : e4 = 1)
    (he5 : e5 = 0)
    (he6 : e6 = 1)
    (he7 : e7 = 0)
    (hc2 : c2 = s + 1)
    (hc3 : c3 = s + 2)
    (hc4 : c4 = s + 2)
    (hc5 : c5 = s + 3)
    (hc6 : c6 = s + 3)
    (hc7 : c7 = s + 4)
    (hk0 : k0 = 2 * s + 1)
    (hk1 : k1 = 2 * s + 2)
    (hk2 : k2 = 2 * s + 3)
    (hk3 : k3 = 2 * s + 4)
    (hk4 : k4 = 2 * s + 5)
    (hk5 : k5 = 2 * s + 6)
    (hx : x = 2 * s + 1)
    : v7 + (-(x + 8) - 2) * v6 + (-(x + 8) ^ 2 + 4 * (x + 8) - 2) * v5 + ((x + 8) ^ 3 - 3 * (x + 8) ^ 2 - 4 * (x + 8) + 11) * v4 - ((x + 8) - 1) * ((x + 8) ^ 2 - 11 * (x + 8) + 26) * v3 + (-(x + 8) ^ 3 + 5 * (x + 8) ^ 2 + 7 * (x + 8) - 43) * v2 + ((x + 8) - 3) * ((x + 8) - 5) ^ 2 * v1 = 0 := by
  subst_vars
  ring

/-- Mathar's identity at `n = r + 8`, in terms of `tot`. -/
private lemma key (r : ℕ) :
    (tot (r + 1 + 1 + 1 + 1 + 1 + 1 + 1) : ℤ) + (-((r : ℤ) + 8) - 2) * (tot (r + 1 + 1 + 1 + 1 + 1 + 1) : ℤ) + (-((r : ℤ) + 8) ^ 2 + 4 * ((r : ℤ) + 8) - 2) * (tot (r + 1 + 1 + 1 + 1 + 1) : ℤ) + (((r : ℤ) + 8) ^ 3 - 3 * ((r : ℤ) + 8) ^ 2 - 4 * ((r : ℤ) + 8) + 11) * (tot (r + 1 + 1 + 1 + 1) : ℤ) - (((r : ℤ) + 8) - 1) * (((r : ℤ) + 8) ^ 2 - 11 * ((r : ℤ) + 8) + 26) * (tot (r + 1 + 1 + 1) : ℤ) + (-((r : ℤ) + 8) ^ 3 + 5 * ((r : ℤ) + 8) ^ 2 + 7 * ((r : ℤ) + 8) - 43) * (tot (r + 1 + 1) : ℤ) + (((r : ℤ) + 8) - 3) * (((r : ℤ) + 8) - 5) ^ 2 * (tot (r + 1) : ℤ) = 0 := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · exact alg0 (s : ℤ) ((2 * s : ℕ) : ℤ)
      (Z1 (2 * s)) (Z1 (2 * s + 1)) (Z1 (2 * s + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1))
      (Z1 (2 * s + 1 + 1 + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1 + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1 + 1 + 1 + 1)) (Z2 (2 * s))
      (Z2 (2 * s + 1)) (Z2 (2 * s + 1 + 1)) (Z2 (2 * s + 1 + 1 + 1)) (Z2 (2 * s + 1 + 1 + 1 + 1))
      (Z2 (2 * s + 1 + 1 + 1 + 1 + 1)) (Z3 (2 * s)) (Z3 (2 * s + 1)) (Z3 (2 * s + 1 + 1))
      (Z3 (2 * s + 1 + 1 + 1)) (Z3 (2 * s + 1 + 1 + 1 + 1)) (Z3 (2 * s + 1 + 1 + 1 + 1 + 1)) (Z4 (2 * s))
      (Z4 (2 * s + 1)) (Z4 (2 * s + 1 + 1)) (Z4 (2 * s + 1 + 1 + 1)) (Z4 (2 * s + 1 + 1 + 1 + 1))
      (Z4 (2 * s + 1 + 1 + 1 + 1 + 1)) (Z5 (2 * s)) (Z5 (2 * s + 1)) (Z5 (2 * s + 1 + 1))
      (Z5 (2 * s + 1 + 1 + 1)) (Z5 (2 * s + 1 + 1 + 1 + 1)) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)
  · exact alg1 (s : ℤ) ((2 * s + 1 : ℕ) : ℤ)
      (Z1 (2 * s + 1)) (Z1 (2 * s + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1 + 1))
      (Z1 (2 * s + 1 + 1 + 1 + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1 + 1 + 1 + 1)) (Z1 (2 * s + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (Z2 (2 * s + 1))
      (Z2 (2 * s + 1 + 1)) (Z2 (2 * s + 1 + 1 + 1)) (Z2 (2 * s + 1 + 1 + 1 + 1)) (Z2 (2 * s + 1 + 1 + 1 + 1 + 1))
      (Z2 (2 * s + 1 + 1 + 1 + 1 + 1 + 1)) (Z3 (2 * s + 1)) (Z3 (2 * s + 1 + 1)) (Z3 (2 * s + 1 + 1 + 1))
      (Z3 (2 * s + 1 + 1 + 1 + 1)) (Z3 (2 * s + 1 + 1 + 1 + 1 + 1)) (Z3 (2 * s + 1 + 1 + 1 + 1 + 1 + 1)) (Z4 (2 * s + 1))
      (Z4 (2 * s + 1 + 1)) (Z4 (2 * s + 1 + 1 + 1)) (Z4 (2 * s + 1 + 1 + 1 + 1)) (Z4 (2 * s + 1 + 1 + 1 + 1 + 1))
      (Z4 (2 * s + 1 + 1 + 1 + 1 + 1 + 1)) (Z5 (2 * s + 1)) (Z5 (2 * s + 1 + 1)) (Z5 (2 * s + 1 + 1 + 1))
      (Z5 (2 * s + 1 + 1 + 1 + 1)) (Z5 (2 * s + 1 + 1 + 1 + 1 + 1)) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)


/-- Mathar's conjectured recurrence holds for every `n ≥ 7`. -/
theorem result : statement := by
  intro n hn
  rcases Nat.lt_or_ge n 8 with h | h
  · obtain rfl : n = 7 := by omega
    exact recurrence_data 7 (by decide)
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 8 := ⟨n - 8, by omega⟩
    have h0 : (a (r + 8) : ℤ) = tot (r + 1 + 1 + 1 + 1 + 1 + 1 + 1) := a_tot _
    have h1 : (a (r + 8 - 1) : ℤ) = tot (r + 1 + 1 + 1 + 1 + 1 + 1) := by
      rw [show r + 8 - 1 = r + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]; exact a_tot _
    have h2 : (a (r + 8 - 2) : ℤ) = tot (r + 1 + 1 + 1 + 1 + 1) := by
      rw [show r + 8 - 2 = r + 1 + 1 + 1 + 1 + 1 + 1 by omega]; exact a_tot _
    have h3 : (a (r + 8 - 3) : ℤ) = tot (r + 1 + 1 + 1 + 1) := by
      rw [show r + 8 - 3 = r + 1 + 1 + 1 + 1 + 1 by omega]; exact a_tot _
    have h4 : (a (r + 8 - 4) : ℤ) = tot (r + 1 + 1 + 1) := by
      rw [show r + 8 - 4 = r + 1 + 1 + 1 + 1 by omega]; exact a_tot _
    have h5 : (a (r + 8 - 5) : ℤ) = tot (r + 1 + 1) := by
      rw [show r + 8 - 5 = r + 1 + 1 + 1 by omega]; exact a_tot _
    have h6 : (a (r + 8 - 6) : ℤ) = tot (r + 1) := by
      rw [show r + 8 - 6 = r + 1 + 1 by omega]; exact a_tot _
    rw [h0, h1, h2, h3, h4, h5, h6]
    push_cast
    linear_combination key r

end Math0.Frontier.A121750

#math0_settles Math0.Frontier.A121750.result Math0.Statements.A121750.statement

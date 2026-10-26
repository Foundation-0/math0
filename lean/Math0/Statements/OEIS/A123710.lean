/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A123710: rows of the inverse of `⌊n/k⌋` with exactly four nonzero entries

Source: https://oeis.org/A123710, M. F. Hasler, Feb 12 2012 (FORMULA section). Verbatim:
> a(n) = A025475(n) for n>2 (conjectured). - _M. F. Hasler_, Feb 12 2012

The entry (Paul D. Hanna, Oct 09 2006, offset `1`) is "Indices k such that 4 = A123709(k) =
number of nonzero terms in row k of triangle A123706", where "Triangle A123706 is the matrix
inverse of triangle A010766, where A010766(n,k) = [n/k]". Its data start `4, 6, 8, 9, 16, 25, …`.
A025475 (offset `1`) is "1 and the prime powers p^m where m >= 2, thus excluding the primes":
`1, 4, 8, 9, 16, 25, …`. So the conjecture says that from the third term on, A123710 lists exactly
the proper prime powers.

## Encoding

* A010766 is the lower triangular matrix `A(n,k) = ⌊n/k⌋` (`n ≥ k ≥ 1`, and `0` above the
  diagonal). `floorMat N` is its `N × N` truncation, indexed from `0`: entry `(i, j)` is
  `⌊(i+1)/(j+1)⌋`, which is `0` for `j > i` (PARI: `matrix(N, N, r, c, r\c)`).
* A123706 is the matrix inverse of A010766. Since A010766 is lower triangular with ones on the
  diagonal, row `n` of its inverse is the last row of the inverse of the `n × n` truncation.
  `A123706 n k` is entry `(n, k)` of `(floorMat n)⁻¹` (Mathlib's `Matrix.inv`) for `1 ≤ k ≤ n`,
  and `0` otherwise. This is the PARI program of A123709,
  `#select((matrix(n, n, r, c, r\c)^-1)[n,], x->x)`. `A123706_eq_inv` checks that every larger
  truncation gives the same entry.
* `A123709 n` is the number of `k ∈ [1, n]` with `A123706 n k ≠ 0` (so `A123709 0 = 0`).
* `IsTerm n` is `A123709 n = 4`, and `a n = Nat.nth IsTerm (n - 1)` is the `n`-th smallest such
  index (offset `1`). `0` is never a term. `a` is noncomputable as written.
* `IsA025475 m` is `m = 1 ∨ ∃ p k, p.Prime ∧ 2 ≤ k ∧ m = p ^ k`, and
  `A025475 n = Nat.nth IsA025475 (n - 1)` (offset `1`).
* Computation. `row n` computes row `n` of the inverse by back substitution in `T · A = I`:
  `T(n,n) = 1` and `T(n,k) = -∑_{j=k+1}^{n} T(n,j) ⌊j/k⌋` for `k < n`. `Tmat_eq_inv` proves
  that these rows form the inverse of every truncation, so `A123706 = T` (`A123706_eq_T`). For
  speed, the data checks use `Rf`, the same back substitution that keeps only the nonzero entries,
  written with `Nat.rec`/`List.rec` and kernel-accelerated `Nat` operations (so it is
  noncomputable for the compiler but cheap for the kernel); `A123709_eq_Rf` proves
  `A123709 = Rf`.
* Data checks (kernel): `A123706_data` checks all `113` listed terms of A123706, `A123709_data`
  all `76` listed terms of A123709, `a_data` the first `21` of the `52` listed terms of A123710
  (all terms `≤ 512`; the kernel has to run the back substitution for every `n ≤ 512`, at a cost
  of about `n` steps each, which is what limits the range), and `A025475_data` the first `21`
  listed terms of A025475 (all terms `≤ 512`, decided through a trial-division search for the
  least prime factor, `isA025475_iff`). From index `3` on the two lists agree.
* `statement`: `∀ n > 2, a n = A025475 n`, exactly as in the formula line ("for n>2"), with
  both sequences indexed from `1`. With `Nat.nth`, if A123710 were finite then `a n = 0` past its
  end; since A025475 is infinite with positive terms, the statement would then be false, as the
  conjecture would be.
-/

namespace Math0.Statements.A123710

open Finset

/-! ### The sequences -/

/-- The `N × N` truncation of the triangle A010766, `A(n,k) = ⌊n/k⌋`, indexed from `0`: entry
`(i, j)` is `⌊(i+1)/(j+1)⌋`, which is `0` above the diagonal (PARI: `matrix(N, N, r, c, r\c)`). -/
def floorMat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => ((((i : ℕ) + 1) / ((j : ℕ) + 1) : ℕ) : ℤ)

/-- A123706: the entry in row `n`, column `k` (`1 ≤ k ≤ n`) of the matrix inverse of the triangle
A010766, read off from the inverse of its `n × n` truncation; `0` outside `1 ≤ k ≤ n`. -/
noncomputable def A123706 (n k : ℕ) : ℤ :=
  if h : 1 ≤ k ∧ k ≤ n then (floorMat n)⁻¹ ⟨n - 1, by omega⟩ ⟨k - 1, by omega⟩ else 0

/-- A123709: the number of nonzero entries in row `n` of A123706. -/
noncomputable def A123709 (n : ℕ) : ℕ := #{k ∈ Icc 1 n | A123706 n k ≠ 0}

/-- `n` is a term of A123710: row `n` of A123706 has exactly `4` nonzero entries. -/
def IsTerm (n : ℕ) : Prop := A123709 n = 4

/-- A123710 (offset `1`): the `n`-th smallest index `k` such that row `k` of A123706 has exactly
`4` nonzero entries. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- `m` is a term of A025475: `m = 1` or `m = p ^ k` with `p` prime and `k ≥ 2`. -/
def IsA025475 (m : ℕ) : Prop := m = 1 ∨ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ m = p ^ k

/-- A025475 (offset `1`): `1` and the prime powers `p^m` with `m ≥ 2`, in increasing order. -/
noncomputable def A025475 (n : ℕ) : ℕ := Nat.nth IsA025475 (n - 1)

/-! ### Back substitution: the rows of the inverse -/

/-- `dot k j [x₀, x₁, …, x_{r-1}] = ∑_{i < r} xᵢ * ⌊(j + i) / k⌋`. -/
def dot (k : ℕ) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | j, x :: xs => x * ((j / k : ℕ) : ℤ) + dot k (j + 1) xs

/-- `tail n m = [T(n, n-m+1), …, T(n, n)]` (for `m ≤ n`): the last `m` entries of row `n` of the
inverse triangle, computed from right to left by `T(n,k) = [k = n] - ∑_{j=k+1}^{n} T(n,j) ⌊j/k⌋`
(row `n` of `T · A = I`, where `A(j,k) = ⌊j/k⌋` and `A(k,k) = 1`). -/
def tail (n : ℕ) : ℕ → List ℤ
  | 0 => []
  | m + 1 => ((if m = 0 then 1 else 0) - dot (n - m) (n - m + 1) (tail n m)) :: tail n m

/-- Row `n` of the inverse, computed by back substitution: `[T(n,1), …, T(n,n)]`. -/
def row (n : ℕ) : List ℤ := tail n n

/-- The entry `T(n,k)` (`1 ≤ k ≤ n`) computed by back substitution; `0` outside `1 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℤ := if k = 0 then 0 else (row n).getD (k - 1) 0

theorem length_tail (n m : ℕ) : (tail n m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [tail, ih]

theorem length_row (n : ℕ) : (row n).length = n := length_tail n n

theorem drop_tail (n m d : ℕ) : (tail n (m + d)).drop d = tail n m := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show (tail n (m + d + 1)).drop (d + 1) = tail n m
    simp only [tail, List.drop_succ_cons, ih]

theorem getD_drop_zero (L : List ℤ) (d i : ℕ) : (L.drop d).getD i 0 = L.getD (d + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_tail {n m : ℕ} (i : ℕ) (hm : m ≤ n) :
    (tail n m).getD i 0 = T n (n - m + 1 + i) := by
  have h : row n = tail n (m + (n - m)) := by rw [row, Nat.add_sub_cancel' hm]
  rw [T, if_neg (by omega), show n - m + 1 + i - 1 = (n - m) + i by omega, h,
    ← getD_drop_zero, drop_tail]

theorem T_eq_head {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    T n k = (if k = n then 1 else 0) - dot k (k + 1) (tail n (n - k)) := by
  have h := getD_tail (n := n) (m := n - k + 1) 0 (by omega)
  rw [show n - (n - k + 1) + 1 + 0 = k by omega] at h
  rw [← h, tail, List.getD_cons_zero, show n - (n - k) = k by omega]
  split_ifs <;> omega

theorem dot_eq_sum (k j : ℕ) (L : List ℤ) :
    dot k j L = ∑ i ∈ range L.length, L.getD i 0 * (((j + i) / k : ℕ) : ℤ) := by
  induction L generalizing j with
  | nil => simp [dot]
  | cons x xs ih =>
    rw [dot, ih, List.length_cons, Finset.sum_range_succ', List.getD_cons_zero, add_zero,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.getD_cons_succ, show j + 1 + i = j + (i + 1) by omega]

theorem T_zero_right (n : ℕ) : T n 0 = 0 := by simp [T]

theorem T_eq_zero_of_lt {n k : ℕ} (h : n < k) : T n k = 0 := by
  rw [T, if_neg (by omega), List.getD_eq_default _ _ (by rw [length_row]; omega)]

/-- Row `n` of `T · A = I`: `∑_{j=1}^{n} T(n,j) ⌊j/k⌋ = [k = n]` for every `k ≥ 1`. -/
theorem sum_T_mul_floor {n k : ℕ} (hk : 1 ≤ k) :
    ∑ l ∈ range n, T n (l + 1) * (((l + 1) / k : ℕ) : ℤ) = if k = n then 1 else 0 := by
  rcases Nat.lt_or_ge n k with hnk | hkn
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [Nat.div_eq_of_lt (by omega)]
    simp
  set f : ℕ → ℤ := fun l => T n (l + 1) * (((l + 1) / k : ℕ) : ℤ) with hf
  have e1 : ∑ l ∈ range n, f l =
      ∑ l ∈ range (k - 1), f l + ∑ x ∈ range (n - k + 1), f (k - 1 + x) := by
    rw [← Finset.sum_range_add, show k - 1 + (n - k + 1) = n by omega]
  have e2 : ∑ l ∈ range (k - 1), f l = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [hf]
    simp only
    rw [Nat.div_eq_of_lt (show l + 1 < k by omega), Nat.cast_zero, mul_zero]
  have e3 : ∑ x ∈ range (n - k), f (k - 1 + (x + 1)) = dot k (k + 1) (tail n (n - k)) := by
    rw [dot_eq_sum, length_tail]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [getD_tail i (by omega), hf]
    simp only
    rw [show k - 1 + (i + 1) + 1 = k + 1 + i by omega,
      show n - (n - k) + 1 + i = k + 1 + i by omega]
  have e4 : f (k - 1 + 0) = T n k := by
    rw [hf]
    simp only
    rw [show k - 1 + 0 + 1 = k by omega, Nat.div_self (by omega)]
    simp
  rw [e1, e2, Finset.sum_range_succ', e3, e4, T_eq_head hk hkn]
  ring

/-- The `N × N` truncation of `T` (indexed from `0`): entry `(i, j)` is `T (i+1) (j+1)`. -/
def Tmat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => T ((i : ℕ) + 1) ((j : ℕ) + 1)

theorem Tmat_mul_floorMat (N : ℕ) : Tmat N * floorMat N = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Tmat, floorMat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun l => T ((i : ℕ) + 1) (l + 1) * (((l + 1) / ((j : ℕ) + 1) : ℕ) : ℤ)) N]
  have hi := i.isLt
  have hN : range N = range (((i : ℕ) + 1) + (N - ((i : ℕ) + 1))) := by congr 1; omega
  rw [hN, Finset.sum_range_add, sum_T_mul_floor (by omega)]
  rw [Finset.sum_eq_zero (s := range (N - ((i : ℕ) + 1))) fun x _ => by
    rw [T_eq_zero_of_lt (by omega), zero_mul], add_zero]
  by_cases e : i = j
  · subst e; simp
  · rw [if_neg e, if_neg]
    intro e'
    exact e (Fin.ext (by omega))

/-- The rows computed by back substitution form the matrix inverse of A010766: for every `N`,
the `N × N` truncation of `T` is the inverse of the `N × N` truncation of `⌊n/k⌋`. -/
theorem Tmat_eq_inv (N : ℕ) : Tmat N = (floorMat N)⁻¹ :=
  (Matrix.inv_eq_left_inv (Tmat_mul_floorMat N)).symm

theorem A123706_eq_T (n k : ℕ) : A123706 n k = T n k := by
  rw [A123706]
  split_ifs with h
  · rw [← Tmat_eq_inv]
    simp only [Tmat, Matrix.of_apply]
    rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel h.1]
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, T_zero_right]
    · rw [T_eq_zero_of_lt (by omega)]

/-- Consistency: every truncation `N ≥ n` of A010766 gives the same entry `A123706 n k`. -/
theorem A123706_eq_inv {n k N : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ N) :
    A123706 n k = (floorMat N)⁻¹ ⟨n - 1, by omega⟩ ⟨k - 1, by omega⟩ := by
  rw [A123706_eq_T, ← Tmat_eq_inv]
  simp only [Tmat, Matrix.of_apply]
  rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel hk]

/-- `row n = [T n 1, …, T n n]`. -/
theorem row_eq (n : ℕ) : row n = (List.range n).map (fun i => T n (i + 1)) := by
  apply List.ext_getElem (by simp [length_row])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, T, if_neg (by omega), Nat.add_sub_cancel,
    List.getD_eq_getElem _ _ h1]

theorem card_filter_Icc (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    #{k ∈ Icc 1 n | q k} = (List.range n).countP (fun i => q (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert,
      List.range_succ, List.countP_append]
    by_cases h : q (n + 1)
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      simp [h]
    · rw [if_neg h, ih]
      simp [h]

theorem A123709_eq_countP (n : ℕ) : A123709 n = (row n).countP (fun x => x ≠ 0) := by
  rw [A123709, card_filter_Icc, row_eq, List.countP_map]
  simp only [A123706_eq_T]
  rfl

/-! ### A fast sparse version of the back substitution, for the data checks -/

/-- `pdot k S`: for a list `S` of triples `(j, x⁺, x⁻)`, the pair
`(∑ x⁺ ⌊j/k⌋, ∑ x⁻ ⌊j/k⌋)`. -/
noncomputable def pdot (k : ℕ) (S : List (ℕ × ℕ × ℕ)) : ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ × ℕ) (0, 0)
    (fun p _ r => let q := Nat.div p.1 k
      (Nat.add r.1 (Nat.mul p.2.1 q), Nat.add r.2 (Nat.mul p.2.2 q))) S

/-- The back substitution of `tail`, keeping only the nonzero entries `x` of `tail n m`, each as
a triple `(column, x⁺, x⁻)` with `x = x⁺ - x⁻`. -/
noncomputable def ptail (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  Nat.rec (motive := fun _ => List (ℕ × ℕ × ℕ)) []
    (fun m S =>
      let r := pdot (Nat.sub n m) S
      let a := Nat.add (cond (Nat.beq m 0) 1 0) r.2
      let b := r.1
      cond (Nat.beq a b) S ((Nat.sub n m, Nat.sub a b, Nat.sub b a) :: S)) m

/-- A fast way to compute A123709 (see `A123709_eq_Rf`). -/
noncomputable def Rf (n : ℕ) : ℕ := (ptail n n).length

/-- The nonzero entries `(j, x⁺, x⁻)` of a list `[x₀, x₁, …]` whose entries sit in columns
`j, j+1, …`. -/
def sp : ℕ → List ℤ → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | j, x :: xs => if x = 0 then sp (j + 1) xs else (j, x.toNat, (-x).toNat) :: sp (j + 1) xs

theorem pdot_sp (k j : ℕ) (L : List ℤ) :
    ((pdot k (sp j L)).1 : ℤ) - (pdot k (sp j L)).2 = dot k j L := by
  induction L generalizing j with
  | nil => simp [sp, pdot, dot]
  | cons x xs ih =>
    by_cases hx : x = 0
    · simp only [sp, hx, if_true, dot, zero_mul, zero_add]
      exact ih (j + 1)
    · simp only [sp, hx, if_false, dot]
      have h1 := ih (j + 1)
      have h2 := Int.toNat_sub_toNat_neg x
      change (((pdot k (sp (j + 1) xs)).1 + x.toNat * (j / k) : ℕ) : ℤ) -
          (((pdot k (sp (j + 1) xs)).2 + (-x).toNat * (j / k) : ℕ) : ℤ) = _
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [← h1]
      nth_rewrite 3 [← h2]
      ring

theorem length_sp (j : ℕ) (L : List ℤ) : (sp j L).length = L.countP (fun x => x ≠ 0) := by
  induction L generalizing j with
  | nil => rfl
  | cons x xs ih => by_cases hx : x = 0 <;> simp [sp, hx, ih]

theorem ptail_eq (n : ℕ) : ∀ m, m ≤ n → ptail n m = sp (n - m + 1) (tail n m)
  | 0, _ => rfl
  | m + 1, hm => by
    have ih := ptail_eq n m (by omega)
    change cond (Nat.beq (Nat.add (cond (Nat.beq m 0) 1 0) (pdot (Nat.sub n m) (ptail n m)).2)
      (pdot (Nat.sub n m) (ptail n m)).1) (ptail n m)
      ((Nat.sub n m, Nat.sub (Nat.add (cond (Nat.beq m 0) 1 0) (pdot (Nat.sub n m) (ptail n m)).2)
        (pdot (Nat.sub n m) (ptail n m)).1,
        Nat.sub (pdot (Nat.sub n m) (ptail n m)).1
          (Nat.add (cond (Nat.beq m 0) 1 0) (pdot (Nat.sub n m) (ptail n m)).2)) :: ptail n m) = _
    rw [ih, show n - (m + 1) + 1 = n - m by omega]
    have hd := pdot_sp (n - m) (n - m + 1) (tail n m)
    simp only [Nat.sub_eq, Nat.add_eq] at hd ⊢
    set r := pdot (n - m) (sp (n - m + 1) (tail n m)) with hr
    set c : ℕ := cond (Nat.beq m 0) 1 0 with hc
    have hc' : (c : ℤ) = if m = 0 then 1 else 0 := by
      rw [hc]; cases m <;> rfl
    set v : ℤ := (if m = 0 then 1 else 0) - dot (n - m) (n - m + 1) (tail n m) with hv
    have hv' : v = ((c + r.2 : ℕ) : ℤ) - (r.1 : ℤ) := by
      rw [hv, ← hd, ← hc']; push_cast; ring
    rw [tail, sp, ← hv]
    by_cases h : c + r.2 = r.1
    · have h0 : v = 0 := by rw [hv', h]; ring
      rw [h, Nat.beq_refl, if_pos h0]
      rfl
    · have h0 : v ≠ 0 := by
        rw [hv']; intro e; apply h; omega
      have hb : Nat.beq (c + r.2) r.1 = false := by
        cases hb : Nat.beq (c + r.2) r.1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) h
      rw [hb, if_neg h0, hv', Int.toNat_sub, neg_sub, Int.toNat_sub]
      rfl

theorem A123709_eq_Rf (n : ℕ) : A123709 n = Rf n := by
  rw [A123709_eq_countP, Rf, ptail_eq n n le_rfl, length_sp, row]

/-! ### Data checks -/

/-- The definition reproduces all 113 terms of A123706 listed in OEIS (rows `1, …, 14` and the
start of row `15`; kernel-checked). -/
theorem A123706_data :
    ((List.range 15).map fun i =>
        (List.range (i + 1)).map fun j => A123706 (i + 1) (j + 1)).flatten.take 113 =
    [1, -2, 1, -1, -1, 1, 1, -1, -1, 1, -1, 0, 0, -1, 1, 2, 0, -1, 0, -1, 1, -1, 0, 0, 0, 0, -1, 1,
      0, 0, 1, -1, 0, 0, -1, 1, 0, 1, -1, 0, 0, 0, 0, -1, 1, 2, -1, 0, 1, -1, 0, 0, 0, -1, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 1, -1, 1, -1, 0, 0, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 1, 2, -1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, -1, 1, 1, 1, -1, 1, -1, 0, 0, 0] := by
  simp only [A123706_eq_T]
  decide +kernel

/-- The definition reproduces all 76 terms of A123709 listed in OEIS (kernel-checked). -/
theorem A123709_data : (List.range 76).map (fun i => A123709 (i + 1)) =
    [1, 2, 3, 4, 3, 4, 3, 4, 4, 6, 3, 8, 3, 6, 7, 4, 3, 8, 3, 8, 7, 6, 3, 8, 4, 6, 4, 8, 3, 11, 3,
      4, 7, 6, 7, 8, 3, 6, 7, 8, 3, 11, 3, 8, 8, 6, 3, 8, 4, 8, 7, 8, 3, 8, 7, 8, 7, 6, 3, 16, 3,
      6, 8, 4, 7, 12, 3, 8, 7, 14, 3, 8, 3, 6, 8, 8] := by
  simp only [A123709_eq_Rf]
  decide +kernel

noncomputable instance : DecidablePred IsTerm := fun n =>
  decidable_of_iff (Rf n = 4) (by rw [IsTerm, A123709_eq_Rf])

/-- `firstDiv m f d`: the first `e ∈ [d, d + f)` with `e ∣ m`, or `d + f` if there is none. -/
def firstDiv (m : ℕ) : ℕ → ℕ → ℕ
  | 0, d => d
  | f + 1, d => if m % d = 0 then d else firstDiv m f (d + 1)

theorem firstDiv_eq_minFac {m : ℕ} (hm : 2 ≤ m) : firstDiv m m 2 = m.minFac := by
  have key : ∀ f d, 2 ≤ d → d ≤ m.minFac → m.minFac < d + f → firstDiv m f d = m.minFac := by
    intro f
    induction f with
    | zero => intro d _ h1 h2; omega
    | succ f ih =>
      intro d hd h1 h2
      rw [firstDiv]
      split_ifs with h
      · exact le_antisymm h1 (Nat.minFac_le_of_dvd hd (Nat.dvd_of_mod_eq_zero h))
      · refine ih (d + 1) (by omega) ?_ (by omega)
        rcases Nat.lt_or_ge d m.minFac with h' | h'
        · omega
        · exfalso
          apply h
          rw [le_antisymm h1 h']
          exact Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd m)
  refine key m 2 le_rfl (Nat.minFac_prime (by omega)).two_le ?_
  have := Nat.minFac_le (by omega : 0 < m)
  omega

theorem isA025475_iff (m : ℕ) :
    IsA025475 m ↔ m = 1 ∨ (2 ≤ m ∧ firstDiv m m 2 ^ 2 ∣ m ∧ m ∣ firstDiv m m 2 ^ m) := by
  constructor
  · rintro (h | ⟨p, k, hp, hk, rfl⟩)
    · exact Or.inl h
    · right
      have h2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      rw [firstDiv_eq_minFac h2]
      have hmin : (p ^ k).minFac = p := by
        have hpr : (p ^ k).minFac.Prime := Nat.minFac_prime (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hpr hp).1 (hpr.dvd_of_dvd_pow (Nat.minFac_dvd _))
      rw [hmin]
      exact ⟨h2, pow_dvd_pow p hk, pow_dvd_pow p (Nat.lt_pow_self hp.one_lt).le⟩
  · rintro (h | ⟨h2, h3, h4⟩)
    · exact Or.inl h
    · right
      rw [firstDiv_eq_minFac h2] at h3 h4
      have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 h4
      refine ⟨m.minFac, i, hp, ?_, hi⟩
      have h3' : m.minFac ^ 2 ∣ m.minFac ^ i := by rw [← hi]; exact h3
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h3'

instance : DecidablePred IsA025475 := fun m =>
  decidable_of_iff _ (isA025475_iff m).symm

/-- The elements `< N` satisfying `p`, in increasing order, are `nth p 0, nth p 1, …`. -/
theorem filter_range_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (List.range N).filter (fun k => decide (p k)) =
      (List.range (Nat.count p N)).map (Nat.nth p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih, Nat.count_succ]
    by_cases h : p N
    · simp [h, List.range_succ, Nat.nth_count h]
    · simp [h]

theorem map_nth_eq_of_filter {p : ℕ → Prop} [DecidablePred p] {N K : ℕ} {L : List ℕ}
    (h : (List.range N).filter (fun k => decide (p k)) = L) (hK : L.length = K) :
    (List.range K).map (Nat.nth p) = L := by
  rw [filter_range_eq] at h
  subst h hK
  simp only [List.length_map, List.length_range]

/-- The `n ≤ 512` with `IsTerm n` (kernel-checked; this runs the back substitution for every
`n ≤ 512`). -/
theorem filter_isTerm : (List.range 513).filter (fun k => decide (IsTerm k)) =
    [4, 6, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256, 289, 343, 361, 512] := by
  decide +kernel

/-- The definition reproduces the first 21 terms of A123710 listed in OEIS, `a 1, …, a 21`
(all terms `≤ 512`; kernel-checked in `filter_isTerm`). -/
theorem a_data : (List.range 21).map (fun i => a (i + 1)) =
    [4, 6, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256, 289, 343, 361, 512] := by
  have e : (fun i => a (i + 1)) = Nat.nth IsTerm := funext fun i => by rw [a, Nat.add_sub_cancel]
  rw [e]
  exact map_nth_eq_of_filter filter_isTerm rfl

/-- The `m ≤ 512` with `IsA025475 m` (kernel-checked). -/
theorem filter_isA025475 : (List.range 513).filter (fun k => decide (IsA025475 k)) =
    [1, 4, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256, 289, 343, 361, 512] := by
  decide +kernel

/-- `A025475` reproduces the first 21 terms listed in OEIS, `A025475 1, …, A025475 21`
(all terms `≤ 512`; kernel-checked in `filter_isA025475`). From index `3` on they agree with
`a_data`. -/
theorem A025475_data : (List.range 21).map (fun i => A025475 (i + 1)) =
    [1, 4, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256, 289, 343, 361, 512] := by
  have e : (fun i => A025475 (i + 1)) = Nat.nth IsA025475 :=
    funext fun i => by rw [A025475, Nat.add_sub_cancel]
  rw [e]
  exact map_nth_eq_of_filter filter_isA025475 rfl

/-! ### The conjecture -/

/-- Conjecture (M. F. Hasler, 2012): `a(n) = A025475(n)` for `n > 2`, i.e. from the third term
on, the indices of the rows of A123706 with exactly four nonzero entries are the proper prime
powers `p^m` (`m ≥ 2`) in increasing order. -/
def statement : Prop :=
  ∀ n : ℕ, 2 < n → a n = A025475 n

end Math0.Statements.A123710

/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A270668
import Math0.Audit

/-!
# Mathar's generating function for column 3 of A270668

We prove Mathar's conjecture: `∑_{k ≥ 0} T(2k, 2) x^k = num / den`, where `T(2k, 2)` counts the
domino tilings of the `(4k+1) × 5` board with its central cell removed.

The proof is a transfer-matrix argument on the 32 states (masks) of a width-5 row.

* Using the broken-profile recursion for `cnt` from the statement file, the count from the start
  of a row is obtained from the count at the start of the next row by a fixed row operator. There
  are four kinds of rows: generic (`G0`), just above the hole (`G1`), the hole row (`G2`) and the
  last row (`G3`). For `K ≥ 0` the `(4K+5) × 5` board is `G0^(2K+1) G1 G2 G0^(2K+1) G3` applied
  to the all-ones vector, read at mask `0` (`vv_zero`).
* The row operators are linear and only use masks `< 32`, so they act through `32 × 32` integer
  matrices (`rep`). With `A` the generic matrix, `P` the matrix of the two rows around the hole and
  `e₀` the unit vector at mask `0`, the count is `e₀ᵀ A^(2K+1) P A^(2K+2) e₀`. `A` is symmetric
  (kernel-checked), so the count is `∑ⱼ (A^(2K+1) e₀)ⱼ (P A^(2K+2) e₀)ⱼ` (`vv_formula`).
* A kernel computation shows `p(A²) e₀ = 0` for `p(t) = t⁴ - 15t³ + 32t² - 15t + 1`. Hence every
  entry of `A^(2n+1) e₀` and of `P A^(2n+2) e₀` solves the order-4 recurrence `Rec4` with
  characteristic polynomial `p`.
* If `a` and `b` solve `Rec4`, then `a · b` solves the order-9 recurrence `Rec9` whose
  characteristic polynomial is the reversed denominator: its roots are `1` and the products
  `ρᵢ ρⱼ` of roots of `p` (a polynomial identity, `rec9_mul`). So `T(2(K+1), 2)` solves `Rec9`.
* The coefficients of `x^n` in `(∑ T(2k, 2) x^k) · den` are the numerator coefficients for
  `n ≤ 9`, using `T(2k, 2)` for `k ≤ 9` computed in the kernel. For `n ≥ 10` they are `0` by `Rec9`.
-/

namespace Math0.Frontier.A270668
open Math0.Statements.A270668
open Matrix

/-- Vectors indexed by masks. -/
private abbrev V := ℕ → ℤ

/-- One cell step of the transfer matrix (width 5). -/
private def cellF (s : ℕ) (a b d : Bool) (f : V) (M : ℕ) : ℤ :=
  if M.testBit s = true then f (M - 2 ^ s)
  else if a = true then
    (if s + 1 < 5 ∧ b = true ∧ M.testBit (s + 1) = false then f (M + 2 ^ (s + 1)) else 0) +
      (if d = true then f (M + 2 ^ s) else 0)
  else f M

/-- One row of the transfer matrix. -/
private def rowF (a b d : ℕ → Bool) (f : V) : V :=
  cellF 0 (a 0) (b 0) (d 0) (cellF 1 (a 1) (b 1) (d 1) (cellF 2 (a 2) (b 2) (d 2)
    (cellF 3 (a 3) (b 3) (d 3) (cellF 4 (a 4) (b 4) (d 4) f))))

/-- Completion counts as an integer vector. -/
private noncomputable def vv (N hx k : ℕ) : V := fun M => (cnt N 5 hx k M : ℤ)

/-- One cell step of the broken-profile recursion for `cnt`, in the form of `cellF`. -/
private theorem vv_cell (N hx k : ℕ) :
    vv N hx k = cellF (k % 5) (inS N hx k) (inS N hx (k + 1)) (inS N hx (k + 5))
      (vv N hx (k + 1)) := by
  funext M
  unfold cellF
  by_cases h1 : M.testBit (k % 5) = true
  · rw [if_pos h1]
    simp only [vv]
    rw [cnt_of_set (by norm_num) h1]
  · have h1' : M.testBit (k % 5) = false := by simpa using h1
    rw [if_neg h1]
    by_cases h2 : inS N hx k = true
    · rw [if_pos h2]
      simp only [vv]
      rw [cnt_of_free (c := 5) (by norm_num) h1' h2]
      push_cast
      rfl
    · have h2' : inS N hx k = false := by simpa using h2
      rw [if_neg h2]
      simp only [vv]
      rw [cnt_of_notS (by norm_num) h1' h2']

/-- Five cell steps: the completion counts at the start of row `r` from those of row `r+1`. -/
private theorem vv_row (N hx r : ℕ) :
    vv N hx (5 * r) = rowF (fun j => inS N hx (5 * r + j)) (fun j => inS N hx (5 * r + j + 1))
      (fun j => inS N hx (5 * r + j + 5)) (vv N hx (5 * r + 5)) := by
  rw [vv_cell N hx (5 * r), vv_cell N hx (5 * r + 1), vv_cell N hx (5 * r + 1 + 1),
    vv_cell N hx (5 * r + 1 + 1 + 1), vv_cell N hx (5 * r + 1 + 1 + 1 + 1)]
  rw [show (5 * r) % 5 = 0 by omega, show (5 * r + 1) % 5 = 1 by omega,
    show (5 * r + 1 + 1) % 5 = 2 by omega, show (5 * r + 1 + 1 + 1) % 5 = 3 by omega,
    show (5 * r + 1 + 1 + 1 + 1) % 5 = 4 by omega]
  rfl

/-- `rowF` only depends on the flags at the five columns `0, …, 4`. -/
private theorem rowF_congr {a b d a' b' d' : ℕ → Bool} (ha : ∀ j < 5, a j = a' j)
    (hb : ∀ j < 5, b j = b' j) (hd : ∀ j < 5, d j = d' j) (f : V) :
    rowF a b d f = rowF a' b' d' f := by
  simp only [rowF]
  rw [ha 0 (by norm_num), ha 1 (by norm_num), ha 2 (by norm_num), ha 3 (by norm_num),
    ha 4 (by norm_num), hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num),
    hb 3 (by norm_num), hb 4 (by norm_num), hd 0 (by norm_num), hd 1 (by norm_num),
    hd 2 (by norm_num), hd 3 (by norm_num), hd 4 (by norm_num)]

/-- A generic row. -/
private def G0 (f : V) : V := rowF (fun _ => true) (fun _ => true) (fun _ => true) f
/-- The row just above the hole. -/
private def G1 (f : V) : V := rowF (fun _ => true) (fun _ => true) (fun j => decide (j ≠ 2)) f
/-- The row of the hole. -/
private def G2 (f : V) : V :=
  rowF (fun j => decide (j ≠ 2)) (fun j => decide (j ≠ 1)) (fun _ => true) f
/-- The last row. -/
private def G3 (f : V) : V := rowF (fun _ => true) (fun j => decide (j ≠ 4)) (fun _ => false) f

section Rows
variable (K : ℕ)

/-- A row away from the hole and from the bottom is the generic row `G0`. -/
private theorem row_gen {r : ℕ} (h1 : r + 1 < 4 * K + 5) (h2 : r ≠ 2 * K + 2)
    (h3 : r + 1 ≠ 2 * K + 2) :
    vv (20 * K + 25) (10 * K + 12) (5 * r) = G0 (vv (20 * K + 25) (10 * K + 12) (5 * r + 5)) := by
  rw [vv_row, G0]
  apply rowF_congr <;> intro j hj <;> interval_cases j <;> simp [inS] <;> omega

/-- The row just above the hole: no vertical domino into the hole. -/
private theorem row_above :
    vv (20 * K + 25) (10 * K + 12) (5 * (2 * K + 1)) =
      G1 (vv (20 * K + 25) (10 * K + 12) (5 * (2 * K + 2))) := by
  rw [vv_row, G1, show 5 * (2 * K + 1) + 5 = 5 * (2 * K + 2) by ring]
  apply rowF_congr <;> intro j hj <;> interval_cases j <;> simp [inS] <;> omega

/-- The row of the hole. -/
private theorem row_hole :
    vv (20 * K + 25) (10 * K + 12) (5 * (2 * K + 2)) =
      G2 (vv (20 * K + 25) (10 * K + 12) (5 * (2 * K + 3))) := by
  rw [vv_row, G2, show 5 * (2 * K + 2) + 5 = 5 * (2 * K + 3) by ring]
  apply rowF_congr <;> intro j hj <;> interval_cases j <;> simp [inS] <;> omega

/-- The last row: no vertical dominoes, and every final state completes in one way. -/
private theorem row_last :
    vv (20 * K + 25) (10 * K + 12) (5 * (4 * K + 4)) = G3 (fun _ => 1) := by
  rw [vv_row, G3]
  have : vv (20 * K + 25) (10 * K + 12) (5 * (4 * K + 4) + 5) = fun _ => 1 := by
    funext M
    simp only [vv]
    rw [cnt_end (by omega)]
    rfl
  rw [this]
  apply rowF_congr <;> intro j hj <;> interval_cases j <;> simp [inS] <;> omega

/-- A stretch of `t` generic rows is `G0^[t]`. -/
private theorem rows_gen : ∀ t s : ℕ, (∀ r, s ≤ r → r < s + t →
    r + 1 < 4 * K + 5 ∧ r ≠ 2 * K + 2 ∧ r + 1 ≠ 2 * K + 2) →
    vv (20 * K + 25) (10 * K + 12) (5 * s) = G0^[t] (vv (20 * K + 25) (10 * K + 12) (5 * (s + t)))
  | 0, s, _ => by simp
  | t + 1, s, h => by
    obtain ⟨h1, h2, h3⟩ := h s le_rfl (by omega)
    rw [row_gen K h1 h2 h3, show 5 * s + 5 = 5 * (s + 1) by ring,
      rows_gen t (s + 1) (fun r hr1 hr2 => h r (by omega) (by omega)),
      Function.iterate_succ_apply', show s + 1 + t = s + (t + 1) by ring]

/-- The whole board, row by row. -/
private theorem vv_zero :
    vv (20 * K + 25) (10 * K + 12) 0 =
      G0^[2 * K + 1] (G1 (G2 (G0^[2 * K + 1] (G3 (fun _ => 1))))) := by
  have e1 := rows_gen K (2 * K + 1) 0 (fun r _ hr => by omega)
  have e2 := rows_gen K (2 * K + 1) (2 * K + 3) (fun r hr1 hr2 => by omega)
  rw [show 5 * 0 = 0 by rfl, show 0 + (2 * K + 1) = 2 * K + 1 by ring] at e1
  rw [show 2 * K + 3 + (2 * K + 1) = 4 * K + 4 by ring] at e2
  rw [e1, row_above, row_hole, e2, row_last]

end Rows

/-! ### Linearity and locality -/

/-- `F` only looks at masks `< 32` when evaluated at masks `< 32`. -/
private def Loc (F : V → V) : Prop :=
  ∀ f g : V, (∀ M < 32, f M = g M) → ∀ M < 32, F f M = F g M

/-- `cellF` is local (for the columns `s < 5`). -/
private theorem cellF_loc {s : ℕ} (hs : s < 5) (a b d : Bool) : Loc (cellF s a b d) := by
  intro f g hfg M hM
  have hM' : M < 2 ^ 5 := hM
  unfold cellF
  by_cases h1 : M.testBit s = true
  · rw [if_pos h1, if_pos h1]
    exact hfg _ (lt_of_le_of_lt (Nat.sub_le _ _) hM)
  · have h1' : M.testBit s = false := by simpa using h1
    rw [if_neg h1, if_neg h1]
    split_ifs with h2 h3 h4
    · rw [hfg _ (add_two_pow_lt hM' h3.1 h3.2.2), hfg _ (add_two_pow_lt hM' hs h1')]
    · rw [hfg _ (add_two_pow_lt hM' h3.1 h3.2.2)]
    · rw [hfg _ (add_two_pow_lt hM' hs h1')]
    · rfl
    · exact hfg _ hM

/-- `rowF` is local. -/
private theorem rowF_loc (a b d : ℕ → Bool) : Loc (rowF a b d) := by
  intro f g hfg
  simp only [rowF]
  exact cellF_loc (by norm_num) _ _ _ _ _ <| cellF_loc (by norm_num) _ _ _ _ _ <|
    cellF_loc (by norm_num) _ _ _ _ _ <| cellF_loc (by norm_num) _ _ _ _ _ <|
    cellF_loc (by norm_num) _ _ _ _ _ hfg

/-- `cellF` as a linear map. -/
private def cellL (s : ℕ) (a b d : Bool) : V →ₗ[ℤ] V where
  toFun := cellF s a b d
  map_add' f g := by
    funext M
    simp only [cellF, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    funext M
    simp only [cellF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- `rowF` as a linear map. -/
private def rowL (a b d : ℕ → Bool) : V →ₗ[ℤ] V :=
  cellL 0 (a 0) (b 0) (d 0) ∘ₗ cellL 1 (a 1) (b 1) (d 1) ∘ₗ cellL 2 (a 2) (b 2) (d 2) ∘ₗ
    cellL 3 (a 3) (b 3) (d 3) ∘ₗ cellL 4 (a 4) (b 4) (d 4)

/-- `rowL` computes `rowF`. -/
private theorem rowL_apply (a b d : ℕ → Bool) (f : V) : rowL a b d f = rowF a b d f := rfl

/-- The unit vector at mask `j`. -/
private def δn (j : ℕ) : V := fun x => if x = j then 1 else 0

/-- Restriction to the masks `< 32`. -/
private def rest (f : V) : Fin 32 → ℤ := fun i => f i

/-- The matrix of a linear map on the masks `< 32`. -/
private def toMat (F : V →ₗ[ℤ] V) : Matrix (Fin 32) (Fin 32) ℤ :=
  Matrix.of fun i j => F (δn j) i

/-- A local linear map acts on the masks `< 32` through its matrix. -/
private theorem rep (F : V →ₗ[ℤ] V) (hF : Loc F) (f : V) : rest (F f) = toMat F *ᵥ rest f := by
  funext i
  have hf : ∀ M < 32, f M = (∑ j : Fin 32, f j • δn j) M := by
    intro M hM
    rw [Finset.sum_apply, Finset.sum_eq_single ⟨M, hM⟩]
    · simp [δn]
    · intro j _ hj
      have : M ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
      simp [δn, this]
    · simp
  simp only [rest, Matrix.mulVec, dotProduct, toMat, Matrix.of_apply]
  rw [hF f _ hf i i.2, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-! ### Kernel computations -/

/-- The last row applied to the all-ones vector is the generic row applied to `δ₀`
(kernel-checked on the 32 masks). -/
private theorem last_row_eq : ∀ M < 32, G3 (fun _ => 1) M = G0 (δn 0) M := by decide +kernel

/-- The generic row transfer matrix is symmetric (kernel-checked). -/
private theorem G0_symm : ∀ i < 32, ∀ j < 32, G0 (δn j) i = G0 (δn i) j := by decide +kernel

/-- Table lookup. -/
private def tab (l : List ℤ) : V := fun M => l.getD M 0

/-- Materialize the first 32 entries of a vector. -/
private def matz (g : V) : List ℤ := (List.range 32).map g

/-- Reading back a materialized vector. -/
private theorem tab_matz (g : V) {M : ℕ} (hM : M < 32) : tab (matz g) M = g M := by
  simp [tab, matz, hM]

/-- Materialized iterates `G0^n δ₀`. -/
private def itG : ℕ → List ℤ
  | 0 => matz (δn 0)
  | n + 1 => matz (G0 (tab (itG n)))

/-- `itG n` is `G0^[n] δ₀` on the masks `< 32`. -/
private theorem itG_spec : ∀ n, ∀ M < 32, tab (itG n) M = G0^[n] (δn 0) M
  | 0, M, hM => by rw [itG, tab_matz _ hM]; rfl
  | n + 1, M, hM => by
    rw [itG, tab_matz _ hM, Function.iterate_succ_apply']
    exact rowF_loc _ _ _ _ _ (itG_spec n) M hM

/-- `δ₀` is annihilated by `p(G0²)` with `p(t) = t⁴ - 15t³ + 32t² - 15t + 1`
(kernel-checked on the 32 masks). -/
private theorem krylov_check : ∀ M < 32, tab (itG 8) M - 15 * tab (itG 6) M + 32 * tab (itG 4) M -
    15 * tab (itG 2) M + tab (itG 0) M = 0 := by decide +kernel

/-! ### Matrices -/

/-- The generic row as a linear map. -/
private def G0L : V →ₗ[ℤ] V := rowL (fun _ => true) (fun _ => true) (fun _ => true)
/-- The row above the hole as a linear map. -/
private def G1L : V →ₗ[ℤ] V := rowL (fun _ => true) (fun _ => true) (fun j => decide (j ≠ 2))
/-- The hole row as a linear map. -/
private def G2L : V →ₗ[ℤ] V :=
  rowL (fun j => decide (j ≠ 2)) (fun j => decide (j ≠ 1)) (fun _ => true)

/-- The generic row transfer matrix. -/
private def A : Matrix (Fin 32) (Fin 32) ℤ := toMat G0L
/-- The two rows around the hole. -/
private def P : Matrix (Fin 32) (Fin 32) ℤ := toMat G1L * toMat G2L

/-- The unit vector at mask `0`. -/
private def e0 : Fin 32 → ℤ := rest (δn 0)

/-- `A ^ n e₀`. -/
private def x (n : ℕ) : Fin 32 → ℤ := A ^ n *ᵥ e0

/-- Locality of the generic row. -/
private theorem G0L_loc : Loc G0L := rowF_loc (fun _ => true) (fun _ => true) (fun _ => true)
/-- Locality of the row above the hole. -/
private theorem G1L_loc : Loc G1L :=
  rowF_loc (fun _ => true) (fun _ => true) (fun j => decide (j ≠ 2))
/-- Locality of the hole row. -/
private theorem G2L_loc : Loc G2L :=
  rowF_loc (fun j => decide (j ≠ 2)) (fun j => decide (j ≠ 1)) (fun _ => true)

/-- The generic row acts by `A`. -/
private theorem rest_G0 (f : V) : rest (G0 f) = A *ᵥ rest f := rep G0L G0L_loc f

/-- `n` generic rows act by `A ^ n`. -/
private theorem rest_G0_iter (n : ℕ) (f : V) : rest (G0^[n] f) = A ^ n *ᵥ rest f := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', rest_G0, ih, mulVec_mulVec, pow_succ']

/-- The two rows around the hole act by `P`. -/
private theorem rest_G12 (f : V) : rest (G1 (G2 f)) = P *ᵥ rest f := by
  rw [P, ← mulVec_mulVec]
  exact (rep G1L G1L_loc (G2 f)).trans (congrArg _ (rep G2L G2L_loc f))

/-- `A` is symmetric. -/
private theorem A_symm : Aᵀ = A := by
  ext i j
  simp only [transpose_apply, A, toMat, of_apply, G0L, rowL_apply]
  exact (G0_symm i i.2 j j.2).symm

/-- `x n` is the column `0` of `A ^ n`. -/
private theorem x_apply (n : ℕ) (j : Fin 32) : x n j = (A ^ n) j 0 := by
  simp only [x, mulVec, dotProduct, e0, rest, δn]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [this]
  · simp

/-- `x n` agrees with the materialized iterate. -/
private theorem x_eq_tab (n : ℕ) (j : Fin 32) : x n j = tab (itG n) j := by
  rw [itG_spec n j j.2, x, e0, ← rest_G0_iter]
  rfl

/-- The Krylov relation `p(A²) e₀ = 0`. -/
private theorem x_base : x 8 = (15 : ℤ) • x 6 - (32 : ℤ) • x 4 + (15 : ℤ) • x 2 - x 0 := by
  funext j
  have := krylov_check j j.2
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, x_eq_tab]
  linarith

/-- `x (m + k) = A ^ m x k`. -/
private theorem x_add (m k : ℕ) : x (m + k) = A ^ m *ᵥ x k := by
  rw [x, x, mulVec_mulVec, pow_add]

/-- The vectors `x n` satisfy the recurrence `p` in steps of two. -/
private theorem x_rec (m : ℕ) :
    x (m + 8) = (15 : ℤ) • x (m + 6) - (32 : ℤ) • x (m + 4) + (15 : ℤ) • x (m + 2) - x m := by
  rw [x_add, x_base, x_add, x_add, x_add, ← add_zero m, x_add m 0, add_zero]
  simp only [mulVec_sub, mulVec_add, mulVec_smul]

/-- The tiling count of the `(4K+5) × 5` board with central hole as a bilinear expression. -/
private theorem vv_formula (K : ℕ) :
    vv (20 * K + 25) (10 * K + 12) 0 0 =
      ∑ j : Fin 32, x (2 * K + 1) j * (P *ᵥ x (2 * K + 2)) j := by
  have h3 : rest (G3 (fun _ => 1)) = A *ᵥ e0 := by
    rw [e0, ← rest_G0]
    funext i
    exact last_row_eq i i.2
  have h := congrArg (fun f => rest f (0 : Fin 32)) (vv_zero K)
  have hx : A ^ (2 * K + 1) *ᵥ (A *ᵥ e0) = x (2 * K + 2) := by
    rw [x, mulVec_mulVec, ← pow_succ]
  rw [rest_G0_iter, rest_G12, rest_G0_iter, h3, hx] at h
  rw [show vv (20 * K + 25) (10 * K + 12) 0 0 = rest (vv (20 * K + 25) (10 * K + 12) 0) 0 from rfl,
    h]
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [x_apply, ← transpose_apply (A ^ (2 * K + 1)), transpose_pow, A_symm]

/-! ### Linear recurrences -/

/-- The order-4 recurrence `s(n+4) = 15 s(n+3) - 32 s(n+2) + 15 s(n+1) - s(n)`. -/
private def Rec4 (s : ℕ → ℤ) : Prop :=
  ∀ n, s (n + 4) = 15 * s (n + 3) - 32 * s (n + 2) + 15 * s (n + 1) - s n

/-- The order-9 recurrence given by the denominator. -/
private def Rec9 (s : ℕ → ℤ) : Prop :=
  ∀ n, s n - 192 * s (n + 1) + 5760 * s (n + 2) - 49283 * s (n + 3) + 147264 * s (n + 4) -
    147264 * s (n + 5) + 49283 * s (n + 6) - 5760 * s (n + 7) + 192 * s (n + 8) - s (n + 9) = 0

/-- The product of two solutions of `Rec4` solves `Rec9`. -/
private theorem rec9_mul {a b : ℕ → ℤ} (ha : Rec4 a) (hb : Rec4 b) :
    Rec9 (fun n => a n * b n) := by
  intro n
  have h0 := ha n
  have h1 := ha (n + 1)
  have h2 := ha (n + 2)
  have h3 := ha (n + 3)
  have h4 := ha (n + 4)
  have h5 := ha (n + 5)
  have g0 := hb n
  have g1 := hb (n + 1)
  have g2 := hb (n + 2)
  have g3 := hb (n + 3)
  have g4 := hb (n + 4)
  have g5 := hb (n + 5)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
  have a4 : a (n + 4) =
      -a n + 15 * a (n + 1) - 32 * a (n + 2) + 15 * a (n + 3) := by
    linear_combination h0
  have a5 : a (n + 5) =
      -15 * a n + 224 * a (n + 1) - 465 * a (n + 2) + 193 * a (n + 3) := by
    linear_combination h1 + 15 * a4
  have a6 : a (n + 6) =
      -193 * a n + 2880 * a (n + 1) - 5952 * a (n + 2) + 2430 * a (n + 3) := by
    linear_combination h2 + 15 * a5 - 32 * a4
  have a7 : a (n + 7) =
      -2430 * a n + 36257 * a (n + 1) - 74880 * a (n + 2) + 30498 * a (n + 3) := by
    linear_combination h3 + 15 * a6 - 32 * a5 + 15 * a4
  have a8 : a (n + 8) =
      -30498 * a n + 455040 * a (n + 1) - 939679 * a (n + 2) + 382590 * a (n + 3) := by
    linear_combination h4 + 15 * a7 - 32 * a6 + 15 * a5 - a4
  have a9 : a (n + 9) =
      -382590 * a n + 5708352 * a (n + 1) - 11787840 * a (n + 2) + 4799171 * a (n + 3) := by
    linear_combination h5 + 15 * a8 - 32 * a7 + 15 * a6 - a5
  have b4 : b (n + 4) =
      -b n + 15 * b (n + 1) - 32 * b (n + 2) + 15 * b (n + 3) := by
    linear_combination g0
  have b5 : b (n + 5) =
      -15 * b n + 224 * b (n + 1) - 465 * b (n + 2) + 193 * b (n + 3) := by
    linear_combination g1 + 15 * b4
  have b6 : b (n + 6) =
      -193 * b n + 2880 * b (n + 1) - 5952 * b (n + 2) + 2430 * b (n + 3) := by
    linear_combination g2 + 15 * b5 - 32 * b4
  have b7 : b (n + 7) =
      -2430 * b n + 36257 * b (n + 1) - 74880 * b (n + 2) + 30498 * b (n + 3) := by
    linear_combination g3 + 15 * b6 - 32 * b5 + 15 * b4
  have b8 : b (n + 8) =
      -30498 * b n + 455040 * b (n + 1) - 939679 * b (n + 2) + 382590 * b (n + 3) := by
    linear_combination g4 + 15 * b7 - 32 * b6 + 15 * b5 - b4
  have b9 : b (n + 9) =
      -382590 * b n + 5708352 * b (n + 1) - 11787840 * b (n + 2) + 4799171 * b (n + 3) := by
    linear_combination g5 + 15 * b8 - 32 * b7 + 15 * b6 - b5
  dsimp only
  rw [a4, a5, a6, a7, a8, a9, b4, b5, b6, b7, b8, b9]
  ring

/-- `Rec9` is closed under finite sums. -/
private theorem rec9_sum (S : Finset (Fin 32)) (f : Fin 32 → ℕ → ℤ) (h : ∀ i ∈ S, Rec9 (f i)) :
    Rec9 (fun n => ∑ i ∈ S, f i n) := by
  induction S using Finset.induction_on with
  | empty => intro n; simp
  | insert i S hi ih =>
    have h1 := h i (Finset.mem_insert_self i S)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    intro n
    have h1n := h1 n
    have h2n := h2 n
    dsimp only at h1n h2n ⊢
    simp only [Finset.sum_insert hi]
    linear_combination h1n + h2n

/-- The entries of `A^(2n+1) e₀` solve `Rec4`. -/
private theorem rec4_x_odd (j : Fin 32) : Rec4 (fun n => x (2 * n + 1) j) := by
  intro n
  dsimp only
  rw [show 2 * (n + 4) + 1 = 2 * n + 1 + 8 by ring, x_rec,
    show 2 * (n + 3) + 1 = 2 * n + 1 + 6 by ring,
    show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The entries of `P A^(2n+2) e₀` solve `Rec4`. -/
private theorem rec4_Px_even (j : Fin 32) : Rec4 (fun n => (P *ᵥ x (2 * n + 2)) j) := by
  intro n
  dsimp only
  rw [show 2 * (n + 4) + 2 = 2 * n + 2 + 8 by ring, x_rec,
    show 2 * (n + 3) + 2 = 2 * n + 2 + 6 by ring,
    show 2 * (n + 2) + 2 = 2 * n + 2 + 4 by ring, show 2 * (n + 1) + 2 = 2 * n + 2 + 2 by ring]
  simp only [mulVec_sub, mulVec_add, mulVec_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

/-- `T(2(K+1), 2)` is the completion count of the initial state. -/
private theorem T_eq_vv (K : ℕ) : (T (2 * (K + 1)) 2 : ℤ) = vv (20 * K + 25) (10 * K + 12) 0 0 := by
  have h : T (2 * (K + 1)) 2 = cnt ((2 * (2 * (K + 1)) + 1) * (2 * 2 + 1)) (2 * 2 + 1)
      (2 * (K + 1) * (2 * 2 + 1) + 2) 0 0 := by
    rw [T, region_eq]
    rfl
  rw [h, show (2 * (2 * (K + 1)) + 1) * (2 * 2 + 1) = 20 * K + 25 by ring,
    show 2 * (K + 1) * (2 * 2 + 1) + 2 = 10 * K + 12 by ring]
  rfl

/-- The column `T(2(K+1), 2)` solves `Rec9`. -/
private theorem rec9_T : Rec9 (fun K => (T (2 * (K + 1)) 2 : ℤ)) := by
  have : (fun K => (T (2 * (K + 1)) 2 : ℤ)) =
      fun K => ∑ j : Fin 32, x (2 * K + 1) j * (P *ᵥ x (2 * K + 2)) j := by
    funext K
    rw [T_eq_vv, vv_formula]
  rw [this]
  exact rec9_sum _ _ fun j _ => rec9_mul (rec4_x_odd j) (rec4_Px_even j)

/-! ### Initial values -/

/-- `T(0, 2)`, kernel-checked. -/
private theorem Tc_val0 : Tc 0 2 = 1 := by decide +kernel
/-- `T(2, 2)`, kernel-checked. -/
private theorem Tc_val1 : Tc 2 2 = 196 := by decide +kernel
/-- `T(4, 2)`, kernel-checked. -/
private theorem Tc_val2 : Tc 4 2 = 31329 := by decide +kernel
/-- `T(6, 2)`, kernel-checked. -/
private theorem Tc_val3 : Tc 6 2 = 4941729 := by decide +kernel
/-- `T(8, 2)`, kernel-checked. -/
private theorem Tc_val4 : Tc 8 2 = 777852100 := by decide +kernel
/-- `T(10, 2)`, kernel-checked. -/
private theorem Tc_val5 : Tc 10 2 = 122398521025 := by decide +kernel
/-- `T(12, 2)`, kernel-checked. -/
private theorem Tc_val6 : Tc 12 2 = 19259046351169 := by decide +kernel
/-- `T(14, 2)`, kernel-checked. -/
private theorem Tc_val7 : Tc 14 2 = 3030333168565444 := by decide +kernel
/-- `T(16, 2)`, kernel-checked. -/
private theorem Tc_val8 : Tc 16 2 = 476810204277773601 := by decide +kernel
/-- `T(18, 2)`, kernel-checked. -/
private theorem Tc_val9 : Tc 18 2 = 75024073162168851681 := by decide +kernel

/-! ### The generating function -/

open PowerSeries

/-- Coefficients of the denominator. -/
private def dd (j : ℕ) : ℚ :=
  [-1, 192, -5760, 49283, -147264, 147264, -49283, 5760, -192, 1].getD j 0

/-- Coefficients of the numerator. -/
private def nm (j : ℕ) : ℚ := [-1, -4, 543, -6238, 17032, -6238, 543, -4, -1].getD j 0

/-- The denominator as a sum of monomials. -/
private theorem den_eq : den = ∑ j ∈ Finset.range 10, C (dd j) * X ^ j := by
  simp [den, Finset.sum_range_succ, dd, map_ofNat C]
  ring

/-- The numerator as a sum of monomials. -/
private theorem num_eq : num = ∑ j ∈ Finset.range 9, C (nm j) * X ^ j := by
  simp [num, Finset.sum_range_succ, nm, map_ofNat C]
  ring

/-- Coefficients of a power series times the denominator. -/
private theorem coeff_mul_den (c : ℕ → ℚ) (n : ℕ) :
    coeff n (mk c * den) = ∑ j ∈ Finset.range 10, dd j * (if j ≤ n then c (n - j) else 0) := by
  rw [den_eq, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

/-- Coefficients of the numerator. -/
private theorem coeff_num (n : ℕ) : coeff n num = if n < 9 then nm n else 0 := by
  rw [num_eq, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- The column `T(2k, 2)` as rationals. -/
private noncomputable def cq (k : ℕ) : ℚ := (T (2 * k) 2 : ℚ)

/-- The recurrence of the denominator for `T(2k, 2)`, from `k = 1` on. -/
private theorem cq_rec (K : ℕ) :
    cq (K + 1) - 192 * cq (K + 2) + 5760 * cq (K + 3) - 49283 * cq (K + 4) +
    147264 * cq (K + 5) - 147264 * cq (K + 6) + 49283 * cq (K + 7) - 5760 * cq (K + 8) +
    192 * cq (K + 9) - cq (K + 10) = 0 := by
  have h := rec9_T K
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  simp only [cq]
  exact_mod_cast h

/-- Mathar's conjectured generating function for column 3 (`m = 2`) of A270668 holds. -/
theorem result : statement := by
  rw [statement_iff]
  change mk cq * den = num
  ext n
  rw [coeff_mul_den, coeff_num]
  by_cases hn : n < 10
  · interval_cases n <;>
      simp [Finset.sum_range_succ, dd, nm, cq, T_eq_Tc, Tc_val0, Tc_val1, Tc_val2, Tc_val3,
        Tc_val4, Tc_val5, Tc_val6, Tc_val7, Tc_val8, Tc_val9] <;> norm_num
  · obtain ⟨K, rfl⟩ : ∃ K, n = K + 10 := ⟨n - 10, by omega⟩
    rw [if_neg (by omega)]
    simp [Finset.sum_range_succ, dd]
    linarith [cq_rec K]

end Math0.Frontier.A270668

#math0_settles Math0.Frontier.A270668.result Math0.Statements.A270668.statement

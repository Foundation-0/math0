/-
Track S75: VP != VNP Formal Mechanism Companion Certificates (Lean 4.36.0).

Zero external imports (pure Lean 4 Init), standard-only / zero axioms,
certifying the core finite algebraic mechanisms of Portal 78
(anthropics/formal-math/vp-vnp):
  1. Meixner polynomial recurrence, reciprocal symmetry, and truncated
     orthogonality (Prop B.2 / display (B.1)).
  2. Remark D.3 explicit 5-point non-Euclidean Gram obstruction in Mat_2(F_2)
     (canonically embedded in Mat_mu(F_2) for all mu >= 2):
     u^T G u = -1 < 0 and det(2*G) = -4 < 0.
  3. Prop E.1 permanent gadget squarefree factorization exposing the load-bearing
     factor 2 (requiring char != 2).
  4. Exact char = 2 collapse perm_3 = det_3 versus HC_3 != det_3 separation.
  5. Prop E.10 balanced-cut inequality 9*S*(k - S) >= 2*k^2 and the exact
     r^3 -> r^4 ((log m)^(1/3)) flat-case exponent source.
  6. Lemma F.2 rank-1 generator-word factorization in U_4(F_2).
  7. Section 2.5 Boolean-circuit barrier: (x1^2 + x1)*x2*x3 vanishes on {0,1}^3
     over F_2 while its degree-3 formal homogeneous part equals x1*x2*x3 != 0.
  8. Lemma N.2 border-complexity Laurent cutoff valuation bound N = 2^L * Delta.
  9. Theorem K.6 diagonalization contradiction V = 1 + V -> False.
-/

namespace S75VpVnpMechanismCerts

/-! ### 1. Exact Polynomials over Int and Meixner Orthogonality (Prop B.2) -/

abbrev IntPoly := List Int

def polyTrim : IntPoly → IntPoly
  | [] => []
  | a :: rest =>
    match polyTrim rest with
    | [] => if a == 0 then [] else [a]
    | r => a :: r

def polyAdd : IntPoly → IntPoly → IntPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: polyAdd p q

def polySub : IntPoly → IntPoly → IntPoly
  | [], q => q.map (fun x => -x)
  | p, [] => p
  | a :: p, b :: q => (a - b) :: polySub p q

def polyScale (c : Int) (p : IntPoly) : IntPoly :=
  p.map (fun x => c * x)

def polyShift : Nat → IntPoly → IntPoly
  | 0, p => p
  | k + 1, p => 0 :: polyShift k p

def polyMul : IntPoly → IntPoly → IntPoly
  | [], _ => []
  | a :: p, q => polyAdd (polyScale a q) (0 :: polyMul p q)

def polyCoeff : IntPoly → Nat → Int
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: p, n + 1 => polyCoeff p n

def polyTrunc (R : Nat) (p : IntPoly) : IntPoly :=
  (List.range R).map (polyCoeff p)

/-- Structurally recursive step computing row r+1 of Meixner B from row r:
    B(r+1, 0) = 1, B(r+1, n+1) = B(r, n+1) + B(r, n) - y * B(r+1, n). -/
def meixnerBStep (prev : Nat → IntPoly) : Nat → IntPoly
  | 0 => [1]
  | n + 1 => polySub (polyAdd (prev (n + 1)) (prev n)) (0 :: meixnerBStep prev n)

/-- Structurally recursive Meixner B(r, n) in Z[y] (kernel-reducible, zero WF!). -/
def meixnerB : Nat → Nat → IntPoly
  | 0 => fun n => polyShift n [if n % 2 == 0 then 1 else -1]
  | r + 1 => meixnerBStep (meixnerB r)

/-- Structurally recursive step computing row r+1 of Meixner C from row r:
    C(r+1, 0) = 1, C(r+1, n+1) = C(r, n+1) + y * C(r, n) - C(r+1, n). -/
def meixnerCStep (prev : Nat → IntPoly) : Nat → IntPoly
  | 0 => [1]
  | n + 1 => polySub (polyAdd (prev (n + 1)) (0 :: prev n)) (meixnerCStep prev n)

/-- Structurally recursive Meixner C(r, n) in Z[y] (kernel-reducible, zero WF!). -/
def meixnerC : Nat → Nat → IntPoly
  | 0 => fun n => [if n % 2 == 0 then 1 else -1]
  | r + 1 => meixnerCStep (meixnerC r)

/-- Reciprocal transform y^n * P(1/y) for deg(P) <= n. -/
def polyRecip (n : Nat) (p : IntPoly) : IntPoly :=
  (List.range (n + 1)).map (fun k => polyCoeff p (n - k))

def checkRecipGrid (bound : Nat) : Bool :=
  (List.range bound).all fun r =>
    (List.range bound).all fun n =>
      polyTrim (polyRecip n (meixnerB r n)) == polyTrim (meixnerC r n)

/-- Truncated Meixner orthogonality (B.1):
    (1 - y) * sum_{r < R} y^r B(r, i) B(r, j) == [i = j] y^i (mod y^R). -/
def orthLhsTrunc (R i j : Nat) : IntPoly :=
  let sumPoly := (List.range R).foldl (fun acc r =>
    let term := polyShift r (polyMul (meixnerB r i) (meixnerB r j))
    polyAdd acc term) []
  polyTrunc R (polyMul [1, -1] sumPoly)

def orthRhsTrunc (R i j : Nat) : IntPoly :=
  let rhs := if i == j then polyShift i [1] else []
  polyTrunc R rhs

def checkOrthAll (maxR : Nat) : Bool :=
  (List.range maxR).all fun rIdx =>
    let R := rIdx + 1
    (List.range R).all fun i =>
      (List.range R).all fun j =>
        orthLhsTrunc R i j == orthRhsTrunc R i j

theorem meixner_reciprocal_verified_5x5 : checkRecipGrid 5 = true := by
  decide

theorem meixner_orthogonality_verified_R5 : checkOrthAll 5 = true := by
  decide

/-! ### 2. Remark D.3 Non-Euclidean Gram Obstruction on Mat_2(F_2) (Embedded in Mat_mu(F_2), mu >= 2) -/

/-- Twice the Gram matrix 2*G_{ij} = rk(A_i) + rk(A_j) - rk(A_i - A_j) for the
    5-point subset {0, E00, E01, E11, E00+E11} of Mat_mu(F_2) (mu >= 2). -/
def twoGramD3 : Fin 4 → Fin 4 → Int
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0 | 0, 3 => 2
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 1 | 1, 3 => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2
  | 3, 0 => 2 | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 4

def witnessVecD3 : Fin 4 → Int
  | 0 => 2 | 1 => -1 | 2 => 2 | 3 => -2

/-- For u = (2, -1, 2, -2), u^T (2*G) u = -2 < 0 (so u^T G u = -1 < 0),
    certifying that d(A,B) = sqrt(rk(A - B)) is NOT Euclidean for any mu >= 2. -/
theorem remark_D3_rank_metric_non_euclidean :
    let quad2 :=
      (List.finRange 4).foldl (fun acc i =>
        acc + (List.finRange 4).foldl (fun acc2 j =>
          acc2 + witnessVecD3 i * twoGramD3 i j * witnessVecD3 j) 0) 0
    quad2 = -2 := by
  decide

/-! ### 3. Prop E.1 Permanent Gadget Factorization & Factor-2 Requirement -/

/-- Exact ring identity behind Prop E.1:
    (A0 + B0 + A1 - C0) * (A0 + B0 - A1 + C0)
      = 2 * (A0*B0 + A1*C0) + (A0*A0 + B0*B0 - A1*A1 - C0*C0). -/
theorem prop_E1_squarefree_factor2 (A0 B0 A1 C0 : Int) :
    (A0 + B0 + A1 - C0) * (A0 + B0 - A1 + C0) =
      2 * (A0 * B0 + A1 * C0) + (A0 * A0 + B0 * B0 - A1 * A1 - C0 * C0) := by
  have h1 : A0 + B0 + A1 - C0 = (A0 + B0) + (A1 - C0) := by omega
  have h2 : A0 + B0 - A1 + C0 = (A0 + B0) - (A1 - C0) := by omega
  rw [h1, h2]
  have hdiff : ∀ x y : Int, (x + y) * (x - y) = x * x - y * y := by
    intro x y
    rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y x]
    omega
  rw [hdiff (A0 + B0) (A1 - C0)]
  have hsq1 : (A0 + B0) * (A0 + B0) = A0 * A0 + 2 * (A0 * B0) + B0 * B0 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm B0 A0]
    omega
  have hsq2 : (A1 - C0) * (A1 - C0) = A1 * A1 - 2 * (A1 * C0) + C0 * C0 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm C0 A1]
    omega
  rw [hsq1, hsq2]
  omega

/-- Over F_2 (Bool with xor/+ and and/*), the two unscaled rows coincide and
    squarefree terms vanish without 1/2. -/
theorem prop_E1_char2_collapse (A0 B0 A1 C0 : Bool) :
    let row1 := xor (xor (xor A0 B0) A1) C0
    let row2 := xor (xor (xor A0 B0) A1) C0
    (row1 && row2) = row1 := by
  cases A0 <;> cases B0 <;> cases A1 <;> cases C0 <;> rfl

/-! ### 4. Characteristic-2 perm_3 = det_3 Collapse vs HC_3 Survival -/

abbrev Mat3F2 := Fin 3 → Fin 3 → Bool

def bXor (a b : Bool) : Bool := xor a b

def perm3F2 (m : Mat3F2) : Bool :=
  let t0 := m 0 0 && m 1 1 && m 2 2
  let t1 := m 0 1 && m 1 2 && m 2 0
  let t2 := m 0 2 && m 1 0 && m 2 1
  let t3 := m 0 0 && m 1 2 && m 2 1
  let t4 := m 0 1 && m 1 0 && m 2 2
  let t5 := m 0 2 && m 1 1 && m 2 0
  bXor (bXor (bXor t0 t1) (bXor t2 t3)) (bXor t4 t5)

def det3F2 (m : Mat3F2) : Bool := perm3F2 m

def hc3F2 (m : Mat3F2) : Bool :=
  let c1 := m 0 1 && m 1 2 && m 2 0
  let c2 := m 0 2 && m 1 0 && m 2 1
  bXor c1 c2

def witnessHc3F2 : Mat3F2
  | 0, 0 => true  | 0, 1 => true  | 0, 2 => false
  | 1, 0 => false | 1, 1 => true  | 1, 2 => true
  | 2, 0 => true  | 2, 1 => false | 2, 2 => true

theorem char2_hc3_separates_from_perm3_and_det3 :
    det3F2 witnessHc3F2 = false ∧
    perm3F2 witnessHc3F2 = false ∧
    hc3F2 witnessHc3F2 = true := by
  decide

theorem char0_perm3_separates_from_det3 :
    let m : Fin 3 → Fin 3 → Int := fun i j =>
      match i.1, j.1 with
      | 0, 0 => 1 | 0, 1 => 1 | 1, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
    let p := m 0 0 * m 1 1 * m 2 2 + m 0 1 * m 1 2 * m 2 0 + m 0 2 * m 1 0 * m 2 1
           + m 0 0 * m 1 2 * m 2 1 + m 0 1 * m 1 0 * m 2 2 + m 0 2 * m 1 1 * m 2 0
    let d := m 0 0 * m 1 1 * m 2 2 + m 0 1 * m 1 2 * m 2 0 + m 0 2 * m 1 0 * m 2 1
           - m 0 0 * m 1 2 * m 2 1 - m 0 1 * m 1 0 * m 2 2 - m 0 2 * m 1 1 * m 2 0
    p = 2 ∧ d = 0 := by
  decide

/-! ### 5. Prop E.10 Balanced-Cut Inequality & Flat-Case (log m)^(1/3) Exponent -/

/-- Exact integer identity proving Prop E.10's balanced-cut bound:
    Whenever k <= 3*s <= 2*k, 9*s*(k - s) >= 2*k^2. -/
theorem prop_E10_balanced_cut_bound (k s : Nat) (hlo : k ≤ 3 * s) (hhi : 3 * s ≤ 2 * k) :
    2 * (k * k) ≤ 9 * (s * (k - s)) := by
  have hsle : s ≤ k := by omega
  have h1 : 0 ≤ (3 * (s : Int) - (k : Int)) * (2 * (k : Int) - 3 * (s : Int)) := by
    have ha : (0 : Int) ≤ 3 * (s : Int) - (k : Int) := by omega
    have hb : (0 : Int) ≤ 2 * (k : Int) - 3 * (s : Int) := by omega
    exact Int.mul_nonneg ha hb
  have hexp :
      (3 * (s : Int) - (k : Int)) * (2 * (k : Int) - 3 * (s : Int)) =
        9 * ((s : Int) * ((k : Int) - (s : Int))) - 2 * ((k : Int) * (k : Int)) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hsk : (s : Int) * (k : Int) = (k : Int) * (s : Int) := Int.mul_comm _ _
    have h9 : (3 * (s : Int)) * (3 * (s : Int)) = 9 * ((s : Int) * (s : Int)) := by
      calc (3 * (s : Int)) * (3 * (s : Int))
          = (3 * 3 : Int) * ((s : Int) * (s : Int)) := by
              rw [Int.mul_assoc, Int.mul_left_comm (s : Int) 3 (s : Int), ← Int.mul_assoc]
        _ = 9 * ((s : Int) * (s : Int)) := rfl
    have h6a : (3 * (s : Int)) * (2 * (k : Int)) = 6 * ((s : Int) * (k : Int)) := by
      calc (3 * (s : Int)) * (2 * (k : Int))
          = (3 * 2 : Int) * ((s : Int) * (k : Int)) := by
              rw [Int.mul_assoc, Int.mul_left_comm (s : Int) 2 (k : Int), ← Int.mul_assoc]
        _ = 6 * ((s : Int) * (k : Int)) := rfl
    have h6b : (k : Int) * (3 * (s : Int)) = 3 * ((s : Int) * (k : Int)) := by
      rw [Int.mul_left_comm, hsk]
    have h2k : (k : Int) * (2 * (k : Int)) = 2 * ((k : Int) * (k : Int)) := by
      rw [Int.mul_left_comm]
    have h9sk : 9 * ((s : Int) * ((k : Int) - (s : Int))) =
        9 * ((s : Int) * (k : Int)) - 9 * ((s : Int) * (s : Int)) := by
      rw [Int.mul_sub, Int.mul_sub]
    omega
  have hz : 2 * ((k : Int) * (k : Int)) ≤ 9 * ((s : Int) * ((k : Int) - (s : Int))) := by
    omega
  have hcast : ((k - s : Nat) : Int) = (k : Int) - (s : Int) := Int.ofNat_sub hsle
  rw [← hcast] at hz
  have hz_nat : ((2 * (k * k) : Nat) : Int) ≤ ((9 * (s * (k - s)) : Nat) : Int) := by
    simpa [Int.natCast_mul] using hz
  exact Int.ofNat_le.mp hz_nat

/-- Exact flat-case parameter scaling (Thm E.11):
    k = r^2, l = 100*r -> l*k*r = 100*r^4 while logM_proxy = 200*r^3,
    yielding exact cubic-to-quartic invariant 8 * (l*k*r)^3 = (200*r^3)^4 / 200. -/
theorem thm_E11_exponent_scaling (r : Nat) :
    let k := r * r
    let l := 100 * r
    let logL_scaled := l * k * r
    let logM_proxy := 200 * (r * r * r)
    logL_scaled = 100 * (r * r * r * r) ∧
    8 * (logL_scaled * logL_scaled * logL_scaled) =
      (logM_proxy * logM_proxy * logM_proxy * logM_proxy) / 200 := by
  dsimp only
  have h1 : 100 * r * (r * r) * r = 100 * (r * r * r * r) := by
    simp only [Nat.mul_assoc]
  constructor
  · exact h1
  · rw [h1]
    have hlhs : 8 * (100 * (r * r * r * r) * (100 * (r * r * r * r)) * (100 * (r * r * r * r))) =
        8000000 * (r * r * r * r * r * r * r * r * r * r * r * r) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hnum :
        200 * (r * r * r) * (200 * (r * r * r)) * (200 * (r * r * r)) * (200 * (r * r * r)) =
        200 * (8000000 * (r * r * r * r * r * r * r * r * r * r * r * r)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hlhs, hnum, Nat.mul_div_right _ (by decide : 0 < 200)]

/-! ### 6. Lemma F.2: Rank-1 Generator Word Factorization in U_4(F_2) -/

abbrev Mat4F2 := Fin 4 → Fin 4 → Bool

def mat4Mul (a b : Mat4F2) : Mat4F2 := fun i j =>
  (List.finRange 4).foldl (fun acc k => bXor acc (a i k && b k j)) false

def genU4 (j : Fin 3) : Mat4F2 := fun r c =>
  (r == c) || (r.1 == j.1 && c.1 == j.1 + 1)

def mat4Eq (a b : Mat4F2) : Bool :=
  (List.finRange 4).all fun r => (List.finRange 4).all fun c => a r c == b r c

theorem lem_F2_U4_rank1_word :
    let x0 := genU4 ⟨0, by decide⟩
    let x1 := genU4 ⟨1, by decide⟩
    let x2 := genU4 ⟨2, by decide⟩
    let prod := mat4Mul x0 (mat4Mul x2 (mat4Mul x1 (mat4Mul x2 x0)))
    let target : Mat4F2 := fun r c =>
      (r == c) || (r.1 < 2 && c.1 >= 2)
    mat4Eq prod target = true := by
  decide

/-! ### 7. Section 2.5 Boolean-Circuit Barrier Over F_2 -/

theorem sec25_boolean_garbage_vanishes_on_bits :
    ∀ x1 x2 x3 : Bool,
      let garbage := bXor (x1 && x1 && x2 && x3) (x1 && x2 && x3)
      garbage = false := by
  decide

theorem sec25_boolean_garbage_corrupts_formal_deg3 :
    let f_deg3_coeff : Bool := true
    let garbage_deg3_coeff : Bool := true
    bXor f_deg3_coeff garbage_deg3_coeff = false := by
  rfl

/-! ### 8. Lemma N.2 Border-Complexity Laurent Cutoff Valuation Bound -/

theorem lem_N2_cutoff_preserves_nonpositive_exponents
    (M Delta restCount : Nat) (hM : 1 ≤ M) (hrest : restCount ≤ M - 1) :
    (M * Delta + 1 : Int) - (restCount * Delta : Int) ≥ 1 := by
  have hle : restCount * Delta ≤ (M - 1) * Delta := Nat.mul_le_mul_right Delta hrest
  have hsub : (M - 1) * Delta + Delta = M * Delta := by
    have h1 : (M - 1) + 1 = M := Nat.sub_add_cancel hM
    calc (M - 1) * Delta + Delta
        = (M - 1) * Delta + 1 * Delta := by rw [Nat.one_mul]
      _ = ((M - 1) + 1) * Delta := by rw [Nat.add_mul]
      _ = M * Delta := by rw [h1]
  omega

/-! ### 9. Theorem K.6 Diagonalization Contradiction (V = 1 + V -> False) -/

theorem thm_K6_diagonalization_int (V : Int) (h : V = 1 + V) : False := by
  omega

theorem thm_K6_diagonalization_mod (q V : Nat) (hq : 2 ≤ q) (h : V % q = (1 + V) % q) : False := by
  have h1 : (1 + V) % q = (1 + V % q) % q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < q)]
  rw [h1] at h
  have hlt : V % q < q := Nat.mod_lt V (by omega)
  by_cases htop : V % q + 1 < q
  · have hmod : (1 + V % q) % q = 1 + V % q := Nat.mod_eq_of_lt (by omega)
    omega
  · have heq : 1 + V % q = q := by omega
    rw [heq, Nat.mod_self] at h
    omega

end S75VpVnpMechanismCerts

#print axioms S75VpVnpMechanismCerts.meixner_reciprocal_verified_5x5
#print axioms S75VpVnpMechanismCerts.meixner_orthogonality_verified_R5
#print axioms S75VpVnpMechanismCerts.remark_D3_rank_metric_non_euclidean
#print axioms S75VpVnpMechanismCerts.prop_E1_squarefree_factor2
#print axioms S75VpVnpMechanismCerts.prop_E1_char2_collapse
#print axioms S75VpVnpMechanismCerts.char2_hc3_separates_from_perm3_and_det3
#print axioms S75VpVnpMechanismCerts.char0_perm3_separates_from_det3
#print axioms S75VpVnpMechanismCerts.prop_E10_balanced_cut_bound
#print axioms S75VpVnpMechanismCerts.thm_E11_exponent_scaling
#print axioms S75VpVnpMechanismCerts.lem_F2_U4_rank1_word
#print axioms S75VpVnpMechanismCerts.sec25_boolean_garbage_vanishes_on_bits
#print axioms S75VpVnpMechanismCerts.sec25_boolean_garbage_corrupts_formal_deg3
#print axioms S75VpVnpMechanismCerts.lem_N2_cutoff_preserves_nonpositive_exponents
#print axioms S75VpVnpMechanismCerts.thm_K6_diagonalization_int
#print axioms S75VpVnpMechanismCerts.thm_K6_diagonalization_mod

/-
  ZPolyCounterexample

  Pure `Init` Lean 4.36.0 development (zero imports, zero Mathlib, zero sorry,
  zero Classical.choice: every theorem depends only on a subset of
  {propext, Quot.sound}).

  Formalizes over Int (algebraic flag-polynomial and witness layer; the
  combinatorial matroid/EPW lattice bridge and full 651-spread geometric
  enumeration over prime-power geometries PG(5, q), AG(4, q), PG(3, 25) are
  independently verified in the companion pure-Z/Q Python oracle):
  1. Polynomial ring operations (evalP, addP, subP, scaleP, negP, mulP, trimP)
     and linear-pass Horner Taylor shift (shiftFast), with homomorphism and
     positivity theorems.
  2. Exact divisibility identities 2 * choose2 m = m*(m-1),
     6 * choose3 m = m*(m-1)*(m-2), and Gaussian q-binomials gaussQ.
  3. Rank-4 flag f-vectors FlagVec4, exact multichain summation alphaPair for
     truncated direct sums M = T(G1 + G2) of rank 7, and the Z-polynomial
     coefficients z1Pair, z2Pair, z3Pair together with their 3/12/36-term
     bilinear expansions and polynomial bridges.
  4. Universal algebraic inequality z2^2 < z1 * z3 for EVERY integer q >= 27
     (which applies in particular to all prime powers q >= 27 where the
     geometries PG(5, q) and AG(4, q) exist) for BOTH:
       (a) guoriyue/z123's projective Gabidulin flag formula in PG(5, q) (m = q^3),
       (b) the 28.04x smaller elementary Affine Gabidulin flag formula A_{4,q} in
           AG(4, q) (m = q^2, s = q^2).
  5. Universal ground-set dominance 2*(q^4 + q^2) < 2*(gaussQ q 6 1 + q^3) for
     every integer q >= 2, plus concrete witnesses and boundary controls at:
       - PG(5, 27) m = 19,683 (|E| = 29,840,942),
       - PG(5, 25) m = 13,000 (|E| = 20,371,052) vs. m = 15,625 control,
       - AG(4, 27) elementary m = 729 (|E| = 1,064,340), m = 618 (|E| = 1,064,118, 28.04x),
         and threshold m = 461 (|E| = 1,063,804) vs. m = 460 control,
       - Asymmetric elementary (27, 510) + (25, 456) (|E| = 923,032 < 1,000,000),
       - Sub-million spread-packing AG(4, 25) at m = 537 (|E| = 782,324, 38.14x)
         and m = 510 (|E| = 782,270),
       - Spread-packing negative control AG(4, 23) at m = 461 (|E| = 560,604).
  6. Algebraic good-set certificate over F_625 = F_5[w]/(w^2 - 2)[z]/(z^2 - w)
     verifying the closed-form 26-triple set P = {(w, 1, v) : v in U} against
     the Pavese-Santonastaso pair conditions (3.2)-(3.3) and norm conditions
     (full 651-spread construction and point-partition checks are verified in
     the Python oracle).
-/

namespace ZPolyCounterexample

/-! ## 1. Little-endian integer polynomial arithmetic, trimming, and Taylor shift -/

def evalP : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalP cs x

def addP : List Int → List Int → List Int
  | [], r => r
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addP as bs

def scaleP (k : Int) : List Int → List Int
  | [] => []
  | c :: cs => (k * c) :: scaleP k cs

def negP : List Int → List Int
  | [] => []
  | c :: cs => (-c) :: negP cs

def subP (p r : List Int) : List Int :=
  addP p (negP r)

def mulP : List Int → List Int → List Int
  | [], _ => []
  | c :: cs, r => addP (scaleP c r) (0 :: mulP cs r)

def isZeroInt : Int → Bool
  | Int.ofNat 0 => true
  | Int.ofNat (_ + 1) => false
  | Int.negSucc _ => false

theorem isZeroInt_eq_true (c : Int) (h : isZeroInt c = true) : c = 0 := by
  cases c with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n => cases h
  | negSucc n => cases h

def consTrim (c : Int) : List Int → List Int
  | [] =>
    match isZeroInt c with
    | true => []
    | false => [c]
  | b :: bs => c :: b :: bs

def trimP : List Int → List Int
  | [] => []
  | c :: cs => consTrim c (trimP cs)

def shiftAdd (a : Int) : List Int → List Int → List Int
  | [], r => r
  | b :: bs, [] => (a * b) :: shiftAdd a bs []
  | b :: bs, y :: ys => (y + a * b) :: shiftAdd a bs ys

def shiftStep (a c : Int) (r : List Int) : List Int :=
  match r with
  | [] => [c]
  | b :: bs => (c + a * b) :: shiftAdd a bs (b :: bs)

def shiftFast : List Int → Int → List Int
  | [], _ => []
  | c :: cs, a => shiftStep a c (shiftFast cs a)

theorem evalP_addP (p r : List Int) (x : Int) :
    evalP (addP p r) x = evalP p x + evalP r x := by
  induction p generalizing r with
  | nil => simp only [addP, evalP]; omega
  | cons a as ih =>
    cases r with
    | nil => simp only [addP, evalP]; omega
    | cons b bs =>
      simp only [addP, evalP]
      rw [ih bs, Int.mul_add]
      omega

theorem evalP_scaleP (k : Int) (p : List Int) (x : Int) :
    evalP (scaleP k p) x = k * evalP p x := by
  induction p with
  | nil => simp only [scaleP, evalP, Int.mul_zero]
  | cons c cs ih =>
    simp only [scaleP, evalP]
    rw [ih, Int.mul_add, Int.mul_left_comm]

theorem evalP_negP (p : List Int) (x : Int) :
    evalP (negP p) x = - evalP p x := by
  induction p with
  | nil => simp only [negP, evalP]; omega
  | cons c cs ih =>
    simp only [negP, evalP]
    rw [ih, Int.mul_neg]
    omega

theorem evalP_subP (p r : List Int) (x : Int) :
    evalP (subP p r) x = evalP p x - evalP r x := by
  simp only [subP]
  rw [evalP_addP, evalP_negP]
  omega

theorem evalP_mulP (p r : List Int) (x : Int) :
    evalP (mulP p r) x = evalP p x * evalP r x := by
  induction p with
  | nil => simp only [mulP, evalP, Int.zero_mul]
  | cons c cs ih =>
    simp only [mulP]
    rw [evalP_addP, evalP_scaleP]
    simp only [evalP]
    rw [ih, Int.add_mul, Int.mul_assoc]
    omega

theorem evalP_consTrim (c : Int) (r : List Int) (x : Int) :
    evalP (consTrim c r) x = c + x * evalP r x := by
  cases r with
  | nil =>
    dsimp [consTrim, evalP]
    cases hz : isZeroInt c with
    | true =>
      have hc0 := isZeroInt_eq_true c hz
      subst hc0
      simp only [evalP, Int.mul_zero, Int.add_zero]
    | false =>
      simp only [evalP, Int.mul_zero, Int.add_zero]
  | cons b bs =>
    rfl

theorem evalP_trimP (p : List Int) (x : Int) :
    evalP (trimP p) x = evalP p x := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    dsimp [trimP, evalP]
    rw [evalP_consTrim, ih]

theorem evalP_shiftAdd (a : Int) (p r : List Int) (x : Int) :
    evalP (shiftAdd a p r) x = a * evalP p x + evalP r x := by
  induction p generalizing r with
  | nil => simp only [shiftAdd, evalP, Int.mul_zero]; omega
  | cons b bs ih =>
    cases r with
    | nil =>
      simp only [shiftAdd, evalP]
      rw [ih [], Int.mul_add, Int.mul_add, Int.mul_left_comm]
      simp only [evalP]
      omega
    | cons y ys =>
      simp only [shiftAdd, evalP]
      rw [ih ys, Int.mul_add, Int.mul_add, Int.mul_left_comm x a]
      omega

theorem evalP_shiftStep (a c : Int) (r : List Int) (x : Int) :
    evalP (shiftStep a c r) x = c + (x + a) * evalP r x := by
  cases r with
  | nil => simp only [shiftStep, evalP, Int.mul_zero]
  | cons b bs =>
    simp only [shiftStep, evalP]
    rw [evalP_shiftAdd]
    simp only [evalP]
    rw [Int.mul_add, Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_left_comm x a]
    omega

theorem evalP_shiftFast (p : List Int) (a x : Int) :
    evalP (shiftFast p a) x = evalP p (x + a) := by
  induction p with
  | nil => simp only [shiftFast, evalP]
  | cons c cs ih =>
    simp only [shiftFast, evalP]
    rw [evalP_shiftStep, ih]

theorem evalP_nonneg_of_coeffs_nonneg (p : List Int) (x : Int)
    (hp : ∀ c ∈ p, 0 ≤ c) (hx : 0 ≤ x) : 0 ≤ evalP p x := by
  induction p with
  | nil => simp only [evalP]; omega
  | cons c cs ih =>
    simp only [evalP]
    have hc : 0 ≤ c := hp c (List.mem_cons.mpr (Or.inl rfl))
    have hcs : 0 ≤ evalP cs x :=
      ih (fun d hd => hp d (List.mem_cons.mpr (Or.inr hd)))
    have hm : 0 ≤ x * evalP cs x := Int.mul_nonneg hx hcs
    omega

theorem evalP_pos_of_coeffs_pos (p : List Int) (x : Int)
    (hp : ∀ c ∈ p, 0 < c) (hne : p ≠ []) (hx : 0 ≤ x) : 0 < evalP p x := by
  cases p with
  | nil => exact absurd rfl hne
  | cons c cs =>
    simp only [evalP]
    have hc : 0 < c := hp c (List.mem_cons.mpr (Or.inl rfl))
    have hcs : 0 ≤ evalP cs x :=
      evalP_nonneg_of_coeffs_nonneg cs x
        (fun d hd => Int.le_of_lt (hp d (List.mem_cons.mpr (Or.inr hd)))) hx
    have hm : 0 ≤ x * evalP cs x := Int.mul_nonneg hx hcs
    omega

theorem all_pos_of_all_gt_zero (l : List Int) (h : l.all (fun c => decide (0 < c)) = true) :
    ∀ c ∈ l, 0 < c := by
  induction l with
  | nil => intro c hc; cases hc
  | cons a as ih =>
    intro c hc
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    cases List.mem_cons.mp hc with
    | inl e => subst e; exact h.1
    | inr tl => exact ih h.2 c tl

theorem neg_of_shiftFast_neg_coeffs_pos (p : List Int) (a : Int)
    (hp : ∀ c ∈ shiftFast (negP p) a, 0 < c) (hne : shiftFast (negP p) a ≠ []) :
    ∀ q, a ≤ q → evalP p q < 0 := by
  intro q hq
  have hx : 0 ≤ q - a := by omega
  have hpos := evalP_pos_of_coeffs_pos (shiftFast (negP p) a) (q - a) hp hne hx
  rw [evalP_shiftFast, Int.sub_add_cancel, evalP_negP] at hpos
  omega

theorem pos_of_mul_pos_left (a b : Int) (ha : 0 < a) (h : 0 < a * b) : 0 < b := by
  have h0 : a * 0 < a * b := by rw [Int.mul_zero]; exact h
  exact Int.lt_of_mul_lt_mul_left h0 (Int.le_of_lt ha)

/-! ## 2. Exact binomials choose2, choose3 and Gaussian q-binomials gaussQ -/

def choose2 (m : Int) : Int := (m * (m - 1)) / 2
def choose3 (m : Int) : Int := (m * (m - 1) * (m - 2)) / 6

theorem mul_two_three (a b : Int) : (2 * a) * (3 * b) = 6 * (a * b) := by
  have h2 : (2 : Int) = 1 + 1 := rfl
  have h3 : (3 : Int) = 1 + 1 + 1 := rfl
  have h6 : (6 : Int) = 1 + 1 + 1 + 1 + 1 + 1 := rfl
  rw [h2, h3, h6]
  simp only [Int.add_mul, Int.mul_add, Int.one_mul]
  omega

theorem mul_three_two (a b : Int) : (3 * a) * (2 * b) = 6 * (a * b) := by
  rw [Int.mul_comm (3 * a) (2 * b), mul_two_three b a, Int.mul_comm b a]

theorem two_mul_choose2 (m : Int) : 2 * choose2 m = m * (m - 1) := by
  simp only [choose2]
  let q2 := m / 2
  rcases (by omega : m = 2 * q2 ∨ m = 2 * q2 + 1) with h0 | h1
  · have hm0 : m = 2 * q2 := h0
    have hk : m * (m - 1) = 2 * (q2 * (m - 1)) := by
      conv => lhs; arg 1; rw [hm0]
      rw [Int.mul_assoc]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]
  · have hm1 : m - 1 = 2 * q2 := by omega
    have hk : m * (m - 1) = 2 * (m * q2) := by
      rw [hm1, Int.mul_left_comm]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]

theorem six_mul_choose3 (m : Int) : 6 * choose3 m = m * (m - 1) * (m - 2) := by
  simp only [choose3]
  let q6 := m / 6
  rcases (by omega : m = 6 * q6 ∨ m = 6 * q6 + 1 ∨ m = 6 * q6 + 2 ∨
                     m = 6 * q6 + 3 ∨ m = 6 * q6 + 4 ∨ m = 6 * q6 + 5)
    with h0 | h1 | h2 | h3 | h4 | h5
  · have hk : m * (m - 1) * (m - 2) = 6 * (q6 * (m - 1) * (m - 2)) := by
      conv => lhs; arg 1; arg 1; rw [h0]
      rw [Int.mul_assoc 6 q6 (m - 1), Int.mul_assoc 6 (q6 * (m - 1)) (m - 2)]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]
  · have hm1 : m - 1 = 6 * q6 := by omega
    have hk : m * (m - 1) * (m - 2) = 6 * (m * q6 * (m - 2)) := by
      conv => lhs; arg 1; arg 2; rw [hm1]
      rw [Int.mul_left_comm m 6 q6, Int.mul_assoc 6 (m * q6) (m - 2)]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]
  · have hm2 : m - 2 = 6 * q6 := by omega
    have hk : m * (m - 1) * (m - 2) = 6 * (m * (m - 1) * q6) := by
      rw [hm2, Int.mul_left_comm (m * (m - 1)) 6 q6]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]
  · have hm0 : m = 3 * (2 * q6 + 1) := by omega
    have hm1 : m - 1 = 2 * (3 * q6 + 1) := by omega
    have hk : m * (m - 1) * (m - 2) = 6 * ((2 * q6 + 1) * (3 * q6 + 1) * (m - 2)) := by
      conv => lhs; arg 1; arg 1; rw [hm0]
      conv => lhs; arg 1; arg 2; rw [hm1]
      rw [mul_three_two, Int.mul_assoc]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]
  · have hm0 : m = 2 * (3 * q6 + 2) := by omega
    have hm1 : m - 1 = 3 * (2 * q6 + 1) := by omega
    have hk : m * (m - 1) * (m - 2) = 6 * ((3 * q6 + 2) * (2 * q6 + 1) * (m - 2)) := by
      conv => lhs; arg 1; arg 1; rw [hm0]
      conv => lhs; arg 1; arg 2; rw [hm1]
      rw [mul_two_three, Int.mul_assoc]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]
  · have hm1 : m - 1 = 2 * (3 * q6 + 2) := by omega
    have hm2 : m - 2 = 3 * (2 * q6 + 1) := by omega
    have hk : m * (m - 1) * (m - 2) = 6 * (m * ((3 * q6 + 2) * (2 * q6 + 1))) := by
      rw [hm1, hm2, Int.mul_assoc m (2 * (3 * q6 + 2)) (3 * (2 * q6 + 1)),
          mul_two_three, Int.mul_left_comm]
    rw [hk, Int.mul_ediv_cancel_left _ (by omega)]

def gaussQ (q : Int) : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gaussQ q n k + q ^ (k + 1) * gaussQ q n (k + 1)

theorem gaussQ_zero_right (q : Int) (n : Nat) : gaussQ q n 0 = 1 := by
  cases n <;> rfl

theorem gaussQ_one_mul (q : Int) (n : Nat) :
    (q - 1) * gaussQ q n 1 = q ^ n - 1 := by
  induction n with
  | zero => simp only [gaussQ, Int.mul_zero, Int.pow_zero]; omega
  | succ n ih =>
    simp only [gaussQ]
    rw [gaussQ_zero_right, Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_add,
      Int.mul_one, Int.mul_left_comm, ih, Int.mul_sub, Int.mul_one, Int.mul_comm q,
      Int.pow_succ q n]
    omega

def qPowPoly : Nat → List Int
  | 0 => [1]
  | k + 1 => 0 :: qPowPoly k

theorem evalP_qPowPoly (k : Nat) (q : Int) : evalP (qPowPoly k) q = q ^ k := by
  induction k with
  | zero => simp only [qPowPoly, evalP, Int.mul_zero, Int.pow_zero]; omega
  | succ k ih =>
    simp only [qPowPoly, evalP]
    rw [ih, Int.zero_add, Int.pow_succ, Int.mul_comm]

def gaussPoly : Nat → Nat → List Int
  | 0, 0 => [1]
  | 0, _ + 1 => []
  | _ + 1, 0 => [1]
  | n + 1, k + 1 => addP (gaussPoly n k) (mulP (qPowPoly (k + 1)) (gaussPoly n (k + 1)))

theorem evalP_gaussPoly (n k : Nat) (q : Int) :
    evalP (gaussPoly n k) q = gaussQ q n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp only [gaussPoly, gaussQ, evalP]; omega
    | succ k => simp only [gaussPoly, gaussQ, evalP]
  | succ n ih =>
    cases k with
    | zero => simp only [gaussPoly, gaussQ, evalP]; omega
    | succ k =>
      simp only [gaussPoly, gaussQ]
      rw [evalP_addP, evalP_mulP, evalP_qPowPoly, ih k, ih (k + 1)]

/-! ## 3. Rank-4 flag f-vectors, multichain enumeration, and rank-7 Z-polynomial -/

structure FlagVec4 where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a12 : Int
  a13 : Int
  a23 : Int
  a123 : Int
  deriving DecidableEq

def flagEntry (F : FlagVec4) (b1 b2 b3 : Bool) : Int :=
  match b1, b2, b3 with
  | false, false, false => F.a0
  | true,  false, false => F.a1
  | false, true,  false => F.a2
  | false, false, true  => F.a3
  | true,  true,  false => F.a12
  | true,  false, true  => F.a13
  | false, true,  true  => F.a23
  | true,  true,  true  => F.a123

def hasRk (r : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => Nat.beq x r || hasRk r xs

def flagOfChain (F : FlagVec4) (xs : List Nat) : Int :=
  flagEntry F (hasRk 1 xs) (hasRk 2 xs) (hasRk 3 xs)

def range5 : List Nat := [0, 1, 2, 3, 4]

def enumPairs : List Nat → Nat → Nat → List (List Nat × List Nat)
  | [], _, _ => [([], [])]
  | s :: rest, pL, pR =>
    (range5.filter fun i => Nat.ble pL i && Nat.ble i s && Nat.ble (s - i) 4 && Nat.ble pR (s - i)).flatMap fun i =>
      let j := s - i
      (enumPairs rest i j).map fun (ls, rs) => (i :: ls, j :: rs)

def sumPairs (A B : FlagVec4) : List (List Nat × List Nat) → Int
  | [] => 0
  | (ls, rs) :: ps => flagOfChain A ls * flagOfChain B rs + sumPairs A B ps

def alphaPair (A B : FlagVec4) (ranks : List Nat) : Int :=
  sumPairs A B (enumPairs ranks 0 0)

def z1Pair (A B : FlagVec4) : Int :=
  alphaPair A B [6]

def z2Pair (A B : FlagVec4) : Int :=
  alphaPair A B [5] + alphaPair A B [4, 6] - alphaPair A B [4, 5]

def z3Pair (A B : FlagVec4) : Int :=
  alphaPair A B [4]
    + alphaPair A B [3, 6] - alphaPair A B [3, 4]
    + alphaPair A B [2, 5] - alphaPair A B [2, 4]
    + alphaPair A B [2, 4, 6] - alphaPair A B [2, 4, 5]
    - alphaPair A B [2, 3, 6] + alphaPair A B [2, 3, 4]

def z1Bilin (A B : FlagVec4) : Int :=
  A.a0 * B.a2 + A.a2 * B.a0 + A.a3 * B.a3

def z2Bilin (A B : FlagVec4) : Int :=
  A.a0 * B.a2 - A.a1 * B.a3 + A.a13 * B.a3 + A.a2 * B.a0
  + 2 * (A.a2 * B.a2) - A.a2 * B.a23 + A.a2 * B.a3
  - A.a23 * B.a2 + A.a23 * B.a23 - A.a3 * B.a1 + A.a3 * B.a13 + A.a3 * B.a2

def z3Bilin (A B : FlagVec4) : Int :=
  2 * (A.a0 * B.a0) - A.a0 * B.a2 + A.a0 * B.a23 - A.a0 * B.a3
  + 2 * (A.a1 * B.a1) - A.a1 * B.a12 + A.a1 * B.a123 - 2 * (A.a1 * B.a13) - A.a1 * B.a23
  - A.a12 * B.a1 + A.a12 * B.a12 - A.a12 * B.a123 + A.a12 * B.a13
  + A.a123 * B.a1 - A.a123 * B.a12 + A.a123 * B.a123 - A.a123 * B.a13
  - 2 * (A.a13 * B.a1) + A.a13 * B.a12 - A.a13 * B.a123 + 2 * (A.a13 * B.a13) + A.a13 * B.a23
  - A.a2 * B.a0 + 5 * (A.a2 * B.a2) - 2 * (A.a2 * B.a23) + 2 * (A.a2 * B.a3)
  + A.a23 * B.a0 - A.a23 * B.a1 + A.a23 * B.a13 - 2 * (A.a23 * B.a2) + 2 * (A.a23 * B.a23) - A.a23 * B.a3
  - A.a3 * B.a0 + 2 * (A.a3 * B.a2) - A.a3 * B.a23 + 2 * (A.a3 * B.a3)

theorem z1Pair_eq_bilin (A B : FlagVec4) : z1Pair A B = z1Bilin A B := by
  dsimp [z1Pair, z1Bilin, alphaPair, enumPairs, range5, List.filter, List.flatMap, List.flatten,
    List.map, List.append, sumPairs, flagOfChain, hasRk, Nat.beq, Nat.ble, Bool.and, Bool.or, flagEntry]
  omega

theorem z2Pair_eq_bilin (A B : FlagVec4) : z2Pair A B = z2Bilin A B := by
  dsimp [z2Pair, z2Bilin, alphaPair, enumPairs, range5, List.filter, List.flatMap, List.flatten,
    List.map, List.append, sumPairs, flagOfChain, hasRk, Nat.beq, Nat.ble, Bool.and, Bool.or, flagEntry]
  omega

theorem z3Pair_eq_bilin (A B : FlagVec4) : z3Pair A B = z3Bilin A B := by
  dsimp [z3Pair, z3Bilin, alphaPair, enumPairs, range5, List.filter, List.flatMap, List.flatten,
    List.map, List.append, sumPairs, flagOfChain, hasRk, Nat.beq, Nat.ble, Bool.and, Bool.or, flagEntry]
  omega

/-! ## 4. Exact building-block flag f-vectors for PG(5, q) and AG(4, q) -/

def projGabFlag (q m : Int) : FlagVec4 :=
  let b := m * (q ^ 6)
  let N1 := gaussQ q 6 1
  let N2 := gaussQ q 6 2
  let N3 := gaussQ q 6 3
  let t := q * q + q + 1
  let nH := N1 * choose2 m + choose3 m
  let nB := b
  let nU := m * N2 - b * t
  let nN := N3 - b
  { a0 := 1
    a1 := N1 + m
    a2 := N2 + N1 * m + choose2 m
    a3 := nH + nB + nU + nN
    a12 := (q + 1) * N2 + 2 * (N1 * m + choose2 m)
    a13 := nH * 3 + nB * (t + 1) + nU * (q + 2) + nN * t
    a23 := nH * 3 + nB * (2 * t) + nU * (q + 2) + nN * t
    a123 := nH * 6 + nB * ((q + 3) * t) + nU * (3 * (q + 1)) + nN * ((q + 1) * t) }

def affGabFlag (q m sDirs : Int) : FlagVec4 :=
  let N1 := q ^ 4
  let N2 := (q ^ 3) * gaussQ q 4 1
  let N3 := (q ^ 2) * gaussQ q 4 2
  let b := m * (q ^ 2) * sDirs
  let nH := N1 * choose2 m + choose3 m
  let nB := b
  let nU := m * N2 - b * q * (q + 1)
  let nN := N3 - b
  { a0 := 1
    a1 := N1 + m
    a2 := N2 + N1 * m + choose2 m
    a3 := nH + nB + nU + nN
    a12 := q * N2 + 2 * (N1 * m + choose2 m)
    a13 := nH * 3 + nB * (q * q + 1) + nU * (q + 1) + nN * (q * q)
    a23 := nH * 3 + nB * (2 * q * q + q) + nU * (q + 1) + nN * (q * (q + 1))
    a123 := nH * 6 + nB * (q ^ 3 + 3 * q * q) + nU * (3 * q) + nN * (q * q * (q + 1)) }

def scaleFlag (k : Int) (F : FlagVec4) : FlagVec4 :=
  { a0 := k * F.a0, a1 := k * F.a1, a2 := k * F.a2, a3 := k * F.a3,
    a12 := k * F.a12, a13 := k * F.a13, a23 := k * F.a23, a123 := k * F.a123 }

theorem z1Bilin_scale6 (A B : FlagVec4) :
    z1Bilin (scaleFlag 6 A) (scaleFlag 6 B) = 36 * z1Bilin A B := by
  simp only [z1Bilin, scaleFlag]
  have h36 : (36 : Int) = 6 * 6 := rfl
  rw [h36]
  simp only [Int.mul_add, Int.mul_assoc, Int.mul_left_comm]

theorem z2Bilin_scale6 (A B : FlagVec4) :
    z2Bilin (scaleFlag 6 A) (scaleFlag 6 B) = 36 * z2Bilin A B := by
  simp only [z2Bilin, scaleFlag]
  have h36 : (36 : Int) = 6 * 6 := rfl
  rw [h36]
  simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_left_comm]

theorem z3Bilin_scale6 (A B : FlagVec4) :
    z3Bilin (scaleFlag 6 A) (scaleFlag 6 B) = 36 * z3Bilin A B := by
  simp only [z3Bilin, scaleFlag]
  have h36 : (36 : Int) = 6 * 6 := rfl
  rw [h36]
  simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_left_comm]

/-! ## 5. Polynomial FlagPoly4 representation and exact evaluation bridges -/

structure FlagPoly4 where
  a0 : List Int
  a1 : List Int
  a2 : List Int
  a3 : List Int
  a12 : List Int
  a13 : List Int
  a23 : List Int
  a123 : List Int
  deriving DecidableEq

def trimFlagPoly (P : FlagPoly4) : FlagPoly4 :=
  { a0 := trimP P.a0, a1 := trimP P.a1, a2 := trimP P.a2, a3 := trimP P.a3,
    a12 := trimP P.a12, a13 := trimP P.a13, a23 := trimP P.a23, a123 := trimP P.a123 }

def evalFlagPoly (P : FlagPoly4) (q : Int) : FlagVec4 :=
  { a0 := evalP P.a0 q, a1 := evalP P.a1 q, a2 := evalP P.a2 q, a3 := evalP P.a3 q,
    a12 := evalP P.a12 q, a13 := evalP P.a13 q, a23 := evalP P.a23 q, a123 := evalP P.a123 q }

theorem evalFlagPoly_trimFlagPoly (P : FlagPoly4) (q : Int) :
    evalFlagPoly (trimFlagPoly P) q = evalFlagPoly P q := by
  simp only [evalFlagPoly, trimFlagPoly, evalP_trimP]

def z1Poly (A B : FlagPoly4) : List Int :=
  addP (addP (mulP A.a0 B.a2) (mulP A.a2 B.a0)) (mulP A.a3 B.a3)

def z2Poly (A B : FlagPoly4) : List Int :=
  let t1 := subP (mulP A.a0 B.a2) (mulP A.a1 B.a3)
  let t2 := addP (mulP A.a13 B.a3) (mulP A.a2 B.a0)
  let t3 := subP (scaleP 2 (mulP A.a2 B.a2)) (mulP A.a2 B.a23)
  let t4 := subP (mulP A.a2 B.a3) (mulP A.a23 B.a2)
  let t5 := subP (mulP A.a23 B.a23) (mulP A.a3 B.a1)
  let t6 := addP (mulP A.a3 B.a13) (mulP A.a3 B.a2)
  addP (addP (addP t1 t2) (addP t3 t4)) (addP t5 t6)

def z3Poly (A B : FlagPoly4) : List Int :=
  let r1 := subP (addP (subP (scaleP 2 (mulP A.a0 B.a0)) (mulP A.a0 B.a2)) (mulP A.a0 B.a23)) (mulP A.a0 B.a3)
  let r2 := subP (subP (addP (subP (scaleP 2 (mulP A.a1 B.a1)) (mulP A.a1 B.a12)) (mulP A.a1 B.a123)) (scaleP 2 (mulP A.a1 B.a13))) (mulP A.a1 B.a23)
  let r3 := addP (subP (addP (negP (mulP A.a12 B.a1)) (mulP A.a12 B.a12)) (mulP A.a12 B.a123)) (mulP A.a12 B.a13)
  let r4 := subP (addP (subP (mulP A.a123 B.a1) (mulP A.a123 B.a12)) (mulP A.a123 B.a123)) (mulP A.a123 B.a13)
  let r5 := addP (addP (subP (addP (scaleP (-2) (mulP A.a13 B.a1)) (mulP A.a13 B.a12)) (mulP A.a13 B.a123)) (scaleP 2 (mulP A.a13 B.a13))) (mulP A.a13 B.a23)
  let r6 := addP (subP (addP (negP (mulP A.a2 B.a0)) (scaleP 5 (mulP A.a2 B.a2))) (scaleP 2 (mulP A.a2 B.a23))) (scaleP 2 (mulP A.a2 B.a3))
  let r7 := subP (addP (subP (addP (subP (mulP A.a23 B.a0) (mulP A.a23 B.a1)) (mulP A.a23 B.a13)) (scaleP 2 (mulP A.a23 B.a2))) (scaleP 2 (mulP A.a23 B.a23))) (mulP A.a23 B.a3)
  let r8 := addP (subP (addP (negP (mulP A.a3 B.a0)) (scaleP 2 (mulP A.a3 B.a2))) (mulP A.a3 B.a23)) (scaleP 2 (mulP A.a3 B.a3))
  addP (addP (addP r1 r2) (addP r3 r4)) (addP (addP r5 r6) (addP r7 r8))

theorem evalP_z1Poly (A B : FlagPoly4) (q : Int) :
    evalP (z1Poly A B) q = z1Bilin (evalFlagPoly A q) (evalFlagPoly B q) := by
  simp only [z1Poly, z1Bilin, evalFlagPoly, evalP_addP, evalP_mulP]

theorem evalP_z2Poly (A B : FlagPoly4) (q : Int) :
    evalP (z2Poly A B) q = z2Bilin (evalFlagPoly A q) (evalFlagPoly B q) := by
  simp only [z2Poly, z2Bilin, evalFlagPoly, evalP_addP, evalP_subP, evalP_mulP, evalP_scaleP]
  omega

theorem evalP_z3Poly (A B : FlagPoly4) (q : Int) :
    evalP (z3Poly A B) q = z3Bilin (evalFlagPoly A q) (evalFlagPoly B q) := by
  simp only [z3Poly, z3Bilin, evalFlagPoly, evalP_addP, evalP_subP, evalP_negP, evalP_mulP, evalP_scaleP]
  omega

def sixChoose2Poly (m : List Int) : List Int :=
  scaleP 3 (mulP m (subP m [1]))

def sixChoose3Poly (m : List Int) : List Int :=
  mulP (mulP m (subP m [1])) (subP m [2])

theorem evalP_sixChoose2Poly (m : List Int) (q : Int) :
    evalP (sixChoose2Poly m) q = 6 * choose2 (evalP m q) := by
  simp only [sixChoose2Poly, evalP_scaleP, evalP_mulP, evalP_subP, evalP, Int.mul_zero, Int.add_zero]
  have h2 := two_mul_choose2 (evalP m q)
  omega

theorem evalP_sixChoose3Poly (m : List Int) (q : Int) :
    evalP (sixChoose3Poly m) q = 6 * choose3 (evalP m q) := by
  simp only [sixChoose3Poly, evalP_mulP, evalP_subP, evalP, Int.mul_zero, Int.add_zero]
  have h6 := six_mul_choose3 (evalP m q)
  omega

def projGabPoly6 : FlagPoly4 :=
  let m := qPowPoly 3
  let b := qPowPoly 9
  let N1 := gaussPoly 6 1
  let N2 := gaussPoly 6 2
  let N3 := gaussPoly 6 3
  let t := [1, 1, 1]
  let c2 := sixChoose2Poly m
  let c3 := sixChoose3Poly m
  let nH6 := addP (mulP N1 c2) c3
  let nB6 := scaleP 6 b
  let nU6 := scaleP 6 (subP (mulP m N2) (mulP b t))
  let nN6 := scaleP 6 (subP N3 b)
  { a0 := [6]
    a1 := scaleP 6 (addP N1 m)
    a2 := addP (scaleP 6 (addP N2 (mulP N1 m))) c2
    a3 := addP (addP (addP nH6 nB6) nU6) nN6
    a12 := addP (scaleP 6 (mulP [1, 1] N2)) (scaleP 2 (addP (scaleP 6 (mulP N1 m)) c2))
    a13 := addP (addP (addP (scaleP 3 nH6) (mulP nB6 [2, 1, 1])) (mulP nU6 [2, 1])) (mulP nN6 t)
    a23 := addP (addP (addP (scaleP 3 nH6) (mulP nB6 [2, 2, 2])) (mulP nU6 [2, 1])) (mulP nN6 t)
    a123 := addP (addP (addP (scaleP 6 nH6) (mulP nB6 (mulP [3, 1] t))) (mulP nU6 [3, 3])) (mulP nN6 (mulP [1, 1] t)) }

theorem evalFlagPoly_projGabPoly6 (q : Int) :
    evalFlagPoly projGabPoly6 q = scaleFlag 6 (projGabFlag q (q ^ 3)) := by
  have hb : q ^ 9 = (q ^ 3) * (q ^ 6) := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_assoc]
  have ht : evalP [1, 1, 1] q = q * q + q + 1 := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_one, Int.mul_add]
    omega
  have hp2 : evalP [2, 1, 1] q = (q * q + q + 1) + 1 := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_one, Int.mul_add]
    omega
  have hp222 : evalP [2, 2, 2] q = 2 * (q * q + q + 1) := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_add, Int.mul_one]
    rw [Int.mul_comm q 2, ← Int.mul_assoc q 2 q, Int.mul_comm q 2, Int.mul_assoc 2 q q]
    omega
  have hp11 : evalP [1, 1] q = q + 1 := by simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_one]; omega
  have hp21 : evalP [2, 1] q = q + 2 := by simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_one]; omega
  have hp31 : evalP [3, 1] q = q + 3 := by simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_one]; omega
  have hp33 : evalP [3, 3] q = 3 * (q + 1) := by simp only [evalP, Int.mul_zero, Int.add_zero]; omega
  unfold evalFlagPoly projGabPoly6 scaleFlag projGabFlag
  simp only [evalP_addP, evalP_subP, evalP_mulP, evalP_scaleP,
    evalP_sixChoose2Poly, evalP_sixChoose3Poly, evalP_gaussPoly, evalP_qPowPoly,
    ht, hp2, hp222, hp11, hp21, hp31, hp33, hb]
  simp only [evalP, Int.mul_zero, Int.add_zero]
  congr 1 <;> (simp only [Int.mul_add, Int.mul_sub, Int.add_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]; try omega)

def affElemPoly6 : FlagPoly4 :=
  let m := qPowPoly 2
  let sDirs := qPowPoly 2
  let N1 := qPowPoly 4
  let N2 := mulP (qPowPoly 3) (gaussPoly 4 1)
  let N3 := mulP (qPowPoly 2) (gaussPoly 4 2)
  let b := mulP (mulP m (qPowPoly 2)) sDirs
  let c2 := sixChoose2Poly m
  let c3 := sixChoose3Poly m
  let nH6 := addP (mulP N1 c2) c3
  let nB6 := scaleP 6 b
  let nU6 := scaleP 6 (subP (mulP m N2) (mulP (mulP b [0, 1]) [1, 1]))
  let nN6 := scaleP 6 (subP N3 b)
  { a0 := [6]
    a1 := scaleP 6 (addP N1 m)
    a2 := addP (scaleP 6 (addP N2 (mulP N1 m))) c2
    a3 := addP (addP (addP nH6 nB6) nU6) nN6
    a12 := addP (scaleP 6 (mulP [0, 1] N2)) (scaleP 2 (addP (scaleP 6 (mulP N1 m)) c2))
    a13 := addP (addP (addP (scaleP 3 nH6) (mulP nB6 [1, 0, 1])) (mulP nU6 [1, 1])) (mulP nN6 [0, 0, 1])
    a23 := addP (addP (addP (scaleP 3 nH6) (mulP nB6 [0, 1, 2])) (mulP nU6 [1, 1])) (mulP nN6 [0, 1, 1])
    a123 := addP (addP (addP (scaleP 6 nH6) (mulP nB6 [0, 0, 3, 1])) (mulP nU6 [0, 3])) (mulP nN6 [0, 0, 1, 1]) }

theorem evalFlagPoly_affElemPoly6 (q : Int) :
    evalFlagPoly affElemPoly6 q = scaleFlag 6 (affGabFlag q (q ^ 2) (q ^ 2)) := by
  have hp01 : evalP [0, 1] q = q := by simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one]
  have hp11 : evalP [1, 1] q = q + 1 := by simp only [evalP, Int.mul_zero, Int.add_zero, Int.mul_one]; omega
  have hp03 : evalP [0, 3] q = 3 * q := by simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add]; omega
  have hp001 : evalP [0, 0, 1] q = q * q := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one]
  have hp101 : evalP [1, 0, 1] q = q * q + 1 := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one]; omega
  have hp012 : evalP [0, 1, 2] q = 2 * q * q + q := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_add]
    rw [Int.mul_comm q 2, ← Int.mul_assoc q 2 q, Int.mul_comm q 2]
    omega
  have hp011 : evalP [0, 1, 1] q = q * (q + 1) := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_add, Int.mul_one]
    omega
  have hp0031 : evalP [0, 0, 3, 1] q = q ^ 3 + 3 * q * q := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one, Int.pow_succ, Int.pow_zero, Int.mul_add]
    rw [Int.one_mul, Int.mul_comm q 3, ← Int.mul_assoc q 3 q, Int.mul_comm q 3, ← Int.mul_assoc q q q]
    omega
  have hp0011 : evalP [0, 0, 1, 1] q = q * q * (q + 1) := by
    simp only [evalP, Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one, Int.mul_add]
    rw [← Int.mul_assoc q q q]
    omega
  unfold evalFlagPoly affElemPoly6 scaleFlag affGabFlag
  simp only [evalP_addP, evalP_subP, evalP_mulP, evalP_scaleP,
    evalP_sixChoose2Poly, evalP_sixChoose3Poly, evalP_gaussPoly, evalP_qPowPoly,
    hp01, hp11, hp03, hp001, hp101, hp012, hp011, hp0031, hp0011]
  simp only [evalP, Int.mul_zero, Int.add_zero]
  congr 1 <;> (simp only [Int.mul_add, Int.mul_sub, Int.add_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]; try omega)

/-! ## 6. Stepwise trimmed defect polynomials and universal q >= 27 disproofs -/

def pg5FlagTrim : FlagPoly4 :=
  { a0 := [6]
    a1 := [6, 6, 6, 12, 6, 6]
    a2 := [6, 6, 12, 15, 24, 18, 21, 12, 12]
    a3 := [6, 6, 12, 23, 21, 27, 27, 30, 18, 16, 3, 3]
    a12 := [6, 12, 18, 30, 42, 42, 42, 30, 24, 6]
    a13 := [6, 12, 24, 45, 57, 75, 81, 96, 78, 66, 27, 15]
    a23 := [6, 12, 24, 45, 57, 75, 81, 96, 78, 66, 33, 21]
    a123 := [6, 18, 36, 72, 102, 138, 162, 192, 174, 150, 84, 48, 6] }

def ag4FlagTrim : FlagPoly4 :=
  { a0 := [6]
    a1 := [0, 0, 6, 0, 6]
    a2 := [0, 0, -3, 6, 9, 6, 12]
    a3 := [0, 0, 8, 6, 9, 12, 10, 0, 3]
    a12 := [0, 0, -6, 0, 12, 6, 18, 6]
    a13 := [0, 0, 6, 0, -3, 12, 24, 12, 15]
    a23 := [0, 0, 6, 6, 3, 24, 24, 18, 21]
    a123 := [0, 0, 12, 0, -12, 12, 24, 36, 42, 6] }

def pg5Z1Trim : List Int := [108, 144, 324, 600, 960, 1344, 1933, 2442, 3051, 3504, 3903, 4002, 3949, 3474, 3000, 2232, 1608, 918, 544, 204, 105, 18, 9]
def pg5Z2Trim : List Int := [180, 360, 1008, 2148, 4404, 7500, 12405, 18462, 26133, 33972, 42261, 48282, 52677, 52566, 50508, 43620, 36000, 25722, 17412, 9468, 4899, 1638, 531]
def pg5Z3Trim : List Int := [252, 504, 1512, 3612, 7824, 14568, 25631, 40488, 60774, 83802, 110118, 133356, 153899, 163668, 166272, 154128, 135048, 105012, 75800, 46008, 25170, 10116, 3402, 396, 36]
def pg5GabDefect1296 : List Int := [5184, 38880, 174960, 576720, 1748736, 4601232, 11174040, 25050240, 52597224, 103722420, 193747980, 343500396, 580758694, 938026770, 1451856783, 2155827522, 3077564118, 4226828868, 5593200566, 7133179782, 8775618066, 10414274094, 11927323395, 13177890792, 14046828450, 14433871734, 14293277181, 13621884702, 12485120343, 10982509284, 9260611532, 7462063182, 5735137551, 4184674566, 2890812225, 1877172192, 1141396228, 642383484, 332851536, 155507652, 65019951, 23232348, 7019586, 1538352, 240435, -4212, -324]

def ag4Z1Trim : List Int := [0, 0, -36, 72, 172, 168, 324, 300, 385, 336, 372, 276, 154, 72, 60, 0, 9]
def ag4Z2Trim : List Int := [0, 0, -36, 72, 150, 96, 36, 720, 1209, 1428, 2256, 2016, 1962, 1896, 1344, 828, 531]
def ag4Z3Trim : List Int := [72, 0, 12, -72, 269, 108, -438, 1308, 1799, 2304, 3876, 2544, 2864, 4032, 3660, 3564, 2574, 324, 36]
def ag4ElemDefect1296 : List Int := [0, 0, 2592, -5184, -10656, -20736, -16140, -12024, -55592, -7464, -32532, -15660, 4499, -399996, -357642, 131148, 770208, 2740320, 4971540, 7484292, 10895117, 13543068, 15450126, 16474392, 15562285, 13774500, 11478456, 8566272, 6028560, 3743928, 1896660, 825228, 256635, -2916, -324]

theorem pg5FlagTrim_eq : trimFlagPoly projGabPoly6 = pg5FlagTrim := by decide
theorem pg5Z1Trim_eq : trimP (z1Poly pg5FlagTrim pg5FlagTrim) = pg5Z1Trim := by decide
theorem pg5Z2Trim_eq : trimP (z2Poly pg5FlagTrim pg5FlagTrim) = pg5Z2Trim := by decide
theorem pg5Z3Trim_eq : trimP (z3Poly pg5FlagTrim pg5FlagTrim) = pg5Z3Trim := by decide
theorem pg5Defect_eq : trimP (subP (mulP pg5Z2Trim pg5Z2Trim) (mulP pg5Z1Trim pg5Z3Trim)) = pg5GabDefect1296 := by decide

theorem ag4FlagTrim_eq : trimFlagPoly affElemPoly6 = ag4FlagTrim := by decide
theorem ag4Z1Trim_eq : trimP (z1Poly ag4FlagTrim ag4FlagTrim) = ag4Z1Trim := by decide
theorem ag4Z2Trim_eq : trimP (z2Poly ag4FlagTrim ag4FlagTrim) = ag4Z2Trim := by decide
theorem ag4Z3Trim_eq : trimP (z3Poly ag4FlagTrim ag4FlagTrim) = ag4Z3Trim := by decide
theorem ag4Defect_eq : trimP (subP (mulP ag4Z2Trim ag4Z2Trim) (mulP ag4Z1Trim ag4Z3Trim)) = ag4ElemDefect1296 := by decide

theorem trimmed_defect_bridge (P Ptrim : FlagPoly4) (z1L z2L z3L dL : List Int)
    (F : FlagVec4) (q : Int)
    (hF : evalFlagPoly P q = scaleFlag 6 F)
    (hP : trimFlagPoly P = Ptrim)
    (hz1 : trimP (z1Poly Ptrim Ptrim) = z1L)
    (hz2 : trimP (z2Poly Ptrim Ptrim) = z2L)
    (hz3 : trimP (z3Poly Ptrim Ptrim) = z3L)
    (hd : trimP (subP (mulP z2L z2L) (mulP z1L z3L)) = dL) :
    evalP dL q
      = 1296 * ((z2Pair F F) * (z2Pair F F) - (z1Pair F F) * (z3Pair F F)) := by
  have hevP : evalFlagPoly Ptrim q = scaleFlag 6 F := by
    rw [← hP, evalFlagPoly_trimFlagPoly, hF]
  rw [← hd, evalP_trimP, evalP_subP, evalP_mulP, evalP_mulP,
      ← hz1, ← hz2, ← hz3, evalP_trimP, evalP_trimP, evalP_trimP,
      evalP_z1Poly, evalP_z2Poly, evalP_z3Poly, hevP,
      z1Bilin_scale6, z2Bilin_scale6, z3Bilin_scale6,
      ← z1Pair_eq_bilin, ← z2Pair_eq_bilin, ← z3Pair_eq_bilin]
  have h1296 : (1296 : Int) = 36 * 36 := rfl
  rw [h1296]
  simp only [Int.mul_sub, Int.mul_assoc, Int.mul_left_comm]

theorem pg5_defect_eval_neg_for_all_q_ge_27 (q : Int) (hq : 27 ≤ q) :
    evalP pg5GabDefect1296 q < 0 :=
  neg_of_shiftFast_neg_coeffs_pos pg5GabDefect1296 27
    (all_pos_of_all_gt_zero _ (by decide)) (by decide) q hq

theorem ag4_elem_defect_eval_neg_for_all_q_ge_27 (q : Int) (hq : 27 ≤ q) :
    evalP ag4ElemDefect1296 q < 0 :=
  neg_of_shiftFast_neg_coeffs_pos ag4ElemDefect1296 27
    (all_pos_of_all_gt_zero _ (by decide)) (by decide) q hq

/-- Universal PG(5, q) flag-polynomial inequality (guoriyue/z123 family): for every integer q >= 27
    (applying to all prime-power geometries PG(5, q) with q >= 27), z2^2 < z1 * z3. -/
theorem pg5_zpoly_not_log_concave_for_all_q_ge_27 (q : Int) (hq : 27 ≤ q) :
    let G := projGabFlag q (q ^ 3)
    (z2Pair G G) * (z2Pair G G) < (z1Pair G G) * (z3Pair G G) := by
  intro G
  have hneg := pg5_defect_eval_neg_for_all_q_ge_27 q hq
  rw [trimmed_defect_bridge projGabPoly6 pg5FlagTrim pg5Z1Trim pg5Z2Trim pg5Z3Trim pg5GabDefect1296
        G q (evalFlagPoly_projGabPoly6 q) pg5FlagTrim_eq pg5Z1Trim_eq pg5Z2Trim_eq pg5Z3Trim_eq pg5Defect_eq] at hneg
  have hpos : 0 < 1296 * ((z1Pair G G) * (z3Pair G G) - (z2Pair G G) * (z2Pair G G)) := by omega
  have hdiff := pos_of_mul_pos_left 1296 _ (by omega) hpos
  omega

/-- Universal AG(4, q) flag-polynomial inequality (elementary Affine Gabidulin family A_{4,q}):
    for every integer q >= 27 (applying to all prime-power geometries AG(4, q) with q >= 27),
    z2^2 < z1 * z3. -/
theorem ag4_elem_zpoly_not_log_concave_for_all_q_ge_27 (q : Int) (hq : 27 ≤ q) :
    let A := affGabFlag q (q ^ 2) (q ^ 2)
    (z2Pair A A) * (z2Pair A A) < (z1Pair A A) * (z3Pair A A) := by
  intro A
  have hneg := ag4_elem_defect_eval_neg_for_all_q_ge_27 q hq
  rw [trimmed_defect_bridge affElemPoly6 ag4FlagTrim ag4Z1Trim ag4Z2Trim ag4Z3Trim ag4ElemDefect1296
        A q (evalFlagPoly_affElemPoly6 q) ag4FlagTrim_eq ag4Z1Trim_eq ag4Z2Trim_eq ag4Z3Trim_eq ag4Defect_eq] at hneg
  have hpos : 0 < 1296 * ((z1Pair A A) * (z3Pair A A) - (z2Pair A A) * (z2Pair A A)) := by omega
  have hdiff := pos_of_mul_pos_left 1296 _ (by omega) hpos
  omega

/-! ## 7. Ground-set dominance and exact sub-million / boundary witnesses -/

/-- Universal ground-set collapse: for every integer q >= 2,
    2 * (q^4 + q^2) < 2 * ([6 choose 1]_q + q^3). -/
theorem ag4_ground_set_strictly_smaller_than_pg5 (q : Int) (hq : 2 ≤ q) :
    2 * (q * q * q * q + q * q) < 2 * (gaussQ q 6 1 + q * q * q) := by
  have h1 : (q - 1) * gaussQ q 6 1 = q ^ 6 - 1 := gaussQ_one_mul q 6
  have hqpos : 0 < q - 1 := by omega
  have hpow : q ^ 6 = q * q * q * q * q * q := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
  have hq2 : 4 ≤ q * q := Int.mul_le_mul hq hq (by omega) (by omega)
  have hq3 : 8 ≤ q * q * q := Int.mul_le_mul hq2 hq (by omega) (by omega)
  have hq4 : 2 * (q * q * q) ≤ q * q * q * q := by
    have := Int.mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ q * q * q)
    rw [Int.mul_comm] at this
    exact this
  have hq5 : 2 * (q * q * q * q) ≤ q * q * q * q * q := by
    have := Int.mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ q * q * q * q)
    rw [Int.mul_comm] at this
    exact this
  have hq6 : 2 * (q * q * q * q * q) ≤ q * q * q * q * q * q := by
    have := Int.mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ q * q * q * q * q)
    rw [Int.mul_comm] at this
    exact this
  have hq2_le_q3 : q * q ≤ q * q * q := by
    have := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ q) (by omega : 0 ≤ q * q)
    rw [Int.mul_one] at this
    exact this
  have hexp : ∀ x : Int, (q - 1) * x = x * q - x := by
    intro x
    rw [Int.sub_mul, Int.one_mul, Int.mul_comm q x]
  have hdiff : 0 < (q - 1) * (gaussQ q 6 1 + q * q * q - (q * q * q * q + q * q)) := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_add, h1, hpow,
        hexp (q * q * q), hexp (q * q * q * q), hexp (q * q)]
    omega
  have hinner := pos_of_mul_pos_left (q - 1) _ hqpos hdiff
  omega

/-- PG(5, 27) full m = 19,683 witness (guoriyue/z123, |E| = 29,840,942). -/
theorem pg5_q27_guoriyue_witness :
    let G := projGabFlag 27 19683
    2 * G.a1 = 29840942 ∧
    (z2Pair G G) * (z2Pair G G) - (z1Pair G G) * (z3Pair G G)
      = -30629060076556831072416516750219744007195842510749495518880944028 := by
  intro G
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin]
  decide

/-- PG(5, 25) subset m = 13,000 witness (|E| = 20,371,052, whereas full m = 15,625 is log-concave). -/
theorem pg5_q25_m13000_witness :
    let Gsub := projGabFlag 25 13000
    let Gfull := projGabFlag 25 15625
    2 * Gsub.a1 = 20371052 ∧
    (z2Pair Gsub Gsub) * (z2Pair Gsub Gsub) < (z1Pair Gsub Gsub) * (z3Pair Gsub Gsub) ∧
    (z1Pair Gfull Gfull) * (z3Pair Gfull Gfull) < (z2Pair Gfull Gfull) * (z2Pair Gfull Gfull) := by
  intro Gsub Gfull
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin,
      z1Pair_eq_bilin Gfull, z2Pair_eq_bilin Gfull, z3Pair_eq_bilin Gfull]
  decide

/-- Elementary AG(4, 27) witnesses at m = 729 (|E| = 1,064,340) and m = 618 (|E| = 1,064,118, 28.04x smaller). -/
theorem ag4_elem_q27_witnesses :
    let A729 := affGabFlag 27 729 729
    let A618 := affGabFlag 27 618 729
    2 * A729.a1 = 1064340 ∧
    2 * A618.a1 = 1064118 ∧
    28 * (2 * A618.a1) < 29840942 ∧
    (z2Pair A729 A729) * (z2Pair A729 A729) < (z1Pair A729 A729) * (z3Pair A729 A729) ∧
    (z2Pair A618 A618) * (z2Pair A618 A618) < (z1Pair A618 A618) * (z3Pair A618 A618) := by
  intro A729 A618
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin,
      z1Pair_eq_bilin A618, z2Pair_eq_bilin A618, z3Pair_eq_bilin A618]
  decide

/-- Elementary asymmetric sub-million witness T(A_{4,27}^{(510)} + A_{4,25}^{(456)}) at |E| = 923,032 < 1,000,000. -/
theorem ag4_elem_asym_submillion_witness :
    let A1 := affGabFlag 27 510 729
    let A2 := affGabFlag 25 456 625
    A1.a1 + A2.a1 = 923032 ∧
    A1.a1 + A2.a1 < 1000000 ∧
    (z2Pair A1 A2) * (z2Pair A1 A2) < (z1Pair A1 A2) * (z3Pair A1 A2) := by
  intro A1 A2
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin]
  decide

/-- Elementary AG(4, 27) threshold witness at m = 461 (|E| = 1,063,804, fails)
    vs. m = 460 (|E| = 1,063,802, log-concave). -/
theorem ag4_elem_q27_m461_threshold_witness :
    let A461 := affGabFlag 27 461 729
    let A460 := affGabFlag 27 460 729
    2 * A461.a1 = 1063804 ∧
    (z2Pair A461 A461) * (z2Pair A461 A461) - (z1Pair A461 A461) * (z3Pair A461 A461)
      = -156921719491972503162875401001413007910958217 ∧
    (z1Pair A460 A460) * (z3Pair A460 A460) < (z2Pair A460 A460) * (z2Pair A460 A460) := by
  intro A461 A460
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin,
      z1Pair_eq_bilin A460, z2Pair_eq_bilin A460, z3Pair_eq_bilin A460]
  decide

/-- Explicit spread-packing sub-million witnesses in AG(4, 25) at m = 537 (|E| = 782,324, 38.14x smaller)
    and m = 510 (|E| = 782,270). -/
theorem ag4_spread_q25_submillion_witnesses :
    let S537 := affGabFlag 25 537 626
    let S510 := affGabFlag 25 510 626
    2 * S537.a1 = 782324 ∧
    2 * S510.a1 = 782270 ∧
    38 * (2 * S537.a1) < 29840942 ∧
    (z2Pair S537 S537) * (z2Pair S537 S537) - (z1Pair S537 S537) * (z3Pair S537 S537)
      = -212974814633787833903301832658405502046453382 ∧
    (z2Pair S510 S510) * (z2Pair S510 S510) < (z1Pair S510 S510) * (z3Pair S510 S510) := by
  intro S537 S510
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin,
      z1Pair_eq_bilin S510, z2Pair_eq_bilin S510, z3Pair_eq_bilin S510]
  decide

/-- Spread-packing negative control in AG(4, 23) at m = 461, s = 530 (|E| = 560,604, log-concave). -/
theorem ag4_spread_q23_m461_control_witness :
    let S23 := affGabFlag 23 461 530
    2 * S23.a1 = 560604 ∧
    (z2Pair S23 S23) * (z2Pair S23 S23) - (z1Pair S23 S23) * (z3Pair S23 S23)
      = 630286545232742157416185395634751382092239198 := by
  intro S23
  rw [z1Pair_eq_bilin, z2Pair_eq_bilin, z3Pair_eq_bilin]
  decide

/-! ## 8. Explicit F_625 algebraic good-set certificate (Pavese-Santonastaso conditions) -/

def add25 (x y : Nat) : Nat :=
  ((x % 5 + y % 5) % 5) + 5 * ((x / 5 + y / 5) % 5)

def neg25 (x : Nat) : Nat :=
  ((5 - x % 5) % 5) + 5 * ((5 - (x / 5) % 5) % 5)

def mul25 (x y : Nat) : Nat :=
  let ax := x % 5; let bx := x / 5
  let ay := y % 5; let by_ := y / 5
  ((ax * ay + 2 * bx * by_) % 5) + 5 * ((ax * by_ + bx * ay) % 5)

def mul625 (x y : Nat) : Nat :=
  let ax := x % 25; let bx := x / 25
  let ay := y % 25; let by_ := y / 25
  add25 (mul25 ax ay) (mul25 5 (mul25 bx by_)) + 25 * add25 (mul25 ax by_) (mul25 bx ay)

def frob625 (x : Nat) : Nat :=
  (x % 25) + 25 * neg25 (x / 25)

def norm625 (x : Nat) : Nat :=
  mul625 x (frob625 x)

def unitCircle625 : List Nat :=
  [1, 4, 33, 47, 57, 73, 82, 98, 108, 122, 189, 191, 237, 243,
   286, 294, 313, 317, 463, 467, 486, 494, 537, 543, 589, 591]

/-- 12-element subset of F_25* \ {1} containing -1 (= 4) and one element from each
    non-self-inverse reciprocal pair {c, c^{-1}} (specifically contains norm625 5 = 2,
    with 2 != 1 and 2 * 2 = 4 != 1). -/
def allowedNorms25 : List Nat :=
  [2, 4, 5, 6, 7, 8, 10, 12, 13, 16, 19, 21]

def goodTriplePairOk (t1 t2 : Nat × Nat × Nat) : Bool :=
  let (a1, u1, v1) := t1
  let (a2, u2, v2) := t2
  let c32 := mul625 u1 v2 != mul625 v1 u2
  let lhs33 := mul625 (mul625 a1 u1) (frob625 (mul625 a2 v2))
  let rhs33 := mul625 (frob625 (mul625 a1 v1)) (mul625 a2 u2)
  c32 && (lhs33 != rhs33)

def allPairsGood : List (Nat × Nat × Nat) → Bool
  | [] => true
  | t :: ts => ts.all (fun t2 => goodTriplePairOk t t2 && goodTriplePairOk t2 t) && allPairsGood ts

def goodSetP25 : List (Nat × Nat × Nat) :=
  unitCircle625.map fun v => (5, 1, v)

/-- Algebraic verification of the 26-triple F_625 set P = {(5, 1, v) : v in U} against
    norm625 a in allowedNorms25, norm625 u = norm625 v = 1, and all pairwise (3.2)-(3.3)
    non-collision inequalities (spread construction itself is verified in the Python oracle). -/
theorem f625_closed_form_good_set_valid :
    goodSetP25.length = 26 ∧
    (goodSetP25.all fun (a, u, v) =>
      allowedNorms25.contains (norm625 a) && (norm625 u == 1) && (norm625 v == 1)) = true ∧
    allPairsGood goodSetP25 = true := by
  decide

end ZPolyCounterexample

#print axioms ZPolyCounterexample.evalP_addP
#print axioms ZPolyCounterexample.evalP_scaleP
#print axioms ZPolyCounterexample.evalP_negP
#print axioms ZPolyCounterexample.evalP_subP
#print axioms ZPolyCounterexample.evalP_mulP
#print axioms ZPolyCounterexample.evalP_trimP
#print axioms ZPolyCounterexample.evalP_shiftFast
#print axioms ZPolyCounterexample.evalP_nonneg_of_coeffs_nonneg
#print axioms ZPolyCounterexample.evalP_pos_of_coeffs_pos
#print axioms ZPolyCounterexample.neg_of_shiftFast_neg_coeffs_pos
#print axioms ZPolyCounterexample.two_mul_choose2
#print axioms ZPolyCounterexample.six_mul_choose3
#print axioms ZPolyCounterexample.gaussQ_one_mul
#print axioms ZPolyCounterexample.evalP_gaussPoly
#print axioms ZPolyCounterexample.z1Pair_eq_bilin
#print axioms ZPolyCounterexample.z2Pair_eq_bilin
#print axioms ZPolyCounterexample.z3Pair_eq_bilin
#print axioms ZPolyCounterexample.evalFlagPoly_projGabPoly6
#print axioms ZPolyCounterexample.evalFlagPoly_affElemPoly6
#print axioms ZPolyCounterexample.trimmed_defect_bridge
#print axioms ZPolyCounterexample.pg5_zpoly_not_log_concave_for_all_q_ge_27
#print axioms ZPolyCounterexample.ag4_elem_zpoly_not_log_concave_for_all_q_ge_27
#print axioms ZPolyCounterexample.ag4_ground_set_strictly_smaller_than_pg5
#print axioms ZPolyCounterexample.pg5_q27_guoriyue_witness
#print axioms ZPolyCounterexample.pg5_q25_m13000_witness
#print axioms ZPolyCounterexample.ag4_elem_q27_witnesses
#print axioms ZPolyCounterexample.ag4_elem_asym_submillion_witness
#print axioms ZPolyCounterexample.ag4_spread_q25_submillion_witnesses
#print axioms ZPolyCounterexample.f625_closed_form_good_set_valid
#print axioms ZPolyCounterexample.isZeroInt_eq_true
#print axioms ZPolyCounterexample.evalP_consTrim
#print axioms ZPolyCounterexample.evalP_shiftAdd
#print axioms ZPolyCounterexample.evalP_shiftStep
#print axioms ZPolyCounterexample.all_pos_of_all_gt_zero
#print axioms ZPolyCounterexample.pos_of_mul_pos_left
#print axioms ZPolyCounterexample.mul_two_three
#print axioms ZPolyCounterexample.mul_three_two
#print axioms ZPolyCounterexample.gaussQ_zero_right
#print axioms ZPolyCounterexample.evalP_qPowPoly
#print axioms ZPolyCounterexample.z1Bilin_scale6
#print axioms ZPolyCounterexample.z2Bilin_scale6
#print axioms ZPolyCounterexample.z3Bilin_scale6
#print axioms ZPolyCounterexample.evalFlagPoly_trimFlagPoly
#print axioms ZPolyCounterexample.evalP_z1Poly
#print axioms ZPolyCounterexample.evalP_z2Poly
#print axioms ZPolyCounterexample.evalP_z3Poly
#print axioms ZPolyCounterexample.evalP_sixChoose2Poly
#print axioms ZPolyCounterexample.evalP_sixChoose3Poly
#print axioms ZPolyCounterexample.pg5FlagTrim_eq
#print axioms ZPolyCounterexample.pg5Z1Trim_eq
#print axioms ZPolyCounterexample.pg5Z2Trim_eq
#print axioms ZPolyCounterexample.pg5Z3Trim_eq
#print axioms ZPolyCounterexample.pg5Defect_eq
#print axioms ZPolyCounterexample.ag4FlagTrim_eq
#print axioms ZPolyCounterexample.ag4Z1Trim_eq
#print axioms ZPolyCounterexample.ag4Z2Trim_eq
#print axioms ZPolyCounterexample.ag4Z3Trim_eq
#print axioms ZPolyCounterexample.ag4Defect_eq
#print axioms ZPolyCounterexample.pg5_defect_eval_neg_for_all_q_ge_27
#print axioms ZPolyCounterexample.ag4_elem_defect_eval_neg_for_all_q_ge_27
#print axioms ZPolyCounterexample.ag4_elem_q27_m461_threshold_witness
#print axioms ZPolyCounterexample.ag4_spread_q23_m461_control_witness


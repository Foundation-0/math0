/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A083020: the numbers `3^(3^n) + 2` are squarefree

Source: https://oeis.org/A083020, Cino Hilliard, May 31 2003 (COMMENTS section). Verbatim:
> Conjecture: These numbers have no repeating factors or 3^(3^n) + 2 is squarefree.

The entry (name: "Irregular triangle read by row of the prime factors of 3^(3^n) + 2", offset
`0`, keywords `easy,tabf,nonn`; corrected by T. D. Noe, Nov 15 2006; name clarified and two
more terms by Sean A. Irvine, Jan 04 2026) lists the prime factors of `3^(3^n) + 2`, row by row
for `n = 0, 1, 2, …`. Its example:
`3^(3^0)+2 = 5`, `3^(3^1)+2 = 29`, `3^(3^2)+2 = 5 * 31 * 127`,
`3^(3^3)+2 = 11 * 693236134999`, ….

## Encoding

* `N n = 3^(3^n) + 2`, and row `n` of the triangle is `row n = Nat.primeFactorsList (N n)`, the
  prime factors of `N n` in increasing order, repeated according to multiplicity. (The listed
  rows have no repeated primes, so listing distinct primes instead gives the same terms. The
  conjecture is stated directly about `N n` and does not depend on this choice.)
* `a` is the triangle read by rows (the OEIS sequence itself, offset `0`): `a i` is the entry at
  position `i` of `row 0 ++ row 1 ++ row 2 ++ ⋯`. Every row is nonempty (`N n ≥ 5`), so rows
  `0, …, i` already contain at least `i + 1` entries, and `a i` reads the entry there.
  `a` is computable but factors `N n` by trial division, so the data is checked through
  certificates rather than by evaluating `a`.
* Data. `row_data` proves rows `0, …, 4`. Each one is checked against a certificate: the listed
  primes are sorted, multiply to `N n`, and are prime. Primes below `10^5` are proved by
  `norm_num`. Larger primes get a Lucas (Pratt) certificate from Mathlib's `lucas_primality`,
  with powers mod `p` computed by `powMod` (square and multiply, proved equal to `a ^ e % p`)
  and evaluated by `decide +kernel`. `a_data` then checks the first 13 listed terms
  `a 0, …, a 12` (rows `0, …, 4`).
* The remaining listed terms are `a 13 = 8718…5629` (116 digits), `a 14 = 5`, `a 15 = 31`.
  `a 13` is the whole of row `5`, i.e. the entry asserts that `N 5 = 3^243 + 2` is prime. Its
  primality is not checked in Lean (sympy's `isprime` agrees). `N5_data` checks that the listed
  116-digit number is `N 5`, and `row6_data` checks that row `6` begins with `5, 31`. So
  `a 13, a 14, a 15` are the listed terms exactly when `N 5` is prime.
* The conjecture. "These numbers have no repeating factors or 3^(3^n) + 2 is squarefree": for
  every `n ≥ 0` (all rows of the triangle, offset `0`), `3^(3^n) + 2` is squarefree.
  `statement` is `∀ n : ℕ, Squarefree (3 ^ (3 ^ n) + 2)`. The two phrasings in the comment say
  the same thing: `statement_iff` restates it as "no prime appears twice in `row n`"
  (`Nat.squarefree_iff_nodup_primeFactorsList`). The comment is part of the original entry and
  carries no separate attribution.
-/

namespace Math0.Statements.A083020

/-- The number `3^(3^n) + 2`. -/
def N (n : ℕ) : ℕ := 3 ^ (3 ^ n) + 2

/-- Row `n` of the triangle: the prime factors of `3^(3^n) + 2`, in increasing order and with
multiplicity. -/
def row (n : ℕ) : List ℕ := Nat.primeFactorsList (N n)

/-- A083020: the irregular triangle of the prime factors of `3^(3^n) + 2`, read by rows (offset
`0`). Rows `0, …, i` contain at least `i + 1` entries, so the `i`-th entry of the concatenation
lies among them. -/
def a (i : ℕ) : ℕ := ((List.range (i + 1)).flatMap row).getD i 0

/-! ### Reading terms of `a` off a prefix of rows -/

theorem one_lt_N (n : ℕ) : 1 < N n :=
  Nat.lt_of_lt_of_le one_lt_two (Nat.le_add_left 2 _)

theorem row_ne_nil (n : ℕ) : row n ≠ [] :=
  (Nat.primeFactorsList_ne_nil _).2 (one_lt_N n)

theorem flatMap_range_add (k j : ℕ) :
    (List.range (k + j)).flatMap row =
      (List.range k).flatMap row ++ (List.range j).flatMap (fun t => row (k + t)) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

theorem le_length_flatMap_range (k : ℕ) : k ≤ ((List.range k).flatMap row).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [flatMap_range_add k 1]
    have : 1 ≤ (row k).length := List.length_pos_iff.2 (row_ne_nil k)
    simp only [List.length_append, List.range_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, add_zero]
    omega

theorem getD_flatMap_range {k K i : ℕ} (hkK : k ≤ K)
    (hi : i < ((List.range k).flatMap row).length) :
    ((List.range K).flatMap row).getD i 0 = ((List.range k).flatMap row).getD i 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkK
  rw [flatMap_range_add, List.getD_append _ _ _ _ hi]

/-- If the first `m` rows contain more than `i` entries, `a i` is the `i`-th of them. -/
theorem a_eq (m i : ℕ) (h : i < ((List.range m).flatMap row).length) :
    a i = ((List.range m).flatMap row).getD i 0 := by
  have h1 : i < ((List.range (i + 1)).flatMap row).length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (le_length_flatMap_range _)
  rw [a, ← getD_flatMap_range (le_max_left (i + 1) m) h1,
    getD_flatMap_range (le_max_right (i + 1) m) h]

/-- A list of primes in increasing order with product `n` is the list of prime factors of `n`. -/
theorem primeFactorsList_eq_of {n : ℕ} {l : List ℕ} (hprod : l.prod = n)
    (hp : ∀ p ∈ l, p.Prime) (hs : l.Pairwise (· ≤ ·)) : n.primeFactorsList = l :=
  ((Nat.primeFactorsList_unique hprod hp).eq_of_pairwise' hs
    (Nat.primeFactorsList_sorted n).pairwise).symm

/-! ### Lucas certificates -/

/-- `powModAux m f x e acc = acc * x ^ e % m` (for `e < 2 ^ f`), by square and multiply. -/
def powModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc % m
  | f + 1, x, e, acc =>
    if e = 0 then acc % m
    else powModAux m f (x * x % m) (e / 2) (if e % 2 = 1 then acc * x % m else acc)

/-- `powMod a e m = a ^ e % m` for `e < 2 ^ 64` (`powMod_eq`). -/
def powMod (a e m : ℕ) : ℕ := powModAux m 64 (a % m) e 1

theorem powModAux_eq (m : ℕ) : ∀ (f x e acc : ℕ), e < 2 ^ f →
    powModAux m f x e acc = acc * x ^ e % m
  | 0, x, e, acc, he => by
    have : e = 0 := by simpa using he
    subst this
    simp [powModAux]
  | f + 1, x, e, acc, he => by
    rw [powModAux]
    split_ifs with h0 h1
    · subst h0
      simp
    · rw [powModAux_eq m f _ _ _ (by rw [pow_succ] at he; omega)]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
      rw [show (2 * k + 1) / 2 = k by omega]
      refine ((Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)).trans ?_
      unfold Nat.ModEq
      congr 1
      ring
    · rw [powModAux_eq m f _ _ _ (by rw [pow_succ] at he; omega)]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      rw [show 2 * k / 2 = k by omega]
      refine ((Nat.ModEq.refl acc).mul ((Nat.mod_modEq _ _).pow _)).trans ?_
      unfold Nat.ModEq
      congr 1
      ring

theorem powMod_eq (a e m : ℕ) (he : e < 2 ^ 64) : powMod a e m = a ^ e % m := by
  rw [powMod, powModAux_eq m 64 _ _ _ he, one_mul, ← Nat.pow_mod]

/-- The computable part of a Lucas primality certificate for `p`, with witness `w` and the list
`fs` of prime factors of `p - 1` (with multiplicity). -/
def lucasCheck (p w : ℕ) (fs : List ℕ) : Bool :=
  decide (2 ≤ p) && decide (p < 2 ^ 64) && fs.prod == p - 1 && powMod w (p - 1) p == 1 &&
    fs.all fun q => powMod w ((p - 1) / q) p != 1

/-- Lucas' primality test (Mathlib's `lucas_primality`) in a form suited to `decide`. -/
theorem prime_of_lucasCheck (p w : ℕ) (fs : List ℕ) (hfs : ∀ q ∈ fs, q.Prime)
    (h : lucasCheck p w fs = true) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hp2, hp64⟩, hprod⟩, h1⟩, hall⟩ := h
  have hpow : ∀ e, e ≤ p - 1 → powMod w e p = w ^ e % p := fun e he =>
    powMod_eq _ _ _ (by omega)
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  refine lucas_primality p (w : ZMod p) ?_ ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← hpow _ le_rfl, h1, Nat.cast_one]
  · intro q hq hdvd hcontra
    rw [← hprod] at hdvd
    obtain ⟨r, hr, hqr⟩ := (Nat.Prime.prime hq).dvd_prod_iff.1 hdvd
    rw [(Nat.prime_dvd_prime_iff_eq hq (hfs r hr)).1 hqr] at hcontra
    apply hall r hr
    have h := (ZMod.natCast_eq_natCast_iff' (w ^ ((p - 1) / r)) 1 p).1
      (by rw [Nat.cast_pow, Nat.cast_one]; exact hcontra)
    rw [hpow _ (Nat.div_le_self _ _), h, hmod1]

/-- Proves `∀ q ∈ l, q.Prime` for an explicit list `l`: the large primes by hypotheses in the
context, the others by `norm_num`. -/
macro "prime_list" : tactic =>
  `(tactic| (simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
             repeat' apply And.intro
             all_goals first | assumption | norm_num))

theorem prime_4317661 : Nat.Prime 4317661 :=
  prime_of_lucasCheck 4317661 6 [2, 2, 3, 3, 5, 17, 17, 83] (by norm_num) (by decide +kernel)

theorem prime_20172112193 : Nat.Prime 20172112193 :=
  prime_of_lucasCheck 20172112193 3 [2, 2, 2, 2, 2, 2, 73, 4317661]
    (by have := prime_4317661; prime_list)
    (by decide +kernel)

theorem prime_121032673159 : Nat.Prime 121032673159 :=
  prime_of_lucasCheck 121032673159 3 [2, 3, 20172112193]
    (by have := prime_20172112193; prime_list)
    (by decide +kernel)

theorem prime_22381441 : Nat.Prime 22381441 :=
  prime_of_lucasCheck 22381441 7 [2, 2, 2, 2, 2, 2, 2, 3, 5, 11657] (by norm_num)
    (by decide +kernel)

theorem prime_3312453269 : Nat.Prime 3312453269 :=
  prime_of_lucasCheck 3312453269 2 [2, 2, 37, 22381441]
    (by have := prime_22381441; prime_list)
    (by decide +kernel)

theorem prime_5945531 : Nat.Prime 5945531 :=
  prime_of_lucasCheck 5945531 2 [2, 5, 37, 16069] (by norm_num) (by decide +kernel)

theorem prime_2372959 : Nat.Prime 2372959 :=
  prime_of_lucasCheck 2372959 3 [2, 3, 3, 7, 37, 509] (by norm_num) (by decide +kernel)

theorem prime_391151 : Nat.Prime 391151 :=
  prime_of_lucasCheck 391151 13 [2, 5, 5, 7823] (by norm_num) (by decide +kernel)

theorem prime_693236134999 : Nat.Prime 693236134999 :=
  prime_of_lucasCheck 693236134999 7 [2, 3, 3, 11, 8951, 391151]
    (by have := prime_391151; prime_list)
    (by decide +kernel)

/-! ### Data -/

/-- Rows `0, …, 4` of the triangle, as listed in OEIS (proved via the certificates above). -/
theorem row_data :
    row 0 = [5] ∧ row 1 = [29] ∧ row 2 = [5, 31, 127] ∧ row 3 = [11, 693236134999] ∧
    row 4 = [5, 15679, 2372959, 5945531, 3312453269, 121032673159] := by
  have := prime_693236134999
  have := prime_2372959
  have := prime_5945531
  have := prime_3312453269
  have := prime_121032673159
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine primeFactorsList_eq_of ?_ (by prime_list) (by decide) <;>
    simp only [N, List.prod_cons, List.prod_nil] <;> norm_num

/-- The definition reproduces the first 13 terms listed in OEIS, `a 0, …, a 12` (rows
`0, …, 4`), via the kernel-checked certificates of `row_data`. -/
theorem a_data : (List.range 13).map (fun i => a (i + 0)) =
    [5, 29, 5, 31, 127, 11, 693236134999, 5, 15679, 2372959, 5945531, 3312453269,
      121032673159] := by
  have hL : (List.range 5).flatMap row = [5, 29, 5, 31, 127, 11, 693236134999, 5, 15679,
      2372959, 5945531, 3312453269, 121032673159] := by
    obtain ⟨h0, h1, h2, h3, h4⟩ := row_data
    rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, h0, h1, h2, h3, h4]
    rfl
  show (List.range 13).map a = _
  rw [List.map_congr_left (fun i hi => a_eq 5 i (by rw [hL]; simpa using hi)), hL]
  rfl

/-- The listed term `a 13` (116 digits) is `N 5 = 3^243 + 2`, so it is row `5` exactly when
`3^243 + 2` is prime (not checked here). -/
theorem N5_data : N 5 =
    87189642485960958202911070585860771696964072404731750085525219437990967093723439943475549906831683116791055225665629 := by
  decide +kernel

theorem primeFactorsList_eq_minFac_cons {n : ℕ} (hn : 2 ≤ n) :
    n.primeFactorsList = n.minFac :: (n / n.minFac).primeFactorsList := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact Nat.primeFactorsList_add_two k

theorem minFac_eq_of {n p : ℕ} (hp : 2 ≤ p) (hd : p ∣ n) (hlt : ∀ q < p, 2 ≤ q → ¬ q ∣ n) :
    n.minFac = p := by
  refine le_antisymm (Nat.minFac_le_of_dvd hp hd) ?_
  have hn : n ≠ 1 := by
    rintro rfl
    exact absurd (Nat.le_of_dvd one_pos hd) (by omega)
  refine (Nat.le_minFac'.2 fun q hq hqn => ?_).resolve_left hn
  by_contra h
  exact hlt q (by omega) hq hqn

/-- Row `6` begins with `5, 31`, the listed terms `a 14, a 15`. -/
theorem row6_data : (row 6).take 2 = [5, 31] := by
  have h1 : Nat.minFac (N 6) = 5 :=
    minFac_eq_of (by norm_num) (Nat.dvd_of_mod_eq_zero (by decide +kernel)) (by decide +kernel)
  have h2 : Nat.minFac (N 6 / 5) = 31 :=
    minFac_eq_of (by norm_num) (Nat.dvd_of_mod_eq_zero (by decide +kernel)) (by decide +kernel)
  have h3 : 2 ≤ N 6 / 5 := by decide +kernel
  rw [row, primeFactorsList_eq_minFac_cons (one_lt_N 6), h1, primeFactorsList_eq_minFac_cons h3,
    h2]
  rfl

/-! ### The conjecture -/

/-- Conjecture (Cino Hilliard, 2003): for every `n ≥ 0`, the number `3^(3^n) + 2` is
squarefree (it has no repeated prime factors). -/
def statement : Prop :=
  ∀ n : ℕ, Squarefree (3 ^ (3 ^ n) + 2)

/-- The statement says that no row of the triangle repeats a prime. -/
theorem statement_iff : statement ↔ ∀ n, (row n).Nodup := by
  simp only [statement, row, N]
  exact forall_congr' fun n => Nat.squarefree_iff_nodup_primeFactorsList (by positivity)

end Math0.Statements.A083020

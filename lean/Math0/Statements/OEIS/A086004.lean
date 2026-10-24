/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A086004: there are no 5-Rotation Cycle Primes

Source: https://oeis.org/A086004, Chuck Seggelin, Jul 07 2003 (COMMENTS section). Verbatim:
> Conjecture 2: There are no 5-Rotation Cycle Primes.

The entry's name: "Primes which remain prime after one and after two and after three
applications of the rotate-and-add operation of A086002." Offset `1`; the listed data start
`12917, 12919, 18911, 18913, 22907, 24907, 26903, 28901, 1088063, …`. The comments just before
the conjecture say "Note: Have not yet found any 4-Rotation Cycle Primes.", and a later comment
by Chai Wah Wu (Aug 20 2015) says "4-Rotation Cycle Primes exist and are listed in A261458",
where A261458 is "Primes which remain prime after one, two, three and four applications of the
rotate-and-add operation of A086002". So a *`k`-Rotation Cycle Prime* is a prime that remains
prime after each of `1, 2, …, k` applications of rotate-and-add, and A086004 lists the
3-Rotation Cycle Primes. (Conjecture 1 of the entry, about even digit counts, was proved by
R. J. Mathar in 2009; it is not formalized here.)

## Encoding

* *Rotation* (A086002): "Let rotation rot(k) of a number k be defined by swapping the blocks of
  the first [d/2] and of the last [d/2] digits of k, where d=A055642(k). If the number of digits
  in k is odd, the center digit remains untouched during rotation." (e.g. `1234 ↦ 3412`,
  `12345 ↦ 45312`). `rot` encodes this with R. J. Mathar's Maple program from A086002: with
  `d = (Nat.digits 10 n).length` the number of decimal digits, `l = ⌊d/2⌋` and `h = ⌈d/2⌉`,
  `rot n = (n mod 10^l)·10^h + (middle digit)·10^l + ⌊n / 10^h⌋`, where the middle term is
  `⌊n / 10^l⌋ mod 10^(h-l)`, i.e. the centre digit for odd `d` and `0` for even `d`.
  `rotDigits` is the same operation written directly on the digit list (last block, centre
  digit if any, first block), and `rot_eq_rotDigits_data` kernel-checks that the two agree on
  all `n < 2000` and on the numbers occurring in the OEIS examples. (`A055642(0) = 1` while
  `Nat.digits 10 0 = []`, but both give `rot 0 = 0`.)
* *Rotate-and-add* is `rotAdd n = n + rot n`, and `rotAdd^[j]` is its `j`-th iterate.
* `IsRotationCyclePrime k p`: `p` is prime and `rotAdd^[j] p` is prime for every
  `j = 1, …, k`.
* The sequence: `a n = Nat.nth (IsRotationCyclePrime 3) (n - 1)` (offset `1`). It is not known
  whether there are infinitely many terms, so `a` is defined with `Nat.nth` and is
  noncomputable. `a_data` checks the first 13 listed terms `a 1, …, a 13` (all listed terms
  below `10^8`). It rests on `term_iff`: below `1530000` the 3-Rotation Cycle Primes are exactly
  these 13 numbers. That is proved by kernel scans (`decide +kernel`) with kernel-friendly
  helpers that are proved equal to, or sound for, the definitions: `fK_eq` (rotate-and-add),
  `primeK_iff` (trial division), `sm_of_prime` (coprime to the primes below `1000`), and
  `term3_iff`. Three elementary facts shrink the scan, and each is proved here: a number
  `≥ 10` ending in `0, 2, 4, 5, 6, 8` is not prime; for `4`- and `6`-digit `q`,
  `rotAdd q = (10^k + 1)·(⌊q/10^k⌋ + q mod 10^k)` is composite (R. J. Mathar's comment); and
  for odd `q` with `2m + 1 ∈ {5, 7}` digits and `⌊q/10^(m+1)⌋` odd, `rotAdd q` is even (Chai Wah
  Wu's comment in A086002). The 14th listed term, `100083679`, would need a scan up to `10^8`.
* The conjecture: for every `p`, `¬ IsRotationCyclePrime 5 p`. There is no prime `p` such that
  `rotAdd^[j] p` is prime for each `j = 1, 2, 3, 4, 5`.
-/

namespace Math0.Statements.A086004

/-! ### The rotate-and-add operation -/

/-- The rotation of A086002: with `d` the number of decimal digits of `n`, swap the block of the
first `⌊d/2⌋` digits with the block of the last `⌊d/2⌋` digits; if `d` is odd the centre digit
stays in place. (R. J. Mathar's formula from A086002, with `l = ⌊d/2⌋`, `h = ⌈d/2⌉`.) -/
def rot (n : ℕ) : ℕ :=
  let d := (Nat.digits 10 n).length
  let l := d / 2
  let h := d - l
  n % 10 ^ l * 10 ^ h + n / 10 ^ l % 10 ^ (h - l) * 10 ^ l + n / 10 ^ h

/-- The same rotation on the digit list, most significant digit first: the last `⌊d/2⌋` digits,
then the centre digit (present only for odd `d`), then the first `⌊d/2⌋` digits. -/
def rotDigits (n : ℕ) : ℕ :=
  let ds := (Nat.digits 10 n).reverse
  let d := ds.length
  let l := d / 2
  Nat.ofDigits 10 (ds.drop (d - l) ++ (ds.drop l).take (d - 2 * l) ++ ds.take l).reverse

/-- The rotate-and-add operation of A086002: `k ↦ k + rot k`. -/
def rotAdd (n : ℕ) : ℕ := n + rot n

/-- `p` is a `k`-Rotation Cycle Prime: `p` is prime and remains prime after each of `1, …, k`
applications of rotate-and-add. -/
def IsRotationCyclePrime (k p : ℕ) : Prop :=
  p.Prime ∧ ∀ j, 1 ≤ j → j ≤ k → (rotAdd^[j] p).Prime

/-- A086004 (offset `1`): the `n`-th prime which remains prime after one, two and three
applications of rotate-and-add, i.e. the `n`-th 3-Rotation Cycle Prime. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (IsRotationCyclePrime 3) (n - 1)

/-- The examples of A086002 (`rot 1234 = 3412`, `rot 12345 = 45312`), the rotate-and-add chain
`12917 ↦ 30829 ↦ 60659 ↦ 120319` of the A086003/A086004 examples, and the chain
`10010905789 ↦ 15800815799 ↦ 31600631599 ↦ 63200263199 ↦ 126399526399` of the A261458 example
(the first listed 4-Rotation Cycle Prime). -/
theorem rot_examples :
    rot 1234 = 3412 ∧ rot 12345 = 45312 ∧ rot 12917 = 17912 ∧ rot 30829 = 29830 ∧
      rotAdd 12917 = 30829 ∧ rotAdd 30829 = 60659 ∧ rotAdd 60659 = 120319 ∧
      rotAdd 10010905789 = 15800815799 ∧ rotAdd 15800815799 = 31600631599 ∧
      rotAdd 31600631599 = 63200263199 ∧ rotAdd 63200263199 = 126399526399 := by
  decide +kernel

/-- The arithmetic `rot` agrees with the digit-list `rotDigits` on all `n < 2000` and on the
numbers of the OEIS examples. -/
theorem rot_eq_rotDigits_data :
    (∀ n < 2000, rot n = rotDigits n) ∧
      [12345, 12917, 30829, 60659, 120319, 1528019, 10010905789].all
        (fun n => rot n == rotDigits n) = true := by
  decide +kernel


/-! ### Kernel-friendly evaluation (used only for the data check)

The functions below are written with the recursors `Nat.rec`, `Bool.rec`, `List.rec` and the
primitive operations `Nat.add`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.beq`, `Nat.blt`,
which the kernel evaluates directly on numerals. Each one is proved equal to (or sound for) the
definitions above. -/

/-- `x && y`, written with the recursor. -/
def andK (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

/-- `x || y`, written with the recursor. -/
def orK (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x

/-- `!x`, written with the recursor. -/
def notK (x : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false x

theorem andK_eq (x y : Bool) : andK x y = (x && y) := by cases x <;> rfl

theorem orK_eq (x y : Bool) : orK x y = (x || y) := by cases x <;> rfl

theorem notK_eq (x : Bool) : notK x = !x := by cases x <;> rfl

theorem blt_eq_decide (x y : ℕ) : Nat.blt x y = decide (x < y) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem ble_eq_decide (x y : ℕ) : Nat.ble x y = decide (x ≤ y) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

theorem beq_eq_decide (x y : ℕ) : Nat.beq x y = decide (x = y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

/-- Number of decimal digits of `n` (correct when `n < 10 ^ fuel`, see `nd_eq`). -/
def nd (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih n => Bool.rec (motive := fun _ => ℕ) (Nat.succ (ih (Nat.div n 10))) 0 (Nat.beq n 0))
    fuel

theorem nd_eq : ∀ fuel n, n < 10 ^ fuel → nd fuel n = (Nat.digits 10 n).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by simpa using hn
    rfl
  | succ fuel ih =>
    intro n hn
    cases h : Nat.beq n 0
    · have h0 : n ≠ 0 := by
        rintro rfl
        exact absurd h (by decide)
      have e : nd (fuel + 1) n = Nat.succ (nd fuel (n / 10)) := by
        show Bool.rec (motive := fun _ => ℕ) (Nat.succ (nd fuel (n / 10))) 0 (Nat.beq n 0) = _
        rw [h]
      rw [e, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0), List.length_cons,
        ih (n / 10) (by rw [pow_succ] at hn; omega)]
    · have h0 : n = 0 := Nat.eq_of_beq_eq_true h
      subst h0
      rfl

/-- `rot`, given `l = ⌊d/2⌋` and `h = ⌈d/2⌉`. -/
def rotLH (n l h : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul (Nat.mod n (Nat.pow 10 l)) (Nat.pow 10 h))
    (Nat.mul (Nat.mod (Nat.div n (Nat.pow 10 l)) (Nat.pow 10 (Nat.sub h l))) (Nat.pow 10 l)))
    (Nat.div n (Nat.pow 10 h))

/-- `rot`, given the number `d` of digits. -/
def rotD (n d : ℕ) : ℕ := rotLH n (Nat.div d 2) (Nat.sub d (Nat.div d 2))

/-- `rotAdd`, kernel-friendly. -/
def fK (n : ℕ) : ℕ := Nat.add n (rotD n (nd n n))

theorem fK_eq (n : ℕ) : fK n = rotAdd n := by
  have h := nd_eq n n (Nat.lt_pow_self (by norm_num))
  unfold fK rotAdd rot
  rw [h]
  rfl

/-- Trial division of `n` by `d, d + 2, d + 4, …` while the square of the divisor is at most
`n`, with `fuel`. -/
def trialK (n : ℕ) (fuel : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih d => orK (Nat.blt n (Nat.mul d d))
      (andK (notK (Nat.beq (Nat.mod n d) 0)) (ih (Nat.add d 2)))) fuel

theorem trialK_succ (n fuel d : ℕ) : trialK n (fuel + 1) d =
    (decide (n < d * d) || (!decide (n % d = 0) && trialK n fuel (d + 2))) := by
  show orK (Nat.blt n (d * d)) (andK (notK (Nat.beq (n % d) 0)) (trialK n fuel (d + 2))) = _
  rw [orK_eq, andK_eq, notK_eq, blt_eq_decide, beq_eq_decide]

theorem trialK_sound : ∀ fuel d n, trialK n fuel d = true →
    ∀ m, d ≤ m → m < d + 2 * fuel → m % 2 = d % 2 → m * m ≤ n → n % m ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro d n _ m h1 h2; omega
  | succ fuel ih =>
    intro d n h m h1 h2 h3 h4
    rw [trialK_succ] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    rcases h with hlt | h
    · have : d * d ≤ m * m := Nat.mul_le_mul h1 h1
      omega
    · rcases Nat.eq_or_lt_of_le h1 with e | e
      · exact e ▸ h.1
      · exact ih (d + 2) n h.2 m (by omega) (by omega) (by omega) h4

theorem trialK_complete : ∀ fuel d n, (∀ m, d ≤ m → m * m ≤ n → n % m ≠ 0) →
    trialK n fuel d = true := by
  intro fuel
  induction fuel with
  | zero => intro d n _; rfl
  | succ fuel ih =>
    intro d n h
    rw [trialK_succ]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · exact Or.inr ⟨h d le_rfl (by omega), ih (d + 2) n fun m hm hmn => h m (by omega) hmn⟩

/-- Primality by trial division. -/
def primeK (n : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (andK (notK (Nat.beq (Nat.mod n 2) 0)) (trialK n n 3))
    (Nat.ble 2 n) (Nat.blt n 4)

theorem primeK_iff (n : ℕ) : primeK n = true ↔ n.Prime := by
  by_cases h4 : n < 4
  · have e : primeK n = Nat.ble 2 n := by
      unfold primeK
      rw [blt_eq_decide, decide_eq_true h4]
    rw [e, ble_eq_decide, decide_eq_true_iff]
    constructor
    · intro h2
      interval_cases n <;> norm_num
    · exact fun hp => hp.two_le
  · have e : primeK n = (!decide (n % 2 = 0) && trialK n n 3) := by
      unfold primeK
      rw [blt_eq_decide, decide_eq_false h4]
      show andK (notK (Nat.beq (n % 2) 0)) (trialK n n 3) = _
      rw [andK_eq, notK_eq, beq_eq_decide]
    rw [e]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨hodd, ht⟩
      by_contra hp
      have hn0 : 0 < n := by omega
      have hn1 : n ≠ 1 := by omega
      set q := n.minFac with hq
      have hqp : q.Prime := Nat.minFac_prime hn1
      have hqd : q ∣ n := Nat.minFac_dvd n
      have hsq : q ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hp
      have hqn : q ≤ n := Nat.le_of_dvd hn0 hqd
      have hq2 : q % 2 = 1 := by
        rcases hqp.eq_two_or_odd with e | e
        · rw [e] at hqd
          exact absurd (Nat.mod_eq_zero_of_dvd hqd) hodd
        · exact e
      have hq3 : 3 ≤ q := by
        have := hqp.two_le
        omega
      exact trialK_sound n 3 n ht q hq3 (by omega) (by omega) (by nlinarith)
        (Nat.mod_eq_zero_of_dvd hqd)
    · intro hp
      refine ⟨?_, trialK_complete n 3 n fun m hm hmn hmod => ?_⟩
      · intro h2
        rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h2) with e | e <;> omega
      · rcases hp.eq_one_or_self_of_dvd m (Nat.dvd_of_mod_eq_zero hmod) with e | e
        · omega
        · subst e
          nlinarith

/-- The primes below `1000`. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
    809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

theorem smallPrimes_spec : ∀ p ∈ smallPrimes, p.Prime ∧ p < 1000 := by
  have h : ∀ p ∈ smallPrimes, primeK p = true ∧ p < 1000 := by decide +kernel
  intro p hp
  exact ⟨(primeK_iff p).1 (h p hp).1, (h p hp).2⟩

/-- A cheap necessary condition for primality: `n < 1000`, or `n` is coprime to the product of
the primes below `1000` (one `Nat.gcd`, which the kernel evaluates directly). -/
def sm (n : ℕ) : Bool := orK (Nat.blt n 1000) (Nat.beq (Nat.gcd n smallPrimes.prod) 1)

theorem sm_of_prime {n : ℕ} (hn : n.Prime) : sm n = true := by
  unfold sm
  rw [orK_eq, blt_eq_decide, beq_eq_decide]
  by_cases h : n < 1000
  · simp [h]
  · have hc : Nat.Coprime n smallPrimes.prod := Nat.coprime_list_prod_right_iff.2 fun p hp =>
      (Nat.coprime_primes hn (smallPrimes_spec p hp).1).2
        (by have := (smallPrimes_spec p hp).2; omega)
    have hg : Nat.gcd n smallPrimes.prod = 1 := hc
    simp [hg]

/-- Decides `IsRotationCyclePrime 3 q` (see `term3_iff`): `q`, `q₁ = rotAdd q`,
`q₂ = rotAdd q₁`, `q₃ = rotAdd q₂` are prime; the cheap tests come first. -/
def term3c (q q1 q2 q3 : ℕ) : Bool :=
  andK (sm q3) (andK (primeK q) (andK (primeK q1) (andK (primeK q2) (primeK q3))))

/-- See `term3c`. -/
def term3b (q q1 q2 : ℕ) : Bool := andK (sm q2) (term3c q q1 q2 (fK q2))

/-- See `term3c`. -/
def term3a (q q1 : ℕ) : Bool := andK (sm q1) (term3b q q1 (fK q1))

/-- See `term3c`. -/
def term3 (q : ℕ) : Bool := andK (sm q) (term3a q (fK q))

theorem isRotationCyclePrime_three_iff (q : ℕ) : IsRotationCyclePrime 3 q ↔
    q.Prime ∧ (rotAdd q).Prime ∧ (rotAdd (rotAdd q)).Prime ∧
      (rotAdd (rotAdd (rotAdd q))).Prime := by
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, h 1 le_rfl (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) le_rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨h0, fun j hj1 hj3 => ?_⟩
    interval_cases j
    · exact h1
    · exact h2
    · exact h3

theorem term3_iff (q : ℕ) : term3 q = true ↔ IsRotationCyclePrime 3 q := by
  rw [isRotationCyclePrime_three_iff]
  simp only [term3, term3a, term3b, term3c, andK_eq, Bool.and_eq_true, primeK_iff, fK_eq]
  constructor
  · rintro ⟨-, -, -, -, h0, h1, h2, h3⟩
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨sm_of_prime h0, sm_of_prime h1, sm_of_prime h2, sm_of_prime h3, h0, h1, h2, h3⟩

instance : DecidablePred (IsRotationCyclePrime 3) :=
  fun q => decidable_of_iff _ (term3_iff q)

/-! ### Scanning -/

/-- The terms listed in OEIS below `10 ^ 8`. -/
def listed : List ℕ :=
  [12917, 12919, 18911, 18913, 22907, 24907, 26903, 28901, 1088063, 1288043, 1408031, 1428029,
    1528019]

/-- `check q = true` iff (`q` is a 3-Rotation Cycle Prime `→ q ∈ listed`). -/
def check (q : ℕ) : Bool := orK (notK (term3 q)) (decide (q ∈ listed))

theorem check_sound {q : ℕ} (h : check q = true) (hq : IsRotationCyclePrime 3 q) :
    q ∈ listed := by
  rw [check, orK_eq, notK_eq, (term3_iff q).2 hq] at h
  simpa using h

/-- `checkAll s len = true` iff `check q` for every `q ∈ [s, s + len)`. -/
def checkAll (s : ℕ) (len : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andK (check (Nat.add s k)) ih) len

theorem checkAll_sound (s : ℕ) : ∀ len, checkAll s len = true →
    ∀ k < len, check (s + k) = true := by
  intro len
  induction len with
  | zero => intro _ k hk; omega
  | succ len ih =>
    intro h k hk
    have h' : andK (check (s + len)) (checkAll s len) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact ih h'.2 k hk
    · subst hk
      exact h'.1

/-- `check` at `b + 1`, `b + 3`, `b + 7`, `b + 9`. -/
def check4 (b : ℕ) : Bool :=
  andK (check (Nat.add b 1))
    (andK (check (Nat.add b 3)) (andK (check (Nat.add b 7)) (check (Nat.add b 9))))

theorem check4_sound {b : ℕ} (h : check4 b = true) :
    ∀ r, (r = 1 ∨ r = 3 ∨ r = 7 ∨ r = 9) → check (b + r) = true := by
  have h' : (check (b + 1) && (check (b + 3) && (check (b + 7) && check (b + 9)))) = true := by
    rw [← andK_eq, ← andK_eq, ← andK_eq]
    exact h
  simp only [Bool.and_eq_true] at h'
  rintro r (rfl | rfl | rfl | rfl)
  · exact h'.1
  · exact h'.2.1
  · exact h'.2.2.1
  · exact h'.2.2.2

/-- `inner c nt = true` iff `check4 (c + 10 t)` for every `t < nt`. -/
def inner (c nt : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andK (check4 (Nat.add c (Nat.mul 10 t))) ih) nt

theorem inner_sound (c : ℕ) : ∀ nt, inner c nt = true → ∀ t < nt, check4 (c + 10 * t) = true := by
  intro nt
  induction nt with
  | zero => intro _ t ht; omega
  | succ nt ih =>
    intro h t ht
    have h' : andK (check4 (c + 10 * nt)) (inner c nt) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · exact ih h'.2 t ht
    · subst ht
      exact h'.1

/-- `outer A₀ nA W nt = true` iff `inner ((A₀ + 2 j) * W) nt` for every `j < nA`. -/
def outer (A0 nA W nt : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => andK (inner (Nat.mul (Nat.add A0 (Nat.mul 2 j)) W) nt) ih) nA

theorem outer_sound (A0 W nt : ℕ) : ∀ nA, outer A0 nA W nt = true →
    ∀ j < nA, inner ((A0 + 2 * j) * W) nt = true := by
  intro nA
  induction nA with
  | zero => intro _ j hj; omega
  | succ nA ih =>
    intro h j hj
    have h' : andK (inner ((A0 + 2 * nA) * W) nt) (outer A0 nA W nt) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact ih h'.2 j hj
    · subst hj
      exact h'.1

/-! ### Facts that cut down the scan -/

theorem length_digits_eq {q k : ℕ} (h1 : 10 ^ k ≤ q) (h2 : q < 10 ^ (k + 1)) :
    (Nat.digits 10 q).length = k + 1 := by
  have a := (Nat.digits_length_le_iff (b := 10) (k := k + 1) (by norm_num) q).2 h2
  have b := mt (Nat.digits_length_le_iff (b := 10) (k := k) (by norm_num) q).1 (not_lt.2 h1)
  omega

/-- A number `q ≥ 10` whose last digit is not `1`, `3`, `7` or `9` is not prime. -/
theorem not_prime_of_last_digit {q : ℕ} (hq : 10 ≤ q)
    (h : ¬ (q % 10 = 1 ∨ q % 10 = 3 ∨ q % 10 = 7 ∨ q % 10 = 9)) : ¬ q.Prime := by
  intro hp
  rcases (by omega : q % 2 = 0 ∨ q % 5 = 0) with h2 | h5
  · rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h2) with e | e <;> omega
  · rcases hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h5) with e | e <;> omega

/-- (R. J. Mathar, in A086004.) For a `4`-digit `q`, `rotAdd q = 101 · (⌊q/100⌋ + q mod 100)`
is not prime. -/
theorem not_prime_rotAdd_four {q : ℕ} (h1 : 1000 ≤ q) (h2 : q < 10000) :
    ¬ (rotAdd q).Prime := by
  have hlen : (Nat.digits 10 q).length = 4 :=
    length_digits_eq (k := 3) (by norm_num; omega) (by norm_num; omega)
  have hr : rotAdd q = 101 * (q / 100 + q % 100) := by
    unfold rotAdd rot
    simp only [hlen]
    norm_num
    omega
  rw [hr]
  exact Nat.not_prime_mul (by norm_num) (by omega)

/-- (R. J. Mathar, in A086004.) For a `6`-digit `q`,
`rotAdd q = 1001 · (⌊q/1000⌋ + q mod 1000)` is not prime. -/
theorem not_prime_rotAdd_six {q : ℕ} (h1 : 100000 ≤ q) (h2 : q < 1000000) :
    ¬ (rotAdd q).Prime := by
  have hlen : (Nat.digits 10 q).length = 6 :=
    length_digits_eq (k := 5) (by norm_num; omega) (by norm_num; omega)
  have hr : rotAdd q = 1001 * (q / 1000 + q % 1000) := by
    unfold rotAdd rot
    simp only [hlen]
    norm_num
    omega
  rw [hr]
  exact Nat.not_prime_mul (by norm_num) (by omega)

/-- (C. W. Wu, in A086002.) For an odd `5`-digit `q` with `⌊q/1000⌋` odd, `rotAdd q` is even,
so not prime. -/
theorem not_prime_rotAdd_five {q : ℕ} (h1 : 10000 ≤ q) (h2 : q < 100000) (hq : q % 2 = 1)
    (hA : q / 1000 % 2 = 1) : ¬ (rotAdd q).Prime := by
  have hlen : (Nat.digits 10 q).length = 5 :=
    length_digits_eq (k := 4) (by norm_num; omega) (by norm_num; omega)
  have hr : rotAdd q = q + (q % 100 * 1000 + q / 100 % 10 * 100 + q / 1000) := by
    unfold rotAdd rot
    simp only [hlen]
    norm_num
  intro hp
  rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by rw [hr]; omega)) with e | e
  · omega
  · rw [hr] at e
    omega

/-- (C. W. Wu, in A086002.) For an odd `7`-digit `q` with `⌊q/10⁴⌋` odd, `rotAdd q` is even,
so not prime. -/
theorem not_prime_rotAdd_seven {q : ℕ} (h1 : 1000000 ≤ q) (h2 : q < 10000000) (hq : q % 2 = 1)
    (hA : q / 10000 % 2 = 1) : ¬ (rotAdd q).Prime := by
  have hlen : (Nat.digits 10 q).length = 7 :=
    length_digits_eq (k := 6) (by norm_num; omega) (by norm_num; omega)
  have hr : rotAdd q = q + (q % 1000 * 10000 + q / 1000 % 10 * 1000 + q / 10000) := by
    unfold rotAdd rot
    simp only [hlen]
    norm_num
  intro hp
  rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by rw [hr]; omega)) with e | e
  · omega
  · rw [hr] at e
    omega

theorem rotAdd_prime_of {q : ℕ} (hq : IsRotationCyclePrime 3 q) : (rotAdd q).Prime :=
  hq.2 1 le_rfl (by norm_num)

/-! ### The kernel scans -/

/-- All `q < 1000`. -/
theorem scan_small : checkAll 0 1000 = true := by decide +kernel

/-- The `5`-digit `q = A · 1000 + B` with `A` even and last digit `1`, `3`, `7` or `9`. -/
theorem scan_five : outer 10 45 1000 100 = true := by decide +kernel

/-- The `7`-digit `q = A · 10⁴ + B` with `A ∈ {100, 102, …, 126}` and last digit `1`, `3`, `7` or
`9`. -/
theorem scan_seven_1 : outer 100 14 10000 1000 = true := by decide +kernel

/-- The `7`-digit `q = A · 10⁴ + B` with `A ∈ {128, 130, …, 152}` and last digit `1`, `3`, `7` or
`9`. -/
theorem scan_seven_2 : outer 128 13 10000 1000 = true := by decide +kernel

/-- From an `outer` scan to the numbers it covers. -/
theorem of_outer {A0 nA W q : ℕ} (hscan : outer A0 nA W (W / 10) = true) (hW : W % 10 = 0)
    (hlo : A0 * W ≤ q) (hhi : q < (A0 + 2 * nA) * W) (hA : (q / W - A0) % 2 = 0)
    (hr : q % 10 = 1 ∨ q % 10 = 3 ∨ q % 10 = 7 ∨ q % 10 = 9) (hW0 : 0 < W) :
    check q = true := by
  have hqA : A0 ≤ q / W := (Nat.le_div_iff_mul_le hW0).2 hlo
  have hqB : q / W < A0 + 2 * nA := (Nat.div_lt_iff_lt_mul hW0).2 hhi
  set j := (q / W - A0) / 2 with hj
  have hj' : j < nA := by omega
  have hin := outer_sound A0 W (W / 10) nA hscan j hj'
  have ht : q % W / 10 < W / 10 := by
    have := Nat.mod_lt q hW0
    omega
  have h4 := inner_sound _ _ hin (q % W / 10) ht
  have e : q = (A0 + 2 * j) * W + 10 * (q % W / 10) + q % 10 := by
    have e1 : A0 + 2 * j = q / W := by omega
    rw [e1]
    have e2 := Nat.div_add_mod q W
    have e3 : q % W % 10 = q % 10 := by
      obtain ⟨c, hc⟩ : 10 ∣ W := Nat.dvd_of_mod_eq_zero hW
      rw [hc, Nat.mod_mul_right_mod]
    have e4 := Nat.div_add_mod (q % W) 10
    rw [mul_comm (q / W) W]
    omega
  rw [e]
  exact check4_sound h4 _ hr

/-- Below `1530000`, the 3-Rotation Cycle Primes are exactly the listed ones. -/
theorem term_iff {q : ℕ} (hq : q < 1530000) : IsRotationCyclePrime 3 q ↔ q ∈ listed := by
  constructor
  · intro hP
    have hp := hP.1
    have h1 := rotAdd_prime_of hP
    by_cases hs : q < 1000
    · have hc := checkAll_sound 0 1000 scan_small q hs
      rw [zero_add] at hc
      exact check_sound hc hP
    by_cases h4 : q < 10000
    · exact absurd h1 (not_prime_rotAdd_four (by omega) h4)
    have hr : q % 10 = 1 ∨ q % 10 = 3 ∨ q % 10 = 7 ∨ q % 10 = 9 := by
      by_contra h
      exact not_prime_of_last_digit (by omega) h hp
    by_cases h5 : q < 100000
    · by_cases hA : q / 1000 % 2 = 0
      · exact check_sound (of_outer scan_five (by norm_num) (by omega) (by omega) (by omega) hr
          (by norm_num)) hP
      · exact absurd h1 (not_prime_rotAdd_five (by omega) h5 (by omega) (by omega))
    by_cases h6 : q < 1000000
    · exact absurd h1 (not_prime_rotAdd_six (by omega) h6)
    by_cases hA : q / 10000 % 2 = 0
    · refine check_sound ?_ hP
      by_cases c1 : q < 1280000
      · exact of_outer scan_seven_1 (by norm_num) (by omega) (by omega) (by omega) hr (by norm_num)
      · exact of_outer scan_seven_2 (by norm_num) (by omega) (by omega) (by omega) hr (by norm_num)
    · exact absurd h1 (not_prime_rotAdd_seven (by omega) (by omega) (by omega) (by omega))
  · intro hq
    have hall : listed.all term3 = true := by decide +kernel
    rw [List.all_eq_true] at hall
    exact (term3_iff q).1 (hall q hq)

theorem count_eq {n : ℕ} (hn : n ≤ 1530000) :
    Nat.count (IsRotationCyclePrime 3) n = (listed.toFinset.filter (· < n)).card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(term_iff (by omega)).1 h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (term_iff (by omega)).2 h1⟩

/-- The definition reproduces the first 13 terms listed in OEIS, `a 1, …, a 13` (all listed
terms below `10^8`; kernel-checked, see `term_iff`). -/
theorem a_data : (List.range 13).map (fun i => a (i + 1)) =
    [12917, 12919, 18911, 18913, 22907, 24907, 26903, 28901, 1088063, 1288043, 1408031,
      1428029, 1528019] := by
  have hcard : ∀ i < 13, (listed.toFinset.filter (· < listed.getD i 0)).card = i := by
    decide +kernel
  have hlt : ∀ i < 13, listed.getD i 0 < 1530000 := by decide +kernel
  have hmem : ∀ i < 13, listed.getD i 0 ∈ listed := by decide +kernel
  show _ = listed
  apply List.ext_getElem (by simp [listed])
  intro i h1 h2
  have hi : i < 13 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, a, Nat.add_sub_cancel]
  have hP : IsRotationCyclePrime 3 (listed.getD i 0) :=
    (term_iff (hlt i hi)).2 (hmem i hi)
  have hc := Nat.nth_count hP
  rw [count_eq (hlt i hi).le, hcard i hi] at hc
  rw [hc, List.getD_eq_getElem]

/-- Conjecture 2 (Seggelin): there are no 5-Rotation Cycle Primes, i.e. there is no prime `p`
such that `rotAdd^[j] p` is prime for each of `j = 1, 2, 3, 4, 5`. -/
def statement : Prop :=
  ∀ p : ℕ, ¬ IsRotationCyclePrime 5 p

end Math0.Statements.A086004

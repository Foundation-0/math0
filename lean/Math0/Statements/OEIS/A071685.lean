/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A071685: reverse-divisor numbers are `1`, `12`, `78` or `89` mod `100`

Source: https://oeis.org/A071685, Harvey P. Dale, Dec 13 2017 (COMMENTS section). Verbatim:
> Conjecture: every term mod 100 is equal to 1, 12, 78, or 89.

The entry's name (Labos Elemer, Jun 03 2002): "Non-palindromic numbers n, not divisible by 10,
such that either n divides R(n) or R(n) divides n, where R(n) is the digit-reversal of n."
Offset `1`; the listed data start `1089, 2178, 8712, 9801, 10989, 21978, 87912, 98901, …`.

## Encoding

* `R n` is the decimal digit reversal of A004086 ("Read n backwards"; "Leading zeros (after the
  reversal has taken place) are omitted"): the base-`10` digits of `n` are reversed and read
  again as a number, `R n = Nat.ofDigits 10 (Nat.digits 10 n).reverse`. So `R 1089 = 9801`,
  `R 120 = 21`, `R 0 = 0`.
* Palindromes are encoded via the comment in A002113 (Palindromes in base 10): "n is a
  palindrome … if and only if n = A004086(n)". So "non-palindromic" is `R n ≠ n`.
* `IsTerm n`: `R n ≠ n`, `¬ 10 ∣ n`, and `n ∣ R n ∨ R n ∣ n`. (`n = 0` is excluded since
  `10 ∣ 0`.) This predicate is decidable.
* The sequence `a n = Nat.nth IsTerm (n - 1)` (offset `1`) lists the terms in increasing order.
  `Nat.nth` is noncomputable, so `a` is noncomputable. `a_data` checks the first `16` listed
  terms `a 1, …, a 16`, i.e. all listed terms below `10^7`. It rests on `term_iff`: below
  `10^7` the terms are exactly these `16` numbers. That is proved by kernel scans
  (`decide +kernel`) over kernel-friendly helpers proved sound for the definitions. To make the
  scan feasible, a few elementary facts about leading and last digits are proved here and used
  only for the data check: with `A` the leading digit and `B` the last digit of a term `n`
  (at least two digits), the quotient `k` (`R n = k n` or `n = k R n`) satisfies `k ≠ 1` and
  `k·A ≤ B` with `k·B ≡ A (mod 10)` (or the same with `A`, `B` swapped). That leaves
  `(A, B) ∈ {(2,6), (1,7), (2,8), (1,9), (6,2), (7,1), (8,2), (9,1)}`, and since
  `R n ≡ n (mod 9)` it also gives `9 ∣ n` (or `3 ∣ n` when `k = 4`).
* The conjecture: every term `n` of the sequence satisfies `n % 100 ∈ {1, 12, 78, 89}`. It is
  stated for every `n` with `IsTerm n`, i.e. for every term of the sequence. This does not
  depend on whether the sequence is infinite. The entry says there are `4·Fibonacci(⌊(d-2)/2⌋)`
  terms with `d` digits, so the sequence is infinite; the statement is then the same as
  `∀ i ≥ 1, a i % 100 ∈ {1, 12, 78, 89}`.
-/

namespace Math0.Statements.A071685

/-- `R n`: the decimal digit reversal of `n` (A004086); leading zeros after the reversal are
omitted. -/
def R (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- `n` is a term of A071685: `n` is non-palindromic (`R n ≠ n`, cf. A002113), not divisible by
`10`, and either `n` divides `R n` or `R n` divides `n`. -/
def IsTerm (n : ℕ) : Prop := R n ≠ n ∧ ¬ 10 ∣ n ∧ (n ∣ R n ∨ R n ∣ n)

instance : DecidablePred IsTerm := fun n => by unfold IsTerm; infer_instance

/-- A071685 (offset `1`): the `n`-th non-palindromic number, not divisible by `10`, that
divides or is divided by its digit reversal. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The digit reversals in the entry's examples: `R 1089 = 9801 = 9 · 1089`,
`R 8712 = 2178 = 8712 / 4`, `R 12021 = 12021` (a palindrome), and `R 8380 = 838`; also
`R 120 = 21` and `R 0 = 0`. -/
theorem R_examples : R 1089 = 9801 ∧ R 8712 = 2178 ∧ R 12021 = 12021 ∧ R 8380 = 838 ∧
    R 120 = 21 ∧ R 0 = 0 := by
  norm_num [R, Nat.ofDigits_cons, Nat.ofDigits_nil]

/-! ### Digit-reversal facts (used only for the data check) -/

theorem R_cons {n : ℕ} (hn : 0 < n) :
    R n = R (n / 10) + 10 ^ (Nat.digits 10 (n / 10)).length * (n % 10) := by
  unfold R
  rw [Nat.digits_def' (by norm_num) hn, List.reverse_cons, Nat.ofDigits_append,
    List.length_reverse, Nat.ofDigits_singleton]

theorem len_cons {n : ℕ} (hn : 0 < n) :
    (Nat.digits 10 n).length = (Nat.digits 10 (n / 10)).length + 1 := by
  rw [Nat.digits_def' (by norm_num) hn, List.length_cons]

theorem R_lt (n : ℕ) : R n < 10 ^ (Nat.digits 10 n).length := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 10) (l := (Nat.digits 10 n).reverse)
    (by norm_num) (fun x hx => Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hx))
  rwa [List.length_reverse] at h

/-- With `d` digits, `10^(d-1) ≤ n < 10 · 10^(d-1)`. -/
theorem lead_bounds {n : ℕ} (hn : 0 < n) :
    10 ^ ((Nat.digits 10 n).length - 1) ≤ n ∧ n < 10 * 10 ^ ((Nat.digits 10 n).length - 1) := by
  have h1 := Nat.base_pow_length_digits_le 10 n (by norm_num) hn.ne'
  have h2 := Nat.lt_base_pow_length_digits (b := 10) (m := n) (by norm_num)
  rw [len_cons hn, pow_succ] at h1 h2
  rw [len_cons hn, Nat.add_sub_cancel]
  constructor <;> omega

/-- The leading digit of `R n` is the last digit of `n`. -/
theorem R_div {n : ℕ} (hn : 0 < n) :
    R n / 10 ^ ((Nat.digits 10 n).length - 1) = n % 10 := by
  rw [len_cons hn, Nat.add_sub_cancel, R_cons hn,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (R_lt _), zero_add]

theorem digits_R {n : ℕ} (h : n % 10 ≠ 0) :
    Nat.digits 10 (R n) = (Nat.digits 10 n).reverse := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact h rfl)
  unfold R
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro x hx
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hx)
  · intro hne
    rw [List.getLast_reverse]
    have key : ∀ (l : List ℕ) (hl : l ≠ []), l = n % 10 :: Nat.digits 10 (n / 10) →
        l.head hl ≠ 0 := by
      rintro l hl rfl
      exact h
    exact key _ _ (Nat.digits_def' (by norm_num) hn)

theorem R_R {n : ℕ} (h : n % 10 ≠ 0) : R (R n) = n := by
  show Nat.ofDigits 10 (Nat.digits 10 (R n)).reverse = n
  rw [digits_R h, List.reverse_reverse, Nat.ofDigits_digits]

theorem len_R {n : ℕ} (h : n % 10 ≠ 0) :
    (Nat.digits 10 (R n)).length = (Nat.digits 10 n).length := by
  rw [digits_R h, List.length_reverse]

/-- The last digit of `R n` is the leading digit of `n` (when `n` does not end in `0`). -/
theorem R_mod {n : ℕ} (h : n % 10 ≠ 0) :
    R n % 10 = n / 10 ^ ((Nat.digits 10 n).length - 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact h rfl)
  have hR : 0 < R n := by
    have := R_div hn
    rcases Nat.eq_zero_or_pos (R n) with h0 | h0
    · rw [h0, Nat.zero_div] at this
      exact absurd this.symm h
    · exact h0
  have := R_div hR
  rw [R_R h, len_R h] at this
  exact this.symm

theorem R_mod_nine (n : ℕ) : R n % 9 = n % 9 := by
  have h1 : R n % 9 = (Nat.digits 10 n).sum % 9 := by
    unfold R
    rw [Nat.ofDigits_mod, show 10 % 9 = 1 from rfl, Nat.ofDigits_one, List.sum_reverse]
  rw [h1]
  exact (Nat.modEq_nine_digits_sum n).symm

/-- `R n = k n` with leading digit `A`, last digit `B`. -/
theorem fwd_cases : ∀ k < 10, ∀ A < 10, ∀ B < 10, 1 ≤ A → k ≠ 1 → k * A ≤ B → B * k % 10 = A →
    (k = 2 ∧ A = 2 ∧ B = 6) ∨ (k = 3 ∧ A = 1 ∧ B = 7) ∨ (k = 4 ∧ A = 2 ∧ B = 8) ∨
      (k = 9 ∧ A = 1 ∧ B = 9) := by
  intro k hk A hA B hB
  interval_cases k <;> interval_cases A <;> omega

/-- `n = k R n` with leading digit `A`, last digit `B`. -/
theorem bwd_cases : ∀ k < 10, ∀ A < 10, ∀ B < 10, 1 ≤ B → k ≠ 1 → k * B ≤ A → A * k % 10 = B →
    (k = 2 ∧ A = 6 ∧ B = 2) ∨ (k = 3 ∧ A = 7 ∧ B = 1) ∨ (k = 4 ∧ A = 8 ∧ B = 2) ∨
      (k = 9 ∧ A = 9 ∧ B = 1) := by
  intro k hk A hA B hB
  interval_cases k <;> interval_cases B <;> omega

/-- The possible (leading digit, last digit, modulus `m` with `m ∣ n`) of a term. -/
def tri : List (ℕ × ℕ × ℕ) :=
  [(2, 6, 9), (1, 7, 9), (2, 8, 3), (1, 9, 9), (6, 2, 9), (7, 1, 9), (8, 2, 3), (9, 1, 9)]

theorem tri_of_term {n : ℕ} (h : IsTerm n) :
    ∃ m, (n / 10 ^ ((Nat.digits 10 n).length - 1), n % 10, m) ∈ tri ∧ n % m = 0 := by
  obtain ⟨hpal, h10, hdiv⟩ := h
  have hB0 : n % 10 ≠ 0 := fun e => h10 (Nat.dvd_of_mod_eq_zero e)
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hB0 rfl)
  have hlb := lead_bounds hn
  have hRd := R_div hn
  have hRm := R_mod hB0
  have hR9 := R_mod_nine n
  have hP0 : 0 < 10 ^ ((Nat.digits 10 n).length - 1) := by positivity
  generalize 10 ^ ((Nat.digits 10 n).length - 1) = P at hlb hRd hRm hP0 ⊢
  have hA1 : 1 ≤ n / P := (Nat.le_div_iff_mul_le hP0).2 (by omega)
  have hA9 : n / P < 10 := (Nat.div_lt_iff_lt_mul hP0).2 (by omega)
  have hB9 : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hB1 : 1 ≤ n % 10 := by omega
  have hRlt : R n < (n % 10 + 1) * P := (Nat.div_lt_iff_lt_mul hP0).1 (by omega)
  have hRge : n % 10 * P ≤ R n := by rw [← hRd]; exact Nat.div_mul_le_self (R n) P
  have hAP : n / P * P ≤ n := Nat.div_mul_le_self n P
  have hnlt : n < (n / P + 1) * P := (Nat.div_lt_iff_lt_mul hP0).1 (Nat.lt_succ_self _)
  rcases hdiv with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `R n = n * k`
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hpal (by rw [hk, mul_one])
    have hkA : k * (n / P) ≤ n % 10 := by
      have h1 : k * (n / P) * P < (n % 10 + 1) * P :=
        calc k * (n / P) * P = k * (n / P * P) := by ring
          _ ≤ k * n := Nat.mul_le_mul_left _ hAP
          _ = R n := by rw [hk, mul_comm]
          _ < _ := hRlt
      have := Nat.lt_of_mul_lt_mul_right h1
      omega
    have hmod : n % 10 * k % 10 = n / P := by
      rw [← hRm, hk, Nat.mul_mod n k 10, Nat.mul_mod (n % 10) k 10, Nat.mod_mod]
    have hk10 : k < 10 := by
      have : k ≤ k * (n / P) := Nat.le_mul_of_pos_right k hA1
      omega
    rw [hk] at hR9
    rcases fwd_cases k hk10 (n / P) hA9 (n % 10) hB9 hA1 hk1 hkA hmod with
      ⟨rfl, hA, hB⟩ | ⟨rfl, hA, hB⟩ | ⟨rfl, hA, hB⟩ | ⟨rfl, hA, hB⟩
    · exact ⟨9, by rw [hA, hB]; decide, by omega⟩
    · exact ⟨9, by rw [hA, hB]; decide, by omega⟩
    · exact ⟨3, by rw [hA, hB]; decide, by omega⟩
    · exact ⟨9, by rw [hA, hB]; decide, by omega⟩
  · -- `n = R n * k`
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hpal (by rw [mul_one] at hk; exact hk.symm)
    have hkB : k * (n % 10) ≤ n / P := by
      have h1 : k * (n % 10) * P < (n / P + 1) * P :=
        calc k * (n % 10) * P = k * (n % 10 * P) := by ring
          _ ≤ k * R n := Nat.mul_le_mul_left _ hRge
          _ = n := by rw [mul_comm]; exact hk.symm
          _ < _ := hnlt
      have := Nat.lt_of_mul_lt_mul_right h1
      omega
    have hmod : n / P * k % 10 = n % 10 := by
      have e : n % 10 = R n * k % 10 := congrArg (· % 10) hk
      rw [e, ← hRm, Nat.mul_mod (R n) k 10, Nat.mul_mod (R n % 10) k 10, Nat.mod_mod]
    have hk10 : k < 10 := by
      have : k ≤ k * (n % 10) := Nat.le_mul_of_pos_right k hB1
      omega
    rcases bwd_cases k hk10 (n / P) hA9 (n % 10) hB9 hB1 hk1 hkB hmod with
      ⟨rfl, hA, hB⟩ | ⟨rfl, hA, hB⟩ | ⟨rfl, hA, hB⟩ | ⟨rfl, hA, hB⟩
    · exact ⟨9, by rw [hA, hB]; decide, by omega⟩
    · exact ⟨9, by rw [hA, hB]; decide, by omega⟩
    · exact ⟨3, by rw [hA, hB]; decide, by omega⟩
    · exact ⟨9, by rw [hA, hB]; decide, by omega⟩

/-- A number `n` with `n / P = A`, `n % 10 = B` and `m ∣ n` (`m ∈ {3, 9}`, `P = 10^e`, `e ≥ 1`)
lies on the arithmetic progression scanned for `(A, B, m)` at scale `P`. -/
theorem cover {n P A B m : ℕ} (hP0 : 0 < P) (hP9 : P % 9 = 1) (hP10 : P % 10 = 0)
    (hm : m = 3 ∨ m = 9) (hA : n / P = A) (hB : n % 10 = B) (hnm : n % m = 0) :
    ∃ t < P / 10 / m + 1, n = A * P + B + 10 * ((m - (A + B) % m) % m) + 10 * m * t := by
  have e1 : A * P + n % P = n := by rw [← hA, mul_comm]; exact Nat.div_add_mod n P
  have e2 : n % P % 10 = n % 10 := Nat.mod_mod_of_dvd n (Nat.dvd_of_mod_eq_zero hP10)
  have e3 := Nat.mod_lt n hP0
  have e4 : A * P % 9 = A % 9 := by rw [Nat.mul_mod, hP9, mul_one, Nat.mod_mod]
  generalize n % P = r at e1 e2 e3
  generalize A * P = X at e1 e4 ⊢
  rcases hm with rfl | rfl
  · exact ⟨r / 10 / 3, by omega, by omega⟩
  · exact ⟨r / 10 / 9, by omega, by omega⟩

/-! ### Kernel-friendly evaluation (used only for the data check)

The functions below are written with the recursors `Nat.rec`, `Bool.rec` and the primitive
operations `Nat.add`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.beq`, which the kernel evaluates
directly on numerals. Each one is proved equal to (or sound for) the definitions above. -/

/-- `x && y`, written with the recursor. -/
def andK (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

/-- `x || y`, written with the recursor. -/
def orK (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x

/-- `!x`, written with the recursor. -/
def notK (x : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false x

theorem andK_eq (x y : Bool) : andK x y = (x && y) := by cases x <;> rfl

theorem orK_eq (x y : Bool) : orK x y = (x || y) := by cases x <;> rfl

theorem notK_eq (x : Bool) : notK x = !x := by cases x <;> rfl

theorem beq_eq_decide (x y : ℕ) : Nat.beq x y = decide (x = y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

/-- `revK fuel n acc = acc · 10^(number of digits of n) + R n` when `n < 10^fuel`. -/
def revK (fuel : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih n acc => Bool.rec (motive := fun _ => ℕ)
      (ih (Nat.div n 10) (Nat.add (Nat.mul acc 10) (Nat.mod n 10))) acc (Nat.beq n 0))
    fuel

theorem revK_eq : ∀ fuel n acc, n < 10 ^ fuel →
    revK fuel n acc = acc * 10 ^ (Nat.digits 10 n).length + R n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc hn
    obtain rfl : n = 0 := by simpa using hn
    simp [revK, R]
  | succ fuel ih =>
    intro n acc hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [revK, R]
    · have hb : Nat.beq n 0 = false := by
        rw [beq_eq_decide, decide_eq_false_iff_not]
        omega
      have e : revK (fuel + 1) n acc = revK fuel (n / 10) (acc * 10 + n % 10) := by
        show Bool.rec (motive := fun _ => ℕ)
          (revK fuel (Nat.div n 10) (Nat.add (Nat.mul acc 10) (Nat.mod n 10))) acc
          (Nat.beq n 0) = _
        rw [hb]
        rfl
      rw [e, ih (n / 10) _ (by rw [pow_succ] at hn; omega), R_cons hpos, len_cons hpos,
        pow_succ]
      ring

/-- `IsTerm n`, given `r = R n` (without the last-digit test). -/
def termR (n r : ℕ) : Bool :=
  andK (notK (Nat.beq r n)) (orK (Nat.beq (Nat.mod r n) 0) (Nat.beq (Nat.mod n r) 0))

/-- `IsTerm n`, kernel-friendly (correct for `n < 10^8`, see `termK_iff`). -/
def termK (n : ℕ) : Bool := andK (notK (Nat.beq (Nat.mod n 10) 0)) (termR n (revK 8 n 0))

theorem termK_iff {n : ℕ} (hn : n < 10 ^ 8) : termK n = true ↔ IsTerm n := by
  have hr : revK 8 n 0 = R n := by rw [revK_eq 8 n 0 hn]; simp
  have e : termK n = (!decide (n % 10 = 0) &&
      (!decide (R n = n) && (decide (R n % n = 0) || decide (n % R n = 0)))) := by
    show andK (notK (Nat.beq (n % 10) 0)) (andK (notK (Nat.beq (revK 8 n 0) n))
      (orK (Nat.beq (revK 8 n 0 % n) 0) (Nat.beq (n % revK 8 n 0) 0))) = _
    simp only [hr, andK_eq, orK_eq, notK_eq, beq_eq_decide]
  rw [e]
  simp only [IsTerm, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.or_eq_true, decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero]
  tauto

/-! ### Scanning -/

/-- The terms listed in OEIS below `10^7`. -/
def listed : List ℕ :=
  [1089, 2178, 8712, 9801, 10989, 21978, 87912, 98901, 109989, 219978, 879912, 989901,
    1099989, 2199978, 8799912, 9899901]

/-- `check q = true` iff (`q` is a term `→ q ∈ listed`), for `q < 10^8`. -/
def check (q : ℕ) : Bool := orK (notK (termK q)) (decide (q ∈ listed))

theorem check_sound {q : ℕ} (h : check q = true) (hq : IsTerm q) (hlt : q < 10 ^ 8) :
    q ∈ listed := by
  rw [check, orK_eq, notK_eq, (termK_iff hlt).2 hq] at h
  simpa using h

/-- `scanLoop base step cnt = true` iff `check (base + step · t)` for every `t < cnt`. -/
def scanLoop (base step : ℕ) (cnt : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andK (check (Nat.add base (Nat.mul step t))) ih) cnt

theorem scanLoop_sound (base step : ℕ) : ∀ cnt, scanLoop base step cnt = true →
    ∀ t < cnt, check (base + step * t) = true := by
  intro cnt
  induction cnt with
  | zero => intro _ t ht; omega
  | succ cnt ih =>
    intro h t ht
    have h' : andK (check (base + step * cnt)) (scanLoop base step cnt) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · exact ih h'.2 t ht
    · subst ht
      exact h'.1

/-- For `x = (A, B, m) ∈ tri`, scan the numbers `n ≡ B (mod 10)` with `m ∣ n` and
`A · P ≤ n < (A + 1) · P` (and a few more). -/
def scanAB (P : ℕ) (x : ℕ × ℕ × ℕ) : Bool :=
  scanLoop (x.1 * P + x.2.1 + 10 * ((x.2.2 - (x.1 + x.2.1) % x.2.2) % x.2.2)) (10 * x.2.2)
    (P / 10 / x.2.2 + 1)

/-- All the scans at scale `P`. -/
def scanP (P : ℕ) : Bool := tri.all (scanAB P)

theorem scanP_sound {P A B m : ℕ} (h : scanP P = true) (hx : (A, B, m) ∈ tri) :
    ∀ t < P / 10 / m + 1,
      check (A * P + B + 10 * ((m - (A + B) % m) % m) + 10 * m * t) = true := by
  have h1 : scanAB P (A, B, m) = true := List.all_eq_true.1 h _ hx
  exact scanLoop_sound _ _ _ h1

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

/-- All `q < 1000`. -/
theorem scan_small : checkAll 0 1000 = true := by decide +kernel

/-- `4`-digit candidates. -/
theorem scan_four : scanP 1000 = true := by decide +kernel

/-- `5`-digit candidates. -/
theorem scan_five : scanP 10000 = true := by decide +kernel

/-- `6`-digit candidates. -/
theorem scan_six : scanP 100000 = true := by decide +kernel

/-- `7`-digit candidates. -/
theorem scan_seven : scanP 1000000 = true := by decide +kernel

theorem mem_of_scan {n P m : ℕ} (hscan : scanP P = true) (hP0 : 0 < P) (hP9 : P % 9 = 1)
    (hP10 : P % 10 = 0) (hmem : (n / P, n % 10, m) ∈ tri) (hm : n % m = 0) (hT : IsTerm n)
    (hn : n < 10 ^ 8) : n ∈ listed := by
  have htri : ∀ x ∈ tri, x.2.2 = 3 ∨ x.2.2 = 9 := by decide
  have hm' : m = 3 ∨ m = 9 := htri _ hmem
  obtain ⟨t, ht, hnt⟩ := cover hP0 hP9 hP10 hm' rfl rfl hm
  have hc := scanP_sound hscan hmem t ht
  rw [← hnt] at hc
  exact check_sound hc hT hn

/-- Below `10^7`, the terms are exactly the listed ones. -/
theorem term_iff {n : ℕ} (hn : n < 10 ^ 7) : IsTerm n ↔ n ∈ listed := by
  constructor
  · intro hT
    by_cases hs : n < 1000
    · have hc := checkAll_sound 0 1000 scan_small n hs
      rw [zero_add] at hc
      exact check_sound hc hT (by omega)
    obtain ⟨m, hmem, hm⟩ := tri_of_term hT
    have hlb := lead_bounds (by omega : 0 < n)
    generalize (Nat.digits 10 n).length - 1 = e at hlb hmem
    have he1 : e < 7 := by
      by_contra hc
      have : 10 ^ 7 ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have he2 : 3 ≤ e := by
      by_contra hc
      have : 10 ^ e ≤ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases e
    · exact mem_of_scan scan_four (by norm_num) (by norm_num) (by norm_num) hmem hm hT
        (by omega)
    · exact mem_of_scan scan_five (by norm_num) (by norm_num) (by norm_num) hmem hm hT
        (by omega)
    · exact mem_of_scan scan_six (by norm_num) (by norm_num) (by norm_num) hmem hm hT
        (by omega)
    · exact mem_of_scan scan_seven (by norm_num) (by norm_num) (by norm_num) hmem hm hT
        (by omega)
  · intro hq
    have hall : listed.all termK = true := by decide +kernel
    have hlt : ∀ x ∈ listed, x < 10 ^ 8 := by decide
    rw [List.all_eq_true] at hall
    exact (termK_iff (hlt n hq)).1 (hall n hq)

theorem count_eq {n : ℕ} (hn : n ≤ 10 ^ 7) :
    Nat.count IsTerm n = (listed.toFinset.filter (· < n)).card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(term_iff (by omega)).1 h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (term_iff (by omega)).2 h1⟩

/-- The definition reproduces the first `16` terms listed in OEIS, `a 1, …, a 16` (all listed
terms below `10^7`; kernel-checked, see `term_iff`). -/
theorem a_data : (List.range 16).map (fun i => a (i + 1)) =
    [1089, 2178, 8712, 9801, 10989, 21978, 87912, 98901, 109989, 219978, 879912, 989901,
      1099989, 2199978, 8799912, 9899901] := by
  have hcard : ∀ i < 16, (listed.toFinset.filter (· < listed.getD i 0)).card = i := by
    decide +kernel
  have hlt : ∀ i < 16, listed.getD i 0 < 10 ^ 7 := by decide +kernel
  have hmem : ∀ i < 16, listed.getD i 0 ∈ listed := by decide +kernel
  show _ = listed
  apply List.ext_getElem (by simp [listed])
  intro i h1 h2
  have hi : i < 16 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, a, Nat.add_sub_cancel]
  have hP : IsTerm (listed.getD i 0) := (term_iff (hlt i hi)).2 (hmem i hi)
  have hc := Nat.nth_count hP
  rw [count_eq (hlt i hi).le, hcard i hi] at hc
  rw [hc, List.getD_eq_getElem]

/-- Conjecture (H. P. Dale, 2017): every term `n` of A071685 (a non-palindromic number, not
divisible by `10`, with `n ∣ R n` or `R n ∣ n`) satisfies `n mod 100 ∈ {1, 12, 78, 89}`. -/
def statement : Prop :=
  ∀ n : ℕ, IsTerm n → n % 100 = 1 ∨ n % 100 = 12 ∨ n % 100 = 78 ∨ n % 100 = 89

end Math0.Statements.A071685

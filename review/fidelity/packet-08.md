# Fidelity review packet 08 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A332010, A333650, A334592, A334595, A334603, A335012, A338885, A341761, A342645, A342992.

## A332010: A332010: the average first letter of one-descent derangements has denominator 2^(n-2)

Verdict of the pre-review: **faithful**. Result: [oeis-a332010](../../results/oeis-a332010/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A332010.lean`](../../lean/Math0/Statements/OEIS/A332010.lean).

**The conjecture as stated in OEIS**

> %C A332010 Conjecture: T(n, 1) = 2^(n-2).  (entry by _Peter Kagey_, Feb 04 2020; name: "Irregular triangle of denominators of the average value of the first letter over all derangements of {1, 2, ..., n} with k descents."; offset 2,2; keyword tabf). Text unchanged in the live oeisdata (rev #17, Mar 30 2024).

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 2 ≤ n → T n 1 = 2 ^ (n - 2)

with
def IsDerangement (w : List ℕ) : Prop := ∀ (i : ℕ) (h : i < w.length), w[i] ≠ i + 1
def des (w : List ℕ) : ℕ := (w.zip w.tail).countP fun p => p.2 < p.1
def ders (n k : ℕ) : List (List ℕ) :=
  (List.range' 1 n).permutations.filter fun w => decide (IsDerangement w) && des w == k
def avgFirstLetter (E : List (List ℕ)) : ℚ :=
  (((E.map fun w => w.headD 0).sum : ℕ) : ℚ) / ((E.length : ℕ) : ℚ)
def avgFirst (n k : ℕ) : ℚ := avgFirstLetter (ders n k)
def T (n k : ℕ) : ℕ := (avgFirst n k).den
```

**What the Lean statement says**

For every n ≥ 2, list the permutations of {1,...,n} in one-line notation that have no fixed point (w_i ≠ i for every position i) and exactly one descent (exactly one i with w_i > w_{i+1}). Take the average of their first letters as a rational number. In lowest terms its denominator is 2^(n-2).

**What the kernel checks against the OEIS data**

a_data kernel-checks the first 25 listed terms (rows n = 2..8 of the triangle, all columns k up to the row length), through a structurally recursive copy (rowC) that is proved equal to the real definition (row_eq_rowC: mem/nodup of the enumeration, derB_one, desB_eq, permutation invariance of the average). example_T41 checks the worked example: the derangements of 4 letters with one descent are exactly [2,3,4,1],[2,4,1,3],[3,4,1,2],[4,1,2,3], the average is 11/4 and T(4,1) = 4. That covers the whole definition (derangement test, descent count, first letter, reduced denominator) across 7 rows and many k, so the definitions are pinned down. Terms 26-50 (rows 9-11) are not kernel-checked. My independent brute force gives T(n,1) = 2^(n-2) for n = 2..9, including T(9,1) = 128, the listed term 26.

**Points for the reviewer**

- *Note.* The range n ≥ 2 is the full set of rows (offset 2), and n - 2 is exact there. The junk case (no derangement with k descents, 0/0 = 0, den = 1) never arises for k = 1 and n ≥ 2, because [2,3,...,n,1] is a derangement with exactly one descent. The statement is not weakened.
- *Note.* Only rows 2-8 (25 of the 50 listed terms) are kernel-checked. The definition is a direct transcription of the entry's name and is exercised on 7 rows and every column, so the risk is negligible. rowLen (row length, taken from the entry's comment) appears only in the data check, never in `statement`.
- *Note.* Catalogue metadata only, not the Lean statement: the area is "Discrete geometry", but this is permutation enumeration (combinatorics).

## A333650: Domino towers of height 2 and of height n-1, n-2, n-3 (A333650): all four Kagey/Luschny conjectures

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a333650](../../results/oeis-a333650/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A333650.lean`](../../lean/Math0/Statements/OEIS/A333650.lean).

**The conjecture as stated in OEIS**

> %C A333650 Conjecture: For n > 1, T(n,2) = A000071(n+2).  [_Peter Kagey_, Mar 31 2020, entry author]
> %C A333650 Conjecture: T(n,n-1) = A339252(n-2). - _Peter Kagey_, Nov 21 2020
> %C A333650 Conjecture: T(n,n-2) = A339254(n-3). - _Peter Luschny_, Nov 29 2020
> %C A333650 Conjecture: T(n,n-3) = A339029(n-4). - _Peter Luschny_, Dec 01 2020
> (Luschny's Dec 01 2020 summary: T(2*n + k, n + k) = d_{n}(n + k - 1) for k >= 1 and 0 <= n <= 3, with explicit d_0..d_3.) Name: "Triangle read by rows: T(n,k) gives the number of domino towers of height k consisting of n bricks." Comment: "The towers must have a contiguous base of bricks, and each brick must be at least half supported below by another brick. The stacks do not need to be stable." Offset 1. Unchanged in the live oeisdata (rev #68, Aug 12 2022).

**The frozen Lean statement**

```lean
def statement : Prop :=
  statement_col2 ∧ statement_diag1 ∧ statement_diag2 ∧ statement_diag3
def statement_col2 : Prop := ∀ n : ℕ, 1 < n → (T n 2 : ℤ) = A000071 (n + 2)
def statement_diag1 : Prop := ∀ n : ℕ, 2 ≤ n → (T n (n - 1) : ℤ) = A339252 (n - 2)
def statement_diag2 : Prop := ∀ n : ℕ, 3 ≤ n → (T n (n - 2) : ℤ) = A339254 (n - 3)
def statement_diag3 : Prop := ∀ n : ℕ, 4 ≤ n → (T n (n - 3) : ℤ) = A339029 (n - 4)

with (abridged)
def base (b : ℕ) : Finset ℤ := (range b).image fun j : ℕ => 2 * (j : ℤ)
def IsTower (n k : ℕ) (t : List (Finset ℤ)) : Prop :=
  t.length = k ∧ (∀ L ∈ t, L.Nonempty) ∧
  (∃ b, 0 < b ∧ t.head? = some (base b)) ∧
  (∀ L ∈ t, ∀ x ∈ L, ∀ y ∈ L, x ≠ y → 2 ≤ |x - y|) ∧
  (∀ (i : ℕ) (hi : i < t.length), ∀ x ∈ t[i], Even (x - i)) ∧
  (∀ (i : ℕ) (hi : i + 1 < t.length), ∀ x ∈ t[i + 1], ∃ y ∈ t[i], |x - y| ≤ 1) ∧
  (t.map Finset.card).sum = n
noncomputable def T (n k : ℕ) : ℕ := {t | IsTower n k t}.ncard
def A000071 (n : ℕ) : ℤ := (Nat.fib n : ℤ) - 1
def A339252 : ℕ → ℤ | 0 => 1 | 1 => 4 | 2 => 11 | n + 3 => 4 * A339252 (n + 2) - 4 * A339252 (n + 1)
def A339254 : ℕ → ℤ | 0 => 1 | 1 => 7 | 2 => 24 | 3 => 70 | 4 => 193
  | n + 5 => 6 * A339254 (n + 4) - 12 * A339254 (n + 3) + 8 * A339254 (n + 2)
noncomputable def A339029 (n : ℕ) : ℤ := coeff n ((1 + 4X - 20X^2 + 8X^3 + 33X^4 - 4X^5 - 33X^6 : ℤ⟦X⟧) * invOfUnit ((1 - 2X)^4) 1)
```

**What the Lean statement says**

A tower is a stack of k nonempty layers of bricks of length 2 (in half-brick units), up to horizontal translation. The bottom layer is b ≥ 1 bricks side by side. Layer i is staggered by i half-bricks (brick-wall pattern, so no brick sits exactly on top of another). Every brick above the bottom overlaps a brick of the layer directly below by exactly half a brick. T(n,k) counts such towers with n bricks and k layers, and mirror images count as different. The claims are: (1) for n ≥ 2, T(n,2) = F(n+2) - 1; (2) for n ≥ 2, T(n,n-1) = A339252(n-2), where A339252 is 1, 4, 11 and then a(m) = 4a(m-1) - 4a(m-2); (3) for n ≥ 3, T(n,n-2) = A339254(n-3), where A339254 is 1, 7, 24, 70, 193 and then a(m) = 6a(m-1) - 12a(m-2) + 8a(m-3); (4) for n ≥ 4, T(n,n-3) = A339029(n-4), the coefficients of (1+4x-20x^2+8x^3+33x^4-4x^5-33x^6)/(1-2x)^4.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 55 listed terms (rows 1-10) through T_eq_Tc (T equals a computable layer-by-layer count, proved). The four right-hand sequences are encoded by their own OEIS %N definitions and kernel-checked against their listed data (A000071: 40 terms with offset 1; A339252: 32 terms; A339254: 30; A339029: 29, via a recurrence proved equal to the power-series definition). statement_check verifies all four identities for n ≤ 10. Ten full rows, which include T(n,n) = 2^(n-1) and row sums 3^(n-1), pin down the tower model, in particular the staggering. My independent Python recomputation of the same model also reproduces row 11 of the entry's %e table (1, 232, 1916, ..., 1024), which is not in DATA, and all four identities up to n = 14.

**Points for the reviewer**

- *Note.* The brick-wall staggering (layer-i left ends ≡ i mod 2) is not spelled out in the entry's wording. It is an interpretive choice, but a forced one: without it T(2,2) = 3 and T(n,n) = 3^(n-1), against the listed T(2,2) = 2 and the stated T(n,n) = 2^(n-1). It also matches the cited literature (Gouyou-Beauchamps–Viennot, Bétréma–Penaud, Zeilberger) and the entry's picture for T(3,2) = 4.
- *Note.* Conjectures 2-4 state no range. The file takes the largest range in which the right-hand index is a natural number (n ≥ 2, 3, 4). That is wider than Luschny's d_n summary, which covers only n ≥ 3, 5, 7 for these diagonals. The extra small cases T(2,1) = T(3,1) = T(4,1) = 1 = a(0) are true and kernel-checked by statement_check, so the wider range strengthens the statement without changing what it settles.
- *Note.* Luschny's closed-form summary T(2n+k, n+k) = d_n(n+k-1) is not formalized separately. Through the closed forms recorded in A339252, A339254 and A339029 it reformulates the same three diagonal conjectures, and its n = 0 case is T(k,k) = 2^(k-1), which the entry lists in FORMULA, not as a conjecture. The file says this explicitly.
- *Note.* Values are cast to ℤ because the right-hand sequences are ℤ-valued. A000071(n+2) = F(n+2) - 1 ≥ 1 for n ≥ 1, so there is no sign or truncation issue. All natural-number subtractions (n-1, n-2, n-3, n-2, n-3, n-4) are exact in the stated ranges.

## A334592: Records of the XOR-triangle zero count A334592 are exactly the powers of two

Verdict of the pre-review: **faithful**. Result: [oeis-a334592](../../results/oeis-a334592/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A334592.lean`](../../lean/Math0/Statements/OEIS/A334592.lean).

**The conjecture as stated in OEIS**

> %C A334592 Conjecture: Records occur at powers of two.  (entry by _Peter Kagey_, May 07 2020; name: "Number of zeros in XOR-triangle with first row generated from the binary expansion of n."; offset 1). Unchanged in the live oeisdata (rev #19, May 09 2020).

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, IsRecord n ↔ ∃ k : ℕ, n = 2 ^ k

with
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → a m < a n
def a (n : ℕ) : ℕ := ((xorTriangle (binary n)).map (List.count false)).sum
def xorTriangle (r : List Bool) : List (List Bool) := rows r.length r
def rows : ℕ → List Bool → List (List Bool) | 0, _ => [] | k + 1, r => r :: rows k (xorRow r)
def xorRow (r : List Bool) : List Bool := List.zipWith xor r r.tail
def binary (n : ℕ) : List Bool := (bitsLE n n).reverse   -- proved = reverse of Nat.digits 2 n, 1 ↦ true
```

**What the Lean statement says**

Let a(n), for n ≥ 1, be the number of 0 entries in the triangle whose top row is the binary expansion of n (most significant bit first). Each later row is the XOR of adjacent pairs of the row above, down to a single entry. Call n ≥ 1 a record if a(n) > a(m) for every 1 ≤ m < n. Then n is a record if and only if n = 2^k for some k ≥ 0.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 77 listed terms a(1..77), and triangle_53 / a_53 check the entry's worked triangle for n = 53 (a(53) = 9). binary_eq_digits proves the hand-rolled binary expansion equals the reversed Nat.digits. With 77 terms and an explicit triangle, the definition is pinned down.

**Points for the reviewer**

- *Note.* Records are strict (a(n) > all earlier terms), the usual OEIS convention, and n = 1 counts as a record (1 = 2^0). The choice matters: with non-strict records, n = 2^k - 1 (k ≥ 2) would also be records (a(3) = a(2), a(7) = a(4), a(15) = a(8), ...; I confirmed this up to 2^16) and the conjecture would be false. The strict reading is the only one under which the author's statement holds.
- *Note.* "Records occur at powers of two" is formalized as a biconditional (record ⇔ power of two). That is stronger than the one-direction reading (every record is a power of two), which is also given as statement_weak and implied by statement. Proving the iff settles both readings.

## A334595: A334595: a(n) = 1 iff n is a power of two, and the records occur exactly at 1 and 2^k + 1

Verdict of the pre-review: **faithful**. Result: [oeis-a334595](../../results/oeis-a334595/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A334595.lean`](../../lean/Math0/Statements/OEIS/A334595.lean).

**The conjecture as stated in OEIS**

> %C A334595 Conjecture: Records occur at 1 and at 2^n + 1.
> %C A334595 Conjecture: a(n) = 1 if and only if n is a power of two.
> (entry by _Peter Kagey_, May 07 2020; name: "Binary interpretation of the right diagonal of the XOR-triangle with first row generated from the binary expansion of n."; offset 1). Unchanged in the live oeisdata (rev #18, May 09 2020).

**The frozen Lean statement**

```lean
def statement : Prop := statement_records ∧ statement_powTwo
def statement_records : Prop :=
  ∀ n : ℕ, IsRecord n ↔ (n = 1 ∨ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k + 1)
def statement_powTwo : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ ∃ k : ℕ, n = 2 ^ k)

with
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → a m < a n
def binExp (n : ℕ) : List ℕ := (Nat.digits 2 n).reverse
def xorRow (row : List ℕ) : List ℕ := List.zipWith (fun x y => x ^^^ y) row row.tail
def triangle (row : List ℕ) : List (List ℕ) := (List.range row.length).map (fun r => xorRow^[r] row)
def rightDiag (row : List ℕ) : List ℕ := (triangle row).map (fun r => r.getLastD 0)
def a (n : ℕ) : ℕ := Nat.ofDigits 2 (rightDiag (binExp n)).reverse
```

**What the Lean statement says**

For n ≥ 1, write n in binary (most significant bit first) and build the XOR-triangle with that top row. Take the last entry of each row, top to bottom, and read the resulting bit string as a binary number with the top entry as the most significant bit. Call that number a(n). Claim (1): with n ≥ 1 a record when a(n) > a(m) for all 1 ≤ m < n, the records are exactly n = 1 and n = 2^k + 1 for k ≥ 1 (3, 5, 9, 17, ...). Claim (2): for n ≥ 1, a(n) = 1 if and only if n is a power of two (2^k, k ≥ 0).

**What the kernel checks against the OEIS data**

a_data kernel-checks all 70 listed terms a(1..70). triangle_19 and a_19 check the entry's worked example (n = 19: the triangle 10011/1010/111/00/0, right side 10100, a(19) = 20). The top-right entry is read as the MSB, matching the PARI program (Vecrev of v indexed by row length). The definition is pinned down.

**Points for the reviewer**

- *Note.* In "2^n + 1" the file takes the exponent as k ≥ 1 and uses strict records. With strict records n = 2 = 2^0 + 1 is not a record (a(2) = a(1) = 1), so excluding k = 0 is required for the conjecture to be true. The alternative natural reading (non-strict records, k ≥ 0) gives the same content: I checked up to 2^16 that the non-strict records are exactly the strict ones plus n = 2. The choice does not change what is settled.
- *Note.* Both conjectures are formalized as biconditionals over n ≥ 1, the strongest reading. "Records occur at 1 and at 2^n+1" becomes "the record set equals {1} ∪ {2^k+1 : k ≥ 1}", which implies both one-directional readings. "Power of two" includes 1 = 2^0, and a(1) = 1 is consistent with that. The junk value a(0) = 0 is excluded by 1 ≤ n in both parts.
- *Note.* Catalogue metadata only: the area is "Discrete geometry" for a binary/XOR-triangle (combinatorics on words) result.

## A334603: The period of 1/11^n is 2 * 11^(n-1)

Verdict of the pre-review: **faithful**. Result: [oeis-a334603](../../results/oeis-a334603/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A334603.lean`](../../lean/Math0/Statements/OEIS/A334603.lean).

**The conjecture as stated in OEIS**

> %F A334603 a(n) = 2 * 11^(n-1) [conjectured, see comments].
> %C A334603 Conjecture proposed by the authors in References page 205: if p is a prime with gcd(p,30) = 1 and if the period of 1/p is m then the period of 1/p^n is m*p^(n-1).
> (entry by _Bernard Schott_, May 07 2020; name: "Period of the fraction 1/11^n for n >= 1."; offset 1). Unchanged in the live oeisdata (rev #31, Nov 19 2023).

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = 2 * 11 ^ (n - 1)

with
theorem exists_pow_modEq_one {m : ℕ} (h : Nat.Coprime 10 m) : ∃ k, 0 < k ∧ 10 ^ k ≡ 1 [MOD m]
def period (m : ℕ) : ℕ :=
  if h : Nat.Coprime 10 m then Nat.find (exists_pow_modEq_one h) else 0
def a (n : ℕ) : ℕ := period (11 ^ n)

(also defined but NOT the settled statement:
def statement_general : Prop :=
  ∀ p n : ℕ, p.Prime → Nat.gcd p 30 = 1 → 1 ≤ n → period (p ^ n) = period p * p ^ (n - 1))
```

**What the Lean statement says**

For every n ≥ 1, the least k ≥ 1 with 10^k ≡ 1 (mod 11^n), that is, the multiplicative order of 10 modulo 11^n, equals 2·11^(n-1). Since 11^n is coprime to 10, 1/11^n has a purely periodic decimal expansion, and this order is its minimal period.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 20 listed terms a(1..20) = 2·11^(n-1) with an order certificate (10^L ≡ 1 and 10^(L/q) ≢ 1 for each prime q | L, by verified binary exponentiation). period_data checks `period` against 35 terms of A051626 (period of 1/m, 3 ≤ m ≤ 90, gcd(m,10) = 1), including non-prime moduli (9, 21, 27, 49, 81, ...). period_eq_orderOf proves period m = orderOf (10 : ZMod m) for m coprime to 10. The definition is pinned down.

**Points for the reviewer**

- *Note.* The settled statement is the sequence-specific FORMULA-line conjecture (the case p = 11), not the general De Koninck–Mercier conjecture quoted in the COMMENTS. That general claim is defined as statement_general, is not proved, and is false: p = 487 has gcd(487,30) = 1 and period(1/487^2) = period(1/487). This is the right target, since the formula line is what this entry conjectures ("conjectured, see comments"). A reader should still not take "settles A334603" to mean the comment's general conjecture. The catalogue notes already flag that it is false at 487.
- *Note.* Junk values of `period` (0 for m not coprime to 10; 1 for m = 1, where A051626 has 0) are unreachable: n ≥ 1 gives m = 11^n ≥ 11, coprime to 10. n - 1 is exact for n ≥ 1, which is the full offset range.
- *Note.* This is a classical result (lifting the order from p to p^n when 10^(p-1) ≢ 1 mod p^2; 11 is not a base-10 Wieferich prime). The catalogue correctly labels it known-result-first-formalization.

## A335012: Repunit residues: a(n) = n - 1 exactly for long period primes

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a335012](../../results/oeis-a335012/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A335012.lean`](../../lean/Math0/Statements/OEIS/A335012.lean).

**The conjecture as stated in OEIS**

> %C A335012 Conjecture: a(n) = n-1 if and only if n is a long period prime (A006883), that is, n is a prime and the decimal expansion of 1/n has period n-1.  [entry by _Sen-Peng Eu_, May 19 2020; name: "Number of different remainders when the first n terms of 1, 11, 111, 1111, ... are divided by n.", offset 1. Local mirror equals upstream oeisdata (#31, Mar 12 2026).]

**The frozen Lean statement**

```lean
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).image (fun k => ((10 ^ k - 1) / 9) % n)).card

def IsLongPeriodPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p = 2 ∨ orderOf (10 : ZMod p) = p - 1)

def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n = n - 1 ↔ IsLongPeriodPrime n)
```

**What the Lean statement says**

For every integer n ≥ 1, let a(n) be the number of distinct residues mod n of the repunits R_1, ..., R_n, where R_k = (10^k - 1)/9. Then a(n) = n - 1 holds exactly when n is prime and either n = 2 or 10 has multiplicative order n - 1 modulo n.

**What the kernel checks against the OEIS data**

a_data checks all 81 listed terms a(1..81) with decide +kernel, and the definition is the entry's PARI/Maple program verbatim, so a is pinned down. isLongPeriodPrime_data checks, through the proven-equivalent Boolean isLongPeriodPrimeB (isLongPeriodPrimeB_iff), that the predicate selects exactly the first 24 terms of A006883 below 270 (2, 7, 17, ..., 269). That pins the predicate's handling of 2, 3 and 5. I also checked numerically that (a(n) = n-1) ⟺ IsLongPeriodPrime(n) for all n < 1500.

**Points for the reviewer**

- *Note.* 2 counts as a long period prime. That follows A006883, which includes 2 by an explicit comment (1/2 = 0.5000..., period 1), and its Maple program (p = 2 or ord_p(10) = p-1). Since a(2) = 1 = 2-1, excluding 2 would make the conjecture trivially false, so including it is the reading the author meant.
- *Note.* "Decimal period of 1/n is n-1" is encoded as ord_n(10) = n-1. This is equivalent for primes other than 2 and 5. For p = 5, Mathlib gives orderOf (0 : ZMod 5) = 0 ≠ 4, which matches the true period 1 ≠ 4. For p = 3, ord = 1 ≠ 2, which also matches.
- *Note.* The range is n ≥ 1, the entry's offset, and both directions of the iff are encoded. Without the hypothesis, n = 0 would hold vacuously via truncated subtraction (0 - 1 = 0), so the hypothesis is correct and loses nothing.

## A338885: A338885: the smallest number in row 655 is 104, not A228286(655) = 115

Verdict of the pre-review: **faithful**. Result: [oeis-a338885](../../results/oeis-a338885/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A338885.lean`](../../lean/Math0/Statements/OEIS/A338885.lean).

**The conjecture as stated in OEIS**

> %C A338885 Conjecture: The smallest number in the n-th row is A228286(n).  [entry by _Peter Kagey_, Nov 14 2020; name: "Irregular triangle read by rows in which the n-th row lists all numbers k such that there exists a diagonal lattice rectangle touching all four sides of an n X k rectangle."; "A diagonal lattice rectangle is a rectangle with integer coordinates and no side parallel to the x-axis."; offset 2. A228286: "Smallest x + y*z, given x*y + z = n (for positive integers x, y, z).", offset 2. Mirror equals upstream (#22, Sep 11 2021).]

**The frozen Lean statement**

```lean
def InBox (n k : ℕ) (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ p.1 ≤ n ∧ 0 ≤ p.2 ∧ p.2 ≤ k
def vertices (x₀ y₀ u₁ u₂ v₁ v₂ : ℤ) : List (ℤ × ℤ) :=
  [(x₀, y₀), (x₀ + u₁, y₀ + u₂), (x₀ + u₁ + v₁, y₀ + u₂ + v₂), (x₀ + v₁, y₀ + v₂)]
def InRow (n k : ℕ) : Prop :=
  ∃ x₀ y₀ u₁ u₂ v₁ v₂ : ℤ, u₁ * v₁ + u₂ * v₂ = 0 ∧ u₂ ≠ 0 ∧ v₂ ≠ 0 ∧
    (∀ p ∈ vertices x₀ y₀ u₁ u₂ v₁ v₂, InBox n k p) ∧
    (∃ p ∈ vertices .., p.1 = 0) ∧ (∃ p ∈ vertices .., p.1 = n) ∧
    (∃ p ∈ vertices .., p.2 = 0) ∧ (∃ p ∈ vertices .., p.2 = k)
def A228286List (n : ℕ) : List ℕ := (List.range' 1 (n - 1)).flatMap fun x =>
  (List.range' 1 (n - 1)).filterMap fun y => if x * y < n then some (x + y * (n - x * y)) else none
def A228286 (n : ℕ) : ℕ := (A228286List n).min?.getD 0

def statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → IsLeast {k : ℕ | InRow n k} (A228286 n)

(Settled negatively: Frontier result : ¬ statement, via n = 655, k = 104.)
```

**What the Lean statement says**

For every n ≥ 2, consider the k such that some rectangle with integer vertices, perpendicular sides and no horizontal side lies in the box [0,n]×[0,k] and has a vertex on each of the four lines x=0, x=n, y=0, y=k. The least such k equals min{x + y·z : x, y, z ≥ 1, x·y + z = n}.

**What the kernel checks against the OEIS data**

a_data checks the 71 listed terms (rows 2–12 complete and the start of row 13) with decide +kernel. These are computed from the list row n, and the proven theorem mem_row says row n contains exactly the k with InRow n k. The geometric InRow is itself proven equivalent (inRow_iff_param) to: n = a+b, k = c+d, ab = cd with a, b, c, d > 0. A228286_data checks 70 listed terms of A228286, and isLeast_A228286 proves that the computed A228286 n is the true minimum of the defining set for n ≥ 2. So both sides are pinned to the entries' definitions, not only to the data. I recomputed independently: A228286(655) = 115, the minimum of row 655 is 104, and the counterexamples below 1100 are 655, 845, 909 and 1019.

**Points for the reviewer**

- *Note.* This is a refutation, so the frozen statement must not be stronger than the conjecture. It is not: IsLeast {k | InRow n k} (A228286 n) is exactly "the smallest number in row n is A228286(n)". The counterexample is an explicit rectangle (4,0), (655,42), (651,104), (0,62): its sides (651,42) and (-4,62) are perpendicular and neither is horizontal. It puts 104 < 115 in row 655, so the conjecture fails under any reasonable reading of "touching all four sides".
- *Note.* Row 655 lies beyond the b-file (rows 2..101), so the counterexample rests on the geometric definition, not on listed data. That definition matches the entry's example: row 6 = 6, 9, 10, with width n and height k.

## A341761: The subword complexity polynomial S(n,x) has leading coefficient n(n+1)/2 (A341761, Guo's conjecture)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a341761](../../results/oeis-a341761/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A341761.lean`](../../lean/Math0/Statements/OEIS/A341761.lean).

**The conjecture as stated in OEIS**

> %C A341761 Conjecture: the coefficient of x^n in S(n,x) is n*(n+1)/2.  [entry by _Shiyao Guo_, Feb 19 2021; "S(n,x) is the sum of subword complexities (number of nonempty distinct subwords) of all words of length n and an alphabet with size x."; "The degree of S(n,x) is n."; offset 0. Mirror equals upstream (#33, Mar 20 2024).]

**The frozen Lean statement**

```lean
def factors {α} [DecidableEq α] (w : List α) : Finset (List α) :=
  (w.tails.flatMap fun t => t.inits.tail).toFinset   -- proven: u ∈ factors w ↔ u ≠ [] ∧ u <:+: w
def complexity (w : List α) : ℕ := (factors w).card
def S (n x : ℕ) : ℕ := ∑ w : Fin n → Fin x, complexity (List.ofFn w)

def statement : Prop :=
  ∀ n : ℕ, ∃ P : ℚ[X], (∀ x : ℕ, P.eval (x : ℚ) = (S n x : ℚ)) ∧
    P.coeff n = (n : ℚ) * (n + 1) / 2
```

**What the Lean statement says**

For every n ≥ 0, let S(n,x) be the total, over all x^n words of length n on an x-letter alphabet, of the number of distinct nonempty contiguous subwords. There is a rational polynomial P with P(x) = S(n,x) for every natural x, including x = 0, and its x^n coefficient is n(n+1)/2. Such a P is unique (poly_unique).

**What the kernel checks against the OEIS data**

rows_data checks rows n = 0..5 of the triangle with decide +kernel, by Newton interpolation of S(n,0..n), and a_data checks the 21 terms a(0..20). This pins down "subword = contiguous factor": the subsequence version would give different values from n = 3 on, e.g. S(3,2) ≠ 36. The entry's example (complexities 3,5,5,5,5,5,5,3 for length 3 over 2 letters) also fixes it. Row 6 is not kernel-checked (too many words); I recomputed it independently by brute force as [0,-2,10,-18,10,-15,21], which matches OEIS.

**Points for the reviewer**

- *Note.* The existential packs in polynomiality of S(n,·) on all of ℕ, including x = 0 where S(n,0) = 0 for n ≥ 1. This is at least as strong as the conjecture, which presupposes polynomiality, and P is unique, so no weaker reading is possible.
- *Note.* The statement does not also assert deg P = n. The entry states that as a fact, not as part of the conjecture, and "the coefficient of x^n" is well defined regardless of degree. Nothing is lost.
- *Note.* The kernel data check covers only rows 0–5. The definition is the literal one, so this is not a weakness of fidelity.

## A342645: A342645: diagonals of the eventual Mahonian-column polynomials

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a342645](../../results/oeis-a342645/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A342645.lean`](../../lean/Math0/Statements/OEIS/A342645.lean).

**The conjecture as stated in OEIS**

> %C A342645 Conjecture: For each m, T(n,n-m) is a polynomial of degree 2m whose leading coefficient is abs(A290030(m)/A053657(m+1)).
> %F A342645 Conjectures:
> %F A342645 T(n,n)   = 1.
> %F A342645 T(n,n-1) = (-3n + n^2)/2.
> %F A342645 T(n,n-2) = (-2n + 21n^2 - 22n^3 + 3n^4)/24.
> %F A342645 T(n,n-3) = (96n - 134n^2 + 13n^3 + 37n^4 - 13n^5 + n^6)/48.
> [entry by _Peter Kagey_, Mar 17 2021; name: "Triangle read by rows: T(n,k) gives n! times the coefficient of x^k in the polynomial that describes the number of permutations on x letters with major index n."; offset 0. Mirror equals upstream (#25, Aug 12 2022).]

**The frozen Lean statement**

```lean
-- mahonian x n = [q^n] ∏_{i<x} (1+q+…+q^i)  (proven = coeff of mahonianPoly; = majCount for x ≤ 6)
def column (n : ℕ) : List ℤ := (List.range (n + 1)).map fun i => (mahonian (n + i) n : ℤ)
def Trow (n : ℕ) : List ℤ := newton n 0 (diffHeads (n + 1) (column n))
  -- coefficients of n!·P_n, P_n = interpolant of degree ≤ n through (x, mahonian x n), x = n..2n
def T (n k : ℕ) : ℤ := (Trow n).getD k 0
def A290030 (n : ℕ) : ℤ := ((lcmDen (norlund n) : ℚ) * (norlund n).getD n 0).num
  -- norlund n = coefficient list in x of B_n^(x) = n![t^n](t/(e^t-1))^x
def A053657 (n : ℕ) : ℕ := ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
    p ^ (∑ k ∈ Finset.range n, (n - 1) / ((p - 1) * p ^ k))

def statementDiagonals : Prop :=
  ∀ m : ℕ, ∃ Q : ℚ[X], Q.degree = ((2 * m : ℕ) : WithBot ℕ) ∧
    Q.leadingCoeff = |(A290030 m : ℚ) / (A053657 (m + 1) : ℚ)| ∧
    ∀ n : ℕ, m ≤ n → (T n (n - m) : ℚ) = Q.eval (n : ℚ)
def statementFormulas : Prop :=
  (∀ n, T n n = 1) ∧
  (∀ n, 1 ≤ n → (T n (n-1) : ℚ) = (-3n + n^2)/2) ∧
  (∀ n, 2 ≤ n → (T n (n-2) : ℚ) = (-2n + 21n^2 - 22n^3 + 3n^4)/24) ∧
  (∀ n, 3 ≤ n → (T n (n-3) : ℚ) = (96n - 134n^2 + 13n^3 + 37n^4 - 13n^5 + n^6)/48)   [all in ℚ]
def statement : Prop := statementDiagonals ∧ statementFormulas
```

**What the Lean statement says**

Let M(x,n) be the Mahonian number, the coefficient of q^n in ∏_{i<x}(1+…+q^i). Let P_n be the polynomial of degree ≤ n through (x, M(x,n)) for x = n, …, 2n, and let T(n,k) = n!·[x^k]P_n. (1) For every m ≥ 0 there is a rational polynomial Q of degree exactly 2m, with leading coefficient |A290030(m)/A053657(m+1)|, such that T(n,n−m) = Q(n) for every n ≥ m. Here A290030(m) is L·[x^m]B_m^(x), with L the lcm of the denominators of the Nørlund polynomial B_m^(x), and A053657 is given by its product formula. (2) The four closed forms for T(n,n), T(n,n−1), T(n,n−2), T(n,n−3) hold for every n at which the entry exists.

**What the kernel checks against the OEIS data**

T_data and a_data check all 55 listed terms (rows 0–9) with decide +kernel. rowPoly_agrees checks for n ≤ 9 that ∑_k T(n,k)x^k = n!·M(x,n) at x = n..3n+2, beyond the interpolation nodes. mahonian_eq_majCount checks MacMahon (major-index count) for x ≤ 6. A290030_data checks 26 listed terms, norlund_check checks the Nørlund series for n ≤ 6 and x ≤ 8, and A053657_data checks all 19 listed terms. Together these pin down every ingredient. I also verified independently, with interpolation on the Mathematica nodes n..2n+2, that the four formulas hold for n < 22.

**Points for the reviewer**

- *Note.* T is defined by interpolation at x = n..2n. That equals the entry's "polynomial that describes" column n only because M(x,n) agrees with a single polynomial of degree ≤ n for all x ≥ n. This is classical: Netto, Knuth TAOCP 3 §5.1.1, and the MSE answer linked from the entry. The Mathematica program interpolates on n..2n+2 and gets the same polynomial. So T is the OEIS triangle, not merely a sequence that agrees on the checked rows.
- *Note.* Both conjectures are encoded in the strong form. Each holds for every n at which the entry exists (n ≥ m), not just eventually, and the COMMENT (diagonals) and FORMULA (four closed forms) conjectures are conjoined. Since the result proves this, it implies every weaker reading. Truncated n − m is never used outside n ≥ m.
- *Note.* A290030 uses "numerator = lcm-of-denominators × polynomial", mirroring Mathematica's Together/Numerator. No content cancels with L, as the docstring argues, and the 26 checked terms (signs included) confirm this. The abs in the conjecture makes the sign convention irrelevant anyway.
- *Note.* Catalog metadata only: the "area" field is "Discrete geometry", but the topic is enumerative combinatorics (Mahonian numbers). This does not affect the statement.

## A342992: Every n not divisible by 5 has a multiple with only prime digits (A342992)

Verdict of the pre-review: **faithful**. Result: [oeis-a342992](../../results/oeis-a342992/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A342992.lean`](../../lean/Math0/Statements/OEIS/A342992.lean).

**The conjecture as stated in OEIS**

> %C A342992 Conjecture: a(n) > 0 for all n that are not divisible by 5.  [entry by _Metin Sariyar_, Apr 13 2021; name: "Smallest k such that k*n contains only prime digits, or 0 if no such k exists."; offset 1. Mirror equals upstream (#60, Apr 22 2021).]

**The frozen Lean statement**

```lean
def PrimeDigits (m : ℕ) : Prop := 0 < m ∧ ∀ d ∈ Nat.digits 10 m, d.Prime

noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k, PrimeDigits (k * n) then Nat.find h else 0

def statement : Prop := ∀ n : ℕ, 1 ≤ n → ¬ 5 ∣ n → 0 < a n
```

**What the Lean statement says**

Every positive integer n not divisible by 5 has a positive multiple whose decimal digits all lie in {2, 3, 5, 7}. Equivalently, the least k with k·n having only prime digits exists and is nonzero.

**What the kernel checks against the OEIS data**

a_data checks all 81 listed terms a(1..81) with decide +kernel, through aSearch with bound 100, which the theorem a_eq_of_aSearch proves sound for both the minimality and the "0 when 10 | n" cases. a_four checks the entry's example a(4) = 8. This pins down the definition, including that k starts at 1 and that 0 is excluded as a digit string. a_pos_iff proves that 0 < a n ⟺ ∃ k, PrimeDigits (k·n). As an extra check, a BFS over residues finds a prime-digit multiple for every n < 3000 with 5 ∤ n.

**Points for the reviewer**

- *Note.* PrimeDigits requires m > 0, so the empty digit list of 0 cannot satisfy it vacuously. As a result k = 0 never qualifies, and a(n) > 0 is exactly the existence of a prime-digit multiple. This matches the entry's intent and its PARI program, which starts at k = 1.
- *Note.* The hypothesis 1 ≤ n is redundant (5 | 0), and the condition 5 ∤ n is the author's, a sufficient condition only. The 625k exceptions in Corneth's comment are all divisible by 5 and do not interact with the statement.
- *Note.* Catalog metadata only: upstream.decl for this entry is "def statement", not the qualified name "Math0.Statements.A342992.statement" that the other entries use. Cosmetic; the frontier file proves `result : statement` against the frozen file.

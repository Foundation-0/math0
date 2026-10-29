# Fidelity review packet 11 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A373359, A375522, A386538, A386655, A388724, A392943, A393794, A394981, A395454, A397315.

## A373359: A373359: Schreier-set row lengths equal the Zeckendorf weight A007895

Verdict of the pre-review: **faithful**. Result: [oeis-a373359](../../results/oeis-a373359/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A373359.lean`](../../lean/Math0/Statements/OEIS/A373359.lean).

**The conjecture as stated in OEIS**

> %Y A373359 Cf. A007895 (conjectured row lengths), A373346 (row sums), A373347. (Paolo Xausa, Jun 04 2024; entry rev #23, Jun 22 2024, the same on the live GitHub copy). Definition: "Irregular triangle read by rows where row n lists (in increasing order) the elements of the Schreier set encoded by A371176(n)." (offset 1). A371176: "Numbers k such that A000120(k) <= A001511(k)." (offset 1). A007895: "Number of terms in the Zeckendorf representation of n" (offset 0).

**The frozen Lean statement**

```lean
def IsTerm (k : ℕ) : Prop := 0 < k ∧ k.bitIndices.length ≤ padicValNat 2 (2 * k)
noncomputable def A371176 (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)
noncomputable def T (n : ℕ) : List ℕ := (A371176 n).bitIndices.map (· + 1)
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (T n).length = (Nat.zeckendorf n).length
```

**What the Lean statement says**

List the positive integers k whose number of 1-bits is at most v_2(2k), i.e. at most one more than the index of the lowest 1-bit, in increasing order: 1, 2, 4, 6, 8, ... Let c_n be the n-th of these (n >= 1). The claim is that for every n >= 1, the number of 1-bits of c_n (the size of the set of 1-based bit positions of c_n) equals the number of terms in the Zeckendorf representation of n.

**What the kernel checks against the OEIS data**

a_data checks all 91 listed terms of the flattened triangle (rows 1-42), and a_eq ties the computable flattening to T. code_data checks the first 42 terms of A371176 (1, 2, 4, 6, 8, ..., 160). statement_check verifies the claimed equality for n = 1..42 against Mathlib's Nat.zeckendorf, via zeckAux_eq. The bridging lemmas (bitPos_eq_bitIndices, isTermB_iff, code_eq_nth, row_eq_T) are proved, not assumed. Together these pin down the encoding (LSB = position 1), the ordering, the offset, and the alignment row n <-> A007895(n).

**Points for the reviewer**

- *Note.* Alignment: row n is matched with A007895(n), not with the n-th listed term A007895(n-1). This is the only alignment the data allows: row lengths 1,1,1,2,1,2,2,1,2,2,2,3 equal A007895(1..12), and row 1 = {1} rules out A007895(0) = 0. The k = 0 / empty Schreier set is excluded, as in A371176 (positive integers). Including it would add the true case 0 = A007895(0) anyway.
- *Note.* The condition popcount(k) <= v_2(2k) is the Schreier condition |X| <= min X under the LSB-first encoding. This matches the entry's example table (6 = 110_2 -> {2,3}; 28 -> {3,4,5}) and the Mathematica program (DigitCount <= IntegerExponent + 1).

## A375522: A375522: S2(n) - S1(n) = 1 fails at n = 42 (the difference is 5)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a375522](../../results/oeis-a375522/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A375522.lean`](../../lean/Math0/Statements/OEIS/A375522.lean).

**The conjecture as stated in OEIS**

> %C A375522 Let S(n) = Sum_{k = 1..n} 1 / (k*A375781(k)) = S1(n)/S2(n) when reduced to lowest terms, where S1(n) = A375521(n), S2(n) = the present sequence.
> %C A375522 The differences S2(n) - S1(n) are surprisingly small: for n = 1,2,...,34 the values S2(n) - S1(n) are:
> %C A375522 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1
> %C A375522 suggesting the conjecture that they are always 1 except for n = 4 and 6 (compare the Theorem in A374983).
> (Rémy Sigrist and N. J. A. Sloane, Aug 30 2024; rev #25, Apr 22 2025, unchanged on live GitHub.)

**The frozen Lean statement**

```lean
def prime (k : ℕ) : ℕ := primeAt (k - 1)   -- proved = Nat.nth Nat.Prime (k-1)
def s : ℕ → ℚ
  | 0 => 0
  | n + 1 => s n + 1 / ((prime (n + 1) : ℚ) *
      ((1 + ⌊1 / ((1 - s n) * (prime (n + 1) : ℚ))⌋ : ℤ) : ℚ))
def S1 (n : ℕ) : ℤ := (s n).num
def a (n : ℕ) : ℕ := (s n).den
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≠ 4 → n ≠ 6 → (a n : ℤ) - S1 n = 1
```

**What the Lean statement says**

Let p_k be the k-th prime. Set s(0) = 0 and s(k) = s(k-1) + 1/(p_k * b_k), where b_k = 1 + floor(1/((1 - s(k-1)) p_k)) is the least positive integer that keeps the sum below 1. Write s(n) in lowest terms as S1(n)/S2(n). The claim is that for every n >= 1 other than 4 and 6, S2(n) - S1(n) = 1. The result proves the negation.

**What the kernel checks against the OEIS data**

a_data checks all 11 listed terms of A375522 (n = 0..10). S1_data checks all 11 listed terms of A375521. b_data checks all 11 listed terms of A375781. diff_data checks S2(n) - S1(n) for n = 1..24 against the comment's list: 2 at n = 4 and 6, 1 elsewhere. primeAt_eq_nth proves the prime function is Mathlib's nth prime. With three independent sequences checked, the recursion, the primes and the offsets are pinned down.

**Points for the reviewer**

- *Note.* The entry's name and comment write 1/(k*A375781(k)), but the Lean uses 1/(prime(k)*A375781(k)). This is correct: A375781's own definition, every program in the entry, and the listed data all use prime(k), and the literal reading would give s(1) = 1. The data checks force the prime reading.
- *Note.* The Lean statement encodes only the 'always 1 except possibly at n = 4, 6' part, not that n = 4 and 6 really are exceptions (diff_data checks those separately). The statement is therefore weaker than the full conjecture. For a refutation (result : ¬ statement) this costs nothing: a counterexample at some n other than 4 and 6 (n = 42 per the catalogue) refutes the conjecture as worded.

## A386538: A386538: moving the circle's center off the grid enlarges the max lattice polygon (counterexample at n = 7)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a386538](../../results/oeis-a386538/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A386538.lean`](../../lean/Math0/Statements/OEIS/A386538.lean).

**The conjecture as stated in OEIS**

> %C A386538 Conjecture: The maximum possible area of a polygon within the circle would be the same if only the vertices but not the center were fixed on grid points. (Felix Huber, Aug 05 2025; rev #23, Aug 19 2025, unchanged on live GitHub.) Definition: "a(n) is the maximum possible area of a polygon within a circle of radius n, where both the center and the vertices lie on points of a unit square grid." (offset 0)

**The frozen Lean statement**

```lean
def latticeDisk (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℤ, p = ((x : ℝ), (y : ℝ)) ∧ ((x : ℝ) - c.1) ^ 2 + ((y : ℝ) - c.2) ^ 2 ≤ r ^ 2}
noncomputable def maxArea (c : ℝ × ℝ) (r : ℝ) : ENNReal :=
  volume (convexHull ℝ (latticeDisk c r))
def statement : Prop :=
  ∀ n : ℕ, (⨆ c : ℝ × ℝ, maxArea c n) = maxArea 0 n
```

**What the Lean statement says**

For every n >= 0, take the convex hull of the integer lattice points in the closed disk of radius n with center c. The claim is that the supremum of its Lebesgue area over all centers c in R^2 equals the area when the center is the origin. Equivalently, no center does better than a lattice-point center. The result proves the negation.

**What the kernel checks against the OEIS data**

a_data checks the listed a(0..12), a_data_more checks the listed a(14), a(15), a(16), a(19), a(20), a(21), a(24), a(25), and a_13 shows a(13) = 516 although 512 is listed. All of these are about a computable function `a` (monotone-chain hull plus shoelace formula at center 0). `a` is NOT proved equal to maxArea 0 n, so the kernel checks do not tie the statement's own definitions (latticeDisk, maxArea) to the data. Those definitions are a direct transcription, checked against the data only through the informal claim that `a` computes them.

**Points for the reviewer**

- *Minor.* Several listed terms from a(13) on are smaller than the true maximum area. The author's Maple/Mathematica program, 4n + 4*Sum floor(sqrt(n^2-x^2)) - 2*#distinct y, is not the convex-hull area for n >= 13; for example it gives 512 at n = 13, where the 20-gon on the circle has area 516. The Lean follows the entry's name (the maximum), not the program. This does not affect the result: the counterexample is at n = 7, where the listed a(7) = 138 equals the true maximum. I recomputed exactly that the center-0 hull has area 138 and that the hull for center (5/12, 5/24) has area 281/2.
- *Note.* 'Only the vertices but not the center fixed on grid points' is read as: the center is free and we take the supremum over it. The other readings are 'for every center the maximum is the same', 'for every off-grid center', or 'no off-grid center does better'. Each of them is implied by the sup reading or contradicted by the same witness, so the refutation settles every one of them.
- *Note.* Polygon area is taken as the area of the convex hull. Every polygon with vertices in a finite set S lies in conv(S), and conv(S) is itself a polygon with vertices in S inside the disk. Closed vs open disk does not affect the witness: I checked that no lattice point lies exactly on the circle of radius 7 around (5/12, 5/24). The closed disk is needed for the grid-center values (a(1) = 2).

## A386655: A386655 modulo 6 is eventually periodic with pattern [1, 0, 3, 0, 3, 2]

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a386655](../../results/oeis-a386655/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A386655.lean`](../../lean/Math0/Statements/OEIS/A386655.lean).

**The conjecture as stated in OEIS**

> %C A386655 Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating. (Paul D. Hanna, Aug 23 2025; rev #14, Aug 24 2025, unchanged on live GitHub.) Definition: "E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!." (offset 0); the entry also lists the formula a(n) = Sum_{k=0..n} binomial(n,k) * 2^(k*(k+1)) * (2^k - (n-k))^(n-k-1).

**The frozen Lean statement**

```lean
def term (n k : ℕ) : ℤ :=
  if k = n then 2 ^ (n * n)
  else (binom n k : ℤ) * 2 ^ (k * (k + 1)) * ((2 : ℤ) ^ k - ((n - k : ℕ) : ℤ)) ^ (n - k - 1)
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), term n k
def statement : Prop :=
  ∀ n : ℕ, 6 ≤ n → a n % 6 = ([1, 0, 3, 0, 3, 2] : List ℤ).getD ((n - 6) % 6) 0
```

**What the Lean statement says**

Let a(n) = Sum_{k=0..n} C(n,k) 2^{k(k+1)} (2^k - (n-k))^{n-k-1}, where the k = n term is read as 2^{n^2} and 0^0 = 1 (binom is proved equal to Nat.choose). The claim is that for every n >= 6, a(n) mod 6 (least nonnegative residue) is 1, 0, 3, 0, 3, 2 according as n ≡ 0, 1, 2, 3, 4, 5 (mod 6).

**What the kernel checks against the OEIS data**

a_data checks all 13 listed terms (n = 0..12). a_eq_egf checks in the kernel that the explicit formula equals a literal truncated-e.g.f. evaluation of Sum_m (2^m x + W(x))^m/m! for n = 0..16. Here W comes from fixed-point iteration, and lambertW_spec checks W e^W = x up to x^16 and the coefficients 0, 1, -2, 9, -64, ... statement_data checks the residue pattern for n = 6..12. The checks pin the formula, the k = n convention, the LambertW branch/sign and the alignment of the pattern (a(6) ≡ 1).

**Points for the reviewer**

- *Note.* The definition is the explicit sum from the entry's FORMULA section, not the e.g.f. in the name. The two agree for all n by a classical identity: expand by the binomial theorem to Sum_j 2^{j^2} e^{2^j W} x^j/j!, then use e^{cW} = Sum_k c(c-k)^{k-1} x^k/k!. The k = n convention 2^{n^2} matches the k = 0 term of that expansion. The equivalence is not proved in Lean and is kernel-checked only up to n = 16; it is mathematically standard and not a conjectural formula.
- *Note.* The threshold n >= 6 is the author's. The pattern really does fail earlier: the residues for n = 0..5 are 1, 3, 5, 0, 3, 2. The Lean matches the stated range.

## A388724: Column sums of strictly superdiagonal reversed partitions by maximum are A000245

Verdict of the pre-review: **faithful**. Result: [oeis-a388724](../../results/oeis-a388724/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A388724.lean`](../../lean/Math0/Statements/OEIS/A388724.lean).

**The conjecture as stated in OEIS**

> %F A388724 Conjecture: Column sums are A000245. (Gus Wiseman, Sep 24 2025; rev #12, Oct 06 2025, unchanged on live GitHub.) Definition: "Triangle read by rows where T(n,k) is the number of strictly superdiagonal reversed integer partitions of n with maximum k." with "A sequence (y_1, ..., y_k) is strictly superdiagonal iff y_i > i for all i = 1..k." (offset 0, tabl). A000245: a(n) = 3*(2*n)!/((n+2)!*(n-1)!), data 0, 1, 3, 9, 28, 90, ...

**The frozen Lean statement**

```lean
def IsRevPartition (n : ℕ) (y : List ℕ) : Prop :=
  (∀ x ∈ y, 0 < x) ∧ y.Pairwise (· ≤ ·) ∧ y.sum = n
def StrictlySuperdiagonal (y : List ℕ) : Prop := ∀ i (h : i < y.length), i + 1 < y[i]
noncomputable def T (n k : ℕ) : ℕ :=
  {y : List ℕ | IsRevPartition n y ∧ StrictlySuperdiagonal y ∧ y.max? = some k}.ncard
def A000245 (n : ℕ) : ℕ :=
  if n = 0 then 0 else 3 * (2 * n).factorial / ((n + 2).factorial * (n - 1).factorial)
def statement : Prop := ∀ k : ℕ, 1 ≤ k → ∑ᶠ n, T n k = A000245 (k - 1)
```

**What the Lean statement says**

For k >= 1, count the weakly increasing lists (y_1 <= ... <= y_m) of positive integers with y_i > i for every i and largest entry exactly k, of any sum. The claim is that this count equals A000245(k-1) = 3(2k-2)!/((k+1)!(k-2)!), with value 0 when k = 1. The finsum over n is an honest finite sum: T(n,k) = 0 for n > k(k-1) is proved.

**What the kernel checks against the OEIS data**

a_data checks all 78 listed terms (rows 0..11) through the proved bridge T_eq_Tc, an enumeration of partitions proved complete and duplicate-free. A000245_data checks 28 listed terms of A000245. statement_check verifies column sums 0, 1, 3, 9, 28 for k = 1..5. I independently recomputed the column sums for k = 0..10 (0, 0, 1, 3, 9, 28, 90, 297, 1001, 3432, 11934), which agree with A000245(k-1) for k >= 1.

**Points for the reviewer**

- *Note.* Alignment: the column sums for k = 0, 1, 2, ... are 0, 0, 1, 3, 9, 28, ..., so 'Column sums are A000245' can only mean column k sums to A000245(k-1). Column 0, which is identically 0, is left out of the claim. This is the only alignment consistent with the values, and nothing substantive is lost.
- *Note.* The empty partition of 0 is counted in no column (max? = none), matching T(0,0) = 0 and Mathematica's Max[] = -Infinity. Columns sum over all n, and T(n,k) = 0 for n < k, so this agrees with summing over the triangle's column n >= k.

## A392943: No primitive Heronian triangle has integer circumradius

Verdict of the pre-review: **faithful**. Result: [oeis-a392943](../../results/oeis-a392943/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A392943.lean`](../../lean/Math0/Statements/OEIS/A392943.lean).

**The conjecture as stated in OEIS**

> %C A392943 Conjecture: There is no primitive Heronian triangle with integer circumradius. (entry by _Felix Huber_, Feb 04 2026; revision #5, Feb 08 2026, unchanged upstream)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ x y z K R : ℕ, IsTriangle x y z → HasArea x y z K → Nat.gcd x (Nat.gcd y z) = 1 →
    4 * K * R ≠ x * y * z

where
def IsTriangle (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x < y + z ∧ y < x + z ∧ z < x + y
def heron16 (x y z : ℕ) : ℤ :=
  ((x : ℤ) + y + z) * (-x + y + z) * (x - y + z) * (x + y - z)
def HasArea (x y z K : ℕ) : Prop :=
  16 * (K : ℤ) ^ 2 = heron16 x y z
```

**What the Lean statement says**

Take positive integers x, y, z satisfying the strict triangle inequalities, with gcd(x, y, z) = 1, and a natural number K with 16K^2 = (x+y+z)(-x+y+z)(x-y+z)(x+y-z), i.e. K is the (integer) area. Then no natural number R satisfies 4KR = xyz, i.e. the circumradius xyz/(4K) is not an integer.

**What the kernel checks against the OEIS data**

a_data kernel-checks a(1..30) (of 88 listed terms), via count/A392942, which go through IsGood = IsTriangle ∧ ∃ K R, HasArea ∧ 4KR = xyz (goodB_iff is proved). So the same IsTriangle/HasArea/heron16 that the statement uses are exercised on real data (e.g. (30,30,48) with area 432 and R = 25 is counted). The statement itself does not use a, count or A392942. Its definitions are a direct transcription of Heron's formula and R = xyz/(4K), so the data check is extra assurance, not the main evidence.

**Points for the reviewer**

- *Note.* Degenerate cases are harmless. Under IsTriangle, heron16 > 0, so any K with HasArea is positive and unique, and R = 0 gives 0 ≠ xyz automatically. All arithmetic is in ℤ, so there is no truncated subtraction.
- *Note.* 'Primitive Heronian' is encoded as integer sides, integer area and gcd(x,y,z) = 1, which is the standard meaning. Integer circumradius is ∃ R ∈ ℕ, 4KR = xyz, which is exact because K > 0. Scaled triangles such as (6,8,10) (gcd 2, R = 5) are correctly excluded by the gcd hypothesis.
- *Note.* The catalog records this as a known result (van Luijk 2008: a Heron triangle with integer circumradius has all sides even). That is consistent with the statement as encoded.

## A393794: The 1089-trick map has two 9-digit fixed points (A393794 uniqueness conjecture is false)

Verdict of the pre-review: **faithful**. Result: [oeis-a393794](../../results/oeis-a393794/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A393794.lean`](../../lean/Math0/Statements/OEIS/A393794.lean).

**The conjecture as stated in OEIS**

> %C A393794 a(n) is the unique fixed point of the 1089-trick map T among all (n+4)-digit numbers (verified exhaustively for n = 1..4; conjectured for all n >= 1). Name: "Fixed points of the 1089-trick map T(n) = |n - reverse(n)| + reverse(|n - reverse(n)|)." %F a(n) = 110*(10^(n+1) - 1). (_Remco Havenaar_, Feb 27 2026; #19, Mar 10 2026, unchanged upstream)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Nat.digits 10 (a n)).length = n + 4 ∧ T (a n) = a n ∧
      ∀ x : ℕ, (Nat.digits 10 x).length = n + 4 → T x = x → x = a n

where
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse
def T (x : ℕ) : ℕ := Nat.dist x (rev x) + rev (Nat.dist x (rev x))
def a (n : ℕ) : ℕ := 110 * (10 ^ (n + 1) - 1)
```

**What the Lean statement says**

Let rev(m) be the decimal reversal of m (leading zeros of the result dropped), and T(x) = |x - rev x| + rev(|x - rev x|). For every n ≥ 1, the number 110·(10^(n+1) - 1) has exactly n+4 decimal digits and is fixed by T, and every (n+4)-digit x with T(x) = x equals it.

**What the kernel checks against the OEIS data**

a_data checks all 18 listed terms. T_data checks that T fixes each of them. digits_data checks that a(i+1) has i+5 digits. least_fixed_point checks that 10890 is the least positive fixed point of T. Together these pin down T's reversal convention: an unpadded reversal of D is needed. With D padded to 5 digits, T(10890) = 1089 + 98010 = 99099 ≠ 10890, so the padded variant fails T_data. The entry's worked example ('1089 + 9801 = 10890') uses the unpadded reversal as well. Taking a from the closed formula, not 'the n-th fixed point', matches the data and both programs, and avoids a circular statement.

**Points for the reviewer**

- *Note.* The statement adds two conjuncts, 'a n has n+4 digits' and 'T(a n) = a n', to the uniqueness clause. Both are true; the entry proves T(110R) = 110R. Negating the conjunction is therefore equivalent to refuting uniqueness. The frozen result does exactly that: it applies the uniqueness clause at n = 5 to x = 108910890.
- *Note.* Independent check: 108910890 has 9 digits (n = 5). rev = 98019801, the difference is 10891089, its reversal is 98019801, and the sum is 108910890. So it is a fixed point other than a(5) = 109999890. It is 10·10891089, a non-primitive term of A001232. The entry's own comment points at such terms when it calls a(n)/10 the 'primitive' A001232 terms. The uniqueness claim nonetheless says 'unique among all (n+4)-digit numbers', so this counterexample answers the conjecture as worded and as meant. Nothing in the entry restricts the claim to primitive terms.

## A394981: Bar tilings of the smallest-perimeter rectangle: a(n+1) = 4 a(n) for odd n >= 3 (A394981)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a394981](../../results/oeis-a394981/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A394981.lean`](../../lean/Math0/Statements/OEIS/A394981.lean).

**The conjecture as stated in OEIS**

> %F A394981 Conjecture: If n is odd, then a(n+1) = 4*a(n). (unattributed formula line; entry by _Gary Yane_, Apr 08 2026; a(1)-a(2) corrected by _Pontus von Brömssen_, May 13 2026; #42, May 16 2026, unchanged upstream). Name: number of tilings up to symmetry of the rectangle having smallest possible perimeter with area n(n+1)/2 using all n tiles 1 X 1, ..., 1 X n. Comment: '...the short side of the rectangle has length floor((n+1)/2)' (n=8: 4 X 9).

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n → a (n + 1) = 4 * a n

where (abridged)
def rows (n : ℕ) : ℕ := (n + 1) / 2
def cols (n : ℕ) : ℕ := n * (n + 1) / 2 / rows n
def a (n : ℕ) : ℕ :=
  let r := rows n; let c := cols n; let w := c + 1
  search w (r * w) n (stabCount r c w n) n (rectMask r c w) 0 /
    (1 + (otherSymmetries r c).length)
-- search: places tiles n, n-1, ..., 1 (each horizontally, or vertically if length ≥ 2) at every placement
-- inside the free cells (padded row bitmask), requires no free cell at the end, and sums stabCount of the
-- resulting labelling; stabCount = 1 + #{non-identity symmetries g of the r×c rectangle with label∘g = label};
-- otherSymmetries = the 2 axis reflections + half-turn (+ the 4 extra square symmetries when r = c).
```

**What the Lean statement says**

Let a(n) be the number of orbits, under the symmetry group of the rectangle, of tilings of the floor((n+1)/2) × (n(n+1)/2)/floor((n+1)/2) rectangle (that is, ((n+1)/2) × n for odd n and (n/2) × (n+1) for even n) by the n bars 1×1, 1×2, ..., 1×n, each used exactly once. The orbits are counted with Burnside's lemma. The claim is that for every odd n ≥ 3, a(n+1) = 4·a(n).

**What the kernel checks against the OEIS data**

a_data kernel-checks a(1..9) = 1,1,1,4,10,40,112,448,1360, which match the listed terms. rect_data and area_data check the rectangle shapes and areas for n ≤ 20; for example the n = 8 rectangle is 4×9, as in the comment. The data pin down the 'up to symmetry' convention: for n = 4 the raw count would be 16, not 4. They also pin the 1×1 bar being placed only once and the bars being distinguishable. The data cover the conjectured pairs n = 3, 5, 7. a(10) and a(11) agree with #eval only, not the kernel.

**Points for the reviewer**

- *Minor.* The literal conjecture ('if n is odd') includes n = 1, but the entry's corrected data give a(2) = 1 ≠ 4 = 4·a(1). The statement restricts to odd n ≥ 3, and literal_fails_at_one kernel-checks the failure at n = 1. This is a deliberate weakening of the literal text, needed because the literal text is false at its first instance. It is the evident intent: the pattern holds for every listed pair n = 3, ..., 19. A reviewer should accept that n = 1 is a degenerate exception (1-row rectangles, after the May 2026 data correction) and not part of what the author meant.
- *Note.* The rectangle is fixed by the comment's formula (short side floor((n+1)/2)), not by minimising the perimeter over all factorisations. The two agree with the intended reading: the 1×n bar needs a side ≥ n, and the least such divisor L of n(n+1)/2 is n (odd n) or n+1 (even n). This is also what excludes the 6×6 square for n = 8, as the comment says.
- *Note.* The symmetry group is the full symmetry group of the rectangle (order 4, or order 8 for the 1×1 square), as 'up to symmetry' suggests, and the data confirm it. Burnside's integer division is exact.

## A395454: Alexandersson's recurrence for the row polynomials of A395454 holds (rows counted from 1)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a395454](../../results/oeis-a395454/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A395454.lean`](../../lean/Math0/Statements/OEIS/A395454.lean).

**The conjecture as stated in OEIS**

> %F A395454 Conjecture: Let P(n) be the generating polynomial (in t) of row n. Then P(n) = (n - 2*t + n*t - 2)*P(n-1) + (t - t^2)*P'(n-1) + t*(2*n-4)*P(n-2). - _Per W. Alexandersson_, Jun 27 2026. (Entry by _Peter Luschny_, Apr 23 2026, offset 0, rows displayed as [0] 1; [1] 0, 0; [2] 0, 2, 0; ... ; upstream #30 differs from the mirror only by dropping the 'changed' keyword.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    P1 n = ((n : ℤ[X]) - 2 * X + (n : ℤ[X]) * X - 2) * P1 (n - 1)
      + (X - X ^ 2) * derivative (P1 (n - 1))
      + X * (2 * (n : ℤ[X]) - 4) * P1 (n - 2)

where
def E2 : ℕ → ℕ → ℤ   -- second-order Eulerian numbers A201637
  | 0, 0 => 1 | 0, _ + 1 => 0 | n + 1, 0 => E2 n 0
  | n + 1, k + 1 => (2 * ((n : ℤ) + 1) - 1 - ((k : ℤ) + 1)) * E2 n k + ((k : ℤ) + 1 + 1) * E2 n (k + 1)
def T (n k : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (n.choose j : ℤ) * E2 j (n - k)
noncomputable def P (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ k
noncomputable def P1 (n : ℕ) : ℤ[X] := P (n - 1)
(statement_literal, with P in place of P1 and n ≥ 2, is recorded and refuted: not_statement_literal.)
```

**What the Lean statement says**

Let T(n,k) = Σ_{j=0..n} (-1)^{n-j} C(n,j) E2(j, n-k), where E2 is the second-order Eulerian triangle, and let P_m(t) = Σ_{k=0..m} T(m,k) t^k (so P_0 = 1, P_1 = 0, P_2 = 2t, P_3 = 6t + 2t^2, ...). Then for every n ≥ 3, P_{n-1} = (n - 2 - 2t + nt)·P_{n-2} + (t - t^2)·P'_{n-2} + t(2n-4)·P_{n-3} in Z[t]. In the entry's own numbering (m = n-1 ≥ 2) this reads P_m = (m-1)(1+t)P_{m-1} + (t - t^2)P'_{m-1} + 2(m-1)t·P_{m-2}. In other words, the recurrence holds with the rows counted from 1.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 55 listed terms (rows 0..9), including the zero entries, and E2_data checks rows 0..8 of A201637. This fully pins the triangle T, including the reading of Maple's binomial(-j-1, -n-1) = (-1)^(n-j) C(n,j). P, P' and the coefficients follow the formula's text. The recurrence itself is not kernel-checked for small n. In an independent Python check, the shifted reading holds for n = 3..29 and the literal reading fails at every n = 2..19. By hand: n = 4 gives (2+2t)(2t) + (t - t^2)·2 = 6t + 2t^2, which is row 3.

**Points for the reviewer**

- *Minor.* Index shift: the statement does not take 'row n' in the entry's offset-0 numbering. Read that way the recurrence is false at n = 2, since the RHS is 0 (P_1 = 0) while P_2 = 2t, and it fails at every n tested. The frozen statement uses P(n) := row n-1, i.e. rows counted from 1. Of the readings I checked, this is the only nearby one that makes the formula true; reversing the row polynomials or dividing by t both fail at once. It almost certainly reflects the author's 1-based row indexing. Still, it is an interpretive reindexing, not the literal text, and a human reviewer should approve it. The proof settles the shifted claim, which is the only meaningful version.
- *Note.* The range n ≥ 3 loses nothing. In the shifted reading, n = 2 holds trivially (both sides are 0, and the P1(0) term has coefficient 2n-4 = 0). All coefficients (n-2, 2n-4) are integers in Z[X], so there is no truncated subtraction. P1(n-2) for n ≥ 3 never reaches a junk index.

## A397315: A397315: a 14-point blackout of the 5 x 8 grid refutes T(n,m) = n + m

Verdict of the pre-review: **faithful**. Result: [oeis-a397315](../../results/oeis-a397315/README.md) (known-result-already-formalized). Frozen statement: [`lean/Math0/Statements/OEIS/A397315.lean`](../../lean/Math0/Statements/OEIS/A397315.lean).

**The conjecture as stated in OEIS**

> %C A397315 Conjecture: T(n,m) = n+m whenever min(n,m) >= 4, except T(4,4) = 7 and T(4,5) = 8 (verified on seven cells through 6 X 6). (_Arjun Pemmasani_, Sep 02 2026; #38, Sep 12 2026, unchanged upstream.) Name: T(n,k) = maximum number of points that can be blacked out of an n X k grid of points so that every rectangle with all four vertices on grid points (tilted rectangles included) is uniquely identifiable from its set of visible vertices; n, k >= 2. Comment: injectivity of R -> C(R) \ S.

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n m : ℕ, 4 ≤ min n m →
    T n m = if n = 4 ∧ m = 4 then 7
      else if (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 4) then 8
      else n + m

where (abridged)
def pt (n i : ℕ) : ℤ × ℤ := (((i / n : ℕ) : ℤ), ((i % n : ℕ) : ℤ))   -- grid {0..k-1}×{0..n-1}
def rectMask? (n k a b c : ℕ) : Option ℕ := -- some {a,b,c,d} iff a,b,c distinct, (A-B)·(C-B) = 0, D = A+C-B in grid
def rects (n k : ℕ) : List ℕ := (all such vertex-set bitmasks over a,b,c < n*k).eraseDups
def visible (R B : ℕ) : ℕ := Nat.xor R (Nat.land R B)          -- R \ B
def isValidBlackout (n k B : ℕ) : Bool := pairwiseDistinct ((rects n k).map (visible · B))
def T (n k : ℕ) : ℕ :=
  ((List.range (2 ^ (n * k))).filter (isValidBlackout n k)).foldr (fun B m => max (card (n * k) B) m) 0
```

**What the Lean statement says**

For the grid {0..k-1} × {0..n-1}, call a rectangle any 4-point vertex set {a, b, c, a+c-b} of grid points with a, b, c distinct and a right angle at b. This includes tilted rectangles and squares. T(n,k) is the largest size of a set B of grid points such that distinct rectangles R ≠ R' always have R \ B ≠ R' \ B. The claim is that for all n, m ≥ 4, T(n,m) = n + m, except T(4,4) = 7 and T(4,5) = T(5,4) = 8.

**What the kernel checks against the OEIS data**

T_2_2 ... T_5_2 kernel-check the first 10 terms (4,4,4,5,5,5,6,6,6,6; grids of at most 12 points), and cell_data checks the antidiagonal order. These cells all have min(n,k) ≤ 3, so none lies in the conjecture's range. They also do not distinguish 'tilted rectangles included' from 'axis-parallel only': my Python check gives the same values 5, 6, 6, 6 for 3×3, 3×4, 4×3 and 2×5 either way. The tilted-rectangle condition is instead certified by inspection: the Lean rectMask? is a line-by-line transcription of the entry's Python and PARI programs (all ordered triples with a right angle at b and the fourth vertex in the grid). A Python transcription reportedly reproduces 15 terms.

**Points for the reviewer**

- *Note.* The exception 'T(4,5) = 8' is read symmetrically, as also covering T(5,4). This is forced: T is symmetric under transposition, and the entry's own data list T(5,4) = 8. The literal one-cell reading would contradict the data and would be trivially false at (5,4). The refutation sits at (5,8), away from both exceptional cells, so this reading does not affect the outcome.
- *Note.* The kernel data check reaches no cell with min(n,m) ≥ 4 and does not separate tilted from axis-parallel rectangles. Fidelity of T rests on the definition matching the entry's programs, which it does on inspection. The catalog notes that the author's own repository records T(5,8) = 14, which agrees with the frozen result (T(5,8) ≥ 14 > 13).
- *Note.* The statement asserts the conjecture for all n, m ≥ 4, which is the author's range, with no finite cutoff. The parenthetical 'verified on seven cells through 6 X 6' is evidence, not a restriction, and it is correctly left out.

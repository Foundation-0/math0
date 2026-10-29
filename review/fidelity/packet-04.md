# Fidelity review packet 04 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A127767, A129455, A132616, A141412, A144637, A160848, A172164, A175385, A176206, A178295.

## A127767: The inverse of the 1/Catalan band triangle (A127767) has integer entries

Verdict of the pre-review: **faithful**. Result: [oeis-a127767](../../results/oeis-a127767/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A127767.lean`](../../lean/Math0/Statements/OEIS/A127767.lean).

**The conjecture as stated in OEIS**

> %C A127767 It is conjectured that all elements of the triangle are integers. [Paul Barry, Jan 28 2007]
> (Name: "Inverse of number triangle A(n,k) = 1/C(n) if k <= n <= 2k, 0 otherwise, where C(n) = A000108(n)."; offset 0, keywords sign,tabl; PARI by Michel Marcus uses (i+1)/binomial(2*i,i) = 1/C(i).)

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n k : ℕ, k ≤ n → ∃ z : ℤ, T n k = z

with
  def cat : ℕ → ℕ | 0 => 1 | n + 1 => cat n * (2 * (2 * n + 1)) / (n + 2)   -- cat_eq_catalan: cat n = catalan n
  def A (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (cat n : ℚ) else 0
  T n k : ℚ := forward substitution T(n,k) = C(n) · ([n = k] - Σ_{j<n} A(n,j) T(j,k)) for k ≤ n, 0 for k > n (T_spec)
Proved helpers: inv_Amat ((Amat N)⁻¹ = Tmat N for every N), statement_iff_matrix.
```

**What the Lean statement says**

Let C(n) be the Catalan numbers, and let A be the infinite lower-triangular rational matrix with A(n,k) = 1/C(n) when k ≤ n ≤ 2k and 0 otherwise. Let T be its inverse, which is proved to be the inverse of every finite leading block. Then every entry T(n,k) with 0 ≤ k ≤ n is an integer.

**What the kernel checks against the OEIS data**

a_data (decide +kernel): all 66 listed terms (rows 0..10). rows_data (decide +kernel): the same rows as lists. cat is proved equal to Mathlib's catalan for all n (cat_eq_catalan), so the integer-division recursion cannot be a junk value. inv_Amat proves T is the inverse of every truncation, so the definitions are pinned by proof, not only by the checked terms.

**Points for the reviewer**

- *Note.* cat uses natural-number division in its recursion. This is harmless, because cat_eq_catalan proves it equals Mathlib's catalan for every n.
- *Note.* Catalog metadata only: the catalog's 'area' is 'Discrete geometry', which does not fit.

## A129455: The triple-gcd Pascal triangle A129455: T(n,k) is an integer, divisible by C(n,k), and T(n,k)/C(n,k) is a sixth power

Verdict of the pre-review: **faithful**. Result: [oeis-a129455](../../results/oeis-a129455/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A129455.lean`](../../lean/Math0/Statements/OEIS/A129455.lean).

**The conjecture as stated in OEIS**

> %C A129455 It appears that the T(n,k) are always integers. This would follow from the conjectured prime factorization given in A129454. Calculation suggests that the binomial coefficients C(n,k) divide T(n,k) and that T(n,k)/C(n,k) are perfect sixth powers. [Peter Bala, Apr 16 2007]
> (Name: "An analog of Pascal's triangle based on A129454. T(n, k) = A129454(n+1)/(A129454(n-k+1)*A129454(k+1))."; offset 0. A129454 (offset 0): a(n) = Product{i=1..n-1} Product{j=1..n-1} Product{k=1..n-1} gcd(i,j,k), with a(n) = 1 for n ≤ 2.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n k : ℕ, k ≤ n →
    A129454 (n - k + 1) * A129454 (k + 1) ∣ A129454 (n + 1) ∧
    n.choose k ∣ T n k ∧
    ∃ m : ℕ, T n k / n.choose k = m ^ 6

with
  def A129454 (n : ℕ) : ℕ :=
    ∏ i ∈ Finset.Icc 1 (n - 1), ∏ j ∈ Finset.Icc 1 (n - 1), ∏ k ∈ Finset.Icc 1 (n - 1), Nat.gcd (Nat.gcd i j) k
  def T (n k : ℕ) : ℕ := A129454 (n + 1) / (A129454 (n - k + 1) * A129454 (k + 1))
```

**What the Lean statement says**

Let G(m) = Π_{i,j,l=1..m} gcd(i,j,l), so G(0) = 1, and set T(n,k) = G(n)/(G(k)·G(n-k)). For all 0 ≤ k ≤ n: (1) G(k)·G(n-k) divides G(n), so T(n,k) is an exact integer; (2) the binomial coefficient C(n,k) divides T(n,k); (3) T(n,k)/C(n,k) is m^6 for some natural number m. Natural-number division appears only in T and in T/C(n,k), and both are exact because of (1) and (2), which are asserted in the same conjunction.

**What the kernel checks against the OEIS data**

A129454_data (decide +kernel): the first 10 terms of A129454 (n = 0..9). This checks the empty-product convention for n = 0, 1, 2 and the gcd product. a_data (decide +kernel): all 45 listed terms of A129455 (rows 0..8). statement_check (decide +kernel): all three claims hold for rows n ≤ 8, with explicit sixth roots. A129454 and T are literal transcriptions of the OEIS formulas, so the data check confirms the transcription rather than replacing a definition.

**Points for the reviewer**

- *Note.* T uses ℕ division. This is sound only because divisibility (1) is a conjunct of the statement, and likewise (2) makes T/C(n,k) in (3) exact. Since the statement is proved, all three hold with exact quotients. n - k is used only under k ≤ n, so truncated subtraction never fires.
- *Note.* 'perfect sixth power' allows m = 0 (and m = 1). T(n,k) ≥ 1, so the quotient is never 0, and the boundary entries T(n,0)/C(n,0) = 1 = 1^6 are correctly counted as sixth powers.
- *Note.* Bala's remark that integrality 'would follow from the conjectured prime factorization given in A129454' is an explanation and is correctly not encoded. The A129454 factorization conjecture is a separate claim and is not settled by this statement.
- *Note.* Catalog metadata only: the catalog's 'area' is 'Discrete geometry', which does not fit.

## A132616: Irwin's nested sums give column 0 of the triangle A132615 (A132616)

Verdict of the pre-review: **faithful**. Result: [oeis-a132616](../../results/oeis-a132616/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A132616.lean`](../../lean/Math0/Statements/OEIS/A132616.lean).

**The conjecture as stated in OEIS**

> %F A132616 From _Benedict W. J. Irwin_, Nov 29 2016: (Start) Conjecture: a(n) is described by a series of nested sums, a(2) = Sum_{i=1..1} 1, a(3) = Sum_{i=1..1+2} Sum_{j=1..i} 1, a(4) = Sum_{i=1..1+4} Sum_{j=1..i+2} Sum_{k=1..j} 1, a(5) = Sum_{i=1..1+6} Sum_{j=1..i+4} Sum_{k=1..j+2} Sum_{l=1..k} 1, and so on, where 2, 4, 6,... are the even numbers. (End)
> [Entry: %N Column 0 of triangle A132615, offset 0, Paul D. Hanna Aug 24 2007. A132615 %N: Triangle T, read by rows, where row n+1 of T = row n of T^(2n-1) with appended '1' for n>=0 with T(0,0)=1.]

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 2 ≤ n → a n = nest (n - 1) 1

def tri : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℕ
  | 0 => 1
  | n + 1 => Matrix.of fun i j =>
      if hi : (i : ℕ) ≤ n then
        if hj : (j : ℕ) ≤ n then tri n ⟨i, _⟩ ⟨j, _⟩ else 0
      else
        if hj : (j : ℕ) ≤ n then (tri n ^ (2 * n - 1)) (Fin.last n) ⟨j, _⟩ else 1
def T (n k : ℕ) : ℕ := if h : k ≤ n then tri n (Fin.last n) ⟨k, _⟩ else 0
def a (n : ℕ) : ℕ := T n 0
def nest : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, c => ∑ i ∈ Icc 1 (c + 2 * m), nest m i
```

**What the Lean statement says**

Build a lower-triangular matrix of naturals row by row: row 0 is [1]; row n+1 is row n of the (2n-1)-th power of the triangle built so far (exponent 0 when n = 0), followed by a 1 on the diagonal. Let a(n) be the entry in row n, column 0. Define nest(0,c) = 1 and nest(m+1,c) = sum over i = 1..c+2m of nest(m,i). Claim: for every n >= 2, a(n) = nest(n-1, 1), i.e. a(n) equals the (n-1)-fold nested sum Sum_{i1=1..1+2(n-2)} Sum_{i2=1..i1+2(n-3)} ... Sum_{i_{n-1}=1..i_{n-2}} 1.

**What the kernel checks against the OEIS data**

T_data: all 55 listed terms of A132615 (rows 0..9) by decide +kernel. a_data: all 19 listed terms a(0..18) of A132616 by decide +kernel. nest_two..nest_five: rfl proofs that nest(n-1,1) is literally Irwin's displayed expression for n = 2,3,4,5. statement_check: identity for 2 <= n <= 12 by kernel. The triangle data (55 terms, incl. row 1 = [1,1] which tests the n=0 exponent handling) pin the definition of T; the rfl lemmas pin the 'and so on' pattern of nest against the four displayed cases.

**Points for the reviewer**

- *Note.* For n = 0 the OEIS exponent 2n-1 = -1 (row 0 of T^-1); Lean's truncated subtraction gives exponent 0. Both give row 0 = [1], hence row 1 = [1,1]; documented in the file and confirmed by T_data. No effect elsewhere since 2n-1 >= 1 for n >= 1.
- *Note.* Range n >= 2 matches Irwin's displayed formulas (which start at a(2)); the identity also holds trivially at n = 0, 1 (nest 0 1 = 1 = a(0) = a(1)), so nothing is lost. The generalization 'and so on' is encoded as nest, which also coincides with Somos's two-argument program a(n,k) in the entry (a(n,k) = nest(n-1,k)).
- *Note.* Catalogue field area = 'Discrete geometry' does not fit this matrix/combinatorics entry (catalogue metadata only, not the statement).

## A141412: Denominators of Curtz's polynomials are Farhi's d(n+1,k+1) (A141412, Marcus's conjecture)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a141412](../../results/oeis-a141412/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A141412.lean`](../../lean/Math0/Statements/OEIS/A141412.lean).

**The conjecture as stated in OEIS**

> %F A141412 Conjecture: T(n, k) = d(n+1, k+1), with d(n,k) = denominator(A000254(n, k)*k!/n!) where A000254 are the unsigned Stirling numbers of the 1st kind. See d(n,k) in Farhi link. - _Michel Marcus_, Oct 18 2018
> [Entry: %N Triangle c(n,k) of the denominators of coefficients [x^k] P(n,x) of the polynomials P(n,x) of A129891; Maple: P(0,x)=1, P(n,x) = (-1)^n/(n+1) + x*add((-1)^i/(i+1)*P(n-1-i,x), i=0..n-1); offset 0, tabl; Paul Curtz Aug 04 2008.]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n k : ℕ, k ≤ n → T n k = d (n + 1) (k + 1)

noncomputable def P : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => C ((-1) ^ (n + 1) / (((n + 1 : ℕ) : ℚ) + 1)) +
      X * ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i / ((i : ℚ) + 1)) * P (n - i)
def c : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (-1) ^ (n + 1) / (((n + 1 : ℕ) : ℚ) + 1)
  | n + 1, k + 1 => ∑ i ∈ Finset.range (n + 1), (-1) ^ i / ((i : ℚ) + 1) * c (n - i) k
theorem coeff_P (n k : ℕ) : (P n).coeff k = c n k
def T (n k : ℕ) : ℕ := (c n k).den
def d (n k : ℕ) : ℕ :=
  ((Nat.stirlingFirst n k : ℚ) * (Nat.factorial k : ℚ) / (Nat.factorial n : ℚ)).den
```

**What the Lean statement says**

Let P(0,x) = 1 and P(n+1,x) = (-1)^(n+1)/(n+2) + x * sum_{i=0..n} (-1)^i/(i+1) * P(n-i,x) over Q. Let T(n,k) be the reduced denominator of the coefficient of x^k in P(n,x). Let d(n,k) be the reduced denominator of c(n,k)*k!/n!, where c(n,k) is the unsigned Stirling number of the first kind. Claim: for all 0 <= k <= n, T(n,k) = d(n+1,k+1).

**What the kernel checks against the OEIS data**

T_data: all 78 listed terms (rows 0..11) of A141412 by decide +kernel, via the computable coefficient recursion c, which coeff_P proves equal to the coefficients of the literal polynomial recursion P. This pins T. There is no kernel data check of d against values, but d is a direct closed form; Mathlib's Nat.stirlingFirst is the unsigned recurrence s(n+1,k+1) = n*s(n,k+1) + s(n,k). I independently checked in Python that T(n,k) = d(n+1,k+1) for all 0 <= k <= n <= 29 with these definitions.

**Points for the reviewer**

- *Note.* Marcus writes 'A000254(n,k)', but A000254 is a one-index sequence. The file reads it as the two-index unsigned Stirling numbers of the first kind, following Marcus's own words 'A000254 are the unsigned Stirling numbers of the 1st kind' and G. C. Greubel's programs in the same entry (Denominator[(k+1)!*StirlingS1[n+1,k+1]/(n+1)!]; the sign does not affect the denominator). This is the only reasonable reading.
- *Note.* Range 0 <= k <= n is the triangle's index range; for k > n both sides are den(0) = 1 anyway. Catalogue classification is 'known-result-first-formalization' (Flajolet–Gourdon–Salvy eq. (6) gives it), which fits. Catalogue area 'Discrete geometry' is a metadata mislabel.

## A144637: A144637: (1/18) 6^n a(n)/n! is odd iff n = 2^k with k >= 1

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a144637](../../results/oeis-a144637/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A144637.lean`](../../lean/Math0/Statements/OEIS/A144637.lean).

**The conjecture as stated in OEIS**

> %F A144637 From _Peter Bala_, Feb 19 2026: (Start) ... (1/18)*A(6*x) = x^2 - 6*x^3 + 33*x^4 - 162*x^5 + 630*x^6 - 972*x^7 - 14499*x^8 + ... appears to be an integral series and satisfies the algebraic equation 36*y(x)^3 + 3*y(x)^2 + (1 + 6*x)*y(x) = x^2. Conjecture: (1/18)*6^(n)*a(n)/n! is odd iff n = 2^k for k >= 1. (End)
> [Entry: %N Column 2 of triangle in A144633, offset 0. A144633: 'take the triangle in A144385, write it as an (infinite) upper triangular square matrix, invert it and transpose it.' A144385: T(n,k) = number of partitions of [1..k] into exactly n blocks of size 1, 2 or 3.]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, (∃ m : ℤ, Odd m ∧ y n = (m : ℚ)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k

def y (n : ℕ) : ℚ := (1 / 18) * 6 ^ n * (a n : ℚ) / (n.factorial : ℚ)
def a (n : ℕ) : ℤ := T n 2
-- S n k = A144385 via row recurrence S(n+1,k) = S(n,k-1) + (k-1)S(n,k-2) + (k-1)(k-2)/2 S(n,k-3), row 0 = [1]
-- T n k (A144633) via forward substitution: T(n,k) = [n=k] - Σ_{j<n} T(j,k) S(j,n) for k ≤ n, 0 otherwise
theorem Tmat_eq (N : ℕ) : Tmat N = ((Mmat N)⁻¹)ᵀ   -- N×N truncation of T is transpose of Mathlib inverse of truncation of M(i,j)=S i j
```

**What the Lean statement says**

Let S(n,k) be the number of partitions of {1..k} into exactly n blocks of size 1, 2 or 3. Let M be the upper unitriangular matrix M(i,j) = S(i,j), and let T be the transpose of its inverse. Let a(n) = T(n,2) and y(n) = (1/18) * 6^n * a(n) / n! in Q. Claim: for every n >= 0, y(n) is an odd integer if and only if n = 2^k for some k >= 1.

**What the kernel checks against the OEIS data**

S_data: all 70 listed terms of A144385 (rows 0..6); S_zero/S_succ prove the recurrence for all n,k. T_data: all 55 listed terms of A144633 (rows 0..9). Tmat_eq proves T is the transposed inverse (not just matching data). a_data: all 23 listed terms a(0..22). y_data: y(0..8) = 0,0,1,-6,33,-162,630,-972,-14499, matching Bala's displayed series. All kernel-checked; definitions are pinned down.

**Points for the reviewer**

- *Note.* 'Odd' is read as 'is an odd integer'. Bala separately says y(n) 'appears to be' integral, and that integrality claim is not part of the statement. Under a looser reading of odd rationals (2-adic units), the iff could differ only if some y(n) were non-integral. Every y(n) is in fact an integer (y = x^2 - 6xy - 3y^2 - 36y^3 has integer coefficients; the proof establishes this), so the readings agree.
- *Note.* Range n >= 0 matches the offset. At n = 0, 1 we have y = 0 (not odd), and 1 = 2^0 is excluded by k >= 1, consistent with the conjecture. Catalogue area 'Discrete geometry' is a metadata mislabel.

## A160848: Barker's order-20 recurrence for the lines through an 8 x n grid holds

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a160848](../../results/oeis-a160848/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A160848.lean`](../../lean/Math0/Statements/OEIS/A160848.lean).

**The conjecture as stated in OEIS**

> %F A160848 Conjectures from _Colin Barker_, Dec 25 2017: (Start) G.f.: x*(1 + 66*x + 132*x^2 + 304*x^3 + 492*x^4 + 771*x^5 + 1003*x^6 + 1273*x^7 + 1390*x^8 + 1480*x^9 + 1374*x^10 + 1241*x^11 + 971*x^12 + 739*x^13 + 476*x^14 + 296*x^15 + 140*x^16 + 74*x^17 + 17*x^18 + 8*x^19 + 8*x^20) / ((1 - x)^3*(1 + x)*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)*(1 + x + x^2 + x^3 + x^4)*(1 + x + x^2 + x^3 + x^4 + x^5 + x^6)). a(n) = -a(n-2) + a(n-5) + a(n-6) + 2*a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2*a(n-13) - a(n-14) - a(n-15) + a(n-18) + a(n-20) for n>21. (End)
> [Entry: %N Number of lines through at least 2 points of an 8 X n grid of points; offset 0; Seppo Mustonen May 28 2009.]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 21 < n → Recurrence (fun m => (a m : ℤ)) n

def Recurrence (f : ℕ → ℤ) (n : ℕ) : Prop :=
  f n = -f (n - 2) + f (n - 5) + f (n - 6) + 2 * f (n - 7) + f (n - 8) + f (n - 9)
    - f (n - 11) - f (n - 12) - 2 * f (n - 13) - f (n - 14) - f (n - 15) + f (n - 18) + f (n - 20)
def pt (i : ℕ) : ℤ × ℤ := (((i / 8 : ℕ) : ℤ), ((i % 8 : ℕ) : ℤ))
def Collinear3 (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)
def lineThrough (n i j : ℕ) : Finset ℕ :=
  (Finset.range (8 * n)).filter fun k => Collinear3 (pt i) (pt j) (pt k)
def a (n : ℕ) : ℕ :=
  (((Finset.range (8 * n) ×ˢ Finset.range (8 * n)).filter fun ij => ij.1 ≠ ij.2).image
    fun ij => lineThrough n ij.1 ij.2).card
-- (statement_gf, the g.f. form, is also defined but is not the settled declaration)
```

**What the Lean statement says**

Let a(n) be the number of distinct lines in the plane that pass through at least two points of the grid {0..n-1} x {0..7}, counted as the number of distinct sets of grid points cut out by the lines through two distinct grid points. Claim: for every n > 21, a(n) = -a(n-2) + a(n-5) + a(n-6) + 2a(n-7) + a(n-8) + a(n-9) - a(n-11) - a(n-12) - 2a(n-13) - a(n-14) - a(n-15) + a(n-18) + a(n-20), with values in Z.

**What the kernel checks against the OEIS data**

a_data: all 41 listed terms a(0..40) by decide +kernel (through aFast, proved equal to a for every n by a_eq_aFast). recurrence_data: the listed terms satisfy the recurrence for 22 <= n <= 40. The 41 terms (including a(1) = 1, a(2) = 66) pin down the line-counting definition.

**Points for the reviewer**

- *Note.* Barker's block contains two conjectures, the g.f. and the order-20 recurrence. The settled statement is the recurrence. statement_gf is defined in the file but not settled. This loses nothing: I checked that Barker's denominator expands to 1 + x^2 - x^5 - x^6 - 2x^7 - x^8 - x^9 + x^11 + x^12 + 2x^13 + x^14 + x^15 - x^18 - x^20, the recurrence's characteristic polynomial, and that (listed a) * D reproduces exactly x * N(x) through x^21 and gives 0 for x^22..x^40. So the recurrence for n > 21 plus the kernel-checked a(0..21) implies the g.f. identity.
- *Note.* Truncated subtraction: for n > 21 every index n-k (k <= 20) is >= 2, so no junk. The grid is oriented n x 8 rather than 8 x n, which gives a congruent point set and the same count. For n = 0 the grid is empty and a(0) = 0, matching the data.

## A172164: A172164: the second differences of the Theodorus-spiral turns are always 18, 19, 20 or 21

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a172164](../../results/oeis-a172164/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A172164.lean`](../../lean/Math0/Statements/OEIS/A172164.lean).

**The conjecture as stated in OEIS**

> %C A172164 Conjecture : The terms are only 18,19,20,21 (From the first thousand turns, there are 2,3% of 18, 36,5% of 19, 46,2% of 20 and 15% of 21). No period found. Probably due to Pi transcendence. [_Sébastien Dumortier_, Jan 27 2010]
> [Entry: %N Differences between numbers of triangles entirely contained in two consecutive turns of Pythagoras's snail (Theodorus spiral); offset 2; %e In the first turn, 16 triangles are complete. In the 2nd turn, there are 36 triangles completely included. The difference is 20. %F The second forward difference of A072895 (R. G. Wilson v).]

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 2 ≤ n → a n = 18 ∨ a n = 19 ∨ a n = 20 ∨ a n = 21

noncomputable def S (k : ℕ) : ℝ := ∑ i ∈ range k, arctan (1 / √((i : ℝ) + 1))
def turnTriangles (n : ℕ) : Set ℕ :=
  {i | 1 ≤ i ∧ 2 * π * ((n : ℝ) - 1) ≤ S (i - 1) ∧ S i ≤ 2 * π * n}
noncomputable def c (n : ℕ) : ℕ := (turnTriangles n).ncard
noncomputable def a (n : ℕ) : ℤ := (c n : ℤ) - c (n - 1)
```

**What the Lean statement says**

Let S(k) = sum_{i=1..k} arctan(1/sqrt(i)), the total central angle of the first k triangles of the Theodorus spiral (triangle i has legs sqrt(i) and 1). Triangle i >= 1 occupies the angle interval [S(i-1), S(i)]. Let c(n) be the number of triangles i >= 1 with 2pi(n-1) <= S(i-1) and S(i) <= 2pi n, i.e. lying entirely in the closed n-th turn. The set is proved finite, so ncard is a genuine count. Claim: for every n >= 2, the integer c(n) - c(n-1) lies in {18, 19, 20, 21}.

**What the kernel checks against the OEIS data**

crossing proves S(K n) < 2pi n < S(K n + 1) for n = 1..70 by a kernel-checked rigorous interval computation; Kseq's first 42 entries equal the listed terms of A137515. From this, c_one_two gives c(1) = 16 and c(2) = 36 (the entry's example), and a_data proves all 69 listed terms a(2..70) against the real-number definition. This pins down the turn and triangle conventions (starting ray, closed sectors, which turn counts as first) on the data range.

**Points for the reviewer**

- *Note.* Turn boundaries are taken as closed intervals. This can only matter if some S(k) equals 2pi n exactly, which the interval check rules out for n <= 70 and which almost certainly never happens. If it did, the 'entirely contained' count (the entry's name, which Lean follows) and the '%F second forward difference of A072895' (strict >) could differ at that n. Since the result proves the Lean form for all n, this does not change what is settled in substance.
- *Note.* 'The terms are only 18,19,20,21' is formalized as 'every term lies in {18,19,20,21}'. Reading it as 'the set of values is exactly {18,..,21}' adds only that each value occurs, which a_data already witnesses: a(8) = 18, a(3) = 19, a(2) = 20, a(7) = 21. The percentages, 'no period' and 'Pi transcendence' remarks are observations and are correctly left out. Range n >= 2 matches offset 2, and the subtraction is done in Z, so it is not truncated.

## A175385: ∑_{i=1..n} C(2n-i-1, i-1)/i is never an integer for n > 1 (A175385)

Verdict of the pre-review: **faithful**. Result: [oeis-a175385](../../results/oeis-a175385/README.md) (known-result-already-formalized). Frozen statement: [`lean/Math0/Statements/OEIS/A175385.lean`](../../lean/Math0/Statements/OEIS/A175385.lean).

**The conjecture as stated in OEIS**

> %C A175385 We conjecture that Sum_{i=1..n} ((1/i)*C(2n-i-1,i-1)) is not an integer for n>1.  [_Vladimir Shevelev_, _Zak Seidov_, Apr 24 2010; %N a(n) = numerator of Sum_{i=1..n} binomial(2n-i-1,i-1)/i; %O 1,2]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 < n → ¬ ∃ k : ℤ, S n = (k : ℚ)

where
def S (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, ((Nat.choose (2 * n - i - 1) (i - 1) : ℕ) : ℚ) / (i : ℚ)
def a (n : ℕ) : ℕ := (S n).num.natAbs
```

**What the Lean statement says**

For every integer n >= 2, the rational number S(n) = sum over i = 1..n of C(2n-i-1, i-1)/i is not an integer.

**What the kernel checks against the OEIS data**

a_data checks the numerators a 1 through a 27 (all 27 listed terms of A175385) by decide +kernel. The denominators (A175386), which are what the conjecture is actually about, are not kernel-checked in the frozen file. I checked independently that the literal definition gives denominators 1, 2, 6, 4, 5, 4, 7, 8, 18, ..., matching A175386, and that 2n*S(n) = L_{2n} - 1 for n < 60. The definition is a literal transcription in Q. For 1 <= i <= n, the subtractions 2n-i-1 (= (2n-i)-1 >= n-1) and i-1 never truncate, and i >= 1 rules out division by zero. So checking numerators only is not a real gap.

**Points for the reviewer**

- *Minor.* The data check pins only the numerators of S(n), not the denominators (A175386), and the conjecture is a statement about the denominator being 1. This does not affect fidelity, because S is a literal, non-truncating transcription of the sum, and I confirmed the denominators match A175386 for n = 1..25.
- *Note.* The range is n > 1 (n >= 2), exactly as stated. n = 1, where S(1) = 1, is correctly excluded. There is no extra hypothesis or index shift.

## A176206: Divisors of the terms of row n of A176206 are the parts of the partitions of n

Verdict of the pre-review: **faithful**. Result: [oeis-a176206](../../results/oeis-a176206/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A176206.lean`](../../lean/Math0/Statements/OEIS/A176206.lean).

**The conjecture as stated in OEIS**

> %C A176206 From _Omar E. Pol_, Nov 23 2020: ... "Conjecture: all divisors of all terms in row n are also all parts of all partitions of n." (Entry: "Irregular triangle T(n,k) (n >= 1, k >= 1) read by rows: row n has length A000070(n-1) and every column k gives the positive integers." Comment: "Row n contains a decreasing sequence where n-k is repeated A000041(k) times, k = 0..n-1." Worked example for n = 5: divisors of row 5 and parts of all partitions of 5 are both "twelve 1's, four 2's, two 3's, one 4 and one 5". Offset 1.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (row n : Multiset ℕ).bind (fun t => t.divisors.val) =
      (Finset.univ : Finset n.Partition).val.bind (fun π => π.parts)

-- dependencies
def p (k : ℕ) : ℕ := Fintype.card (Nat.Partition k)
def rowOf (f : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).flatMap fun k => List.replicate (f k) (n - k)
def row (n : ℕ) : List ℕ := rowOf p n
```

**What the Lean statement says**

For every n ≥ 1, let row n be the list in which n−k appears p(k) times for k = 0,…,n−1 (p is the partition function). Take the multiset of all divisors of all entries of row n, with each entry contributing each of its divisors once. This multiset equals the multiset of all parts of all partitions of n, with each partition contributing all of its parts with multiplicity.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 94 listed terms of the flattened triangle (rows 1–7 and the first 19 terms of row 8) through p = pb (proved equal). This pins `row` completely. row_five_divisors kernel-checks the left-hand side for n = 5 against the entry's worked example. The right-hand side (the multiset of parts over Nat.Partition n) is not kernel-checked for any n. It is plain Mathlib, though, and a Python check confirms the identity under these definitions for n ≤ 25 (n ≤ 14 by enumerating the partitions directly).

**Points for the reviewer**

- *Note.* The conjecture is read as an equality of multisets, which is what the worked example for n = 5 says. This is stronger than the set reading, which is trivial (both sides are {1,…,n}), and implies it. So the reading is not weaker than intended.
- *Note.* Only the left-hand side has a kernel data check (n = 5). The right-hand side is Mathlib's Nat.Partition with no custom encoding, so the risk is low.
- *Note.* Metadata only: the catalog tags this partition/divisor identity as area "Discrete geometry". That does not affect fidelity.

## A178295: A178295: collinear 4-subsets of {0,...,4}^n number 9^n/2 + 3*7^n/2 - 2*5^n (Mathar's conjecture, all three formulas)

Verdict of the pre-review: **faithful**. Result: [oeis-a178295](../../results/oeis-a178295/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A178295.lean`](../../lean/Math0/Statements/OEIS/A178295.lean).

**The conjecture as stated in OEIS**

> %F A178295 Conjecture: a(n) = 9^n/2+3*7^n/2-2*5^n. a(n)= +21*a(n-1) -143*a(n-2) +315*a(n-3). G.f.: x*(-5+41*x)/((9*x-1)*(7*x-1)*(5*x-1)). [_R. J. Mathar_, May 24 2010]  (Name: "Number of collinear point 4-tuples in a 5 X 5 X 5 X... n-dimensional cubic grid." Offset 0, data 0,5,64,629,5632,...)

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ n : ℕ, (a n : ℚ) = 9 ^ n / 2 + 3 * 7 ^ n / 2 - 2 * 5 ^ n) ∧
  (∀ n : ℕ, 3 ≤ n →
    (a n : ℤ) = 21 * (a (n - 1) : ℤ) - 143 * (a (n - 2) : ℤ) + 315 * (a (n - 3) : ℤ)) ∧
  PowerSeries.mk (fun n => (a n : ℚ)) =
    PowerSeries.X * (-5 + 41 * PowerSeries.X) *
      ((9 * PowerSeries.X - 1) * (7 * PowerSeries.X - 1) * (5 * PowerSeries.X - 1))⁻¹

-- dependencies
abbrev Pt (n : ℕ) := Fin n → Fin 5
def coord {n : ℕ} (p : Pt n) (i : Fin n) : ℤ := ((p i : ℕ) : ℤ)
def Coll3 {n : ℕ} (p q r : Pt n) : Prop :=
  ∀ i j : Fin n, (coord q i - coord p i) * (coord r j - coord p j) =
    (coord q j - coord p j) * (coord r i - coord p i)
def IsCollinear {n : ℕ} (s : Finset (Pt n)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, Coll3 p q r
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Pt n)).powersetCard 4 |>.filter IsCollinear).card
```

**What the Lean statement says**

Let a(n) be the number of 4-element sets of points of {0,…,4}^n that lie on one line of ℝ^n (isCollinear_iff_collinear proves the minor condition equals Mathlib's Collinear ℝ). Then three things hold. (1) For every n ≥ 0, a(n) = 9^n/2 + 3·7^n/2 − 2·5^n, computed in ℚ. (2) For every n ≥ 3, a(n) = 21a(n−1) − 143a(n−2) + 315a(n−3), computed in ℤ. (3) As formal power series over ℚ, Σ a(n)xⁿ = x(−5+41x)·((9x−1)(7x−1)(5x−1))⁻¹. The denominator has constant term −1, so the inverse is the true inverse (genFun_iff).

**What the kernel checks against the OEIS data**

a_data kernel-checks a(0), a(1), a(2) = 0, 5, 64 through fastA (proved equal to a). a(1) = 5 = C(5,4) rules out ordered tuples (that would give 120), and a(2) = 64 fixes collinearity in the plane. a(3) = 629 is not kernel-checked. I recomputed a(1..3) = 5, 64, 629 in Python from the Lean definition (4-subsets with vanishing minors), and they match the data. closedForm_data and recurrence_data check only the transcription of the formulas against the 10 listed terms, not a.

**Points for the reviewer**

- *Note.* "Point 4-tuples" is read as unordered 4-sets of distinct points. a(1) = 5 and a(2) = 64 force this reading, and a(3) = 629 matches it (checked outside the kernel). Lines meeting the grid in 4 or more points have directions in {0,±1}^n, so this reading gives exactly (9^n−5^n)/2 + 3(7^n−5^n)/2, which is the conjectured closed form. The reading matches the formula's intent.
- *Note.* The statement is the conjunction of all three formulas, so it is at least as strong as the closed form alone. There is no truncated subtraction: the closed form is over ℚ and the recurrence is over ℤ with n ≥ 3. The n = 0 case (one point, a(0) = 0) is included, consistent with offset 0.

# Fidelity review packet 09 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A344710, A348484, A350499, A350557, A350900, A351743, A354571, A355076, A355339, A355360.

## A344710: A344710: non-obtuse lattice triangles with sides >= sqrt(n) have |det| > (sqrt 3 / 2) n

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a344710](../../results/oeis-a344710/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A344710.lean`](../../lean/Math0/Statements/OEIS/A344710.lean).

**The conjecture as stated in OEIS**

> FORMULA: "a(n) > sqrt(3/4)*n (conjectured)." Name: "a(n)/2 is the smallest possible area of a non-obtuse triangle with coordinates in Z^2 and no side shorter than sqrt(n)." Offset 1. Entry by _Jonathan F. Waldmann_, May 26 2021 (revision #84, Feb 16 2022; the mirror and current GitHub oeisdata are identical). Related COMMENT: "Conjectured next terms (from the conjectured inequality a(n) > sqrt(3/4)*n) are a(50,...,64) ?= 45, 48, 48, 52, 55, 55, 55, 55, 55, 56, 56, 56, 56, 56, 56."

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → Real.sqrt (3 / 4) * (n : ℝ) < (a n : ℝ)

where
def det2 (A B C : ℤ × ℤ) : ℤ := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
def dist2 (P Q : ℤ × ℤ) : ℤ := (P.1 - Q.1) * (P.1 - Q.1) + (P.2 - Q.2) * (P.2 - Q.2)
def dotAt (V P Q : ℤ × ℤ) : ℤ := (P.1 - V.1) * (Q.1 - V.1) + (P.2 - V.2) * (Q.2 - V.2)
def IsValid (n : ℕ) (A B C : ℤ × ℤ) : Prop :=
  det2 A B C ≠ 0 ∧
  (n : ℤ) ≤ dist2 A B ∧ (n : ℤ) ≤ dist2 B C ∧ (n : ℤ) ≤ dist2 C A ∧
  0 ≤ dotAt A B C ∧ 0 ≤ dotAt B C A ∧ 0 ≤ dotAt C A B
def areas (n : ℕ) : Set ℕ := {k | ∃ A B C : ℤ × ℤ, IsValid n A B C ∧ (det2 A B C).natAbs = k}
noncomputable def a (n : ℕ) : ℕ := sInf (areas n)
(plus proved: areas_nonempty, isLeast_a : IsLeast (areas n) (a n), nonObtuse_iff linking the dot-product test to the entry's 2*max ≤ sum criterion)
```

**What the Lean statement says**

For every n ≥ 1, let a(n) be the least value of |det(B−A, C−A)| (twice the area) over all triples of lattice points A, B, C in Z² that are not collinear, have all three squared side lengths ≥ n, and have all three angles ≤ 90° (dot product at each vertex ≥ 0). Then a(n) > (√3/2)·n, with √(3/4) computed in the reals.

**What the kernel checks against the OEIS data**

Two kernel-checked facts. aRegion_data: a computable search aRegion n (A = (0,0), B in the first octant, C in the annulus n ≤ |C|² ≤ 5n/4+2, same IsValid predicate) equals all 49 listed terms. a_data_le: a(n) ≤ listed term for n = 1..49 (via a_le_aRegion). The check is one-sided for a itself: no lower bound a(n) ≥ listed term is proved, because the optimality of the search region is not proved. It still tests IsValid itself. For example, requiring strictly acute angles would raise a(4) above 4, and dropping the angle condition would lower several terms, so either change would break aRegion_data. The definition of a is a direct sInf over all valid triangles, and isLeast_a shows it is a true minimum.

**Points for the reviewer**

- *Note.* The data check pins a(n) only from above (a(n) ≤ listed term). Equality with the listed data is shown only for the restricted search aRegion, whose region is not proved to contain an optimum. The definition is a literal transcription of the name, so this does not affect fidelity, but the data do not independently confirm a(n) from below.
- *Note.* Strict vs non-strict makes no difference: √(3/4)·n is irrational for n ≥ 1 and a(n) is an integer. Real.sqrt (3/4) is elaborated in ℝ (0.75), so there is no ℕ-division junk. The non-collinearity conjunct is redundant for n ≥ 1, since a collinear triple with pairwise distances ≥ 1 has an obtuse (180°) angle at the middle point.
- *Note.* The comment's 'conjectured next terms a(50..64)' are not formalized. That is reasonable, because they are guesses that combine the inequality with constructions and are not a separate claim of the author. The inequality itself is classical: a non-obtuse triangle with all sides ≥ D has area ≥ (√3/4)D², and Z² has no equilateral triangle. So the settled statement is elementary, which bears on novelty, not fidelity.

## A348484: A348484: no two squares two steps apart; the conjectured formula holds

Verdict of the pre-review: **faithful**. Result: [oeis-a348484](../../results/oeis-a348484/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A348484.lean`](../../lean/Math0/Statements/OEIS/A348484.lean).

**The conjecture as stated in OEIS**

> FORMULA: "Conjectures: a(n) = n^2/2 for n == 0 (mod 4). a(n) = (n^2 + 1)/2 for n == 1 or 3 (mod 4). a(n) = n^2/2 + 2 for n == 2 (mod 4)." Name: "Maximum number of squares on an n X n chessboard such that no two are two steps apart horizontally or vertically." Offset 1. Entry by _Yang Hong_, Oct 20 2021 (revision #33, Dec 06 2022; mirror and current GitHub identical).

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (n % 4 = 0 → a n = n ^ 2 / 2) ∧
    (n % 4 = 1 ∨ n % 4 = 3 → a n = (n ^ 2 + 1) / 2) ∧
    (n % 4 = 2 → a n = n ^ 2 / 2 + 2)

where
def TwoApart {n : ℕ} (c d : Fin n × Fin n) : Prop :=
  (c.1 = d.1 ∧ (c.2.val + 2 = d.2.val ∨ d.2.val + 2 = c.2.val)) ∨
    (c.2 = d.2 ∧ (c.1.val + 2 = d.1.val ∨ d.1.val + 2 = c.1.val))
def Admissible {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop := ∀ c ∈ S, ∀ d ∈ S, ¬ TwoApart c d
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Finset (Fin n × Fin n))).filter Admissible).sup Finset.card
```

**What the Lean statement says**

For n ≥ 1, let a(n) be the largest size of a set of cells of the n×n board containing no two cells in the same row whose columns differ by exactly 2, and no two cells in the same column whose rows differ by exactly 2. Then a(n) = n²/2 when 4 | n, a(n) = (n²+1)/2 when n is odd, and a(n) = n²/2 + 2 when n ≡ 2 (mod 4). The ℕ divisions are exact in each case.

**What the kernel checks against the OEIS data**

a_data proves a(1..10) = 1,4,5,8,13,20,25,32,41,52 (all 10 listed terms) in the kernel. Each value is proved by a two-sided certificate: an admissible witness set of that size, and a labelling with v labels in which equal labels force equal or two-apart cells (sound upper bound, lemma a_eq_of_cert). a_small re-checks a(1..3) by brute force from the definition. This pins the reading of 'two steps apart'. I brute-forced the alternatives for n = 1..6: taxicab distance exactly 2 gives 1,2,3,6,9,12; Chebyshev distance exactly 2 gives 1,4,4,4,9,16; offset (±2,±2) gives 1,4,7,8,16,24. Only the encoded rook-distance-exactly-2 reading gives 1,4,5,8,13,20.

**Points for the reviewer**

- *Note.* The ℕ divisions n^2/2 and (n^2+1)/2 are exact in their residue classes, so they match the entry's rational expressions. n = 0 is excluded, as the offset requires. The three implications cover every n ≥ 1, so the conjecture is not weakened.

## A350499: Kurkov's recursion computes the free cumulants (A350499)

Verdict of the pre-review: **faithful**. Result: [oeis-a350499](../../results/oeis-a350499/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A350499.lean`](../../lean/Math0/Statements/OEIS/A350499.lean).

**The conjecture as stated in OEIS**

> FORMULA: "Conjecture: free cumulants in terms of the free moments are R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) - Sum_{j=1..n-1} R(j,k)*R(n-j,1) for n > 1, k > 0 with R(1,k) = m_k for k > 0. - _Mikhail Kurkov_, Mar 30 2025". Free cumulants per the entry: "O.g.f.: C(x) = 1 + c_1 x + c_2 x^2 + ... = x / (x + m_1 x^2 + m_2 x^3 + m_3 x^4 + ...)^(-1) = x / M^(-1)(x) ..." (entry by _Tom Copeland_, Jan 01 2022; revision #63, Apr 04 2025; mirror and current GitHub identical).

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 0 < n → R (fun k => (MvPolynomial.X k : MvPolynomial ℕ ℤ)) n 1 = freeCumulant n

where (abridged)
noncomputable def mom (k : ℕ) : MvPolynomial ℕ ℤ := if k = 0 then 1 else MvPolynomial.X k
noncomputable def M : PowerSeries (MvPolynomial ℕ ℤ) := PowerSeries.mk fun i => if i = 0 then 0 else mom (i - 1)
noncomputable def Minv := M.substInvOfIsUnit isUnit_coeff_one_M   -- two-sided compositional inverse
noncomputable def Cgf := invOfUnit (PowerSeries.mk fun n => coeff (n + 1) Minv) 1   -- C = x / Minv (Cgf_mul_Minv : Cgf * Minv = X)
noncomputable def freeCumulant (n : ℕ) : MvPolynomial ℕ ℤ := coeff n Cgf
def R {A : Type*} [CommRing A] (m : ℕ → A) : ℕ → ℕ → A
  | 0, _ => 0
  | 1, k => m k
  | n + 2, k => R m (n + 1) (k + 1) - ∑ j : Fin (n + 1), R m (j + 1) k * R m (n + 1 - j) 1
(proved: R_one : R m 1 k = m k; R_rec : 1 < n → R m n k = R m (n-1) (k+1) - ∑ j ∈ Finset.Icc 1 (n-1), R m j k * R m (n-j) 1)
```

**What the Lean statement says**

In the polynomial ring Z[m_1, m_2, …], let M(x) = x + m_1x² + m_2x³ + ⋯ and let M^⟨−1⟩ be its compositional inverse. Let c_n be the coefficient of xⁿ in C(x) = x / M^⟨−1⟩(x). Define R(1,k) = m_k and, for n > 1, R(n,k) = R(n−1,k+1) − Σ_{j=1}^{n−1} R(j,k)·R(n−j,1). Then R(n,1) = c_n for every n ≥ 1, as an identity of polynomials.

**What the kernel checks against the OEIS data**

a_data checks all 66 listed terms, which are the unsigned coefficients of c_1..c_8 in Abramowitz–Stegun order. The partition order is itself checked against 99 terms of A036036. cumulant_examples checks the signed coefficients of c_1..c_5 against the entry's EXAMPLE section. The computable T is proved equal to |coeff of freeCumulant n| (T_eq_coeff, ev_cumPoly), so these checks bear on the noncomputable freeCumulant used in the statement. Together they pin freeCumulant down, and the definition is literally the entry's o.g.f. Kurkov's array is pinned by the proved lemmas R_one and R_rec, which state the entry's clauses literally with ℕ indices. These clauses determine R(n,k) for all n ≥ 1 by induction, whatever the junk value R(0,k) = 0 is. The data do not test R, which is fine because R is the object of the conjecture.

**Points for the reviewer**

- *Note.* The identity is stated in Z[m_1, m_2, …] with indeterminate moments. That is the universal case, and it implies the identity for any moment sequence in any commutative ring, which is the natural reading of 'free cumulants in terms of the free moments'.
- *Note.* The junk values R(0,k) = 0 and R(1,0) = X 0 are never reached from R(n,1) with n ≥ 1, because the recursion only increases k and uses n−j ≥ 1 and j ≥ 1. The entry's normalization m_0 = 1 enters only through M(x) = x + m_1x² + ⋯, as in the entry. The entry's c_n agree with the standard free cumulants, since the derived relation C(M(x)) = M(x)/x is the standard moment–cumulant functional equation.

## A350557: Signed A350557 is the matrix inverse of A350512, proved

Verdict of the pre-review: **faithful**. Result: [oeis-a350557](../../results/oeis-a350557/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A350557.lean`](../../lean/Math0/Statements/OEIS/A350557.lean).

**The conjecture as stated in OEIS**

> FORMULA: "Conjecture: M(n,k) = (-1)^(n-k) * T(n,k) is matrix inverse of A350512." Name: "Triangle T(n,k) read by rows with T(n,0) = (2*n)! / (2^n * n!) for n >= 0 and T(n,k) = (Sum_{i=k..n} binomial(i-1,k-1) * 2^i * i! / (2*i)!) * (2*n)! / (2^n * n!) for 0 < k <= n." Entry by _Werner Schulte_, Jan 05 2022 (revision #8, Jan 18 2022). A350512 name: "Triangle read by rows with T(n,0) = 1 for n >= 0 and T(n,k) = binomial(n-1,k-1)*(2*k*(n-k) + n)/k for 0 < k <= n." (Schulte; revision #17, Jan 18 2022). Mirror and current GitHub identical for both.

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ n j : ℕ, ∑ k ∈ Finset.range (n + 1), L n k * M k j = if n = j then 1 else 0) ∧
  (∀ n j : ℕ, ∑ k ∈ Finset.range (n + 1), M n k * L k j = if n = j then 1 else 0)

where
def T (n k : ℕ) : ℚ :=
  if n < k then 0
  else if k = 0 then ((2 * n).factorial : ℚ) / (2 ^ n * n.factorial)
  else (∑ i ∈ Finset.Icc k n,
      ((i - 1).choose (k - 1) : ℚ) * 2 ^ i * i.factorial / (2 * i).factorial) *
    (2 * n).factorial / (2 ^ n * n.factorial)
def L (n k : ℕ) : ℚ :=
  if n < k then 0
  else if k = 0 then 1
  else ((n - 1).choose (k - 1) : ℚ) * (2 * k * (n - k : ℕ) + n) / k
def M (n k : ℕ) : ℚ := (-1) ^ (n - k) * T n k
```

**What the Lean statement says**

Let T be the A350557 triangle and L the A350512 triangle, both computed in ℚ from their defining formulas and extended by 0 above the diagonal. Let M(n,k) = (−1)^{n−k} T(n,k). Then the infinite lower-triangular matrices L and M are two-sided inverses: for all n, j ≥ 0, Σ_{k=0}^{n} L(n,k)M(k,j) = [n=j] and Σ_{k=0}^{n} M(n,k)L(k,j) = [n=j].

**What the kernel checks against the OEIS data**

T_data checks all 45 listed terms of A350557 (rows 0..8) as exact rationals. L_data checks all 66 listed terms of A350512 (rows 0..10). a_data checks the row-reading of A350557 with offset 0. Together these pin both triangles, including the ℚ divisions and the exact ℕ subtractions (i−1, k−1, n−k with k ≥ 1 and k ≤ n). statement_check confirms both identities for n, j < 12, which is a sanity check of the transcription.

**Points for the reviewer**

- *Note.* The statement requires both L·M = I and M·L = I. For lower-triangular matrices with unit diagonal, either one implies the other, so this is equivalent to 'M is the matrix inverse of L', not a strengthening. Finite sums are legitimate because both matrices are lower triangular.
- *Note.* In (−1)^(n−k) the natural subtraction truncates only when k > n, where T(n,k) = 0, so the junk value never matters.

## A350900: OEIS A350900: Schulte's gcd-ratio double sum is a Dirichlet convolution

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a350900](../../results/oeis-a350900/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A350900.lean`](../../lean/Math0/Statements/OEIS/A350900.lean).

**The conjecture as stated in OEIS**

> COMMENT: "Conjecture: Let f be an arbitrary arithmetic function. Define for n > 0 the sequence a(f; n) = Sum_{i=1..n, k=1..n} f(gcd(i,n)/gcd(gcd(i,k),n)); a(f; n) equals Dirichlet convolution of f(n)*A000010(n) and A057660(n); if f is multiplicative, then a(f; n) is multiplicative; row sums of this triangle use f(n) = n (see formula section)." FORMULA: "Conjecture: Row sums equal Dirichlet convolution of A002618 and A057660." Name: "Triangle read by rows: T(n, k) = Sum_{i=1..n} gcd(i,n) / gcd(gcd(i,k),n) for 1 <= k <= n." Entry by _Werner Schulte_, Jan 21 2022 (revision #13, May 24 2024; mirror and current GitHub identical).

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ f : ArithmeticFunction ℂ, ∀ n : ℕ, 0 < n →
      aF f n = (f.pmul (phi : ArithmeticFunction ℂ) * (A057660Fn : ArithmeticFunction ℂ)) n) ∧
  (∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (aFun f).IsMultiplicative) ∧
  (∀ n : ℕ, 0 < n →
      ((∑ k ∈ Finset.Icc 1 n, T n k : ℕ) : ℂ) =
        aF ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) ∧
  (∀ n : ℕ, 0 < n → ∑ k ∈ Finset.Icc 1 n, T n k = (A002618Fn * A057660Fn) n)

where
def T (n k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, Nat.gcd i n / Nat.gcd (Nat.gcd i k) n
def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
def A057660 (m : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 m, m / Nat.gcd m k   (A057660Fn its ArithmeticFunction)
def A002618 (n : ℕ) : ℕ := n * Nat.totient n   (A002618Fn its ArithmeticFunction)
def aF {R} [AddCommMonoid R] (f : ArithmeticFunction R) (n : ℕ) : R :=
  ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n)
def aFun f : ArithmeticFunction R := ⟨aF f, _⟩
```

**What the Lean statement says**

Let a(f;n) = Σ_{i=1}^{n} Σ_{k=1}^{n} f(gcd(i,n)/gcd(gcd(i,k),n)). The statement has four parts. (1) For every complex-valued arithmetic function f and every n ≥ 1, a(f;n) = Σ_{de=n} f(d)φ(d)·A057660(e), where A057660(m) = Σ_{k=1}^{m} m/gcd(m,k). (2) If f is multiplicative (f(1) = 1 and f(mn) = f(m)f(n) for coprime m, n), so is n ↦ a(f;n). (3) For n ≥ 1, the row sum Σ_{k=1}^{n} T(n,k) of the triangle T(n,k) = Σ_i gcd(i,n)/gcd(gcd(i,k),n) equals a(id;n). (4) For n ≥ 1, that row sum equals the Dirichlet convolution of A002618(n) = nφ(n) with A057660, evaluated at n.

**What the kernel checks against the OEIS data**

T_data and a_data check all 78 listed terms of A350900 (rows 1..12), which pins T and the exact ℕ division. A057660_data checks 52 listed terms of A057660 and A002618_data checks 20 terms of A002618, so the referenced sequences are pinned. The definitions are the OEIS names, and φ is Mathlib's totient. statement_check_rows confirms part 4 for n ≤ 12, and statement_check_aF confirms the identity of part 1 for one non-multiplicative test function and n ≤ 12. Both are transcription sanity checks.

**Points for the reviewer**

- *Note.* 'Arbitrary arithmetic function' is read as ArithmeticFunction ℂ, which forces f(0) = 0. f is never evaluated at 0, since its argument is ≥ 1 on the sum's range and Dirichlet convolution uses only positive divisors, so nothing is lost. Part 1 is linear in the values of f with integer coefficients, so the ℂ version implies it for any additive-group-valued f. Part 2 is stated only for ℂ-valued multiplicative f, which is the standard meaning.
- *Note.* Part 3 reads 'row sums of this triangle use f(n) = n' as the identity rowsum(n) = a(id;n). That identity holds by exchanging the finite sums, so this part is trivially true. It is the most natural reading of a loosely worded clause, and part 4 (the FORMULA-section conjecture) carries the substantive row-sum claim.
- *Note.* aFun f is a(f;·) with value 0 at n = 0 (empty sum). Mathlib's IsMultiplicative imposes nothing beyond n ≥ 1 that could fail here, so 'a(f;n) is multiplicative' for n > 0 is captured faithfully.

## A351743: A351743: from n = 139 the sequence is affine in 42-blocks, which proves Sycamore's, Sigrist's and the A355149 conjectures

Verdict of the pre-review: **faithful**. Result: [oeis-a351743](../../results/oeis-a351743/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A351743.lean`](../../lean/Math0/Statements/OEIS/A351743.lean).

**The conjecture as stated in OEIS**

> A351743 %N (offset 1): "a(1)=1. Thereafter, a(n+1) is the greatest divisor of s(n) which is prime to a(n), where s(n) is the n-th partial sum."
> A351743 %C (unsigned line; entry by _David James Sycamore_, Jun 07 2022): "Conjecture: a(n)=1 occurs infinitely many times, and therefore so does a(n)=2."
> A351743 %F: "Conjectures from _Rémy Sigrist_, Jun 20 2022: (Start) - a(2*(n+21)-1) = a(2*n-1) for n >= 70, - a(2*(n+21)) = 3645*a(2*n) + b(n) for n >= 70 (where b is 21-periodic). (End)"
> A355149 ("Partial sums of A351743", offset 1; _Michael De Vlieger_, _Rémy Sigrist_ and _David James Sycamore_, Jun 21 2022) %F: "Conjecture: a(n + 42) = 3645*a(n) + b(n) for n >= 138 (where b is 42-periodic)."
> (Upstream oeisdata main is identical to the mirror: A351743 #43, A355149 #11.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  sycamore ∧ sigristOdd ∧ sigristEven ∧ partialSums

def sycamore : Prop :=
  {n : ℕ | a n = 1}.Infinite ∧ {n : ℕ | a n = 2}.Infinite
def sigristOdd : Prop :=
  ∀ n : ℕ, 70 ≤ n → a (2 * (n + 21) - 1) = a (2 * n - 1)
def sigristEven : Prop :=
  ∃ b : ℕ → ℤ, (∀ n, b (n + 21) = b n) ∧
    ∀ n : ℕ, 70 ≤ n → (a (2 * (n + 21)) : ℤ) = 3645 * (a (2 * n) : ℤ) + b n
def partialSums : Prop :=
  ∃ c : ℕ → ℤ, (∀ n, c (n + 42) = c n) ∧
    ∀ n : ℕ, 138 ≤ n → (s (n + 42) : ℤ) = 3645 * (s n : ℤ) + c n

-- definitions (abridged)
def strip : ℕ → ℕ → ℕ → ℕ   -- divide w by gcd(w,v) while gcd ≠ 1, with fuel
  | 0, w, _ => w
  | fuel + 1, w, v => if Nat.gcd w v = 1 then w else strip fuel (w / Nat.gcd w v) v
def coprimePart (w v : ℕ) : ℕ := strip w w v
def step (p : ℕ × ℕ) : ℕ × ℕ := match p with | (x, y) => match coprimePart y x with | z => (z, y + z)
def state (n : ℕ) : ℕ × ℕ := step^[n] (1, 1)
def a : ℕ → ℕ | 0 => 0 | n + 1 => (state n).1
def s (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k
-- proved in the file: a_one : a 1 = 1;
-- a_succ_isGreatest (n ≥ 1) : IsGreatest {d | d ∣ s n ∧ Nat.Coprime d (a n)} (a (n + 1))
```

**What the Lean statement says**

Let a(1) = 1 and, for n ≥ 1, let a(n+1) be the largest d with d | s(n) and gcd(d, a(n)) = 1, where s(n) = a(1) + ... + a(n). The statement asserts all four of the following. (i) a(n) = 1 for infinitely many n, and a(n) = 2 for infinitely many n. (ii) For every n ≥ 70, a(2n+41) = a(2n-1). (iii) There is an integer sequence b with b(n+21) = b(n) for all n such that a(2n+42) = 3645·a(2n) + b(n) for every n ≥ 70. (iv) There is an integer sequence c with c(n+42) = c(n) for all n such that s(n+42) = 3645·s(n) + c(n) for every n ≥ 138.

**What the kernel checks against the OEIS data**

a_one and a_succ_isGreatest prove that `a` satisfies the OEIS definition for every n ≥ 1, which determines the sequence. Kernel checks: a_data covers all 67 listed terms a(1..67), s_data all 50 listed terms of A355149 (s(1..50)), and a_example the values a(150..153) = 473394, 1, 2840365, 2 from the entry's last example. The definitions are pinned down, so the data checks are only sanity checks.

**Points for the reviewer**

- *Note.* The statement is the conjunction of four separate conjectures (Sycamore's, Sigrist's two, and the A355149 one). The catalogue mode is settles-proves, so proving the conjunction proves each of them. A disproof would not have said which one fails, but that case does not arise here.
- *Note.* 'b is 21-periodic' and 'b is 42-periodic' are encoded as existential ℤ-valued sequences that are periodic on all of ℕ, constrained only for n ≥ 70 and n ≥ 138 respectively. This is equivalent to the literal reading: the differences are integers automatically, and a sequence periodic from some point on extends backwards periodically. Sigrist's b(n) is indexed by n, period 21, as in the text.
- *Note.* a 0 = 0 is a junk value. It plays no role: 0 is in neither {n | a n = 1} nor {n | a n = 2}, and the formulas only use indices 2n-1 ≥ 139, 2n ≥ 140 and s(n) with n ≥ 138. The natural-number subtraction 2*n - 1 is exact for n ≥ 70.
- *Note.* Sycamore's 'and therefore so does a(n)=2' is encoded as a second conjunct ({n | a n = 2}.Infinite), not as an implication. Since the statement is proved, this is the stronger and correct reading.

## A354571: Even and odd legs with odd prime factors ≡ 3 (mod 4): a(n)/n → π (A354571, A354570)

Verdict of the pre-review: **faithful**. Result: [oeis-a354571](../../results/oeis-a354571/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A354571.lean`](../../lean/Math0/Statements/OEIS/A354571.lean).

**The conjecture as stated in OEIS**

> A354571 %N (offset 1): "Ordered even leg lengths k (listed with multiplicity) of primitive Pythagorean triangles such that all odd prime factors of k are congruent to 3 (mod 4) and at least one prime factor is odd."
> A354571 %C (unsigned line; entry by _Lothar Selle_, Jun 04 2022): "Conjecture: lim_{n->oo} a(n)/n = Pi. Also, lim_{n->oo} A354570(n)/n = Pi."
> A354570 %N (offset 1; _Lothar Selle_, Jun 03 2022): "Ordered odd leg lengths k (listed with multiplicity) of primitive Pythagorean triangles such that all prime factors of k are congruent to 3 (mod 4)." with %C "Conjecture: lim_{n->oo} a(n)/n = Pi. Also, lim_{n->oo} A354571(n)/n = Pi."
> (Upstream oeisdata main is identical to the mirror: A354571 #41, A354570 #54.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop (nhds Real.pi) ∧
    Filter.Tendsto (fun n : ℕ => (a354570 n : ℝ) / n) Filter.atTop (nhds Real.pi)

-- definitions (abridged)
def IsPPT (x y z : ℕ) : Prop := 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ Nat.gcd (Nat.gcd x y) z = 1
def legTriangles (k : ℕ) : Finset (ℕ × ℕ) := ...  -- proved: (b, c) ∈ legTriangles k ↔ IsPPT b k c
def CondE (k : ℕ) : Prop := (∀ p ∈ k.primeFactors, Odd p → p % 4 = 3) ∧ ∃ p ∈ k.primeFactors, Odd p
def CondO (k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p % 4 = 3
def wE (k : ℕ) : ℕ := if Even k ∧ CondE k then (legTriangles k).card else 0
def wO (k : ℕ) : ℕ := if Odd k ∧ CondO k then (legTriangles k).card else 0
def numLE (w : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), w j
noncomputable def nthTerm (w : ℕ → ℕ) (n : ℕ) : ℕ := sInf {k | n ≤ numLE w k}
noncomputable def a (n : ℕ) : ℕ := nthTerm wE n
noncomputable def a354570 (n : ℕ) : ℕ := nthTerm wO n
```

**What the Lean statement says**

For a positive integer k, let N(k) be the number of primitive Pythagorean triangles that have k as a leg (pairs (b, c) with b > 0, b² + k² = c², gcd(b, k, c) = 1). Form the increasing list in which each even k appears N(k) times, when every odd prime factor of k is ≡ 3 (mod 4) and k has at least one odd prime factor; let a(n) be its n-th term (n ≥ 1). Form the increasing list in which each odd k whose prime factors are all ≡ 3 (mod 4) appears N(k) times; let A354570(n) be its n-th term. The statement asserts that a(n)/n → π and A354570(n)/n → π as n → ∞, as real limits.

**What the kernel checks against the OEIS data**

mem_legTriangles proves, for every k, that legTriangles k is exactly the set of primitive triangles with leg k. So the multiplicity is pinned down for all k, not only on the checked range. a_spec and a354570_spec, together with the proofs that both lists are infinite, show that nthTerm gives the genuine n-th term. Kernel checks: a_data covers all 58 listed terms of A354571 (multiplicities such as 12×2 and 84×4 included), and a354570_data all 60 listed terms of A354570 (21×2, 33×2 and so on included).

**Points for the reviewer**

- *Note.* 'Listed with multiplicity' is read as the number of primitive triangles having k as a leg. For even k the other leg is necessarily odd, so k is the even leg; for odd k it is the odd leg. This matches the entries' examples (12 from (5,12,13) and (12,35,37); 21 from (20,21,29) and (21,220,221)) and all listed data.
- *Note.* a 0 = a354570 0 = 0, and the division by n = 0 gives a junk value at n = 0. Neither affects a limit along atTop.
- *Note.* Both limits from Selle's sentence (the A354571 one and the 'Also' A354570 one) are included as a conjunction. The result proves both.

## A355076: Integer partial sums of the Calkin-Wilf ratios fusc(k)/fusc(k+1) at n = 2*4^k-1 and 2*4^k-2 (A355076)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a355076](../../results/oeis-a355076/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A355076.lean`](../../lean/Math0/Statements/OEIS/A355076.lean).

**The conjecture as stated in OEIS**

> A355076 %N (offset 0): "a(n) is the denominator of Sum_{k = 0..n} fusc(k)/fusc(k+1) (where fusc is Stern's diatomic series A002487)."
> A355076 %F (unsigned line; entry by _Rémy Sigrist_, Jun 18 2022): "Conjecture: a(n) = 1 for n of the form 2*4^k - 1 or 2*4^k - 2 for some k >= 0."
> A002487 %N: "Stern's diatomic series (or Stern-Brocot sequence): a(0) = 0, a(1) = 1; for n > 0: a(2*n) = a(n), a(2*n+1) = a(n) + a(n+1)."
> (Upstream oeisdata main is identical to the mirror, #11.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, (∃ k : ℕ, n = 2 * 4 ^ k - 1 ∨ n = 2 * 4 ^ k - 2) → a n = 1

-- definitions
def fuscAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then n
    else if n % 2 = 0 then fuscAux fuel (n / 2)
    else fuscAux fuel (n / 2) + fuscAux fuel (n / 2 + 1)
def fusc (n : ℕ) : ℕ := fuscAux (n + 1) n
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.range (n + 1), ((fusc k : ℚ) / (fusc (k + 1) : ℚ))).den
-- proved: fusc_zero, fusc_one, fusc_even (fusc (2n) = fusc n), fusc_odd (fusc (2n+1) = fusc n + fusc (n+1))
```

**What the Lean statement says**

Let fusc be Stern's diatomic sequence. For n ≥ 0, let a(n) be the reduced denominator of the rational number Σ_{k=0}^{n} fusc(k)/fusc(k+1). The statement asserts that for every k ≥ 0, a(2·4^k − 1) = 1 and a(2·4^k − 2) = 1, i.e. the partial sum is an integer at n = 0, 1, 6, 7, 30, 31, 126, 127, ...

**What the kernel checks against the OEIS data**

fusc_zero, fusc_one, fusc_even and fusc_odd prove the A002487 recursion for all n, which determines fusc. fusc_data checks the 92 listed terms of A002487. a_data checks all 53 listed terms a(0..52), including the 1's at n = 0, 1, 6, 7, 30, 31 and the non-1 values elsewhere. Rat.den is the reduced denominator, as in the PARI `denominator`. Together these pin the definitions down.

**Points for the reviewer**

- *Note.* The statement covers one direction only: if n has the form 2·4^k − 1 or 2·4^k − 2, then a(n) = 1. This is exactly the OEIS wording. It does not claim that these are the only n with a(n) = 1. My Python check to n = 9000 finds a(n) = 1 exactly at n ∈ {0, 1, 6, 7, 30, 31, 126, 127, 510, 511, 2046, 2047, 8190, 8191}, so an 'iff' reading would also fit the data. However, the same author writes 'iff' explicitly when he means it (e.g. A355339), and he does not do so here. The one-directional reading is therefore the natural one, and the result does not cover the converse.
- *Note.* The truncated subtraction is harmless: 2·4^k ≥ 2, so 2*4^k - 1 and 2*4^k - 2 are exact (k = 0 gives n = 1 and n = 0). Division by zero cannot occur, since fusc(k+1) ≥ 1 for all k ≥ 0.

## A355339: A355339: the central even run of the knight-move triangle has length 1 iff n = 2^m - 2

Verdict of the pre-review: **faithful**. Result: [oeis-a355339](../../results/oeis-a355339/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A355339.lean`](../../lean/Math0/Statements/OEIS/A355339.lean).

**The conjecture as stated in OEIS**

> A355339 %N (offset 0): "a(n) is the number of central even terms in the n-th row of triangle A355320; a(0) = 0."
> A355339 %F (unsigned line; entry by _Rémy Sigrist_, Jun 29 2022): "Conjecture: a(n) = 1 iff n > 0 and n belongs to A000918."
> A000918 %N (offset 0): "a(n) = 2^n - 2."
> A355320 %N: "Irregular triangle T(n, k), n >= 0, -2*n <= k <= 2*n, read by rows; T(0, 0) = 1; for n > 0, T(n, k) is the sum of all terms in previous rows at one knight's move away." with %F "T(n, k) = T'(n-1, k-2) + T'(n-1, k+2) + T'(n-2, k-1) + T'(n-2, k+1) for n > 0 (where T' extends T with 0's outside its domain of definition)."
> A355339 PARI: max(0, 2*valuation(r >> (2*n), 2)-1).
> (Upstream oeisdata main is identical to the mirror, #10.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, a n = 1 ↔ (0 < n ∧ ∃ m : ℕ, (n : ℤ) = 2 ^ m - 2)

-- definitions (abridged)
def step (pq : List ℕ × List ℕ) : List ℕ × List ℕ :=
  (pq.2, addL (addL pq.2 (List.replicate 4 0 ++ pq.2))
    (addL (List.replicate 3 0 ++ pq.1) (List.replicate 5 0 ++ pq.1)))
def rowPair (n : ℕ) : List ℕ × List ℕ := step^[n] ([], [1])
def row (n : ℕ) : List ℕ := (rowPair n).2
def entry (r : List ℕ) (m : ℕ) (k : ℤ) : ℕ := if 0 ≤ k + 2 * m then r.getD (k + 2 * m).toNat 0 else 0
def T (n : ℕ) (k : ℤ) : ℕ := entry (row n) n k
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    let r := row n
    let right := (((List.range (2 * n + 1)).map fun k : ℕ => entry r n k).takeWhile fun x => x % 2 == 0).length
    let left := (((List.range (2 * n + 1)).map fun k : ℕ => entry r n (-k)).takeWhile fun x => x % 2 == 0).length
    if right = 0 then 0 else left + right - 1
-- proved: T_zero_zero, T_eq_zero (|k| > 2n), T_one, T_add_two (the knight-move recurrence for all k ∈ ℤ)
```

**What the Lean statement says**

Let T(n,k) (n ≥ 0, k ∈ ℤ) be defined by T(0,0) = 1, T(n,k) = 0 for |k| > 2n, and T(n,k) = T(n−1,k−2) + T(n−1,k+2) + T(n−2,k−1) + T(n−2,k+1), where rows with negative index are zero. Let a(0) = 0. For n ≥ 1, let a(n) be the length of the maximal run of consecutive even entries T(n,k) that contains k = 0, or 0 if T(n,0) is odd. The statement asserts that for every n ≥ 0, a(n) = 1 if and only if n ≥ 1 and n = 2^m − 2 for some m ≥ 0, i.e. n ∈ {2, 6, 14, 30, ...}.

**What the kernel checks against the OEIS data**

T_zero_zero, T_eq_zero, T_one and T_add_two prove that T satisfies the A355320 definition (the recurrence with zero extension) for all n and k, which determines T. T_data checks the 91 listed terms of A355320 (rows 0–6). a_data checks all 77 listed terms a(0..76), including the 1's at n = 2, 6, 14, 30, 62 and many values > 1 that exercise the run-length reading. The run-length reading is also confirmed by the entry's example (parenthesized central blocks) and by its PARI program (2·valuation − 1 for the symmetric rows).

**Points for the reviewer**

- *Note.* 'Number of central even terms' is encoded as left + right − 1, the run of evens to the left and right of k = 0 sharing the center. The PARI program computes 2·right − 1. The two agree because the rows are symmetric (A355320 %F: T(n,−k) = T(n,k)), but that symmetry is not proved in the statement file. They also agree on all 77 checked terms.
- *Note.* Membership in A000918 is encoded in ℤ as (n : ℤ) = 2^m − 2 with m : ℕ. This includes the terms −1 and 0, which are excluded by n > 0 as in the OEIS text. The 'iff' is encoded as a genuine ↔ for every n ≥ 0, and a(0) = 0 is imposed literally.

## A355360: Columns 1 and 2 of the theta-series triangle A355360 are P(x)^3 and 2P(x)^6

Verdict of the pre-review: **faithful**. Result: [oeis-a355360](../../results/oeis-a355360/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A355360.lean`](../../lean/Math0/Statements/OEIS/A355360.lean).

**The conjecture as stated in OEIS**

> A355360 %N (offset 0, tabl): "G.f. A(x,y) satisfies: x*y*A(x,y) = Sum_{n=-oo..+oo} (-1)^n * x^(n*(n+1)/2) * A(x,y)^n, with coefficients T(n,k) of x^n*y^k in A(x,y) given as a triangle read by rows."
> A355360 %C (unsigned lines; entry by _Paul D. Hanna_, Jul 19 2022): "Conjectures. (C.1) Column 1 equals A000716, the number of partitions into parts of 3 kinds. (C.2) Column 2 equals twice A023005, the number of partitions into parts of 6 kinds."
> %e: "in which column 1 appears to equal A000716, the coefficients in P(x)^3, and column 2 appears to equal twice A023005, the coefficients in P(x)^6".
> (Upstream oeisdata main is identical to the mirror, #7.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ n : ℕ, T (n + 1) 1 = A000716 n) ∧ (∀ n : ℕ, T (n + 2) 2 = 2 * A023005 n)

-- definitions (abridged; Poly = List ℤ (coeffs in y), Ser = List Poly (coeffs in x))
def thetaCoeff (B : Ser) (m : ℕ) : Poly :=   -- [x^m] Σ_{n≥0} (-1)^n x^{n(n+1)/2} (B^n - B^{-(n+1)})
  let L := m + 1
  let Binv := sinv L B
  ((List.range L).foldl (fun (st : Poly × Ser × Ser) n =>
    let t := n * (n + 1) / 2
    if t ≤ m then
      (padd st.1 (pscale ((-1) ^ n) (padd (st.2.1.getD (m - t) []) (pscale (-1) (st.2.2.getD (m - t) [])))),
        smul L st.2.1 B, smul L st.2.2 Binv)
    else st) ([], [[1]], Binv)).1
def coeffs : ℕ → Ser
  | 0 => [[1]]
  | m + 1 => let B := coeffs m; B ++ [padd (0 :: B.getD m []) (pscale (-1) (thetaCoeff B (m + 1)))]
def T (n k : ℕ) : ℤ := ((coeffs n).getD n []).getD k 0
def p (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)
def partitionsOfKinds (j n : ℕ) : ℕ := ∑ f ∈ Finset.Nat.antidiagonalTuple j n, ∏ i, p (f i)
def A000716 (n : ℕ) : ℕ := partitionsOfKinds 3 n
def A023005 (n : ℕ) : ℕ := partitionsOfKinds 6 n
```

**What the Lean statement says**

Let A(x,y) = Σ_m a_m(y) x^m, with a_m ∈ ℤ[y], be given by a_0 = 1 and a_{m+1} = y·a_m − [x^{m+1}] F(a_0 + a_1 x + ... + a_m x^m), where F(B) = Σ_{n∈ℤ} (−1)^n x^{n(n+1)/2} B^n. This is the unique power-series solution of x·y·A = F(A). Let T(n,k) = [x^n y^k] A. The statement asserts that for every n ≥ 0, T(n+1, 1) equals the number of partitions of n into parts of 3 kinds (= [x^n] P(x)^3), and T(n+2, 2) equals twice the number of partitions of n into parts of 6 kinds (= 2·[x^n] P(x)^6). Equivalently, the y- and y²-coefficients of A are x·P³ and 2x²·P⁶.

**What the kernel checks against the OEIS data**

a_data checks all 66 DATA terms (rows 0–10), and T_example_rows checks rows 11 and 12 from the EXAMPLE section, 91 triangle entries in all. A000716_data checks 10 terms of A000716 and A023005_data 6 terms of A023005 (via p_eq_pb, proved). statement_check verifies the column alignment for 10 and 6 values. The recursion `coeffs` is literally the entry's PARI program (new coefficient = [x^m](x y A − F(A)) with that coefficient set to 0). With 91 matching entries a wrong definition is implausible, but see the note.

**Points for the reviewer**

- *Note.* T is defined by the coefficient recursion, which is the entry's PARI program, not as the coefficients of a series proved in the statement file to satisfy x·y·A = F(A). The equivalence is argued only in the docstring, and the argument is correct: order x^0 forces a_0 = 1, and at order x^m only the n = −1 term −A^{−1} sees a_m, contributing +a_m. Since the OEIS data were generated by this same program and 13 rows match, this is not a fidelity risk.
- *Note.* The column alignment is T(n+1,1) = A000716(n) and T(n+2,2) = 2·A023005(n): column k starts at the diagonal entry T(k,k), and the targets have offset 0. The entry's EXAMPLE section displays exactly this alignment (column 1 = 1, 3, 9, 22, ... against P³ = 1 + 3x + 9x² + ...). The entries T(0,1), T(0,2) and T(1,2), which lie outside the triangle, are correctly not included.
- *Note.* 'Partitions into parts of j kinds' is defined as a sum over j-tuples (n_1, ..., n_j) with Σ n_i = n of Π p(n_i), which is the coefficient of x^n in P(x)^j. This is the g.f. given in both A000716 and A023005, and it is checked on their first listed terms.

# Fidelity review packet 03 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A115026, A116184, A119936, A120069, A121750, A123710, A124526, A126127, A127752, A127755.

## A115026: A115026 has a term greater than 370: a(119) = 371

Verdict of the pre-review: **faithful**. Result: [oeis-a115026](../../results/oeis-a115026/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A115026.lean`](../../lean/Math0/Statements/OEIS/A115026.lean).

**The conjecture as stated in OEIS**

> %C A115026 Conjecture: no term is greater than 370. - _Harvey P. Dale_, Jun 08 2022  [Entry: %N Limiting value of n under iteration of "sum of the digits raised to the power of the number of digits of n" (A101337). %C Iterate A101337 starting at n until reaching a constant value (like 370) or a cycle (like 160, 217, 352, 160, ...). In the latter case, a(n) takes the smallest value in the cycle (e.g., a(59) = 160). %O 1,2; _Sergio Pimentel_, Feb 24 2006]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n ≤ 370

where
def F (m : ℕ) : ℕ := ((Nat.digits 10 m).map (· ^ (Nat.digits 10 m).length)).sum
def limitCycle (n : ℕ) : Set ℕ := {m | (∃ k, F^[k] n = m) ∧ ∃ p, 0 < p ∧ F^[p] m = m}
def a (n : ℕ) : ℕ :=
  let y := meet (fuel n) (F n) (F (F n))   -- Floyd tortoise/hare
  cycleMin y (fuel n) (F y) y               -- minimum around the cycle of y
-- fuel n = (max n (70*9^70) + 2)^2
theorem a_spec (n : ℕ) : a n ∈ limitCycle n ∧ ∀ m ∈ limitCycle n, a n ≤ m
```

**What the Lean statement says**

Let F(m) be the sum of the d^L over the decimal digits d of m, where L is the number of digits of m. For every n >= 1, the orbit n, F(n), F(F(n)), ... eventually enters a cycle (possibly a fixed point). The statement claims that the smallest element of that cycle is at most 370.

**What the kernel checks against the OEIS data**

a_data checks all 65 listed terms a 1 through a 65 by decide +kernel. These include the fixed-point value 370, small fixed points 1..9, and the genuine cycle case a(59) = 160. Beyond the data, a_spec proves for every n that a n is exactly the minimum of the periodic part of the orbit, so the definition is pinned for all n, not only on the checked terms. F matches A101337 ('Sum of (each digit of n raised to the power (number of digits in n))'): the exponent is the digit count of the current iterate, as the entry's example 89 -> 145 -> 190 -> 730 -> 370 requires.

**Points for the reviewer**

- *Note.* The conjecture is false in a trivial way: 371 = 3^3+7^3+1^3 is a narcissistic number, so a(371) = 371. The smallest counterexample is a(119) = 371 (119 -> 731 -> 371), which the result uses. The Lean statement is the literal 'every term <= 370' over the full offset-1 range, so a single term > 370 refutes exactly what Dale wrote. There is no reading of 'no term is greater than 370' under which a(119) = 371 is not a counterexample.
- *Note.* n = 0 (where F 0 = 0) is excluded by 1 <= n, matching offset 1. Orbits of n >= 1 never reach 0.

## A116184: A116184: Adamchuk's conjectures on 37^3 dividing the numerator of sum_{k=1}^{36} 1/k^n

Verdict of the pre-review: **faithful**. Result: [oeis-a116184](../../results/oeis-a116184/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A116184.lean`](../../lean/Math0/Statements/OEIS/A116184.lean).

**The conjecture as stated in OEIS**

> %C (_Alexander Adamchuk_, Apr 08 2007, entry author; comment unsigned): "... Conjecture: All terms of the arithmetic progression 3+36k belong to a(n). Prime terms in a(n) are {3, 37, 73, 443, 739, 887, 1109, ...}. It appears that all primes in a(n) that are greater than 37 are of the form 37k-1. ..." %N: "Numbers n such that 37^3 divides the numerator of generalized harmonic number H(36,n) = Sum[ 1/k^n, {k,1,36} ]." Offset 1. Rev #6 (Feb 16 2025); unchanged on GitHub main.

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ k : ℕ, IsTerm (3 + 36 * k)) ∧
    (∀ p : ℕ, p.Prime → 37 < p → IsTerm p → ∃ k : ℕ, p = 37 * k - 1)

where:
def H (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc (1 : ℕ) 36, 1 / ((k : ℚ) ^ n)
def IsTerm (n : ℕ) : Prop := (37 ^ 3 : ℤ) ∣ (H n).num
(a n := Nat.nth IsTerm (n - 1) is defined but not used in the statement; exists_a_eq_iff proves that for x ≠ 0, x is some a(m) with m >= 1 iff IsTerm x.)
```

**What the Lean statement says**

Let H(n) = sum_{k=1}^{36} 1/k^n, an exact rational number, and call n a term if 37^3 divides the numerator of H(n) in lowest terms. Claim (a): 3 + 36k is a term for every integer k >= 0. Claim (b): every prime p > 37 that is a term satisfies p = 37k - 1 for some natural k, i.e. p ≡ -1 (mod 37).

**What the kernel checks against the OEIS data**

a_data kernel-checks all 53 listed terms (3, 37, ..., 975) by a kernel-decided filter of IsTerm over [0, 976). This uses isTerm_iff_check, proved because gcd(37, 36!) = 1, and coeffs_eq, which is also kernel-checked. It pins the predicate exactly on [0, 976). not_isTerm_zero shows that 0, outside the sequence's domain, is not a term.

**Points for the reviewer**

- *Note.* The statement is the conjunction of the explicitly labelled 'Conjecture' (the 3+36k progression) and the hedged 'It appears that ...' claim about primes. Proving the conjunction settles both. The quoted list of prime terms {3, 37, 73, 443, ...} and the separate 37^4 remark are data observations and are not formalized.
- *Note.* 'Belongs to a(n)' is expressed through IsTerm instead of membership in the range of a. These are equivalent for nonzero x (exists_a_eq_iff), and 3+36k ≠ 0. Natural subtraction in 37k - 1 is harmless: k = 0 gives 0, which is not a prime > 37, and for k >= 1 it is the true value. 'Numerator' is Rat.num in lowest terms, as Mathematica's Numerator is. k ranges over k >= 0, which includes the term 3.

## A119936: The row-LCM of denominators of the cube of the mean matrix is n · lcm(1..n)²

Verdict of the pre-review: **faithful**. Result: [oeis-a119936](../../results/oeis-a119936/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A119936.lean`](../../lean/Math0/Statements/OEIS/A119936.lean).

**The conjecture as stated in OEIS**

> %F A119936 a(n)/n^3 = A027451(n) = A002944(n)^2 (the second equation is a conjecture). [_Wolfdieter Lang_, Jul 20 2006; entry #22, Nov 05 2019, identical in the mirror and on GitHub main.] Context: %N "Least common multiple (LCM) of denominators of the rows of the triangle of rationals A119935/A119932."; %C "The triangle of rationals is the matrix cube of the matrix with elements a(i,j) = 1/i if j <= i, 0 if j > i."; %F "a(n) = lcm_{m=1..n} seq(A119932(n,m)), n >= 1."; offset 1. A027451 = "First diagonal of A027447" (A027447 = rows of A^3 written over the least common denominator); A002944 = "a(n) = LCM(1,2,...,n) / n".

**The frozen Lean statement**

```lean
def A (i j : ℕ) : ℚ := if j ≤ i then 1 / (i : ℚ) else 0
def Amat (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i j => A ((i : ℕ) + 1) ((j : ℕ) + 1)
def r (n m : ℕ) : ℚ := if h : 1 ≤ m ∧ m ≤ n then (Amat n ^ 3) ⟨n - 1, by omega⟩ ⟨m - 1, by omega⟩ else 0
def a (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm fun m => (r n m).den
def lcmUpTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id
def A002944 (n : ℕ) : ℕ := lcmUpTo n / n

def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n : ℚ) / (n : ℚ) ^ 3 = ((A002944 n : ℕ) : ℚ) ^ 2
```

**What the Lean statement says**

Let A be the infinite lower-triangular matrix with A(i,j) = 1/i for j ≤ i and 0 otherwise. Let r(n,m) be the (n,m) entry of A^3, and let a(n) be the lcm of the reduced denominators of r(n,1), ..., r(n,n). Then for every n ≥ 1, a(n)/n^3 = (lcm(1..n)/n)^2 (equivalently, as statement_iff proves, a(n) = n·lcm(1..n)^2).

**What the kernel checks against the OEIS data**

a_data checks all 19 listed terms a(1..19) of A119936. triangle_num_data and triangle_den_data check the 37 listed numerators (A119935) and 32 listed denominators (A119932) of the triangle r read by rows. A002944_data checks the 31 listed terms of A002944. All are decide +kernel. Together they pin down the matrix, the row-LCM and A002944. A027451 is not encoded separately: it is replaced by a(n)/n^3, which is the entry's own first (non-conjectural) equation.

**Points for the reviewer**

- *Note.* The conjecture is literally A027451(n) = A002944(n)^2. The Lean statement replaces A027451(n) by a(n)/n^3, which is the entry's own unconjectured first equation. It holds by definition: A027447 writes row n of A^3 over the least common denominator a(n), and the diagonal entry of A^3 is 1/n^3, so A027451(n) = a(n)/n^3. The substitution is correct, but a reviewer should know A027451's data is not checked directly. Its listed terms (1,1,4,9,144,...) do agree with (lcm(1..n)/n)^2.
- *Note.* Natural division in A002944 n = lcmUpTo n / n is exact for n ≥ 1 (A002944_mul), and n = 0 is excluded. The equation is stated in ℚ, so there is no truncation issue. statement_iff gives the integer form a(n) = n·lcm(1..n)^2, which I confirmed independently on all 19 listed terms.

## A120069: Denominators of Sum C(k)/4^(k-1): Groux's and Staunton's conjectures (A120069)

Verdict of the pre-review: **faithful**. Result: [oeis-a120069](../../results/oeis-a120069/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A120069.lean`](../../lean/Math0/Statements/OEIS/A120069.lean).

**The conjecture as stated in OEIS**

> %F A120069 Conjecture: a(n) = denominator(Catalan(n)/4^(n-1)). - _Groux Roland_, Dec 11 2010
> %F A120069 Conjecture: a(n) = 2^(A283208(n)-2). - _Alexander Staunton_, Feb 28 2026
> [Entry #30, Mar 10 2026, identical on GitHub main.] Context: a(n) = denominator(r(n)), r(n) = Sum_{k=1..n} C(k)/2^(2*(k-1)) in lowest terms, C = A000108; offset 1. A283208 (offset 0): "a(n) is the least nonnegative integer such that 2^a(n) (2n+1)/(n+1) c(2n) is a nonnegative integer, where c(2n) = c(2n-1) = Pochhammer(1/2,n)/(n!)".

**The frozen Lean statement**

```lean
def r (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / 2 ^ (2 * (k - 1))
def a (n : ℕ) : ℕ := (r n).den
def pochhammer (x : ℚ) (n : ℕ) : ℚ := ∏ i ∈ Finset.range n, (x + i)
def vietoris (n : ℕ) : ℚ := pochhammer (1 / 2) n / (n.factorial : ℚ)
def w (n : ℕ) : ℚ := (2 * n + 1) / (n + 1) * vietoris n
def IsNatExp (n e : ℕ) : Prop := ∃ m : ℕ, (2 : ℚ) ^ e * w n = m
def A283208 (n : ℕ) : ℕ := Nat.find ⟨2 * n, isNatExp_two_mul n⟩

def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    a n = ((catalan n : ℚ) / 4 ^ (n - 1)).den ∧
      (a n : ℚ) = (2 : ℚ) ^ ((A283208 n : ℤ) - 2)
```

**What the Lean statement says**

For every n ≥ 1, let a(n) be the reduced denominator of Σ_{k=1}^{n} C_k/4^{k-1}, with C_k the Catalan numbers. Then (i) a(n) equals the reduced denominator of C_n/4^{n-1}, and (ii) a(n) = 2^{e(n)-2}, where e(n) is the least e ≥ 0 such that 2^e·(2n+1)/(n+1)·(1/2)_n/n! is a nonnegative integer. The exponent is an integer, so it is not truncated.

**What the kernel checks against the OEIS data**

a_data checks all 27 listed terms a(1..27) of A120069 (kernel, through the proven-equal catFast). A283208_data checks all 63 listed terms A283208(0..62) against the comment's definition (kernel). Both definitions are pinned down. The index alignment (A120069 at offset 1 and A283208 at offset 0, both evaluated at the same n) agrees with the data: a(1)=1=2^(2-2), a(2)=2=2^(3-2), a(3)=16=2^(6-2). I re-checked both conjectured identities independently on all 27 listed terms.

**Points for the reviewer**

- *Note.* The statement is the conjunction of two separate conjectures (Groux 2010 and Staunton 2026). A proof settles both. A disproof of the conjunction would not say which one fails, but the catalog mode is settles-proves, so this does not matter here.
- *Note.* Staunton's exponent A283208(n)-2 is taken in ℤ. Because A283208(n) ≥ 2 for all n ≥ 1 (A283208(1) = 2 and the sequence increases), this matches the intended natural-number reading exactly. Using ℤ does not weaken the statement.

## A121750: Mathar's order-6 recurrence for A121750 (even-length columns in deco polyominoes) holds for all n >= 7

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a121750](../../results/oeis-a121750/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A121750.lean`](../../lean/Math0/Statements/OEIS/A121750.lean).

**The conjecture as stated in OEIS**

> %F A121750 Conjecture D-finite with recurrence a(n) +(-n-2)*a(n-1) +(-n^2+4*n-2)*a(n-2) +(n^3-3*n^2-4*n+11)*a(n-3) -(n-1)*(n^2-11*n+26)*a(n-4) +(-n^3+5*n^2+7*n-43)*a(n-5) +(n-3)*(n-5)^2*a(n-6)=0. - _R. J. Mathar_, Jul 26 2022
> [Entry #13, Aug 20 2024, identical on GitHub main.] %N: "Number of columns of even length in all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column." Offset 1 (_Emeric Deutsch_, Aug 20 2006).

**The frozen Lean statement**

```lean
def IsDeco (n : ℕ) (cs : List (ℕ × ℕ)) : Prop :=
  cs ≠ [] ∧ (∀ c ∈ cs, c.1 ≤ c.2) ∧ (∀ c ∈ cs.head?, c.1 = 0) ∧
  (∀ i (h : i + 1 < cs.length), cs[i].1 ≤ cs[i + 1].1 ∧ cs[i + 1].1 ≤ cs[i].2) ∧
  (∀ i (h : i < cs.length), i + cs[i].2 + 1 ≤ n) ∧
  (∃ i, ∃ h : i < cs.length, i + cs[i].2 + 1 = n) ∧
  (∀ i (h : i < cs.length), i + cs[i].2 + 1 = n → i + 1 = cs.length)
def tails ... ; def decos : ℕ → List (List (ℕ × ℕ)) | 0 => [] | n + 1 => tails n 0   -- mem_decos: cs ∈ decos n ↔ IsDeco n cs; nodup_decos
def evenCols (cs : List (ℕ × ℕ)) : ℕ := cs.countP fun c => (c.2 + 1 - c.1) % 2 == 0
def a (n : ℕ) : ℕ := ((decos n).map evenCols).sum

def statement : Prop :=
  ∀ n : ℕ, 7 ≤ n →
    (a n : ℤ) + (-(n : ℤ) - 2) * a (n - 1) + (-(n : ℤ) ^ 2 + 4 * n - 2) * a (n - 2) +
      ((n : ℤ) ^ 3 - 3 * n ^ 2 - 4 * n + 11) * a (n - 3) -
      ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 11 * n + 26) * a (n - 4) +
      (-(n : ℤ) ^ 3 + 5 * n ^ 2 + 7 * n - 43) * a (n - 5) +
      ((n : ℤ) - 3) * ((n : ℤ) - 5) ^ 2 * a (n - 6) = 0
```

**What the Lean statement says**

Encode a polyomino as a nonempty list of columns (b_i, t_i) with b_i ≤ t_i, b_0 = 0, and b_i ≤ b_{i+1} ≤ t_i (directed and column-convex, with the source at the origin). Call it deco of height n if max_i(i + t_i) + 1 = n and that maximum is reached only at the last column. Let a(n) be the total number of even-length columns (t-b+1 even) over all deco polyominoes of height n. Then for every n ≥ 7, a(n) - (n+2)a(n-1) + (-n^2+4n-2)a(n-2) + (n^3-3n^2-4n+11)a(n-3) - (n-1)(n^2-11n+26)a(n-4) + (-n^3+5n^2+7n-43)a(n-5) + (n-3)(n-5)^2 a(n-6) = 0, computed in ℤ.

**What the kernel checks against the OEIS data**

Direct enumeration in the kernel: a_data_direct checks a(1..6); decos_length_data_direct checks the counts 1!,...,6!; triangle_data checks rows 1-6 of A121748 (the distribution by number of even columns). Through the proven-equal DP (a_eq_aDP), a_data checks all 19 listed terms a(1..19) and decos_length_data checks n! deco polyominoes for n = 1..19. recurrence_data checks the transcribed recurrence for n = 7..19. Together these strongly pin down the encoding: the diagonal height, directedness and the 'only in the last column' condition all affect the n! counts and the A121748 rows. I recomputed independently that the recurrence vanishes on the OEIS data for n = 7..19.

**Points for the reviewer**

- *Note.* The translation from cell-set polyominoes up to translation to column lists, with 'height along the diagonal' read as the number of anti-diagonals x+y = const met, is argued only in the prose docstring and not proved. The kernel checks above (n! counts for 19 heights, 6 rows of A121748, 19 terms) make a wrong encoding that still matched all of them very unlikely.
- *Note.* Mathar gives no range. n ≥ 7 is the largest range for which every a(n-6) is a term (offset 1), so this is the strongest natural reading, and it holds on the data from n = 7. With natural subtraction, n-6 ≥ 1, so there is no truncation. (For the record: the recurrence would also hold at n = 6 if one set a(0) = 1, but a(0) is not a term and Lean's a 0 = 0 is never used.)

## A123710: A123710: the rows of inv(floor(n/k)) with four nonzero entries are 6 and the proper prime powers

Verdict of the pre-review: **faithful**. Result: [oeis-a123710](../../results/oeis-a123710/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A123710.lean`](../../lean/Math0/Statements/OEIS/A123710.lean).

**The conjecture as stated in OEIS**

> %F A123710 a(n) = A025475(n) for n>2 (conjectured). - _M. F. Hasler_, Feb 12 2012
> [Entry #27, Sep 05 2025, identical on GitHub main.] %N: "Indices k such that 4 = A123709(k) = number of nonzero terms in row k of triangle A123706." %C: "Triangle A123706 is the matrix inverse of triangle A010766, where A010766(n,k) = [n/k]." Offset 1. A025475 (offset 1): "1 and the prime powers p^m where m >= 2, thus excluding the primes."

**The frozen Lean statement**

```lean
def floorMat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i j => ((((i : ℕ) + 1) / ((j : ℕ) + 1) : ℕ) : ℤ)
noncomputable def A123706 (n k : ℕ) : ℤ :=
  if h : 1 ≤ k ∧ k ≤ n then (floorMat n)⁻¹ ⟨n - 1, by omega⟩ ⟨k - 1, by omega⟩ else 0
noncomputable def A123709 (n : ℕ) : ℕ := #{k ∈ Icc 1 n | A123706 n k ≠ 0}
def IsTerm (n : ℕ) : Prop := A123709 n = 4
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)
def IsA025475 (m : ℕ) : Prop := m = 1 ∨ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ m = p ^ k
noncomputable def A025475 (n : ℕ) : ℕ := Nat.nth IsA025475 (n - 1)

def statement : Prop :=
  ∀ n : ℕ, 2 < n → a n = A025475 n
```

**What the Lean statement says**

Let F be the lower-triangular integer matrix F(n,k) = ⌊n/k⌋ and T = F^{-1}. Let R(n) be the number of nonzero entries T(n,k), 1 ≤ k ≤ n. List the n with R(n) = 4 in increasing order as a(1), a(2), .... List 1 and the prime powers p^m with m ≥ 2 in increasing order as b(1), b(2), .... Then a(n) = b(n) for every n ≥ 3. If there were fewer than n indices with R = 4, Nat.nth would make a(n) = 0 and the statement would be false, as the conjecture would be.

**What the kernel checks against the OEIS data**

A123706_data checks all 113 listed terms of A123706 (rows 1-14 and part of row 15). A123709_data checks all 76 listed terms of A123709. a_data checks the first 21 of the 52 listed terms of A123710 (all terms ≤ 512). A025475_data checks the first 21 listed terms of A025475. All are decide +kernel, using the proven-equal back-substitution T (Tmat_eq_inv proves it is the inverse of every truncation). The definitions of the triangle, the row count and both index sequences are pinned down, including the exceptional a(2) = 6 and the offset alignment (A025475(1) = 1 and A025475(2) = 4 against a(1) = 4 and a(2) = 6, so equality starts exactly at n = 3).

**Points for the reviewer**

- *Note.* Only 21 of the 52 listed A123710 terms are kernel-checked, because of the back-substitution cost up to 512. The defining ingredients (A123706 and A123709) are checked on all their listed terms, so this does not leave the definition underdetermined.
- *Note.* Matrix.inv over ℤ is Mathlib's adjugate-based inverse, which is a junk value when the determinant is not a unit. Here det = 1, and Tmat_eq_inv proves the computed rows are the true two-sided inverse of every truncation, so no junk values occur.

## A124526: Hanna's conjecture A124418(n,k) = k! * A124526(n,k) (partitions with k mixed-parity blocks) proved

Verdict of the pre-review: **faithful**. Result: [oeis-a124526](../../results/oeis-a124526/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A124526.lean`](../../lean/Math0/Statements/OEIS/A124526.lean).

**The conjecture as stated in OEIS**

> %C A124526 A124418(n,k) = k!*T(n,k) (conjecture). [_Paul D. Hanna_, Nov 08 2006; entry #14, Nov 02 2020, identical on GitHub main.] Here T(n,k) = A049020([n/2],k)*A049020([(n+1)/2],k), "Row n has 1+floor(n/2) terms", offset 0, A049020(n,k) = Sum_{i=0..n} S2(n,i)*C(i,k). The same conjecture is in A124418 %F: "Conjecture: T(n,k) = k!*A049020([n/2],k)*A049020([(n+1)/2],k) ... - _Paul D. Hanna_, Nov 08 2006". A124418 %N: "T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries (0<=k<=floor(n/2))."

**The frozen Lean statement**

```lean
def A049020 (m k : ℕ) : ℕ := ∑ i ∈ range (m + 1), Nat.stirlingSecond m i * Nat.choose i k
def T (n k : ℕ) : ℕ := A049020 (n / 2) k * A049020 ((n + 1) / 2) k
def IsMixed (b : Finset ℕ) : Prop := (∃ x ∈ b, Odd x) ∧ (∃ x ∈ b, Even x)
def A124418 (n k : ℕ) : ℕ :=
  (univ.filter fun P : Finpartition (Icc 1 n) => (P.parts.filter IsMixed).card = k).card

def statement : Prop :=
  ∀ n k : ℕ, k ≤ n / 2 → A124418 n k = k.factorial * T n k
```

**What the Lean statement says**

For all n ≥ 0 and 0 ≤ k ≤ ⌊n/2⌋, the number of set partitions of {1,...,n} with exactly k blocks that contain both an odd and an even element equals k!·B(⌊n/2⌋,k)·B(⌊(n+1)/2⌋,k), where B(m,k) = Σ_{i=0}^{m} S2(m,i)·C(i,k) and S2 is the Stirling number of the second kind.

**What the kernel checks against the OEIS data**

T_data and a_data check all 16 listed rows and all 72 listed terms of A124526 (kernel). rhs_data checks that k!·T(n,k) reproduces all 49 listed terms of A124418 (this checks only the transcription of the right-hand side). A124418_data checks the combinatorial definition directly only on rows n = 0..3 ([1],[1],[1,1],[2,3]), because enumerating Finpartition is doubly exponential. The right-hand side is thoroughly pinned down. The left-hand side is pinned down only weakly by data, but its definition is a literal three-line transcription: Finpartition (Icc 1 n) is exactly the set partitions of {1..n} into nonempty blocks, and IsMixed is 'contains an odd and an even entry'.

**Points for the reviewer**

- *Note.* The combinatorial side A124418 is kernel-checked against OEIS only for n ≤ 3 (6 values). Its fidelity therefore rests on reading the short definition (Finpartition of Icc 1 n, count of IsMixed parts), which I read as correct, rather than on data.
- *Note.* The range k ≤ ⌊n/2⌋ matches the index range of both triangles. Outside it both sides are 0 anyway: there are only ⌊n/2⌋ even elements, and A049020(m,k) = 0 for k > m. So the restriction does not weaken the statement. A049020 uses Mathlib's Nat.stirlingSecond rather than the quoted alternating-sum closed form, which is the same function, and it is confirmed on all 72 terms.

## A126127: A126127: Israel's conjectured bivariate g.f. of the inverse square of A061554 holds

Verdict of the pre-review: **faithful**. Result: [oeis-a126127](../../results/oeis-a126127/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A126127.lean`](../../lean/Math0/Statements/OEIS/A126127.lean).

**The conjecture as stated in OEIS**

> %F A126127 G.f. as triangle (conjectured): (1-x)*(1-x+x^2)/(1-x*y+3*x^2-x^3*y+x^4). - _Robert Israel_, Jul 07 2019
> (Context: name "Inverse square of A061554."; %F "Given M = Pascal's triangle with descending row terms, (A061554); A126127 = M^(-2)."; offset 0, keywords tabl,sign; Maple: T:= Matrix(20,20,(n,k) -> binomial(n-1, floor((n)/2 - (-1)^(n-k)*(k)/2)), shape=triangular[lower]): A:= T^(-2).)

**The frozen Lean statement**

```lean
def statement : Prop :=
  gf = (1 - X 0) * (1 - X 0 + X 0 ^ 2) *
    (1 - X 0 * X 1 + 3 * X 0 ^ 2 - X 0 ^ 3 * X 1 + X 0 ^ 4 : MvPowerSeries (Fin 2) ℚ)⁻¹

with
  def M (n k : ℕ) : ℤ := if k ≤ n then (n.choose ((n - k) / 2) : ℤ) else 0
  Minv n k := row n of N computed by forward substitution N(n,k) = [k = n] - Σ_{j<n} M(n,j) N(j,k) (k ≤ n), 0 for k > n (via nextRow/invRows lists)
  def T (n k : ℕ) : ℤ := ∑ j ∈ range (n + 1), Minv n j * Minv j k
  noncomputable def gf : MvPowerSeries (Fin 2) ℚ := fun m => if m 1 ≤ m 0 then (T (m 0) (m 1) : ℚ) else 0
Proved helpers: Nmat_eq_inv (L×L truncation of Minv = (Mmat L)⁻¹), T_spec (Tmat L = Mmat L ^ (-2 : ℤ) for every L), coeff_gf, statement_iff (equivalent to gf * den = (1 - X 0) * (1 - X 0 + X 0 ^ 2)).
```

**What the Lean statement says**

Let M be the infinite lower-triangular integer matrix M(n,k) = C(n, floor((n-k)/2)) for 0 ≤ k ≤ n (0 above the diagonal), and let T = M^(-2) (proved to agree with the inverse-square of every finite leading block). Then the bivariate formal power series Σ_{n≥0} Σ_{k=0}^{n} T(n,k) x^n y^k (x marks the row, y the column) equals (1-x)(1-x+x^2)·(1 - xy + 3x^2 - x^3 y + x^4)^(-1) in Q[[x,y]]. Equality of whole series, so it also says the right side has no coefficients above the diagonal (k > n).

**What the kernel checks against the OEIS data**

a_data (decide +kernel): all 66 listed terms a(0..65) = rows 0..10 of the triangle, read by rows via pos (pos_spec proves pos(n(n+1)/2+k) = (n,k)). The definition of T is not only data-pinned: T_spec proves T = M^(-2) for every truncation, and M is the closed form for A061554 read as a triangle (Barry/Bala formula, equivalent to the entry's Maple program). M is not checked directly against A061554 terms, but the unipotent square root of M^2 is unique, so the 66 T-terms pin M on rows 0..10. I also checked independently (sympy, 16 rows) that the series expansion with x = row variable matches M^(-2), and that the swapped orientation (y = row) does not. So the encoded orientation is the only one consistent with the data.

**Points for the reviewer**

- *Note.* A061554 is primarily a square array read by antidiagonals. The encoding uses its triangle reading, T(n,k) = binomial(n, floor((n-k)/2)), which the A126127 formula ('Pascal's triangle with descending row terms') and Maple program clearly intend. This is correct, but it is a choice a reviewer may want to confirm.
- *Note.* The g.f. is stated over Q with the formal inverse of a series whose constant term is 1 (statement_iff gives the cleared-denominator form). T is an integer triangle cast to Q, which is harmless.
- *Note.* Catalog metadata only, not the statement: the catalog's 'area' is 'Discrete geometry', which does not fit (this is combinatorics / Riordan arrays).

## A127752: A127752 mod 2 is the first Feigenbaum symbolic sequence A035263

Verdict of the pre-review: **faithful**. Result: [oeis-a127752](../../results/oeis-a127752/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A127752.lean`](../../lean/Math0/Statements/OEIS/A127752.lean).

**The conjecture as stated in OEIS**

> %C A127752 a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture). [Paul Barry, Jan 28 2007]
> %C A127752 The conjecture is true at least up to 2048 first terms. (But please note the different indexing, here 0-based.) - _Antti Karttunen_, Sep 29 2018
> (Name: "Row sums of inverse of number triangle A(n,k) = 1/(3n+1) if k <= n <= 2k, 0 otherwise."; offset 0. A035263: "Trajectory of 1 under the morphism 0 -> 11, 1 -> 10", offset 1.)

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, a n % 2 = (A035263 (n + 1) : ℤ)

with
  def A (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (3 * n + 1 : ℚ) else 0
  def next (l : List ℤ) : ℤ := 3 * l.length + 1 - ∑ j ∈ range l.length, if l.length ≤ 2 * j then l.getD j 0 else 0
  def vals : ℕ → List ℤ | 0 => [] | n + 1 => vals n ++ [next (vals n)]
  def a (n : ℕ) : ℤ := (vals (n + 1)).getD n 0      -- a_rec: a n = 3n+1 - Σ_{j<n, n≤2j} a j
  def sigma (x : ℕ) : List ℕ := if x = 0 then [1, 1] else [1, 0]
  def word : ℕ → List ℕ | 0 => [1] | k + 1 => (word k).flatMap sigma
  def A035263 (n : ℕ) : ℕ := (word n).getD (n - 1) 0
Proved helpers: a_spec (a i = Σ_j (Amat N)⁻¹ i j for every N and i < N), word_length, word_prefix, A035263_eq.
```

**What the Lean statement says**

Let A be the infinite lower-triangular rational matrix with A(n,k) = 1/(3n+1) when k ≤ n ≤ 2k and 0 otherwise, and let a(n) (n ≥ 0) be the n-th row sum of its inverse. The proof shows this equals the row sum of the inverse of every finite leading block, and that it is an integer. Let w be the infinite fixed point, starting from 1, of the morphism 0 → 11, 1 → 10, with letters numbered from 1. Then for every n ≥ 0, a(n) mod 2 equals the (n+1)-th letter of w.

**What the kernel checks against the OEIS data**

a_data (decide +kernel): all 106 listed terms a(0..105). A035263_data (decide +kernel): all 105 listed terms of A035263(1..105). Both definitions are pinned: a_spec proves a is the row-sum vector of the inverse of every truncation, and the morphic word is the unique fixed point (word_prefix / A035263_eq). The data also confirm the index shift: a mod 2 = 1,0,1,1,1,0,1,0,... = A035263(1),A035263(2),..., while the unshifted reading fails at n = 1 (a(1) = 4 is even, A035263(1) = 1). I independently checked the parity identity in Python up to n = 3000.

**Points for the reviewer**

- *Note.* Index shift a(n) mod 2 = A035263(n+1): a(n) has offset 0 and A035263 has offset 1. Karttunen's note in the entry asks for exactly this shift, and it is the only alignment consistent with the data.
- *Note.* 'mod 2' is Int.emod, which always returns 0 or 1. a(n) is positive (keyword nonn), so there is no sign issue anyway.
- *Note.* Catalog metadata only: the catalog's 'area' is 'Discrete geometry', which does not fit.

## A127755: The inverse of the triangle 1/n! [k ≤ n ≤ 2k] is an integer triangle

Verdict of the pre-review: **faithful**. Result: [oeis-a127755](../../results/oeis-a127755/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A127755.lean`](../../lean/Math0/Statements/OEIS/A127755.lean).

**The conjecture as stated in OEIS**

> %C A127755 It is conjectured that this is an integer triangle. Row sums are A127756. [Paul Barry, Jan 28 2007]
> (Name: "Inverse of number triangle A(n,k) = 1/n! if k <= n <= 2k, 0 otherwise."; offset 0, keywords sign,tabl.)

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n k : ℕ, k ≤ n → ∃ z : ℤ, T n k = z

with
  def A (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (n.factorial : ℚ) else 0
  T n k : ℚ := forward substitution T(n,k) = n! · ([n = k] - Σ_{j<n} A(n,j) T(j,k)) for k ≤ n, 0 for k > n (via nextRow/rows lists; T_spec)
Proved helpers: inv_Amat ((Amat N)⁻¹ = Tmat N for every N), statement_iff_matrix (statement ↔ ∀ N i j, ∃ z : ℤ, (Amat N)⁻¹ i j = z).
```

**What the Lean statement says**

Let A be the infinite lower-triangular rational matrix with A(n,k) = 1/n! when k ≤ n ≤ 2k and 0 otherwise, and let T be its inverse, which is lower triangular and is proved to be the inverse of every finite leading block. Then every entry T(n,k) with 0 ≤ k ≤ n is an integer. Equivalently, for every N, all entries of the inverse of the N×N leading block of A are integers.

**What the kernel checks against the OEIS data**

a_data (decide +kernel): all 64 listed terms (rows 0..9 plus the first 9 entries of row 10), using the reading by rows given by rowOf. rows_data (decide +kernel): the 13 example rows 0..12. The definition is pinned by proof, not just by data: inv_Amat proves T is Mathlib's inverse of every truncation of A, and A is transcribed literally from the name.

**Points for the reviewer**

- *Note.* Only the first sentence of the comment is a conjecture. 'Row sums are A127756' is a cross-reference and is correctly left out.
- *Note.* The OEIS-sequence function a : ℕ → ℚ is used only for the data check and does not appear in statement.
- *Note.* Catalog metadata only: the catalog's 'area' is 'Discrete geometry', which does not fit.

# Fidelity review packet 06 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A249434, A262957, A265210, A265649, A267486, A270668, A275815, A278212, A281000, A294512.

## A249434: A249151(k) = k exactly when k + 1 is prime (Karttunen's conjecture, A249434/A249151)

Verdict of the pre-review: **faithful**. Result: [oeis-a249434](../../results/oeis-a249434/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A249434.lean`](../../lean/Math0/Statements/OEIS/A249434.lean).

**The conjecture as stated in OEIS**

> %C A249434 It seems that A006093 gives all those k for which A249151(k) = k. If that is true, then this is a disjoint union of A006093 and A249429. (_Antti Karttunen_, Nov 02 2014). Also %Y A249434 Subsequences: A006093 (conjectured), A249429, ...; and in A249151: "A006093 seems to give all such k, that a(k) = k." A249151 (offset 0): "Largest m such that m! divides the product of elements on row n of Pascal's triangle". A006093: a(n) = prime(n) - 1. A249429: n with A249151(n) > n.

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ k : ℕ, IsGreatest {m : ℕ | m ! ∣ rowProd k} k ↔ (k + 1).Prime

where
def rowProd (n : ℕ) : ℕ := ∏ j ∈ range (n + 1), n.choose j
-- theorem statement_iff : statement ↔ ∀ k : ℕ, A249151 k = k ↔ (k + 1).Prime
-- def A249151 (n : ℕ) : ℕ := lastFact (rowProd n) (rowProd n) 0   (A249151_isGreatest: it is the greatest m with m! ∣ rowProd n)
```

**What the Lean statement says**

For every natural number k >= 0, k is the largest m such that m! divides the product C(k,0)·C(k,1)·...·C(k,k) if and only if k+1 is prime. In other words, the fixed points of A249151 are exactly the numbers p-1 with p prime.

**What the kernel checks against the OEIS data**

a_data checks all 81 listed A249434 terms (a(1..81), all terms <= 256) in the kernel, using a proved recurrence for rowProd. A249151_data checks the first 81 terms of A249151, which pins down rowProd and the 'largest m' notion (A249151_isGreatest, A249151_eq_iff). A006093 is encoded as {k | (k+1).Prime}, which is definitional. I also checked numerically that the iff holds for k < 200.

**Points for the reviewer**

- *Note.* 'A006093 gives all those k for which A249151(k) = k' is read as the set equality {k | A249151(k) = k} = A006093 (both inclusions). A purely literal reading could be just {fixed points} ⊆ A006093. The two-sided reading is what the author meant: the follow-up 'disjoint union of A006093 and A249429' (A249434 = {A249151 >= k}, A249429 = {A249151 > k}) and the %Y 'Subsequences: A006093 (conjectured)' both need A006093 ⊆ {fixed points}. The Lean statement is the stronger form, so the proof settles either reading.
- *Note.* k = 0 is included. A249151(0) = 1 ≠ 0 and 1 is not prime, so k = 0 satisfies both sides consistently. 0 belongs to A249429, not A006093, which matches.

## A262957: A262957: Israel's b(n), c(n) are coprime integers and a(n) = b(n)

Verdict of the pre-review: **faithful**. Result: [oeis-a262957](../../results/oeis-a262957/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A262957.lean`](../../lean/Math0/Statements/OEIS/A262957.lean).

**The conjecture as stated in OEIS**

> %C A262957 From _Robert Israel_, Dec 22 2015: (Start)
> a(n) is the numerator of b(n)/c(n) where
> b(1) = 2, b(2) = 3, c(1) = 3, c(2) = 5,
> b(n+1) = (((-1)^n*(n-1)+n*(n+2))*b(n) - (1+(-1)^n*(n+1))*b(n-1))/(n-(-1)^n),
> c(n+1) = (((-1)^n*(n-1)+n*(n+2))*c(n) - (1+(-1)^n*(n+1))*c(n-1))/(n-(-1)^n).
> Conjecture: b(n) and c(n) are coprime for all n, so that a(n) = b(n).
> I have verified this for n <= 10000. (End)
> [Entry: "Numerators of the n-th iteration of the alternating continued fraction formed from the positive integers, starting with (1 - ...)", offset 1, _Mohamed Sabba_, Nov 19 2015; examples 1-1/(2+1)=2/3, 1-1/(2+1/(3-1))=3/5, ... Mirror rev #80 (Mar 04 2025) is identical to current GitHub oeisdata.]

**The frozen Lean statement**

```lean
def cf (n : ℕ) : ℚ :=
  (List.range' 1 (n + 1)).foldr (fun (k : ℕ) (t : ℚ) => (k : ℚ) + (-1) ^ k / t) 1
def a (n : ℕ) : ℕ := (cf n).num.natAbs
def step (m : ℕ) (u v : ℚ) : ℚ :=
  (((-1) ^ m * ((m : ℚ) - 1) + (m : ℚ) * ((m : ℚ) + 2)) * v
      - (1 + (-1) ^ m * ((m : ℚ) + 1)) * u) / ((m : ℚ) - (-1) ^ m)
def israelPair (x₁ x₂ : ℚ) : ℕ → ℚ × ℚ
  | 0 => (x₁, x₂)
  | n + 1 => let p := israelPair x₁ x₂ n; (p.2, step (n + 2) p.1 p.2)
def b (n : ℕ) : ℚ := (israelPair 2 3 (n - 1)).1
def c (n : ℕ) : ℚ := (israelPair 3 5 (n - 1)).1

def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ p q : ℤ, b n = (p : ℚ) ∧ c n = (q : ℚ) ∧ Int.gcd p q = 1 ∧
      ((a n : ℕ) : ℚ) = b n
```

**What the Lean statement says**

Let cf(n) be the rational number 1 - 1/(2 + 1/(3 - 1/(4 + ... (n+1) + (-1)^(n+1)/1))), using the integers 1..n+1, the sign after k being (-1)^k and the innermost tail 1, and let a(n) be |numerator| of cf(n) in lowest terms. Let b, c be the rational sequences with b(1)=2, b(2)=3, c(1)=3, c(2)=5 and, for m >= 2, x(m+1) = ((( -1)^m (m-1) + m(m+2)) x(m) - (1 + (-1)^m (m+1)) x(m-1)) / (m - (-1)^m). Claim: for every n >= 1, b(n) and c(n) are integers, gcd(b(n), c(n)) = 1, and a(n) = b(n).

**What the kernel checks against the OEIS data**

a_data: a(1..22) equal all 22 listed terms (decide +kernel), which pins cf (the continued fraction with integers 1..n+1, alternating signs, inner tail 1) to the entry's examples and PARI program. bc_data: (b(n), c(n)) for n = 1..6 equal (2,3),(3,5),(19,33),(64,111),(538,933),(2833,4913), i.e. the first terms of A262957/A263295, checking the indexing of the recurrence (x(m+1) = step m x(m-1) x(m), applied for m >= 2). b and c are literal transcriptions of the displayed recurrence, so the data check is adequate. I also checked independently (exact rationals) for n < 300 that b, c are integers, coprime, a(n) = b(n), and cf(n) = b(n)/c(n).

**Points for the reviewer**

- *Note.* Integrality of b(n), c(n) is asserted explicitly (the recurrence divides, so the terms are a priori rational). This is implicit in calling them coprime, and it makes the statement stronger, not weaker.
- *Note.* The statement asserts coprimality and the stated consequence a(n) = b(n), but not Israel's premise cf(n) = b(n)/c(n) (equivalently c(n) = A263295(n)). Because b and c are defined literally by the recurrence, the coprimality claim is exactly Israel's conjecture. The premise itself is outside the conjecture sentence. It holds numerically for n < 300.
- *Note.* Range n >= 1 matches the recurrence's indexing. The junk values b 0, c 0 are never used. The divisor m - (-1)^m is nonzero for every m >= 2 where the step is applied, and every intermediate value of cf is >= 1, so Lean's x/0 = 0 never intervenes.

## A265210: Ternary digits of 2^n: column k has least period 2*3^(k-1) and balanced digits for k ≥ 2

Verdict of the pre-review: **faithful**. Result: [oeis-a265210](../../results/oeis-a265210/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A265210.lean`](../../lean/Math0/Statements/OEIS/A265210.lean).

**The conjecture as stated in OEIS**

> %C A265210 Conjecture 1: The sequence in column k is periodic, with period p(k) = 2*3^(k-1) = A008776(k-1), k >= 1, and in which the numbers 0,1,2 appear with equal frequency, for each k>1.
> [Entry: "Irregular triangle read by rows in which row n lists the base 3 digits of 2^n in reverse order, n >= 0.", offset 0, _L. Edson Jeffery_, Dec 04 2015; rev #18, unchanged on GitHub.]

**The frozen Lean statement**

```lean
def row (n : ℕ) : List ℕ := Nat.digits 3 (2 ^ n)
def T (n k : ℕ) : ℕ := (row n).getD (k - 1) 0
def IsColPeriod (k q : ℕ) : Prop :=
  ∀ n : ℕ, k ≤ (row n).length → T (n + q) k = T n k
def p (k : ℕ) : ℕ := 2 * 3 ^ (k - 1)

def statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (IsColPeriod k (p k) ∧ ∀ q : ℕ, 0 < q → q < p k → ¬ IsColPeriod k q) ∧
    (2 ≤ k → ∀ m : ℕ, k ≤ (row m).length → ∀ d e : ℕ, d < 3 → e < 3 →
      ((Finset.Ico m (m + p k)).filter (fun n => T n k = d)).card =
        ((Finset.Ico m (m + p k)).filter (fun n => T n k = e)).card)
```

**What the Lean statement says**

Let T(n,k) be the k-th base-3 digit of 2^n counted from the least significant end (the digit at 3^(k-1)). Column k consists of the rows n for which 2^n has at least k ternary digits. For every k >= 1: (a) shifting by p(k) = 2*3^(k-1) rows preserves column k (T(n+p(k),k) = T(n,k) whenever row n lies in column k), and no smaller positive shift q does, so p(k) is the least period. (b) For k >= 2, every block of p(k) consecutive rows m, ..., m+p(k)-1 (starting at a row m in column k) contains the digits 0, 1 and 2 equally often in column k.

**What the kernel checks against the OEIS data**

a_data checks all 84 listed terms (rows 0..15) from row n = Nat.digits 3 (2^n) (least significant digit first, i.e. 'reverse order'). row_example checks example rows 13, 14 and 15. col1_data, col2_data and col3_data check where columns 1, 2 and 3 start (rows 0, 2, 4) and their first values. sanity_small_columns checks p(2)=6 and p(3)=18 as periods on 40 rows, and balanced digit counts [2,2,2] and [6,6,6] in the first period. The definitions are literal, so these checks pin them down.

**Points for the reviewer**

- *Note.* 'Periodic, with period p(k)' is read as p(k) being the least period: it is a period and no 0 < q < p(k) is one. This is stronger than 'p(k) is a period', so a proof settles both readings.
- *Note.* 'Equal frequency' is read as equal counts of 0, 1 and 2 in every window of p(k) consecutive column entries. Together with the periodicity conjunct, this is equivalent to equal asymptotic frequencies (1/3 each), so it is not a weaker reading.
- *Note.* Column k starts at the first row with at least k digits. Periodicity is asserted only on rows that have an entry in column k, so the getD default 0 is never used. This matches 'the sequence in column k' read as a sequence from its first entry. The periodicity part is asserted for all k >= 1 and the balance part for k >= 2, as in the text.

## A265649: A265649: both of Werner Schulte's closed forms hold

Verdict of the pre-review: **faithful**. Result: [oeis-a265649](../../results/oeis-a265649/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A265649.lean`](../../lean/Math0/Statements/OEIS/A265649.lean).

**The conjecture as stated in OEIS**

> %F A265649 Conjecture: T(n,k) = 2^(n-k)*(n-k)!*binomial(n,k)*(Sum_{j=0..n-k} (-1/4)^j* binomial(2*j+k,j)*binomial(n,j+k)).
> %F A265649 Conjecture: T(n,k) = (-1)^k*Sum_{j=0..n-1} A001497(n-1,j)*A021009(j+1,k).
> [Both in the FORMULA section of the entry by _Werner Schulte_, Dec 11 2015 (no separate attribution on these lines). Name: T(0,0)=1, T(n,k)=0 for k<0 or k>n, T(n,k) = T(n-1,k-1) + (2*n-1+k)*T(n-1,k) for n>0, 0<=k<=n; offset 0. Rev #40 (Mar 11 2024), unchanged on GitHub.]

**The frozen Lean statement**

```lean
def T : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (2 * (n + 1) - 1 + 0) * T n 0
  | n + 1, k + 1 => T n k + (2 * (n + 1) - 1 + (k + 1)) * T n (k + 1)
def A001497 (n m : ℕ) : ℚ :=
  if m ≤ n then ((2 * n - m).factorial : ℚ) / ((m.factorial : ℚ) * ((n - m).factorial : ℚ) * 2 ^ (n - m)) else 0
def A021009 (n m : ℕ) : ℚ :=
  if m ≤ n then (-1) ^ m * (n.factorial : ℚ) * (n.choose m : ℚ) / (m.factorial : ℚ) else 0

def statement : Prop :=
  (∀ n k : ℕ, k ≤ n →
      (T n k : ℚ) = 2 ^ (n - k) * ((n - k).factorial : ℚ) * (n.choose k : ℚ) *
        ∑ j ∈ Finset.range (n - k + 1),
          (-1 / 4 : ℚ) ^ j * ((2 * j + k).choose j : ℚ) * (n.choose (j + k) : ℚ)) ∧
    (∀ n k : ℕ, 1 ≤ n → k ≤ n →
      (T n k : ℚ) = (-1) ^ k * ∑ j ∈ Finset.range n, A001497 (n - 1) j * A021009 (j + 1) k)
```

**What the Lean statement says**

Let T be the triangle with T(0,0)=1, T(0,k)=0 for k>0, T(n,0) = (2n-1)T(n-1,0) and T(n,k) = T(n-1,k-1) + (2n-1+k)T(n-1,k) for n >= 1. Then (1) for all 0 <= k <= n, T(n,k) = 2^(n-k)(n-k)! C(n,k) Σ_{j=0}^{n-k} (-1/4)^j C(2j+k,j) C(n,j+k), as rationals. (2) For all n >= 1 and 0 <= k <= n, T(n,k) = (-1)^k Σ_{j=0}^{n-1} B(n-1,j) L(j+1,k), where B(n,m) = (2n-m)!/(m!(n-m)!2^(n-m)) and L(n,m) = (-1)^m n! C(n,m)/m! for m <= n, both 0 otherwise.

**What the kernel checks against the OEIS data**

a_data and T_data check all 55 listed terms of A265649 (rows 0..9). A001497_data checks all 55 listed terms of A001497. A021009_data checks all 47 listed terms of A021009. The Lean closed forms are verbatim the first %F lines of those entries, which hold for all n. statement₁_check and statement₂_check verify both identities for n <= 12 in the kernel. T is a literal transcription of the defining recurrence (natural subtraction 2(n+1)-1 is never truncated). T_eq_zero_of_lt proves T(n,k)=0 for k>n. The definitions are pinned down.

**Points for the reviewer**

- *Note.* Conjecture 2 is asserted only for n >= 1. This is forced: A001497(n-1,j) has no meaning at n = 0, and the empty sum would give 0 ≠ T(0,0) = 1.
- *Note.* Both identities are asserted only for 0 <= k <= n, the entries of the tabl triangle. For k > n both sides vanish anyway (C(n,k) = 0, resp. A021009(j+1,k) = 0 for j+1 <= n < k), so nothing is lost.
- *Note.* (n-k) in Conjecture 1 is a genuine difference because k <= n. (-1/4)^j and all sums are in ℚ, so there is no natural-number division or truncation.

## A267486: O'Sullivan's Gaussian-polynomial / Chebyshev representation conjecture (A267486), proved

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a267486](../../results/oeis-a267486/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A267486.lean`](../../lean/Math0/Statements/OEIS/A267486.lean).

**The conjecture as stated in OEIS**

> %C A267486 Conjecture: More generally, the Gaussian polynomial [2*n+m+1-(m mod 2),m]_q = Sum_{k=0..g(m;n)} a(m;n,k)*(1+q^2)^k*q^(g(m;n)-k), for m >= 0, n >= 0, where g(m;n) = m*n if m is odd and (2*n+1)*m/2 if m is even, and the tabf array entries a(m;n,k) are the coefficients of the g.f. for the row n polynomials G(m;n,x) = (d^m/dt^m)G(m;n,t,x)/m!|_{t=0}, with G(m;n,t,x) = (1+t)*Product_{k=1..n+(m - m (mod 2))/2}(1 + t^2 + 2*t*T(k,x/2) (Chebyshev's T-polynomials). Hence a(m;n,k) = [x^k]G(m;n,x), for k=0..g(m;n). The present entry is the instance m = 2. (Thanks to _Wolfdieter Lang_ for clarifying the text on the general prescription of a(m;n,k).)
> [Entry by _Stephen O'Sullivan_, Jan 15 2016; rev #23 (May 30 2026), unchanged on GitHub. Name: coefficients of [2n+7,6]_q in the basis (1+q^2)^k q^(g-k), g = 6n+3.]

**The frozen Lean statement**

```lean
noncomputable def gaussBinom : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, m + 1 => gaussBinom N m + X ^ (m + 1) * gaussBinom N (m + 1)
def g (m n : ℕ) : ℕ := if m % 2 = 1 then m * n else (2 * n + 1) * m / 2
noncomputable def chebHalf (k : ℕ) : ℚ[X] := (Chebyshev.T ℚ k).comp (C (1 / 2 : ℚ) * X)
noncomputable def Gt (m n : ℕ) : ℚ[X][X] :=
  (1 + X) * ∏ k ∈ Finset.Icc 1 (n + (m - m % 2) / 2), (1 + X ^ 2 + 2 * X * C (chebHalf k))
noncomputable def G (m n : ℕ) : ℚ[X] :=
  C ((m.factorial : ℚ)⁻¹) * (derivative^[m] (Gt m n)).eval 0

def statement : Prop :=
  ∀ m n : ℕ,
    (G m n).natDegree ≤ g m n ∧
      (gaussBinom (2 * n + m + 1 - m % 2) m).map (Int.castRingHom ℚ) =
        ∑ k ∈ Finset.range (g m n + 1), C ((G m n).coeff k) * (1 + X ^ 2) ^ k * X ^ (g m n - k)
```

**What the Lean statement says**

For all m, n >= 0: let N = n + ⌊m/2⌋ and let G(m;n,x) be (1/m!) times the m-th t-derivative at t = 0 (that is, the t^m coefficient) of (1+t) ∏_{k=1}^{N} (1 + t^2 + 2t T_k(x/2)), where T_k is the Chebyshev polynomial of the first kind. Let g = mn for odd m and (2n+1)m/2 for even m. Then G(m;n,x) has x-degree at most g, and the Gaussian binomial [2n+m+1-(m mod 2), m]_q (defined by the q-Pascal rule) equals Σ_{k=0}^{g} ([x^k]G(m;n,x)) (1+q^2)^k q^(g-k) in ℚ[q].

**What the kernel checks against the OEIS data**

a_data (80 listed terms, rows 0..4) and row_exact (zero remainder, row length 6n+4) check the entry's own sequence. That sequence is computed from the Gaussian polynomial [2n+7,6]_q by triangular elimination, not from G, and `statement` does not use it. The statement's own objects are checked by G_two_zero (G(2;0) = 1 + x), G_six_zero (G(6;0) = -1 - 2x + x^2 + x^3 = row 0 of the data), gaussBinom_four_two, gaussBinom_five_two_mul (q-Pascal against the product formula), g_six and the chebHalf identities. These are literal transcriptions of standard objects, so the checks suffice. I also checked independently with sympy that the identity and degree bound hold for m = 0..7, n = 0..3, and that G(6;n,x) reproduces data rows n = 0, 1, 2.

**Points for the reviewer**

- *Note.* The entry is internally inconsistent: the comment says 'The present entry is the instance m = 2', but the name, data and Maple program are the m = 6 instance ([2n+7,6]_q, product to n+3). The %F line and the Mathematica program use Product_{i=1..n+1}, which matches neither the data nor the general formula at m = 6. The Lean formalizes the general conjecture for all m, n as written, so these slips do not affect the statement. Its m = 6 instance reproduces the data.
- *Note.* The extra conjunct natDegree(G m n) <= g(m;n) encodes 'a(m;n,k) ... for k=0..g(m;n)' (the row has no terms beyond x^g). It is a strengthening of the bare identity, which by itself would say nothing about higher coefficients of G.
- *Note.* There are no degenerate readings: 2n+m+1-(m mod 2) never truncates, (2n+1)m/2 is exact for even m, g-k is a true difference for k <= g, and m = 0 gives the true trivial case [2n+1,0]_q = 1.

## A270668: Mathar's generating function for column 3 of A270668 (domino tilings of (4k+1)x5 boards with central hole)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a270668](../../results/oeis-a270668/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A270668.lean`](../../lean/Math0/Statements/OEIS/A270668.lean).

**The conjecture as stated in OEIS**

> %F A270668 Conjectured g.f. for column 3: ( -1 -4*x +543*x^2 -6238*x^3 +17032*x^4 -6238*x^5 +543*x^6 -4*x^7 -x^8 ) / ( (x-1) *(x^2-7*x+1) *(x^2-23*x+1) *(x^4 -161*x^3 +576*x^2 -161*x +1) ). - _R. J. Mathar_, Mar 23 2016
> [Entry: "Triangle read by rows: The number of domino tilings of the (2n+1) X (2m+1) board with a central free square.", 'Arrangements obtained by rotations and flips are counted as distinct.', offset 0, tabl, _R. J. Mathar_, Mar 21 2016. Rev #23 (Apr 13 2016), unchanged on GitHub.]

**The frozen Lean statement**

```lean
def IsDomino (d : Finset Cell) : Prop :=
  ∃ i j : ℕ, d = {(i, j), (i, j + 1)} ∨ d = {(i, j), (i + 1, j)}
def IsTiling (S : Finset Cell) (D : Finset (Finset Cell)) : Prop :=
  (∀ d ∈ D, IsDomino d ∧ d ⊆ S) ∧ ∀ x ∈ S, ∃! d, d ∈ D ∧ x ∈ d
def board (r c : ℕ) : Finset Cell := range r ×ˢ range c
def region (n m : ℕ) : Finset Cell := (board (2 * n + 1) (2 * m + 1)).erase (n, m)
noncomputable def T (n m : ℕ) : ℕ := {D | IsTiling (region n m) D}.ncard
noncomputable def num : ℚ⟦X⟧ :=
  -1 - 4 * X + 543 * X ^ 2 - 6238 * X ^ 3 + 17032 * X ^ 4 - 6238 * X ^ 5 + 543 * X ^ 6 - 4 * X ^ 7 - X ^ 8
noncomputable def den : ℚ⟦X⟧ :=
  (X - 1) * (X ^ 2 - 7 * X + 1) * (X ^ 2 - 23 * X + 1) * (X ^ 4 - 161 * X ^ 3 + 576 * X ^ 2 - 161 * X + 1)

def statement : Prop :=
  PowerSeries.mk (fun k => (T (2 * k) 2 : ℚ)) = num * den⁻¹
(Cell := ℕ × ℕ; the file also proves statement_iff: statement ↔ mk(T(2k,2)) * den = num.)
```

**What the Lean statement says**

Let c_k be the number of domino tilings of the (4k+1) x 5 rectangle with its central cell removed, counting tilings as sets of dominoes (so rotations and reflections are distinct). For k = 0 this is the 1 x 5 strip without its middle cell, so c_0 = 1. Then, as formal power series over ℚ, Σ_{k>=0} c_k x^k = (-1 - 4x + 543x^2 - 6238x^3 + 17032x^4 - 6238x^5 + 543x^6 - 4x^7 - x^8) / ((x-1)(x^2-7x+1)(x^2-23x+1)(x^4-161x^3+576x^2-161x+1)). The denominator has constant term -1, so the inverse is genuine.

**What the kernel checks against the OEIS data**

a_data checks all 36 listed terms (rows 0..7) through the transfer-matrix Tc, and T_eq_Tc is proved for all n, m. The set-theoretic tiling count T is therefore tied to the data, not just the computable proxy. column_data checks T(2k,2) = 1, 196, 31329, 4941729 for k = 0..3, which are the first four coefficients of the conjectured g.f. I independently recomputed T(2k,2) for k = 0..8 by a profile DP and expanded num/den. All nine coefficients agree (…, 777852100, 122398521025, …), so the Lean reading of 'column 3' is the one the g.f. describes.

**Points for the reviewer**

- *Note.* Reading choice: 'column 3' is taken as m = 2 (third column, 0-based index 2; 5-wide boards). The g.f. is taken as Σ_k T(2k,2) x^k over the even rows only. The odd rows are 0 by colouring, and the statement says nothing about them. This is the only reading matching the g.f.'s expansion (the m = 3 column 75272, ... does not match), and I confirmed agreement through k = 8.
- *Note.* The constant term T(0,2) = 1 (the 1 x 5 strip) lies outside the triangle (m > n) but comes from the same definition. By transposition it equals T(2,0) = 1, which is in the triangle, so it agrees with how a transfer-matrix g.f. for 5-wide boards would be indexed.
- *Note.* Tilings are counted as Finsets of dominoes with exact cover, so tilings related by symmetry are distinct, as the entry requires. ncard is justified by the proved finiteness, so there is no junk 0 from an infinite set.

## A275815: A275815: Jones's conjecture a(n) = 8(n-2)^2 for n >= 6 holds

Verdict of the pre-review: **faithful**. Result: [oeis-a275815](../../results/oeis-a275815/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A275815.lean`](../../lean/Math0/Statements/OEIS/A275815.lean).

**The conjecture as stated in OEIS**

> %F A275815 Conjecture: a(n) = 8(n-2)^2 for n >= 6. - _Alec Jones_, Nov 16 2016
> (Entry name: "Maximum total number of possible moves that any number of queens of the same color can make on an n X n chessboard." Offset 1. Entry unchanged on GitHub oeisdata, #43 Jul 11 2021.)

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 6 ≤ n → a n = 8 * (n - 2) ^ 2

where
def board (n : ℕ) : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n
def isEmptySquare (n : ℕ) (S : Finset (ℕ × ℕ)) (x y : ℤ) : Bool :=
  decide (0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n ∧ (x.toNat, y.toNat) ∉ S)
def rayMoves (n : ℕ) (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) (d : ℤ × ℤ) : ℕ :=
  ((List.range' 1 n).takeWhile fun t =>
    isEmptySquare n S (p.1 + t * d.1) (p.2 + t * d.2)).length
def queenDirs : List (ℤ × ℤ) :=
  [(1, 1), (1, -1), (-1, 1), (-1, -1), (1, 0), (-1, 0), (0, 1), (0, -1)]
def totalMoves (n : ℕ) (S : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p ∈ S, (queenDirs.map (rayMoves n S p)).sum
def a (n : ℕ) : ℕ := (board n).powerset.sup (totalMoves n)
```

**What the Lean statement says**

For every n >= 6: over all sets S of squares of the n x n board (one queen on each square of S), the maximum of the total number of moves is exactly 8(n-2)^2, where a queen's moves are the squares reachable along any of its 8 lines by passing only through empty squares and stopping on an empty square (no capture, no jumping), and the total sums this count over all queens of S.

**What the kernel checks against the OEIS data**

a_data: kernel computes a(1), a(2), a(3) = 0, 4, 17 exactly (first three listed terms). example3: the entry's 3x3 example (A3, A2, B1, C3) gives per-queen counts 3,4,5,5 and total 17. a_ge_data (via witness_spec): explicit placements give exactly the listed values for 4 <= n <= 12, so a(n) >= A275815(n) there (lower bounds only). The exact values a(2)=4 and a(3)=17 pin down the move semantics: blocking by own pieces, no landing on occupied squares, per-queen summation (e.g. allowing moves onto occupied squares would give a(2)=12). Upper bounds are kernel-checked only for n <= 3, but the definition is a literal transcription of the entry's name, so this is not a gap in the definitions.

**Points for the reviewer**

- *Note.* The values for n >= 4 are checked only as lower bounds (the kernel cannot run the 2^(n^2) search). The definition is a direct transcription of the entry's name, and the exact values at n = 2, 3 rule out the plausible alternative move rules, so the definition is still adequately pinned.
- *Note.* a 0 = 0 and natural-number subtraction in (n - 2) are both harmless: the statement requires n >= 6.

## A278212: Kagey's conjecture for A278212: a(n) = floor(A275815(n)/2), via exact bishop and queen maxima from flow (LP-dual) certificates

Verdict of the pre-review: **faithful**. Result: [oeis-a278212](../../results/oeis-a278212/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A278212.lean`](../../lean/Math0/Statements/OEIS/A278212.lean).

**The conjecture as stated in OEIS**

> %C A278212 Conjecture: a(n) = floor(A275815(n)/2). - _Peter Kagey_, Nov 24 2016
> (A278212: "Maximum total number of possible moves that any number of bishops of the same color can make on an n X n chessboard.", offset 1; A275815: same for queens, offset 1. Entry unchanged on GitHub oeisdata, #36 Nov 19 2023.)

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = queenMax n / 2

where (board, isEmptySquare, rayMoves as in A275815)
def bishopDirs : List (ℤ × ℤ) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]
def queenDirs : List (ℤ × ℤ) :=
  [(1, 1), (1, -1), (-1, 1), (-1, -1), (1, 0), (-1, 0), (0, 1), (0, -1)]
def totalMoves (dirs : List (ℤ × ℤ)) (n : ℕ) (S : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p ∈ S, (dirs.map (rayMoves n S p)).sum
def a (n : ℕ) : ℕ := (board n).powerset.sup (totalMoves bishopDirs n)
def queenMax (n : ℕ) : ℕ := (board n).powerset.sup (totalMoves queenDirs n)
```

**What the Lean statement says**

For every n >= 1, the maximum total number of moves of a set of bishops on an n x n board equals the floor of half the maximum total number of moves of a set of queens on the same board. Pieces move only through and onto empty squares along their lines (bishops: 4 diagonals; queens: 8 directions). Both maxima are defined from scratch by exhaustive search over all placements, not by any conjectured formula.

**What the kernel checks against the OEIS data**

a_data: a(1), a(2), a(3) = 0, 2, 8 exactly. queenMax_data: queenMax(1), queenMax(2), queenMax(3) = 0, 4, 17 exactly. bishopWitness_spec / a_ge_data and queenWitness_spec / queenMax_ge_data: explicit placements, including the entry's own n = 5 bishop example, reach the listed values for 4 <= n <= 10, so these are lower bounds only. The exact a(2) = 2 settles the reading of 'same color' as pieces of one side: if the bishops had to stand on squares of one color, a(2) would be 1.

**Points for the reviewer**

- *Note.* 'Same color' could be misread as bishops standing on squares of one color. The kernel-checked a(2) = 2 and the entry's n = 5 example, which uses both square colors, both confirm the file's reading (pieces of one side).
- *Note.* The catalogued proof does not fix queenMax(4), queenMax(5) or queenMax(6) exactly (each is 'X or X+1'), but floor(./2) takes the same value either way. The statement asks only for the floor identity, so the result settles exactly the conjecture.
- *Note.* A275815 is encoded as queenMax, the true sequence defined from its own definition, not Jones's formula 8(n-2)^2. The statement is therefore Kagey's conjecture itself and does not depend on A275815's conjecture.

## A281000: Schulte's conjectures on A281000, T(n,k) = C(2n+1,2k+1)·Cat(n-k): antidiagonal sums and matrix inverse

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a281000](../../results/oeis-a281000/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A281000.lean`](../../lean/Math0/Statements/OEIS/A281000.lean).

**The conjecture as stated in OEIS**

> %F A281000 Conjectures:
> %F A281000   (1) Antidiagonal sums equal A001003(n+1);
> %F A281000   (2) Sum_{k=0..n} (-1)^k*T(n,k)*(2*k+1)*A000108(k)*A103365(k) = A000007(n);
> %F A281000   (3) Matrix inverse equals T(n,k)*A103365(n+1-k).
> (Werner Schulte, Jan 12 2017; T(n,k) = binomial(2*n+1, 2*k+1)*binomial(2*n-2*k, n-k)/(n+1-k), 0 <= k <= n, offset 0. A103365 has offset 1: 1, -1, 2, -7, 39, ... Entries unchanged on GitHub oeisdata.)

**The frozen Lean statement**

```lean
def statement : Prop := conj1 ∧ conj2 ∧ conj3

def conj1 : Prop :=
  ∀ n : ℕ, ∑ k ∈ Finset.range (n / 2 + 1), T (n - k) k = A001003 (n + 1)
def conj2 : Prop :=
  ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
    (T n k : ℤ) * (2 * k + 1) * (catalan k : ℤ) * A103365 (k + 1) = (0 : ℤ) ^ n
def conj3 : Prop :=
  ∀ N : ℕ, (Matrix.of fun i j : Fin N => (T i j : ℚ))⁻¹ =
    Matrix.of fun i j : Fin N => (T i j : ℚ) * (A103365 ((i : ℕ) + 1 - (j : ℕ)) : ℚ)

def T (n k : ℕ) : ℕ :=
  Nat.choose (2 * n + 1) (2 * k + 1) * Nat.choose (2 * n - 2 * k) (n - k) / (n + 1 - k)
def narayana (n k : ℕ) : ℕ := Nat.choose (n - 1) (k - 1) * Nat.choose n (k - 1) / k
def A001003 (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ j ∈ Finset.Icc 1 n, 2 ^ (j - 1) * narayana n j
def invNarayanaCol : ℕ → List ℤ   -- forward substitution, b(n) = [n=1] - Σ_{j<n} N(n,j) b(j)
def A103365 (n : ℕ) : ℤ := (invNarayanaCol n).getD (n - 1) 0
```

**What the Lean statement says**

Let T(n,k) = C(2n+1,2k+1)·C(2n-2k,n-k)/(n+1-k) (zero for k > n), N(n,j) the Narayana numbers, s(n) the little Schroeder numbers (s(0)=1, s(n) = Σ_{j=1..n} 2^{j-1} N(n,j)), and b the first column of the inverse of the Narayana matrix (b(1)=1, b(2)=-1, b(3)=2, ...). Then (1) for all n >= 0, Σ_{k=0..⌊n/2⌋} T(n-k,k) = s(n+1); (2) for all n >= 0, Σ_{k=0..n} T(n,k)(2k+1)Cat(k)·b(k+1) = [n=0]; (3) for every N, the inverse over Q of the N x N leading block of T is the N x N leading block of U(n,k) = T(n,k)·b(n+1-k).

**What the kernel checks against the OEIS data**

a_data: all 55 listed terms of the triangle (rows 0-9). A001003_data: all 26 listed little Schroeder numbers. A103365_data: all 20 listed terms of A103365, signs included. conj1_check (n <= 24), conj2_check (n <= 15) and conj3_check (entries of T·U for n,k <= 14) are sanity checks of the transcription. These checks pin down every auxiliary definition and the index alignment of (1) (1 = s(1), 3 = s(2), 10+1 = s(3)). I independently recomputed that the literal shift with (-1)^k kept gives 1, 6, 60, 910, ... instead of 0^n.

**Points for the reviewer**

- *Minor.* Conjecture (2) is not well defined as written: A103365 has offset 1, so the k = 0 term uses A103365(0). With only the shift A103365(k) -> A103365(k+1) it is false at n = 1 (sum 3 + 3 = 6; I recomputed this). The file instead reads (-1)^k·A103365(k) as A103365(k+1), which equals (-1)^k·|A103365(k+1)|. This is an editorial correction, not the literal text. It does not change the strength of the statement: in this reading (2) is the k = 0 column of T·T^{-1} = I, so it follows from conj3. The other plausible true readings, such as Σ T(n,k)(2k+1)Cat(k)·b(n+1-k) = 0^n (row 0 of U·T), also follow from conj3. The conjunction is therefore equivalent to (1) ∧ (3), which are transcribed faithfully.
- *Note.* A001003 is defined by Cloitre's Narayana-sum formula, not by any of its combinatorial definitions. This is a classical identity (s(n) = Σ 2^{j-1} N(n,j)) and all 26 listed terms are kernel-checked, so the definition is right for all n.
- *Note.* conj3 uses Mathlib's ⁻¹, which returns 0 for singular matrices. Every leading block of T is lower unitriangular (T(n,n) = 1, T(n,k) = 0 for k > n), so the inverse is the honest one. The junk value A103365 0 = 0 and the truncated n+1-k are reached only where T(i,j) = 0.
- *Note.* The statement bundles three separate conjectures into one conjunction. That is fine here, because the result proves the conjunction and therefore each conjecture.

## A294512: Lang's conjecture a(n) = A250400(n+1)/(n+1) for A294512 fails at n = 164

Verdict of the pre-review: **faithful**. Result: [oeis-a294512](../../results/oeis-a294512/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A294512.lean`](../../lean/Math0/Statements/OEIS/A294512.lean).

**The conjecture as stated in OEIS**

> %F A294512 a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture].
> (Entry by _Wolfdieter Lang_, Nov 01 2017. a(n) = denominator(V(3,1;n)), V(3,1;n) = Sum_{k=0..n} 1/((k + 1)*(3*k + 1)); offset 0. A250400: "Numerator of the harmonic mean of the first n octagonal numbers", offset 1, PARI numerator(n / sum(k=1..n, 1/(3k^2-2k))). Lang's companion comment in A250401 says "[assuming that n+1 divides A250400(n+1) to give A294512(n) for n >= 0]". Entry unchanged on GitHub oeisdata, #13 Nov 12 2017.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, (A250400 (n + 1) : ℚ) / ((n : ℚ) + 1) = (a n : ℚ)

def V (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), 1 / (((k : ℚ) + 1) * (3 * (k : ℚ) + 1))
def a (n : ℕ) : ℕ := (V n).den
def octagonal (j : ℕ) : ℕ := j * (3 * j - 2)
def harmonicMean (m : ℕ) : ℚ := (m : ℚ) / ∑ j ∈ Finset.Icc 1 m, 1 / (octagonal j : ℚ)
def A250400 (m : ℕ) : ℕ := (harmonicMean m).num.natAbs
```

**What the Lean statement says**

For every n >= 0, let a(n) be the reduced denominator of Σ_{k=0..n} 1/((k+1)(3k+1)) and A250400(n+1) the reduced numerator of (n+1)/Σ_{j=1..n+1} 1/(j(3j-2)). The statement says the rational number A250400(n+1)/(n+1) equals a(n). (math0 refutes it: it fails at n = 164.)

**What the kernel checks against the OEIS data**

a_data: all 23 listed terms of A294512. A250400_data: all 20 listed terms of A250400. octagonal_data: 0, 1, 8, 21, 40. The definitions are exact transcriptions of the entries' own Mathematica and PARI programs. The counterexample n = 164 lies beyond the listed data, so the refutation rests on these definitions, which match the entries exactly rather than only on the checked terms. I independently recomputed (exact rationals, n < 400) that the only failure in that range is n = 164, where gcd(165, num V(164)) = 11 and A250400(165) = 15·a(164).

**Points for the reviewer**

- *Note.* The conjecture holds exactly when n+1 is coprime to the numerator of V(n), since A250400(n+1) = (n+1)·a(n)/gcd(n+1, num V(n)). At n = 164, 165 does not divide A250400(165) = 15·a(164). The refutation therefore holds whether '/' is read as an exact rational quotient (the file's reading), as natural-number floor division (floor(a/11) ≠ a), or as a claim that n+1 divides A250400(n+1) (Lang's own reading in A250401). It is not an artifact of the division convention.
- *Note.* A250400 takes Int.natAbs of the numerator, which is harmless because the harmonic mean of positive numbers is positive. n = 164 is inside the stated range n >= 0, so the failure is a genuine counterexample, not a degenerate case.

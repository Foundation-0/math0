/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A350900
import Math0.Audit

/-!
# OEIS A350900: Schulte's gcd-ratio double sum is a Dirichlet convolution

We prove all four parts of Werner Schulte's conjecture (Jan 21 2022) in A350900: for every
arithmetic function `f` and `n > 0`,
`a(f; n) = ∑_{i,k=1}^{n} f(gcd(i,n)/gcd(gcd(i,k),n)) = ((f·φ) * A057660)(n)`;
`a(f; ·)` is multiplicative when `f` is; the row sums of the triangle are `a(id; n)`; and the
row sums equal `(A002618 * A057660)(n)`.

Idea. Since `gcd(gcd(i,k),n) = gcd(g,k)` with `g = gcd(i,n)`, and both indices may be taken
modulo `n`, the sum over `k` is `(n/g)` copies of a full period `∑_{k<g} f(g/gcd(g,k))`,
which equals `∑_{e ∣ g} φ(e) f(e)` after grouping `k` by `gcd(g,k)` (each divisor `d` of `g`
occurs `φ(g/d)` times). Grouping `i` by `gcd(i,n)` in the same way gives
`a(f; n) = ∑_{g ∣ n} φ(n/g)(n/g) ∑_{e ∣ g} φ(e) f(e) = (((f·φ) * ζ) * (id·φ))(n)`.
The same grouping shows `A057660 = ζ * (id·φ)`, so associativity of Dirichlet convolution
gives part 1 (over any commutative semiring). Parts 2–4 follow: Dirichlet convolution and
pointwise products preserve multiplicativity, the row sums are `a(id; n)` by swapping the two
sums, and `id·φ = A002618`.
-/

namespace Math0.Frontier.A350900
open Math0.Statements.A350900 ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta

/-- `∑_{k=1}^{n} F k = ∑_{k=0}^{n-1} F (k+1)`. -/
private lemma sum_Icc_eq_sum_range_succ {M : Type*} [AddCommMonoid M] (F : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, F k = ∑ k ∈ range n, F (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- For `F 0 = F n`, summing over `1, …, n` is the same as summing over `0, …, n-1`. -/
private lemma sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) (n : ℕ)
    (h : F 0 = F n) : ∑ k ∈ Icc 1 n, F k = ∑ k ∈ range n, F k := by
  rw [sum_Icc_eq_sum_range_succ]
  cases n with
  | zero => simp
  | succ m => rw [sum_range_succ, sum_range_succ' F, h]

/-- Grouping `0 ≤ i < n` by `gcd(n, i)`: each divisor `d` occurs `φ(n/d)` times. -/
private lemma sum_range_gcd {M : Type*} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (G : ℕ → M) :
    ∑ i ∈ range n, G (Nat.gcd n i) = ∑ d ∈ n.divisors, Nat.totient (n / d) • G d := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => Nat.gcd n i) (t := n.divisors)]
  · refine sum_congr rfl fun d hd => ?_
    rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), ← sum_const]
    refine sum_congr rfl fun i hi => ?_
    rw [(mem_filter.1 hi).2]
  · intro i _
    simp [Nat.mem_divisors, Nat.gcd_dvd_left, hn.ne']

/-- Periodicity of `k ↦ gcd(g, k)`: a sum over `g * m` consecutive values is `m` full periods. -/
private lemma sum_range_mul_gcd {M : Type*} [AddCommMonoid M] (g m : ℕ) (F : ℕ → M) :
    ∑ k ∈ range (g * m), F (Nat.gcd g k) = m • ∑ k ∈ range g, F (Nat.gcd g k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, succ_nsmul]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.gcd_mul_left_add_right]

/-- `phi` evaluates to Euler's totient. -/
private lemma phi_apply (n : ℕ) : phi n = Nat.totient n := rfl

/-- Euler's totient is multiplicative. -/
private lemma phi_mult : phi.IsMultiplicative :=
  ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩

/-- `∑_{k=1}^{m} m / gcd(m,k) = ∑_{d ∣ m} d φ(d)`, i.e. `A057660 = ζ * (id · φ)`. -/
private lemma A057660Fn_eq :
    A057660Fn = (ζ : ArithmeticFunction ℕ) * (ArithmeticFunction.id.pmul phi) := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [zeta_mul_apply]
  show A057660 m = _
  unfold A057660
  rw [sum_Icc_eq_sum_range (fun k => m / Nat.gcd m k) m (by simp),
    sum_range_gcd m hm (fun d => m / d)]
  have := Nat.sum_div_divisors m (fun x => Nat.totient x • x)
  rw [this]
  refine sum_congr rfl fun d _ => ?_
  simp [pmul_apply, phi_apply, mul_comm]

/-- `A057660` is multiplicative, being `ζ * (id · φ)`. -/
private lemma A057660Fn_mult : A057660Fn.IsMultiplicative := by
  rw [A057660Fn_eq]
  exact isMultiplicative_zeta.mul (isMultiplicative_id.pmul phi_mult)

/-- The core computation: `a(f; n) = ∑_{g ∣ n} φ(n/g) (n/g) ∑_{e ∣ g} φ(e) f(e)`. -/
private lemma aF_eq {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) (n : ℕ)
    (hn : 0 < n) :
    aF f n = ∑ g ∈ n.divisors,
      Nat.totient (n / g) • ((n / g) • ∑ e ∈ g.divisors, Nat.totient e • f e) := by
  have h1 : aF f n = ∑ i ∈ range n, ∑ k ∈ range n,
      f (Nat.gcd n i / Nat.gcd (Nat.gcd n i) k) := by
    unfold aF
    rw [sum_Icc_eq_sum_range _ n (by simp [Nat.gcd_comm])]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_Icc_eq_sum_range _ n (by simp)]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.gcd_right_comm, Nat.gcd_comm i n]
  rw [h1, sum_range_gcd n hn
    (fun g => ∑ k ∈ range n, f (g / Nat.gcd g k))]
  refine sum_congr rfl fun g hg => ?_
  have hgn : g ∣ n := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  congr 1
  conv_lhs => rw [← Nat.mul_div_cancel' hgn]
  rw [sum_range_mul_gcd g (n / g) (fun d => f (g / d)), sum_range_gcd g hg0 (fun d => f (g / d))]
  congr 1
  exact Nat.sum_div_divisors g (fun x => Nat.totient x • f x)

/-- Part 1 over an arbitrary commutative semiring. -/
private lemma main {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) (n : ℕ)
    (hn : 0 < n) :
    aF f n = (f.pmul (phi : ArithmeticFunction R) * (A057660Fn : ArithmeticFunction R)) n := by
  rw [aF_eq f n hn, A057660Fn_eq, natCoe_mul, ← mul_assoc, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ((f.pmul (phi : ArithmeticFunction R)) *
      (ζ : ArithmeticFunction R)) a *
        (↑(ArithmeticFunction.id.pmul phi) : ArithmeticFunction R) b)]
  refine sum_congr rfl fun g _ => ?_
  rw [coe_mul_zeta_apply]
  simp only [pmul_apply, natCoe_apply, phi_apply, id_apply, nsmul_eq_mul]
  push_cast
  rw [show ∑ e ∈ g.divisors, f e * (Nat.totient e : R) =
      ∑ e ∈ g.divisors, (Nat.totient e : R) * f e from sum_congr rfl fun _ _ => mul_comm _ _]
  ring

/-- The row sums of the triangle are `a(id; n)`. -/
private lemma rowsum_eq (n : ℕ) :
    ∑ k ∈ Icc 1 n, T n k = aF (ArithmeticFunction.id : ArithmeticFunction ℕ) n := by
  unfold T aF
  rw [Finset.sum_comm]
  rfl

/-- Schulte's conjecture (all four parts) holds. -/
theorem result : statement := by
  refine ⟨fun f n hn => main f n hn, fun f hf => ?_, fun n _ => ?_, fun n hn => ?_⟩
  · have : aFun f =
        f.pmul (phi : ArithmeticFunction ℂ) * (A057660Fn : ArithmeticFunction ℂ) := by
      ext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact main f n hn
    rw [this]
    exact (hf.pmul phi_mult.natCast).mul A057660Fn_mult.natCast
  · rw [rowsum_eq]
    simp only [aF, natCoe_apply, id_apply, Nat.cast_sum]
  · have hA : (ArithmeticFunction.id : ArithmeticFunction ℕ).pmul phi = A002618Fn := by
      ext x
      simp [pmul_apply, phi_apply, A002618Fn, A002618]
    rw [rowsum_eq, main _ n hn, natCoe_nat, natCoe_nat, hA]

end Math0.Frontier.A350900

#math0_settles Math0.Frontier.A350900.result Math0.Statements.A350900.statement

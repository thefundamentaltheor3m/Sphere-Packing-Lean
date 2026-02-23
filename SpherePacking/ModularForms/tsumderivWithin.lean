module
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.ContinuousMap.Compact
public import SpherePacking.ModularForms.exp_lems

/-!
# Termwise differentiation of series

`hasDerivAt_tsum_fun` differentiates a series of functions termwise on an open set, given
locally-uniform summable bounds on the derivatives on compact subsets. Mathlib's
`derivWithin_tsum` (in `Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn`) is the
`derivWithin` version of this; the `HasDerivAt` form proved here is not yet in Mathlib.

`iter_deriv_comp_bound3` provides the summable geometric bounds on compact subsets of the
upper half-plane for `(2π n)^k · ‖exp (2π i n z)‖`, used for the q-expansion derivative
bounds in `FG.lean`.
-/


/-!
# Termwise differentiation of `tsum`

This file contains infrastructure for differentiating a series `∑' n, f n z` termwise using
`derivWithin` and `iteratedDerivWithin`, specialized to exponential series on the upper half-plane.

## Main definitions
* `ℍ'`

## Main statements
* `derivWithin_tsum_fun'`
* `hasDerivAt_tsum_fun`
* `hasDerivWithinAt_tsum_fun`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

/-- The exponential `exp(2π i z)` has norm strictly less than `1` for `z ∈ ℍ`. -/
public theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  simpa using UpperHalfPlane.norm_exp_two_pi_I_lt_one z

/-- A shifted-power variant of `exp_upperHalfPlane_lt_one`. -/
public theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n + 1) * z))‖ < 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  let z' : ℍ :=
    ⟨(n + 1 : ℂ) * z, by
      simpa [Complex.mul_im] using mul_pos hn z.im_pos⟩
  simpa [z', mul_assoc] using UpperHalfPlane.norm_exp_two_pi_I_lt_one z'

/-- Periodicity of the exponential factor under integer translation. -/
public lemma exp_periodo (z : ℍ) (n : ℕ) :
    cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) := by
  simpa [mul_add, add_mul, mul_assoc, add_assoc, add_comm, mul_comm, mul_left_comm]
    using (exp_periodic.nat_mul n (2 * π * Complex.I * n * z))


noncomputable def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)

private lemma norm_exp_two_pi_I_mul_le_norm_pow (K : Set ℂ) [CompactSpace K] (t : K) (n : ℕ) :
    ‖Complex.exp (2 * π * Complex.I * n * (t : ℂ))‖ ≤
      ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ ^ n := by
  have hpow :
      ‖Complex.exp (2 * π * Complex.I * n * (t : ℂ))‖ =
        ‖Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ^ n := by
    simpa [Complex.norm_pow, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : ℂ => ‖z‖) (exp_nat_mul (2 * π * Complex.I * (t : ℂ)) n)
  have hle : ‖Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ≤
      ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ := by
    simpa [BoundedContinuousFunction.mkOfCompact_apply, cts_exp_two_pi_n] using
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
  simpa [hpow] using (pow_le_pow_left₀ (by positivity) hle n)

theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x :=
  hasDerivAt_tsum_fun_core f hs x hx hf hu hf2


theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ {z : ℂ | 0 < z.im}) (hK2 : IsCompact K)
    (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n := by
  have : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    · intro x
      simpa [BoundedContinuousFunction.mkOfCompact_apply, cts_exp_two_pi_n]
        using exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
    linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hr' : ‖(r : ℂ)‖ < 1 := by
    have : r < 1 := by simpa [r] using hr
    simpa [Complex.norm_real, Real.norm_of_nonneg hr2] using this
  have huBase : Summable fun n : ℕ => ‖(((n : ℂ) ^ k * (r : ℂ) ^ n : ℂ))‖ := by
    simpa using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) (k := k) (r := (r : ℂ)) hr')
  have hu : Summable fun n : ℕ => ‖(((2 * ↑π * Complex.I * n : ℂ) ^ k * (r : ℂ) ^ n : ℂ))‖ := by
    have := (huBase.mul_left ‖((2 * ↑π * Complex.I : ℂ) ^ k)‖)
    refine this.congr (fun n => ?_)
    simp [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  refine ⟨fun n : ℕ => ‖(((2 * ↑π * Complex.I * n : ℂ) ^ k * (r : ℂ) ^ n : ℂ))‖, hu, ?_⟩
  intro n t
  simp
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
        ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
          norm_cast
          rw [← Complex.norm_pow];
          congr;
          rw [← exp_nat_mul];
          ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    · simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    rw [norm_norm]
    simpa [cts_exp_two_pi_n] using this
  apply mul_le_mul
  · simp
  · simp at ineqe
    convert ineqe
  · positivity
  positivity

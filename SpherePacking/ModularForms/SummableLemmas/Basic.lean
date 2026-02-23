module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import SpherePacking.ModularForms.BigO
public import SpherePacking.ModularForms.equivs
public import SpherePacking.ModularForms.tsumderivWithin


/-!
# Basic summability lemmas for modular forms

This file collects general summability and `tsum` lemmas used throughout
`SpherePacking.ModularForms`.

## Main statements
* `int_sum_neg`, `summable_neg`
* `tsum_pNat`, `int_tsum_pNat`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open ArithmeticFunction

/-!
### UpperHalfPlane helper lemmas

These are used throughout the modular-forms development to build points in `ℍ` of the form `-n / z`.
-/

/-- The imaginary part of `-(n : ℂ) / z` is positive when `n > 0` and `z ∈ ℍ`. -/
public lemma pos_nat_div_upper (n : ℤ) (hn : 0 < n) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  simpa [neg_div, div_neg, div_eq_mul_inv, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm] using
    (mul_pos (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ)) (UpperHalfPlane.im_inv_neg_coe_pos z))

/-- A `ℕ+` version of `pos_nat_div_upper`. -/
public lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im :=
  by simpa using (UpperHalfPlane.im_pnat_div_pos (n := (n : ℕ)) z)

/-- The scalar `(-1)^n * n!` is nonzero in `ℂ`. -/
public lemma neg_one_pow_mul_factorial_ne_zero (n : ℕ) :
    ((-1 : ℂ) ^ n * (n ! : ℂ)) ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero n (by simp)) (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Reindex a `tsum` over `ℤ` via negation. -/
public theorem int_sum_neg {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]
    (f : ℤ → α) : ∑' d : ℤ, f d = ∑' d, f (-d) :=
  by simp

/-- Rewrite a `tsum` over `ℕ+` as a shifted `tsum` over `ℕ`. -/
public lemma tsum_pnat_eq_tsum_succ3 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1) :=
  by simpa using (tsum_pnat_eq_tsum_succ (f := f))

/-- If `f 0 = 0`, then summability over `ℕ+` is equivalent to summability over `ℕ`. -/
public theorem nat_pos_tsum2 {α : Type _} [TopologicalSpace α] [AddCommMonoid α]
    (f : ℕ → α) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f := by
  simpa [Function.comp] using
    (PNat.coe_injective.summable_iff (f := f) (by
      intro x hx
      rcases Nat.eq_zero_or_pos x with rfl | hx'
      · simpa using hf
      · exact (hx ⟨⟨x, hx'⟩, rfl⟩).elim))

/-- If `f 0 = 0`, then the `tsum` over `ℕ+` agrees with the `tsum` over `ℕ`. -/
public theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
    [T2Space α] [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n := by
  by_cases hf2 : Summable f
  · simpa [hf2.tsum_eq_zero_add, hf] using (tsum_pnat_eq_tsum_succ (f := f))
  have hf2' : ¬ Summable fun x : ℕ+ => f x := by
    simpa [nat_pos_tsum2 f hf] using hf2
  simp [tsum_eq_zero_of_not_summable hf2, tsum_eq_zero_of_not_summable hf2']

/-- Closed form for ∑ n·rⁿ over ℕ+ when ‖r‖ < 1. -/
public lemma tsum_pnat_coe_mul_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
  simpa [tsum_pNat (fun n => n * r ^ n) (by simp)] using tsum_coe_mul_geometric_of_norm_lt_one hr

public theorem nat_pos_tsum2' {α : Type*} [TopologicalSpace α] [AddCommMonoid α] (f : ℕ → α) :
    (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) := by
  simpa using (summable_pnat_iff_summable_succ (f := f))

/-- Decompose a `tsum` over `ℤ` into `0`, positive and negative contributions (as `ℕ+` sums). -/
public theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α] [IsUniformAddGroup α]
  [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) := by
  simpa [add_assoc, add_left_comm, add_comm] using (tsum_int_eq_zero_add_tsum_pnat (f := f) hf2)

/-- A point in `ℍ` is never an integer (viewed in `ℂ`). -/
public theorem upp_half_not_ints (z : ℍ) (n : ℤ) : (z : ℂ) ≠ n := by
  simpa using UpperHalfPlane.ne_intCast z n

/-- For `z ∈ ℍ`, the complex number `(z : ℂ) + n` is nonzero for any integer `n`. -/
public lemma upper_half_plane_ne_int_add (z : ℍ) (n : ℤ) : (z : ℂ) + n ≠ 0 := by
  simpa [add_eq_zero_iff_eq_neg, Int.cast_neg] using (upp_half_not_ints z (-n))

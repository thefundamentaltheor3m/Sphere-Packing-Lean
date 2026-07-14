module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Bound
public import SpherePacking.Tactic.PushReIm

@[expose] public section


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

@[bound]
theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  norm_exp_simp [Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

@[bound]
theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n+1) * z))‖ < 1 := by
  norm_exp_simp [Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

/-- `exp (-2π) < 1/2`, the numeric leaf bound of the `q`-expansion estimates. -/
@[bound]
theorem exp_neg_two_pi_lt_half : Real.exp (-2 * π) < 1 / 2 := by
  have h1 : (1 : ℝ) < 2 * π := by nlinarith [Real.pi_gt_three]
  calc Real.exp (-2 * π) < Real.exp (-1) := Real.exp_strictMono (by linarith)
    _ < 1 / 2 := by
      rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)]
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith

lemma exp_periodo (z : ℍ) (n : ℕ) :
  cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) := by
  rw [mul_add]
  have := exp_periodic.nat_mul n
  rw [Periodic] at this
  have ht := this (2 * π * Complex.I * n * z)
  rw [← ht]
  congr 1
  ring

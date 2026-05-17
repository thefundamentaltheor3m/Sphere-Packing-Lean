module
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exponential bounds on `ℍ`

The basic decay `‖exp(2π i z)‖ < 1` (and a `(n+1)`-multiplied variant) for `z ∈ ℍ`.
-/

@[expose] public section

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  rw [norm_exp]; simp; positivity

theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n + 1) * z))‖ < 1 := by
  rw [norm_exp]; simp; positivity

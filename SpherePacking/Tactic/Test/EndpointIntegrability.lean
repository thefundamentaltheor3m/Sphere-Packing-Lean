/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import SpherePacking.Tactic.EndpointIntegrability.Tactic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.SplitIfs

/-!
# Tests for the `endpoint_integrability` tactic

The `#guard_msgs` tests in this file are sensitive to any other diagnostics emitted at the
guarded commands, so this file must keep a style-conformant header.

The goals left by the tactic are pinned either by the error `unsolved goals` or by `trace_state`,
in which case they are then closed by a proof, or by hypotheses of the form `h : True → P`, so
that `assumption` does not close the goal `P` itself at an end.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology

/- The explanation of the goals left, an `info` message, is turned off for the tests before the
section "The explanation of the goals left", which pin the goals and the traces only. -/
set_option tactic.endpoint_integrability.explain false

/-! ### Goals closed outright -/

example (a b : ℝ) : IntervalIntegrable (fun x : ℝ ↦ x ^ 3 - 2 * x + 1) volume a b := by
  endpoint_integrability

example (a b : ℝ) : IntervalIntegrable (fun x ↦ rexp (-x ^ 2)) volume a b := by
  endpoint_integrability

example (a b : ℝ) : IntervalIntegrable Real.sin volume a b := by
  endpoint_integrability

example (f : ℂ → ℂ) (hf : Continuous f) (a₁ a₂ b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + b * Complex.I)) volume a₁ a₂ := by
  endpoint_integrability

example (a b : ℝ) : IntegrableOn (fun x ↦ Real.sin x + x ^ 2) (Icc a b) := by
  endpoint_integrability

example (a b : ℝ) : IntegrableOn (fun x ↦ Real.sin x + x ^ 2) (Ioo a b) := by
  endpoint_integrability

example (a b : ℝ) : IntegrableOn (fun x ↦ Real.sin x + x ^ 2) (Ico a b) := by
  endpoint_integrability

example (a b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp (x * Complex.I) + x) (Icc a b) := by
  endpoint_integrability

example (a b : ℝ) : IntegrableOn (fun x : ℝ ↦ (Real.cos x, x ^ 2)) (Icc a b) := by
  endpoint_integrability

example (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (a b : ℝ) :
    IntegrableOn (fun x ↦ Real.sin x * x) (Icc a b) μ := by
  endpoint_integrability

example : LocallyIntegrable (fun x : ℝ ↦ Real.sin x + x ^ 2) := by
  endpoint_integrability

example : LocallyIntegrableOn Real.log (Ioi 0) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) : IntegrableOn f (Icc 0 1) := by
  endpoint_integrability

/-- A hypothesis closes the goal at `atTop`, which the comparison does not
prove: the exponent is not bounded above. -/
example (h : IntegrableAtFilter (fun x : ℝ ↦ rexp (x ^ 2)) atTop) :
    IntegrableOn (fun x : ℝ ↦ rexp (x ^ 2)) (Ioi 0) := by
  endpoint_integrability

/-- A discharger given by the user. -/
example (s : ℝ) (h : IntegrableAtFilter (fun x : ℝ ↦ x ^ s) (𝓝[>] 0)) :
    IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioc 0 1) := by
  endpoint_integrability (disch := intro x hx; exact ne_of_gt hx.1)

/-! ### Goals closed by comparison -/

example : IntegrableOn (fun x ↦ rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example (c : ℝ) : IntegrableOn (fun x ↦ rexp (-x)) (Ioi c) := by
  endpoint_integrability

example : IntegrableOn (fun x ↦ rexp (-x)) (Ici 0) := by
  endpoint_integrability

example : Integrable (fun x ↦ rexp (-x)) (volume.restrict (Ioi 0)) := by
  endpoint_integrability

example (s : ℝ) (hs : s < -1) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioi 1) := by
  endpoint_integrability

/-- The hypothesis `0 < t` is not needed: the integrand is measurable. -/
example (s t : ℝ) (_ht : 0 < t) (hs : -1 < s) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioo 0 t) := by
  endpoint_integrability

example (s : ℝ) (hs : -1 < s) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioc 0 1) := by
  endpoint_integrability

example (s : ℝ) (hs : -1 < s) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Icc 0 1) := by
  endpoint_integrability

/-- The coefficient `-2 * π + -π * r` of the exponent of a product of exponentials is negative
because one of its summands is negative and the other one nonpositive. -/
example (r C₀ : ℝ) (hr : 0 ≤ r) :
    IntegrableOn (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) (Ici 1) := by
  endpoint_integrability

/-- The integrand of the Gamma function. -/
example (s : ℝ) (hs : 0 < s) : IntegrableOn (fun x : ℝ ↦ rexp (-x) * x ^ (s - 1)) (Ioi 0) := by
  endpoint_integrability

example (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun x : ℝ ↦ ((rexp (-x) * x ^ (s - 1) : ℝ) : ℂ)) (Ioi 0) := by
  endpoint_integrability

example (s c : ℝ) (hc : 0 < c) : IntegrableOn (fun x : ℝ ↦ x ^ (s - 1) * rexp (-x)) (Ioi c) := by
  endpoint_integrability

example (a : ℂ) (ha : a.re < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp (a * x)) (Ioi c) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ rexp (-x ^ 2)) (Ioi 0) := by
  endpoint_integrability

example (b s : ℝ) (hb : 0 < b) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ ↦ x ^ s * rexp (-b * x ^ 2)) (Ioi 0) := by
  endpoint_integrability

/-- Exponential decay at `𝓝[>] 0` beats any power. -/
example : IntegrableOn (fun t : ℝ ↦ rexp (-(1 / t)) * t ^ (-5 : ℝ)) (Ioc 0 1) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x⁻¹ * rexp (-x)) (Ioi 1) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ rexp (-x) / x ^ 2) (Ici 1) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ (1 + x) * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ rexp (-x) + x * rexp (-2 * x)) (Ici 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ Real.sin x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * Real.cos x) (Ioc 0 1) := by
  endpoint_integrability

/-- The signs of the coefficients are also asked as `0 < π` and `0 < b⁻¹`, for `positivity`. -/
example : IntegrableOn (fun x : ℝ ↦ rexp (-π * x)) (Ioi 0) := by
  endpoint_integrability

example (b : ℝ) (hb : 0 < b) : IntegrableOn (fun x : ℝ ↦ rexp (-x / b)) (Ioi 0) := by
  endpoint_integrability

/-- The sum `1 + sin x` is not exact: its majorant is the sum of the majorants. -/
example : IntegrableOn (fun x : ℝ ↦ (1 + Real.sin x) * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-- A numeral power of a sum which is not exact is expanded. -/
example : IntegrableOn (fun x : ℝ ↦ (1 + Real.sin x + Real.cos x) ^ 2 * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-- A constant which is not proved nonzero is `O(1)`. -/
example (c : ℝ) : IntegrableOn (fun x : ℝ ↦ c * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-- A numeral power of a sum is expanded. -/
example : IntegrableOn (fun x : ℝ ↦ (1 + x) ^ 2 * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-- The integrand is not proved measurable: its strong measurability at `𝓝[>] 0` comes from its
continuity on `Ioc 0 1`. -/
example (g : ℝ → ℝ) (hg : ContinuousOn g (Ioc 0 1)) (hg₀ : ContinuousAt g 0) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * g x) (Ioc 0 1) := by
  endpoint_integrability

/-- Near `0`, the sum `1 + x` has the order of its dominant summand `1`. -/
example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) / (1 + x)) (Ioc 0 1) := by
  endpoint_integrability

/-- The real part of the exponent is a polynomial in `x`. -/
example : IntegrableOn (fun x : ℝ ↦ Complex.exp (-(x : ℂ) ^ 2)) (Ioi 0) := by
  endpoint_integrability

/-- The real part of the exponent is `-x ^ 2 / 2`. -/
example : IntegrableOn (fun x : ℝ ↦ Complex.exp (-(x : ℂ) ^ 2 / 2)) (Ioi 0) := by
  endpoint_integrability

/-- `fun_prop` proves the continuity of `(x : ℂ) ^ 2` within the default `maxHeartbeats`. -/
example (a : ℂ) (ha : a.re < 0) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ 2 * Complex.exp (a * x)) (Ici 2) := by
  endpoint_integrability

/-- The side goal `∀ x ∈ Ioo 0 5, x ^ 3 ≠ 0` of `fun_prop` is proved by `positivity`, the
membership being split into `0 < x` and `x < 5`. -/
example : IntegrableOn (fun x : ℝ ↦ rexp (-(1 / x)) / x ^ 3) (Ioc 0 5) := by
  endpoint_integrability

/-! ### Goals closed by reduction to `atTop` and `𝓝[>] 0` -/

example : Integrable fun x : ℝ ↦ rexp (-x ^ 2) := by
  endpoint_integrability

example (b : ℝ) (hb : 0 < b) : Integrable fun x : ℝ ↦ rexp (-b * x ^ 2) := by
  endpoint_integrability

example (b : ℝ) (hb : 0 < b) : Integrable fun x : ℝ ↦ x * rexp (-b * x ^ 2) := by
  endpoint_integrability

example (b : ℝ) (hb : 0 < b) : Integrable fun x : ℝ ↦ Complex.exp (-b * (x : ℂ) ^ 2) := by
  endpoint_integrability

example (c : ℝ) : IntegrableOn Real.exp (Iic c) := by
  endpoint_integrability

example (a : ℂ) (ha : 0 < a.re) (c : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp (a * x)) (Iic c) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ rexp x * x ^ 2) (Iio 0) := by
  endpoint_integrability

/-- At `𝓝[>] 1` the integrand becomes `(1 + t - 1) ^ (-1 / 2)`, normalised to `t ^ (-1 / 2)`. -/
example : IntegrableOn (fun x : ℝ ↦ (x - 1) ^ (-1 / 2 : ℝ)) (Ioc 1 2) := by
  endpoint_integrability

/-- At `𝓝[<] 2` the integrand becomes `(2 - (2 - t)) ^ (-1 / 2)`, normalised to `t ^ (-1 / 2)`. -/
example : IntegrableOn (fun x : ℝ ↦ (2 - x) ^ (-1 / 2 : ℝ)) (Ico 0 2) := by
  endpoint_integrability

/-- Both ends are singular; at each of them the other factor is continuous. -/
example : IntegrableOn (fun x : ℝ ↦ (x - 1) ^ (-1 / 2 : ℝ) * (3 - x) ^ (-1 / 3 : ℝ)) (Ioo 1 3) := by
  endpoint_integrability

/-- The hypothesis `a < b` is not needed: the integrand is measurable. -/
example (a b s : ℝ) (_hab : a < b) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ ↦ (x - a) ^ s) (Ioc a b) := by
  endpoint_integrability

example (a b s : ℝ) (hs : -1 < s) : IntegrableOn (fun x : ℝ ↦ (-a + x) ^ s) (Ioc a b) := by
  endpoint_integrability

/-- At `𝓝[>] (-1)` the integrand becomes `(-1 + t + 1) ^ s`, normalised to `t ^ s`. -/
example (s : ℝ) (hs : -1 < s) : IntegrableOn (fun x : ℝ ↦ (x + 1) ^ s) (Ioc (-1) 0) := by
  endpoint_integrability

/-- At `𝓝[>] 1` the exponent becomes `-(1 + t) ^ 2`. -/
example : IntegrableOn (fun x : ℝ ↦ rexp (-x ^ 2) * (x - 1) ^ (-1 / 2 : ℝ)) (Ioc 1 2) := by
  endpoint_integrability

/-- At `𝓝[<] 2` the integrand becomes `rexp (1 / -t) / t ^ 3`, which decays exponentially. -/
example : IntegrableOn (fun x : ℝ ↦ rexp (1 / (x - 2)) / (2 - x) ^ 3) (Ico 0 2) := by
  endpoint_integrability

/-- At `𝓝[>] a` the integrand becomes `rexp (1 / -t) / t ^ 2`. -/
example (a b : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (1 / (a - x)) / (x - a) ^ 2) (Ioc a b) := by
  endpoint_integrability

/-- The real part of `-(a * x) ^ 2` is `-(a ^ 2).re * x ^ 2`. -/
example (a : ℂ) (ha : 0 < (a ^ 2).re) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp (-(a * x) ^ 2)) (Ioi 0) := by
  endpoint_integrability

/-! ### Inverses of sums -/

example : Integrable fun x : ℝ ↦ (1 + x ^ 2)⁻¹ := by
  endpoint_integrability

example : Integrable fun x : ℝ ↦ ‖(1 + x ^ 2)⁻¹‖ := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ 1 / (1 + x ^ 2)) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x / (1 + x ^ 2) ^ 2) (Ici 0) := by
  endpoint_integrability

/-- The dominant summand of `1 + x` is `1` at `𝓝[>] 0` and `x` at `atTop`. -/
example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) / (1 + x)) (Ioi 0) := by
  endpoint_integrability

/-- At `𝓝[>] 0` the summand `x ^ 2` is negligible against `1`, since `0 < ↑2 * 1`. -/
example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) / (x ^ 2 + 1)) (Ioc 0 1) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ rexp (-x) / (1 + x ^ 2)) (Ioi 0) := by
  endpoint_integrability

/-- A sum of three terms: `x ^ 2` dominates `x`, then `1`, at `atTop`. -/
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 + x + 1)⁻¹) (Ioi 0) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: it is `Θ(x⁻¹)`, and the condition `-1 < -1` is
false. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (1 + x)⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (1 + x)⁻¹) (Ioi 0) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: the difference `x - 1` is `Θ(x)`, its inverse
`Θ(x⁻¹)`, and the condition `-1 < -1` is false. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (x - 1)⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x - 1)⁻¹) (Ioi 2) := by
  endpoint_integrability

example : Integrable fun x : ℝ ↦ (1 + x ^ 4)⁻¹ := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * (1 + x)⁻¹) (Ioi 0) := by
  endpoint_integrability

/-- At `atTop`, `x ^ 3` is negligible against `rexp x`: the difference `-x` of the exponents
decays. -/
example : IntegrableOn (fun x : ℝ ↦ (rexp x + x ^ 3)⁻¹) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ (1 + rexp (-x))⁻¹ * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-- The inverse `(1 + x ^ 2)⁻¹` is exact, so that it dominates `rexp (-x)` in the outer sum. -/
example : IntegrableOn (fun x : ℝ ↦ ((1 + x ^ 2)⁻¹ + rexp (-x))⁻¹ * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-- At `𝓝[>] 0`, `rexp (-(1 / x))` is negligible against `1`: the exponent decays. -/
example : IntegrableOn (fun x : ℝ ↦ (1 + rexp (-(1 / x)))⁻¹ * x ^ (-1 / 2 : ℝ)) (Ioc 0 1) := by
  endpoint_integrability

/-- At `𝓝[>] 0` neither summand of `1 + rexp x` dominates, but they have the same order and are
positive, so that the sum is exact, and so is its inverse. -/
example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * (1 + rexp x)⁻¹) (Ioc 0 1) := by
  endpoint_integrability

/-- At `atBot`, the integrand becomes `(1 + |-t| ^ 3)⁻¹`. -/
example : Integrable fun x : ℝ ↦ (1 + |x| ^ 3)⁻¹ := by
  endpoint_integrability

/-- The dominant term `x ^ 2 * log x` has a logarithm, which the inverse keeps, with the opposite
power. The default discharger does not prove the side goal `x ^ 2 * log x + 1 ≠ 0` of `fun_prop`,
which is left. -/
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 * Real.log x + 1)⁻¹) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  have := Real.log_pos (by linarith : (1 : ℝ) < x)
  exact (by positivity : 0 < x ^ 2 * Real.log x + 1).ne'

/-- The second term of a difference dominates. The side goal `1 - x ^ 2 ≠ 0` is left. -/
example : IntegrableOn (fun x : ℝ ↦ (1 - x ^ 2)⁻¹) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  exact (by nlinarith : 1 - x ^ 2 < 0).ne

/-- A complex sum. The side goal `↑x + Complex.I ≠ 0` is left. -/
example : IntegrableOn (fun x : ℝ ↦ ((x : ℂ) + Complex.I)⁻¹ ^ 2) (Ioi 0) := by
  endpoint_integrability
  intro x _ h
  simpa using congrArg Complex.im h

/- The ends are proved; the default discharger does not prove the side goal `x ^ 2 - x + 1 ≠ 0`
of `fun_prop`, which is left. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ univ, x ^ 2 - x + 1 ≠ 0
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ (x ^ 2 - x + 1)⁻¹ := by
  endpoint_integrability

/- The end `atTop` is proved; the side goal `x + log x ≠ 0` of `fun_prop` is left. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 1, x + log x ≠ 0
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x + Real.log x)⁻¹ ^ 2) (Ioi 1) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: it is `Θ(1)`, `rexp (-x)` being negligible. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (1 + rexp (-x))⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (1 + rexp (-x))⁻¹) (Ioi 0) := by
  endpoint_integrability

/- The integrand is not integrable at `𝓝[>] 1`, where it becomes `((1 + t) ^ 2 - 1)⁻¹`: no summand
dominates, and there is no rule. The side goal of `fun_prop` is left on the open interval. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioo 1 2, x ^ 2 - 1 ≠ 0

case nhds1
⊢ IntegrableAtFilter (fun x ↦ (x ^ 2 - 1)⁻¹) (𝓝[>] 1) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 - 1)⁻¹) (Ioc 1 2) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`, where it is `Θ(x⁻¹)`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 1, x - log x ≠ 0

case nhds1
⊢ IntegrableAtFilter (fun x ↦ (x - log x)⁻¹) (𝓝[>] 1) volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ (x - log x)⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x - Real.log x)⁻¹) (Ioi 1) := by
  endpoint_integrability

/-- The summands have the same order and are nonnegative: the sum is `Θ(x ^ 2)` at `atTop` and,
after the change of variables, at `atBot`. -/
example : Integrable fun x : ℝ ↦ (x ^ 2 + (1 + x) ^ 2)⁻¹ := by
  endpoint_integrability
  intro x _ h
  nlinarith [sq_nonneg (2 * x + 1)]

example : IntegrableOn (fun x : ℝ ↦ 1 / (x + 2 * x) ^ 2) (Ioi 1) := by
  endpoint_integrability

/-- At `atTop` the summands have the same order; at `𝓝[>] 0`, `√(1 + x)` dominates. -/
example : IntegrableOn (fun x : ℝ ↦ (√x + √(1 + x))⁻¹ ^ 3) (Ioi 0) := by
  endpoint_integrability

/- The integrand is `Θ(x⁻¹)` at `atTop`, and is not integrable there. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (x + 2 * x)⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x + 2 * x)⁻¹) (Ioi 1) := by
  endpoint_integrability

/- At `𝓝[>] 0` the summands have the same order: the integrand is `Θ(x⁻¹)`, and is not integrable
there. -/
/--
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ (x + 2 * x)⁻¹) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x + 2 * x)⁻¹) (Ioc 0 1) := by
  endpoint_integrability

/- At `𝓝[>] 0` the integrand is `Θ(x⁻¹)`, and is not integrable there. -/
/--
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ (√x + √(2 * x))⁻¹ ^ 2) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (√x + √(2 * x))⁻¹ ^ 2) (Ioc 0 1) := by
  endpoint_integrability

/- The integrand is `x⁻¹`, by cancellation: the summand `(1 - x) * x` is not proved nonnegative, and
there is no rule for the inverse of the sum. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (x ^ 2 + (1 - x) * x)⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 + (1 - x) * x)⁻¹) (Ioi 1) := by
  endpoint_integrability

/- The integrand is `x⁻¹`, by cancellation: the summand `x - x ^ 2` is not proved nonnegative. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (x ^ 2 + (x - x ^ 2))⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 + (x - x ^ 2))⁻¹) (Ioi 1) := by
  endpoint_integrability

/-! ### Quotients, inverses and powers of expressions -/

/-- The quotient `1 / x` is exact, so that it dominates `rexp (-x)` in the sum. -/
example : IntegrableOn (fun x : ℝ ↦ (1 / x + rexp (-x))⁻¹ * rexp (-x)) (Ioi 1) := by
  endpoint_integrability

/-- The inverse of a quotient is bounded as the quotient the other way round. -/
example : IntegrableOn (fun x : ℝ ↦ (x / (1 + x ^ 2))⁻¹ * rexp (-x)) (Ioi 1) := by
  endpoint_integrability

/-- At `atBot`, the integrand becomes `((1 + ‖-t‖) ^ 3)⁻¹`. -/
example : Integrable fun t : ℝ ↦ ((1 + ‖t‖) ^ 3)⁻¹ := by
  endpoint_integrability

example (J : ℕ) : Integrable fun t : ℝ ↦ (1 + ‖t‖) ^ J * ((1 + ‖t‖) ^ (J + 2))⁻¹ := by
  endpoint_integrability

example (n : ℕ) (c : ℝ) (hc : 0 < c) : Integrable fun x : ℝ ↦ |x| ^ n * rexp (-(c * x ^ 2)) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ Real.sqrt x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ (Real.sqrt x)⁻¹) (Ioc 0 1) := by
  endpoint_integrability

/-- A real power of an exact sum. The default discharger proves the left side of the side goal
`1 + x ^ 2 ≠ 0 ∨ 0 ≤ -3 / 4` of `fun_prop`. -/
example : IntegrableOn (fun x : ℝ ↦ (1 + x ^ 2) ^ (-3 / 4 : ℝ)) (Ioi 0) := by
  endpoint_integrability

example : Integrable fun x : ℝ ↦ (1 + x ^ 2) ^ (-3 / 4 : ℝ) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℤ)) (Ioi 1) := by
  endpoint_integrability

/-- A complex power of the variable. The default discharger proves the side goal
`↑x ∈ slitPlane` of `fun_prop` as `0 < x`. -/
example (s : ℂ) (hs : 0 < s.re) : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (-s - 1)) (Ioi 1) := by
  endpoint_integrability

/-- The integrand of the complex Gamma function. -/
example (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.exp (-u)) (Ioi 0) := by
  endpoint_integrability

/-- With a discharger given by the user, proving `↑x ∈ slitPlane`. -/
example (s : ℂ) (hs : 0 < s.re) : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (-s - 1)) (Ioi 1) := by
  endpoint_integrability (disch := first
    | (intro x hx
       simp only [Set.mem_Ioi, Set.mem_Ici] at hx
       exact Complex.ofReal_mem_slitPlane.2 (by linarith))
    | (simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith))

/-- At `atTop`, `log x` dominates `1`: the powers of `x` are equal, the power of the logarithm is
larger. The default discharger does not prove the side goal `1 + log x ≠ 0` of `fun_prop`, which
is left. -/
example : IntegrableOn (fun x : ℝ ↦ (1 + Real.log x)⁻¹ * x ^ (-2 : ℝ)) (Ioi 1) := by
  endpoint_integrability
  intro x (hx : 1 < x)
  exact (by linarith [Real.log_pos hx] : 0 < 1 + Real.log x).ne'

/- The integrand is not integrable at `atBot` and `atTop`, where it is `Θ(|x|⁻¹)`. -/
/--
error: unsolved goals
case atBot
⊢ IntegrableAtFilter (fun t ↦ ((1 + ‖t‖) ^ 1)⁻¹) atBot volume

case atTop
⊢ IntegrableAtFilter (fun t ↦ ((1 + ‖t‖) ^ 1)⁻¹) atTop volume
-/
#guard_msgs in
example : Integrable fun t : ℝ ↦ ((1 + ‖t‖) ^ 1)⁻¹ := by
  endpoint_integrability

/- The integrand `x⁻¹` is not integrable at `𝓝[>] 0`: the condition `-1 < 2 * -(1 / 2 * 1)` is
false. -/
/--
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ (√x)⁻¹ ^ 2) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (Real.sqrt x)⁻¹ ^ 2) (Ioc 0 1) := by
  endpoint_integrability

/- The norm of the integrand is `x ^ (-s.re)`: the condition `1 < s.re` is left. -/
/--
error: unsolved goals
case atTop
s : ℂ
hs : 0 < s.re
⊢ 1 < s.re
-/
#guard_msgs in
example (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (-s)) (Ioi 1) := by
  endpoint_integrability

/-! ### Exponents with real degrees -/

example : IntegrableOn (fun x : ℝ ↦ rexp (-Real.sqrt x)) (Ioi 0) := by
  endpoint_integrability

/-- The sign of the degree `p` is asked of the discharger: `0 < p` at `atTop`, `0 ≤ p` at
`𝓝[>] 0`. -/
example (p : ℝ) (hp : 0 < p) : IntegrableOn (fun x : ℝ ↦ rexp (-x ^ p)) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x ^ 5 * rexp (-x ^ (1 / 3 : ℝ))) (Ioi 1) := by
  endpoint_integrability

/-- At `𝓝[>] 0`, the exponent `-(1 / √x)` is the monomial `-1⁻¹ * x ^ (-(1 / 2))`, of singular
degree. -/
example : IntegrableOn (fun x : ℝ ↦ rexp (-(1 / Real.sqrt x)) / x ^ 4) (Ioc 0 1) := by
  endpoint_integrability

/- The sign of `p` is unknown: at `atTop` the exponent is only bounded above, by its negative
coefficient, and the condition `0 < -1` is false. At `𝓝[>] 0` the integrand is bounded by `1`. -/
/--
error: unsolved goals
case atTop
p : ℝ
⊢ IntegrableAtFilter (fun x ↦ rexp (-x ^ p)) atTop volume
-/
#guard_msgs in
example (p : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (-x ^ p)) (Ioi 0) := by
  endpoint_integrability

/-! ### Absorption of monomials by a decaying monomial -/

/-- The monomial `c * x`, of unknown sign, is absorbed by `-b * x ^ 2`, of higher degree. -/
example (b c : ℝ) (hb : 0 < b) : Integrable fun x : ℝ ↦ rexp (c * x) * rexp (-b * x ^ 2) := by
  endpoint_integrability

example (c : ℝ) : Integrable fun x : ℝ ↦ rexp (c * x - x ^ 2) := by
  endpoint_integrability

example (a : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (a * √x - x)) (Ioi 0) := by
  endpoint_integrability

example (c : ℂ) : Integrable fun x : ℝ ↦ Complex.exp (c * x - x ^ 2) := by
  endpoint_integrability

/-- At `𝓝[>] 0`, `a / x` is absorbed by `-1 / x ^ 2`, of more negative degree. -/
example (a : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (a / x - 1 / x ^ 2)) (Ioc 0 1) := by
  endpoint_integrability

example (c : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ 3 * rexp (c * x - x ^ 2)) (Ioi 0) := by
  endpoint_integrability

/-- Two monomials are absorbed by the same one. -/
example (a b : ℝ) : Integrable fun x : ℝ ↦ rexp (a * x + b * x ^ 2 - x ^ 4) := by
  endpoint_integrability

/-- The comparison of the degrees `1` and `p` is asked of the discharger. -/
example (a p : ℝ) (hp : 1 < p) : IntegrableOn (fun x : ℝ ↦ rexp (a * x - x ^ p)) (Ioi 0) := by
  endpoint_integrability

/-- The dominance of `rexp (x ^ 2)` over `rexp (c * x)` in the inverse of their sum. -/
example (c : ℝ) : IntegrableOn (fun x : ℝ ↦ (rexp (x ^ 2) + rexp (c * x))⁻¹) (Ioi 0) := by
  endpoint_integrability

/- The monomial of unknown sign has the higher degree: it is not absorbed, and its sign is left,
`-x` giving the decay. -/
/--
error: unsolved goals
case atTop
c : ℝ
⊢ c ≤ 0
-/
#guard_msgs in
example (c : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (c * x ^ 2 - x)) (Ioi 0) := by
  endpoint_integrability

/- The degrees are equal: the monomials are merged into `(c - 1) * x`, of unknown sign, and there
is no absorption: the monomial is the witness of the decay, and its sign is left. -/
/--
error: unsolved goals
case atTop
c : ℝ
⊢ c < 1
-/
#guard_msgs in
example (c : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (c * x - x)) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case atTop
c : ℝ
⊢ c < 0
-/
#guard_msgs in
example (c : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (c * x)) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case atBot
c : ℝ
⊢ 0 ≤ c

case atTop
c : ℝ
⊢ c ≤ 0
-/
#guard_msgs in
example (c : ℝ) : Integrable fun x : ℝ ↦ rexp (c * x ^ 3 - x ^ 2) := by
  endpoint_integrability

/- At `𝓝[>] 0`, the monomial of unknown sign `a / x ^ 2` is the more singular one: its sign is
left. -/
/--
error: unsolved goals
case nhds0
a : ℝ
⊢ a ≤ 0
-/
#guard_msgs in
example (a : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (a / x ^ 2 - 1 / x)) (Ioc 0 1) := by
  endpoint_integrability

/-! ### Absolute values and norms in exponents -/

/-- Along `atTop` and `𝓝[>] 0`, `|t| = t`; at `atBot`, the exponent becomes `-|-t|`. -/
example : Integrable fun x : ℝ ↦ rexp (-|x|) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ rexp (-|x|)) (Ioi 0) := by
  endpoint_integrability

example : Integrable fun x : ℝ ↦ |x| ^ (1 / 2 : ℝ) * rexp (-|x|) := by
  endpoint_integrability

example (a : ℝ) (ha : 0 < a) : Integrable fun x : ℝ ↦ rexp (-a * |x|) := by
  endpoint_integrability

example : Integrable fun x : ℝ ↦ rexp (-‖x‖ ^ 2) := by
  endpoint_integrability

/-- At `𝓝[>] 0`, the exponent `-|x| ^ (-1 / 2)` is the monomial `-x ^ (-1 / 2)`, of singular
degree. -/
example : IntegrableOn (fun x : ℝ ↦ rexp (-|x| ^ (-1 / 2 : ℝ)) / x ^ 2) (Ioc 0 1) := by
  endpoint_integrability

/- The exponent `|x|` is not bounded above. -/
/--
error: unsolved goals
case atBot
⊢ IntegrableAtFilter (fun x ↦ rexp |x|) atBot volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ rexp |x|) atTop volume
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ rexp |x| := by
  endpoint_integrability

/- The exponent of the product is `|x|`, which is not bounded above. -/
/--
error: unsolved goals
case atBot
⊢ IntegrableAtFilter (fun x ↦ rexp (-|x|) * rexp (2 * |x|)) atBot volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ rexp (-|x|) * rexp (2 * |x|)) atTop volume
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ rexp (-|x|) * rexp (2 * |x|) := by
  endpoint_integrability

/- The integrand tends to `1` at `atBot` and `atTop`. The side goal `|x| ≠ 0` of `fun_prop` is
false, the integrand not being continuous at `0`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ univ, |x| ≠ 0

case atBot
⊢ IntegrableAtFilter (fun x ↦ rexp (-|x|⁻¹)) atBot volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ rexp (-|x|⁻¹)) atTop volume
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ rexp (-|x|⁻¹) := by
  endpoint_integrability

/-! ### Logarithms -/

example (s t : ℝ) (ht : 0 < t) (hs : s < -1) :
    IntegrableOn (fun x : ℝ ↦ x ^ s * Real.log x) (Ioi t) := by
  endpoint_integrability

/-- The hypothesis `0 < t` is not needed: the integrand is measurable. -/
example (s t : ℝ) (_ht : 0 < t) (hs : -1 < s) :
    IntegrableOn (fun x : ℝ ↦ x ^ s * Real.log x) (Ioo 0 t) := by
  endpoint_integrability

example : IntegrableOn (fun u : ℝ ↦ Real.log u * rexp (-u)) (Ioi 0) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ Real.log x ^ 2 / x ^ 2) (Ioi 1) := by
  endpoint_integrability

example : IntegrableOn Real.log (Ioc 0 1) := by
  endpoint_integrability

/-- The default discharger does not prove the side goal `log x ≠ 0` of `fun_prop`, which is left
on the open interval; both ends are proved. -/
example : IntegrableOn (fun x : ℝ ↦ (Real.log x)⁻¹) (Ioc 0 (1 / 2)) := by
  endpoint_integrability
  intro x ⟨hx₀, hx₁⟩
  exact (Real.log_neg hx₀ (by linarith)).ne

/- The goal at `atTop` is proved, `(log x)⁻¹` being `Θ(|log x|⁻¹)`; the default discharger does not
prove the side goal `log x ≠ 0` of `fun_prop` from `2 < x`, which is left. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, log x ≠ 0
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (Real.log x)⁻¹ * rexp (-x)) (Ioi 2) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: the condition `0 + -1 < -1` is false. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ log x / x) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ Real.log x / x) (Ioi 1) := by
  endpoint_integrability

/-! ### Real powers of the logarithm -/

/-- A Bertrand integral at `atTop`: `t⁻¹ * |log t| ^ (-2)`, with `a = -1` and `k < -1`. -/
example : IntegrableOn (fun x : ℝ ↦ 1 / (x * Real.log x ^ 2)) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  have := Real.log_pos (by linarith : (1 : ℝ) < x)
  positivity

example : IntegrableOn (fun x : ℝ ↦ (Real.log x)⁻¹ ^ 2 * x⁻¹) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  exact (Real.log_pos (by linarith)).ne'

/-- A Bertrand integral at `𝓝[>] 0`. -/
example : IntegrableOn (fun x : ℝ ↦ (x * Real.log x ^ 2)⁻¹) (Ioo 0 (1 / 2)) := by
  endpoint_integrability
  intro x ⟨hx₀, hx₁⟩
  exact mul_ne_zero hx₀.ne' (pow_ne_zero _ (Real.log_neg hx₀ (by linarith)).ne)

/-- The sum `log x + log x ^ 2` is `Θ(|log x| ^ 2)`, and so is exact, as is its inverse. -/
example : IntegrableOn (fun x : ℝ ↦ (Real.log x + Real.log x ^ 2)⁻¹ * x⁻¹) (Ioi 3) := by
  endpoint_integrability
  intro x (hx : 3 < x)
  have := Real.log_pos (by linarith : (1 : ℝ) < x)
  positivity

example : IntegrableOn (fun x : ℝ ↦ x⁻¹ * |Real.log x| ^ (-3 / 2 : ℝ)) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  exact .inl (abs_pos.2 (Real.log_pos (by linarith)).ne').ne'

/-- The condition `-s < -1` is proved by the discharger. -/
example (s : ℝ) (hs : 1 < s) : IntegrableOn (fun x : ℝ ↦ x⁻¹ * |Real.log x| ^ (-s)) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  exact .inl (abs_pos.2 (Real.log_pos (by linarith)).ne').ne'

example : IntegrableOn (fun x : ℝ ↦ (Real.log x)⁻¹ * x ^ (-2 : ℝ)) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  exact (Real.log_pos (by linarith)).ne'

example : IntegrableOn (fun x : ℝ ↦ Real.log x ^ 3 / (x ^ 2 * Real.log x)) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  have := Real.log_pos (by linarith : (1 : ℝ) < x)
  positivity

/-- A real power of the logarithm: `√(log x)` is `Θ(|log x| ^ (1 / 2))`. -/
example : IntegrableOn (fun x : ℝ ↦ √(Real.log x) * x ^ (-2 : ℝ)) (Ioi 2) := by
  endpoint_integrability

/-- A power of the logarithm with a variable exponent: the condition `1 < n` is proved by the
discharger. -/
example (n : ℕ) (hn : 2 ≤ n) : IntegrableOn (fun x : ℝ ↦ x⁻¹ * (Real.log x ^ n)⁻¹) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  exact pow_ne_zero _ (Real.log_pos (by linarith)).ne'

/- A power of the logarithm with a variable exponent: the condition `1 < n` is left. -/
/--
error: unsolved goals
case continuity
n : ℕ
⊢ ∀ x ∈ Ioi 2, log x ^ n ≠ 0

case atTop
n : ℕ
⊢ 1 < n
-/
#guard_msgs in
example (n : ℕ) : IntegrableOn (fun x : ℝ ↦ x⁻¹ * (Real.log x ^ n)⁻¹) (Ioi 2) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: `a = -1` and the condition `-1 < -1` on the power
of the logarithm is false. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, x * log x ≠ 0

case atTop
⊢ IntegrableAtFilter (fun x ↦ (x * log x)⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x * Real.log x)⁻¹) (Ioi 2) := by
  endpoint_integrability

/- The integrand is not integrable at `𝓝[>] 0`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioo 0 (1 / 2), x * log x ≠ 0

case nhds0
⊢ IntegrableAtFilter (fun x ↦ (x * log x)⁻¹) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x * Real.log x)⁻¹) (Ioo 0 (1 / 2)) := by
  endpoint_integrability

/- The integrand is not integrable at `𝓝[>] 0`, where it is `Θ(t⁻¹ * |log t|⁻¹)`: `a = -1` and the
condition `-1 < -1` on the power of the logarithm is false. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioo 0 (1 / 2), x * |log x| ≠ 0

case nhds0
⊢ IntegrableAtFilter (fun x ↦ (x * |log x|)⁻¹) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x * |Real.log x|)⁻¹) (Ioo 0 (1 / 2)) := by
  endpoint_integrability

/-- The inverse of the absolute value `|log x|`, which is exact. -/
example : IntegrableOn (fun x : ℝ ↦ (x * |Real.log x| ^ 2)⁻¹) (Ioi 2) := by
  endpoint_integrability
  intro x (hx : 2 < x)
  have := Real.log_pos (by linarith : (1 : ℝ) < x)
  positivity

/-! ### Inverses of exact functions -/

/-- The inverse of a negation, which is exact. -/
example : Integrable fun x : ℝ ↦ (-(1 + x ^ 2))⁻¹ := by
  endpoint_integrability
  intro x _
  exact (neg_neg_of_pos (by positivity)).ne

/-- The inverse of a norm, which is exact: `‖x + I‖⁻¹ ^ 2` is `Θ(x ^ (-2))` at both ends. -/
example : Integrable fun x : ℝ ↦ ‖(x : ℂ) + Complex.I‖⁻¹ ^ 2 := by
  endpoint_integrability
  intro x _
  refine norm_ne_zero_iff.mpr fun h ↦ ?_
  simpa using congrArg Complex.im h

/- `‖x + I‖⁻¹` is `Θ(x⁻¹)`, not integrable at either end. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ univ, ‖↑x + Complex.I‖ ≠ 0

case atBot
⊢ IntegrableAtFilter (fun x ↦ ‖↑x + Complex.I‖⁻¹) atBot volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ ‖↑x + Complex.I‖⁻¹) atTop volume
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ ‖(x : ℂ) + Complex.I‖⁻¹ := by
  endpoint_integrability

/- `(-(1 + x))⁻¹` is `Θ(x⁻¹)` at `atTop`, not integrable. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (-(1 + x))⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (-(1 + x))⁻¹) (Ioi 0) := by
  endpoint_integrability

/-! ### Exponentials of exponents which are not polynomials -/

/-- `exp (sin x)` is not an atom of the engine, its exponent not being a polynomial: it is
bounded at `𝓝[>] 0` by its continuity at `0`, with its inverse and the absolute value of its
inverse. -/
example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * rexp (Real.sin x)) (Ioc 0 1) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * (rexp (Real.sin x))⁻¹) (Ioc 0 1) := by
  endpoint_integrability

example : IntegrableOn (fun x : ℝ ↦ x ^ (-1 / 2 : ℝ) * |rexp (Real.sin x)|⁻¹) (Ioc 0 1) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: the condition `-1 / 2 < -1` is false. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, |log x| ≠ 0 ∨ 0 ≤ -1 / 2

case atTop
⊢ IntegrableAtFilter (fun x ↦ x⁻¹ * |log x| ^ (-1 / 2)) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ x⁻¹ * |Real.log x| ^ (-1 / 2 : ℝ)) (Ioi 2) := by
  endpoint_integrability

/- Without a hypothesis on `s`, the condition `1 < s` is left. -/
/--
error: unsolved goals
case continuity
s : ℝ
⊢ ∀ x ∈ Ioi 2, |log x| ≠ 0 ∨ 0 ≤ -s

case atTop
s : ℝ
⊢ 1 < s
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x⁻¹ * |Real.log x| ^ (-s)) (Ioi 2) := by
  endpoint_integrability

/- The integrand is not integrable at `atTop`: the power of the logarithm is positive. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ log x ^ 2 / x) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ Real.log x ^ 2 / x) (Ioi 2) := by
  endpoint_integrability

/- The integrand is `(log x)⁻¹ ^ 2`, not integrable at `atTop`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, x * log x ^ 2 ≠ 0

case atTop
⊢ IntegrableAtFilter (fun x ↦ (x * log x ^ 2)⁻¹ * x) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x * Real.log x ^ 2)⁻¹ * x) (Ioi 2) := by
  endpoint_integrability

/-! ### Asymptotic facts from the context -/

example (g : ℝ → ℝ) (hg : g =O[atTop] fun x ↦ x ^ (-2 : ℝ)) (hc : Continuous g) :
    IntegrableOn g (Ici 1) := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : g =O[atTop] fun x ↦ x ^ (-2 : ℝ)) (hc : Continuous g) :
    IntegrableOn (fun x ↦ g x * Real.log x) (Ici 1) := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : g =O[𝓝[>] 0] fun x ↦ x ^ (-1 / 2 : ℝ))
    (hc : ContinuousOn g (Ioc 0 1)) : IntegrableOn g (Ioc 0 1) := by
  endpoint_integrability

/-- No rule bounds `g x ^ (3 / 2)`: the rules for the real power and for the inverse do not apply,
and the hypothesis on the whole integrand is used. -/
example (g : ℝ → ℝ) (hc : ContinuousOn (fun x ↦ (g x ^ (3 / 2 : ℝ))⁻¹) (Ici 1))
    (hg : (fun x ↦ (g x ^ (3 / 2 : ℝ))⁻¹) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn (fun x ↦ (g x ^ (3 / 2 : ℝ))⁻¹) (Ici 1) := by
  endpoint_integrability

/-- No rule bounds `f x`: the rule for the product declines, and the hypothesis on the whole
integrand is used. -/
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (h : (fun x ↦ f x * g x) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn (fun x ↦ f x * g x) (Ici 1) := by
  endpoint_integrability

/-- The first hypothesis does not give a bound, since `g` is not bounded: the second one is
used. -/
example (f g : ℝ → ℝ) (_h₁ : f =O[atTop] g) (h₂ : f =O[atTop] fun x ↦ x ^ (-2 : ℝ))
    (hc : Continuous f) : IntegrableOn f (Ici 1) := by
  endpoint_integrability

/- The hypotheses are not used to bound `g`: the engine does not loop. -/
/--
error: unsolved goals
case atTop
f g : ℝ → ℝ
h₁ : f =O[atTop] g
h₂ : g =O[atTop] f
hc : Continuous f
⊢ IntegrableAtFilter f atTop volume
-/
#guard_msgs in
example (f g : ℝ → ℝ) (h₁ : f =O[atTop] g) (h₂ : g =O[atTop] f) (hc : Continuous f) :
    IntegrableOn f (Ici 1) := by
  endpoint_integrability

/-- The end `𝓝[>] 1` is reduced to `𝓝[>] 0` by the change of variables `x = 1 + t`, along which
the hypothesis is transported: `(fun t ↦ g (1 + t)) =O[𝓝[>] 0] fun t ↦ t ^ (-1 / 2)`. -/
example (g : ℝ → ℝ) (hg : g =O[𝓝[>] 1] fun x ↦ (x - 1) ^ (-1 / 2 : ℝ))
    (hc : ContinuousOn g (Ioc 1 2)) : IntegrableOn g (Ioc 1 2) := by
  endpoint_integrability

/-- Each end uses the hypothesis at that end, the one at `atBot` after the change of variables
`x = -t`. -/
example (f : ℝ → ℝ) (hf : Continuous f) (hO : f =O[atTop] fun _ ↦ (1 : ℝ))
    (hO' : f =O[atBot] fun _ ↦ (1 : ℝ)) : Integrable fun x : ℝ ↦ f x * rexp (-x ^ 2) := by
  endpoint_integrability

/-- A hypothesis at `cocompact ℝ` is stated at `atBot` and at `atTop` by the user. -/
example (f : ℝ → ℝ) (hf : Continuous f) (hO : f =O[cocompact ℝ] fun x ↦ (1 + x ^ 2)⁻¹) :
    Integrable f := by
  have hO₁ := hO.mono atBot_le_cocompact
  have hO₂ := hO.mono atTop_le_cocompact
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Continuous f) (hO : f =O[atBot] fun x ↦ rexp x) :
    IntegrableOn (fun x ↦ f x * x ^ 2) (Iic 0) := by
  endpoint_integrability

/- A hypothesis at `atTop` says nothing at `atBot`. -/
/--
error: unsolved goals
case atBot
f : ℝ → ℝ
hf : Continuous f
hO : f =O[atTop] fun x ↦ 1
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x ^ 2)) atBot volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Continuous f) (hO : f =O[atTop] fun _ ↦ (1 : ℝ)) :
    Integrable fun x : ℝ ↦ f x * rexp (-x ^ 2) := by
  endpoint_integrability

/- The hypothesis is transported to `atTop`, but `t ↦ (-t)⁻¹` is not integrable there. -/
/--
error: unsolved goals
case atBot
f : ℝ → ℝ
hf : Continuous f
hO : f =O[atBot] fun x ↦ x⁻¹
⊢ IntegrableAtFilter f atBot volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Continuous f) (hO : f =O[atBot] fun x ↦ x⁻¹) :
    IntegrableOn f (Iic (-1)) := by
  endpoint_integrability

/--
error: unsolved goals
case nhds0
f : ℝ → ℝ
hf : ContinuousOn f (Ioc 0 1)
hO : f =O[𝓝[>] 0] fun x ↦ x⁻¹
⊢ IntegrableAtFilter f (𝓝[>] 0) volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : ContinuousOn f (Ioc 0 1)) (hO : f =O[𝓝[>] 0] fun x ↦ x⁻¹) :
    IntegrableOn f (Ioc 0 1) := by
  endpoint_integrability

/- A function for which the engine has no rule is bounded at an end by a hypothesis. -/
example (f : ℝ → ℝ) (hf : Continuous f) (h : (fun x ↦ f x) =O[atTop] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- A subexpression which is not bounded, but of a known order, is given its order as a
hypothesis. -/
example : IntegrableOn (fun x : ℝ ↦ Real.log (1 + x) / x ^ 3) (Ioi 1) := by
  have h : (fun x : ℝ ↦ Real.log (1 + x)) =O[atTop] fun x ↦ x := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg hx, one_mul]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x by linarith)]
  endpoint_integrability

/-! ### Pointwise bounds near an end

A pointwise bound on a set which belongs to the filter of an end, such as `Ici 2` for `atTop` or
`Ioc 0 (1 / 2)` for `𝓝[>] 0`, is an asymptotic bound at that end: `∀ x ∈ t, ‖g x‖ ≤ b x` gives
`g =O[l] b`. The rest of the interval is left to the continuity. This reading is the last resort
at an end, after the comparison with the stated hypotheses and the integrable factors. -/

example (f : ℝ → ℂ) (hC : Continuous f) (h : ∀ x ∈ Ici 2, ‖f x‖ ≤ rexp (-x)) :
    IntegrableOn f (Ici 0) := by
  endpoint_integrability

/- The bounded function is a factor of the integrand. -/
example (f : ℝ → ℝ) (hC : Continuous f) (h : ∀ x ∈ Ici 1, ‖f x‖ ≤ rexp (-x)) :
    IntegrableOn (fun x ↦ f x * x ^ 2) (Ioi 0) := by
  endpoint_integrability

/- Near a finite end. -/
example (f : ℝ → ℝ) (hC : ContinuousOn f (Ioc 0 1)) (h : ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖f x‖ ≤ 1) :
    IntegrableOn (fun x ↦ f x / √x) (Ioc 0 1) := by
  endpoint_integrability

/- At `atBot`, after the change of variables, and with an absolute value. -/
example (f : ℝ → ℝ) (hC : Continuous f) (h : ∀ x ∈ Iic (-1), |f x| ≤ rexp x) :
    IntegrableOn f (Iic 0) := by
  endpoint_integrability

/- One bound for each end. -/
example (f : ℝ → ℝ) (hC : Continuous f) (h : ∀ x ∈ Ici 1, ‖f x‖ ≤ rexp (-x))
    (h' : ∀ x ∈ Iic (-1), ‖f x‖ ≤ rexp x) : Integrable f := by
  endpoint_integrability

/- Near a finite end other than `0`, after its change of variables, and near an upper end, with a
bound on a closed interval. -/
example (f : ℝ → ℝ) (hC : ContinuousOn f (Ioc 1 2)) (h : ∀ x ∈ Ioc (1 : ℝ) (3 / 2), ‖f x‖ ≤ 1) :
    IntegrableOn (fun x ↦ f x / √(x - 1)) (Ioc 1 2) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hC : ContinuousOn f (Ico 0 1)) (h : ∀ x ∈ Icc (1 / 2 : ℝ) 1, ‖f x‖ ≤ 1) :
    IntegrableOn (fun x ↦ f x / √(1 - x)) (Ico 0 1) := by
  endpoint_integrability

/- Of two bounds of the same function, the one on a set of the filter of the end is preferred to
the one which holds everywhere. -/
example (f : ℝ → ℝ) (hc : Continuous f) (_hb : ∀ x, ‖f x‖ ≤ 1)
    (h : ∀ x ∈ Ici 2, ‖f x‖ ≤ rexp (-x)) : IntegrableOn f (Ici 0) := by
  endpoint_integrability

/- A pointwise bound is read at an end only when the comparison and the integrable factors do not
prove it: here `f` is an integrable factor, which leaves `s ≤ 0`, where the bound `f = O(1)`
would leave `s < -1`. -/
/--
error: unsolved goals
case atTop
f : ℝ → ℝ
hc : Continuous f
hf : Integrable f volume
hb : ∀ x ∈ Ici 2, ‖f x‖ ≤ 1
s : ℝ
⊢ s ≤ 0
-/
#guard_msgs in
example (f : ℝ → ℝ) (hc : Continuous f) (hf : Integrable f) (hb : ∀ x ∈ Ici 2, ‖f x‖ ≤ 1)
    (s : ℝ) : IntegrableOn (fun x ↦ f x * x ^ s) (Ioi 1) := by
  endpoint_integrability

/- A bound on a set which does not belong to the filter of the end is not used there, and the
explanation says so. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no rule bounds `f t` as a function of `t`
  • the bound `∀ x ∈ Icc 0 1, ‖f x‖ ≤ 1` is not used at this end: `Icc 0 1 ∈ atTop` is not
    proved

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
f : ℝ → ℝ
hC : Continuous f
h : ∀ x ∈ Icc 0 1, ‖f x‖ ≤ 1
⊢ IntegrableAtFilter f atTop volume
-/
#guard_msgs in
set_option tactic.endpoint_integrability.explain true in
example (f : ℝ → ℝ) (hC : Continuous f) (h : ∀ x ∈ Icc 0 1, ‖f x‖ ≤ 1) :
    IntegrableOn f (Ici 0) := by
  endpoint_integrability

/-! ### Hypotheses about a compound function

A hypothesis about a compound function, such as `Continuous fun x ↦ f x * g x`, is used wherever a
hypothesis about an opaque function would be: for the continuity on the interval and at an end,
for the measurability, and after the change of variables of an end. `fun_prop` alone looks for
the continuity of `f` and of `g`. -/

/- The continuity of the product gives the middle and the measurability; `f` is an integrable
factor, and `g` is bounded. -/
example (f g : ℝ → ℝ) (hc : Continuous fun x ↦ f x * g x) (hf : Integrable f)
    (hg : ∀ x, ‖g x‖ ≤ 1) : IntegrableOn (fun x ↦ f x * g x) (Ioi 1) := by
  endpoint_integrability

/- With an asymptotic bound of the product. -/
example (f g : ℝ → ℝ) (hc : Continuous fun x ↦ f x * g x)
    (h : (fun x ↦ f x * g x) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn (fun x ↦ f x * g x) (Ioi 1) := by
  endpoint_integrability

/- The product is a subterm, continuous at the end `0`. -/
example (f g : ℝ → ℝ) (hc : Continuous fun x ↦ f x * g x) :
    IntegrableOn (fun x ↦ f x * g x / √x) (Ioc 0 1) := by
  endpoint_integrability

/- After the change of variables `x = 1 + t`, the engine asks for the continuity at `0` of
`fun t ↦ f (1 + t) * g (1 + t)`, an instance of the product. -/
example (f g : ℝ → ℝ) (hc : Continuous fun x ↦ f x * g x) :
    IntegrableOn (fun x ↦ f x * g x / √(x - 1)) (Ioc 1 2) := by
  endpoint_integrability

/- The product is the cofactor of the integrable factor `f`. -/
example (f g h : ℝ → ℝ) (hf : Integrable f) (hc : Continuous fun x ↦ g x * h x)
    (hb : (fun x ↦ g x * h x) =O[atTop] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (fun x ↦ g x * h x * f x) (Ioi 1) := by
  endpoint_integrability

/- A side goal of the continuity is left as for an opaque function: here the product is used at
`x ^ 2`, and the denominator leaves its condition. -/
/--
error: unsolved goals
case continuity
f g : ℝ → ℝ
hc : Continuous fun x ↦ f x * g x
hb : (fun x ↦ f (x ^ 2) * g (x ^ 2)) =O[atTop] fun x ↦ 1
⊢ ∀ x ∈ Ioi 2, (x ^ 2 - 1) ^ 2 ≠ 0
-/
#guard_msgs in
example (f g : ℝ → ℝ) (hc : Continuous fun x ↦ f x * g x)
    (hb : (fun x ↦ f (x ^ 2) * g (x ^ 2)) =O[atTop] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (fun x ↦ f (x ^ 2) * g (x ^ 2) / (x ^ 2 - 1) ^ 2) (Ioi 2) := by
  endpoint_integrability

/- The continuity of the product on the interval only. -/
example (f g : ℝ → ℝ) (hc : ContinuousOn (fun x ↦ f x * g x) (Ioi 1))
    (h : (fun x ↦ f x * g x) =O[atTop] fun x ↦ x ^ (-2 : ℝ))
    (h' : (fun x ↦ f x * g x) =O[𝓝[>] 1] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (fun x ↦ f x * g x) (Ioi 1) := by
  endpoint_integrability

/-! ### Side goals of the continuity -/

/- The side goal `∀ v ∈ Ioi a, v ^ 3 ≠ 0`, which `positivity` does not prove from `0 < a` and
`a < v`, is left with the case tag `continuity`, for the user. -/
example (a : ℝ) (ha : 0 < a) : IntegrableOn (fun v : ℝ ↦ (v ^ 3)⁻¹) (Ioi a) := by
  endpoint_integrability
  case continuity =>
    intro v hv
    have : 0 < v := ha.trans hv
    positivity

example (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-3 / 2 : ℝ) * rexp (-x)) (Ioi a) := by
  endpoint_integrability

/--
error: unsolved goals
case continuity
a b : ℝ
ha : 1 < a
⊢ ∀ x ∈ Ioo a b, x * (x + 1) ≠ 0

case nhdsb
a b : ℝ
ha : 1 < a
⊢ IntegrableAtFilter (fun x ↦ (x * (x + 1))⁻¹) (𝓝[<] b) volume
-/
#guard_msgs in
example (a b : ℝ) (ha : 1 < a) : IntegrableOn (fun x : ℝ ↦ (x * (x + 1))⁻¹) (Ioo a b) := by
  endpoint_integrability

/- The side goal `x ^ 2 - 1 ≠ 0` of `fun_prop`, which the default discharger does not prove, is
left with the case tag `continuity`; the end `atTop` is proved. -/
/--
trace: case continuity
⊢ ∀ x ∈ Ioi 2, x ^ 2 - 1 ≠ 0
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 - 1)⁻¹) (Ioi 2) := by
  endpoint_integrability
  trace_state
  intro x (hx : 2 < x)
  exact (by nlinarith : 0 < x ^ 2 - 1).ne'

/- The side goal is left on the open interval `Ioi 3`, and the end `3` is proved by comparison, from
the continuity at `0` of the integrand `((3 + t) ^ 2 - 1)⁻¹`, whose side goal
`(3 + 0) ^ 2 - 1 ≠ 0` the default discharger proves. -/
/--
trace: case continuity
⊢ ∀ x ∈ Ioi 3, x ^ 2 - 1 ≠ 0
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 - 1)⁻¹) (Ici 3) := by
  endpoint_integrability
  trace_state
  intro x (hx : 3 < x)
  exact (by nlinarith : 0 < x ^ 2 - 1).ne'

example : IntegrableOn (fun x : ℝ ↦ rexp (-x) / (x + Real.log x)) (Ioi 1) := by
  endpoint_integrability
  intro x (hx : 1 < x)
  exact (by linarith [Real.log_pos hx] : 0 < x + Real.log x).ne'

/- The same side goal comes from the inverse and from the quotient: it is left once. The
integrand is not integrable at `atTop`, where it is `Θ(x⁻¹)`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, x ^ 2 - 1 ≠ 0

case atTop
⊢ IntegrableAtFilter (fun x ↦ (x ^ 2 - 1)⁻¹ + x / (x ^ 2 - 1)) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 - 1)⁻¹ + x / (x ^ 2 - 1)) (Ioi 2) := by
  endpoint_integrability

/- Distinct side goals are left in the order of the integrand. The end `2` is not proved: the
continuity at `2` needs `2 - log 2 ≠ 0`, which the default discharger does not prove. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, x ^ 2 - 1 ≠ 0

case continuity
⊢ ∀ x ∈ Ioi 2, x - log x ≠ 0

case nhds2
⊢ IntegrableAtFilter (fun x ↦ rexp (-x) * ((x ^ 2 - 1)⁻¹ + (x - log x)⁻¹)) (𝓝[>] 2) volume
-/
#guard_msgs in
example :
    IntegrableOn (fun x : ℝ ↦ rexp (-x) * ((x ^ 2 - 1)⁻¹ + (x - Real.log x)⁻¹)) (Ioi 2) := by
  endpoint_integrability

/- The goal `IntervalIntegrable` is reduced to `IntegrableOn f (Ioc 2 3)`, the continuity on
`uIcc 2 3` not being proved: the side goal is left on `Ioo 2 3`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioo 2 3, x ^ 2 - 1 ≠ 0
-/
#guard_msgs in
example : IntervalIntegrable (fun x : ℝ ↦ (x ^ 2 - 1)⁻¹) volume 2 3 := by
  endpoint_integrability

/- The integrand is not integrable at `𝓝[>] 2`, and the side goal `x ^ 2 - 4 ≠ 0` holds on
`Ioi 2` but the comparison fails at `2`: both are left. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioi 2, x ^ 2 - 4 ≠ 0

case nhds2
⊢ IntegrableAtFilter (fun x ↦ (x ^ 2 - 4)⁻¹) (𝓝[>] 2) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x ^ 2 - 4)⁻¹) (Ioi 2) := by
  endpoint_integrability

/- The side goals are sufficient conditions, not necessary ones. The statement is true, but the
side goal `|x - 1| ≠ 0 ∨ 0 ≤ -1 / 2` of `ContinuousOn.rpow_const` is false at `1`: the integrand
has an integrable singularity inside the interval. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioo 0 2, |x - 1| ≠ 0 ∨ 0 ≤ -1 / 2
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ |x - 1| ^ (-1 / 2 : ℝ)) (Ioo 0 2) := by
  endpoint_integrability

/- Only side goals which are pointwise conditions on the interval are left: here `fun_prop` fails
on the continuity of `g`, and the local integrability is left. -/
/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
⊢ LocallyIntegrableOn (fun x ↦ g x / (x - 1)) (Ioi 2) volume

case nhds2
g : ℝ → ℝ
⊢ IntegrableAtFilter (fun x ↦ g x / (x - 1)) (𝓝[>] 2) volume

case atTop
g : ℝ → ℝ
⊢ IntegrableAtFilter (fun x ↦ g x / (x - 1)) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) : IntegrableOn (fun x : ℝ ↦ g x / (x - 1)) (Ioi 2) := by
  endpoint_integrability

/- The discharger is run without error recovery: the failure of `positivity` in the nested `by`
does not admit the side goal `∀ x ∈ Icc 0 1, x ≠ 0 ∨ 0 ≤ s` with `sorry`, as it would with
`fun_prop (disch := intro x hx; exact Or.inl (by positivity))`. The side goal is left on the
open interval, where it holds, and the end `1` is not proved, the discharger proving no
continuity. -/
/--
error: unsolved goals
case continuity
s : ℝ
⊢ ∀ x ∈ Ioo 0 1, x ≠ 0 ∨ 0 ≤ s

case nhds0
s : ℝ
⊢ -1 < s

case nhds1
s : ℝ
⊢ IntegrableAtFilter (fun x ↦ x ^ s) (𝓝[<] 1) volume
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Icc 0 1) := by
  endpoint_integrability (disch := intro x hx; exact Or.inl (by positivity))

/-! ### Domination of bounded atoms -/

/- The pieces of `f` leave goals: `f` is not continuous, and the comparison does not bound it.
The integrand is dominated by `1 * ‖rexp (-x)‖`, integrable on `Ioi 0`. -/
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Continuous f) (hb : ∀ x, |f x| ≤ 1) :
    Integrable fun x ↦ f x * rexp (-x ^ 2) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    Integrable fun x ↦ f x * rexp (-x ^ 2) := by
  endpoint_integrability

/- A bounded function, such as `Int.fract`, is given its bound by a hypothesis. -/
example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) :
    IntegrableOn (fun x ↦ Int.fract x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example (f : ℝ → ℂ) (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 3) :
    Integrable fun x : ℝ ↦ f x * ((1 + x ^ 2)⁻¹ : ℝ) := by
  endpoint_integrability

/- The majorant `3 * ‖(1 + ↑x ^ 2)⁻¹‖` leaves the side goal of the continuity which
`(1 + (x : ℂ) ^ 2)⁻¹` alone leaves. -/
/--
error: unsolved goals
case continuity
f : ℝ → ℂ
hf : Measurable f
hb : ∀ (x : ℝ), ‖f x‖ ≤ 3
⊢ ∀ x ∈ univ, 1 + ↑x ^ 2 ≠ 0
-/
#guard_msgs in
example (f : ℝ → ℂ) (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 3) :
    Integrable fun x : ℝ ↦ f x * (1 + (x : ℂ) ^ 2)⁻¹ := by
  endpoint_integrability

/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ univ, 1 + ↑x ^ 2 ≠ 0
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ (1 + (x : ℂ) ^ 2)⁻¹ := by
  endpoint_integrability

/- A bound by a function. -/
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ rexp (-x)) :
    IntegrableOn (fun x ↦ f x * x ^ 2) (Ioi 0) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ rexp (-x)) :
    IntegrableOn f (Ioi 0) := by
  endpoint_integrability

/- A bound on the interval of the goal. -/
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x ∈ Ioi (0 : ℝ), |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- An unrestricted bound at an argument other than the variable. -/
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    Integrable fun x ↦ f (2 * x + 1) * rexp (-x ^ 2) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) (hbf : ∀ x, |f x| ≤ 1)
    (hbg : ∀ x, |g x| ≤ 1) : Integrable fun x ↦ (f x + g x * x) * rexp (-x ^ 2) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntervalIntegrable (fun x ↦ f x * x ^ (-1 / 2 : ℝ)) volume 0 1 := by
  endpoint_integrability

example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) :
    Integrable (fun x ↦ Int.fract x * rexp (-x)) (volume.restrict (Ioi 0)) := by
  endpoint_integrability

/- The pieces of the integrand leave only the condition `s < 2`, from the hypothesis `ho`: the
majorant `1 * ‖x ^ s‖` is not tried, as it would leave the stronger condition `s < -1`. -/
/--
error: unsolved goals
case atTop
f : ℝ → ℝ
hf : Continuous f
hb : ∀ (x : ℝ), |f x| ≤ 1
ho : f =O[atTop] fun x ↦ x ^ (-3)
s : ℝ
⊢ s < 2
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Continuous f) (hb : ∀ x, |f x| ≤ 1)
    (ho : f =O[atTop] fun x ↦ x ^ (-3 : ℝ)) (s : ℝ) :
    IntegrableOn (fun x ↦ f x * x ^ s) (Ioi 1) := by
  endpoint_integrability

/- The condition on the power left by the majorant `1 * ‖x ^ (-s)‖`, as for `x ^ (-s)` alone. -/
/--
error: unsolved goals
case atTop
f : ℝ → ℝ
hf : Measurable f
s : ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ 1 < s
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (s : ℝ) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * x ^ (-s)) (Ioi 1) := by
  endpoint_integrability

/- The trace class reports the majorant. -/
/--
trace: [Tactic.endpoint_integrability] ❌️ case locallyIntegrableOn: not proved
  [Tactic.endpoint_integrability] the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
[Tactic.endpoint_integrability] ✅️ case nhds0: proved
  [Tactic.endpoint_integrability] `Int.fract t * rexp (-t)` is in `O(rexp (-t))`
    [Tactic.endpoint_integrability] `Int.fract t` is in `O(1)`
    [Tactic.endpoint_integrability] `rexp (-t)` has the order of `rexp (-t)`
  [Tactic.endpoint_integrability] ✅️ which is integrable at `𝓝[>] 0`
[Tactic.endpoint_integrability] ✅️ case atTop: proved
  [Tactic.endpoint_integrability] `Int.fract t * rexp (-t)` is in `O(rexp (-t))`
    [Tactic.endpoint_integrability] `Int.fract t` is in `O(1)`
    [Tactic.endpoint_integrability] `rexp (-t)` has the order of `rexp (-t)`
  [Tactic.endpoint_integrability] ✅️ which is integrable at `atTop`
[Tactic.endpoint_integrability] ✅️ with each bounded term replaced by its bound: the majorant is integrable, and so is the integrand
  [Tactic.endpoint_integrability] the majorant is `fun x ↦ 1 * ‖rexp (-x)‖`
  [Tactic.endpoint_integrability] ✅️ in the middle: the majorant is continuous on `Ici 0`
  [Tactic.endpoint_integrability] ✅️ case atTop: proved
    [Tactic.endpoint_integrability] `1 * ‖rexp (-t)‖` has the order of `rexp (-t)`
      [Tactic.endpoint_integrability] `‖rexp (-t)‖` has the order of `rexp (-t)`
        [Tactic.endpoint_integrability] `rexp (-t)` has the order of `rexp (-t)`
    [Tactic.endpoint_integrability] ✅️ which is integrable at `atTop`
-/
#guard_msgs (trace) in
set_option trace.Tactic.endpoint_integrability true in
example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) :
    IntegrableOn (fun x ↦ Int.fract x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- The goals of the pieces of the integrand are left when the domination fails. The majorant
`1 * ‖x⁻¹‖` is not integrable at `atTop`. -/
/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ f x * x⁻¹) (Ioi 1) volume

case atTop
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ f x * x⁻¹) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * x⁻¹) (Ioi 1) := by
  endpoint_integrability

/- A bound on `Ioi 5` is an asymptotic bound at `atTop`, which is proved; it says nothing of the
middle, nor of the end `0`, where no rule bounds `f`. -/
/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hf : Measurable f
hb : ∀ x ∈ Ioi 5, |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) volume

case nhds0
f : ℝ → ℝ
hf : Measurable f
hb : ∀ x ∈ Ioi 5, |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x)) (𝓝[>] 0) volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x ∈ Ioi (5 : ℝ), |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- The majorant `rexp x * ‖rexp (-x)‖` is not integrable at `atTop`. -/
/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ rexp x
⊢ LocallyIntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) volume

case atTop
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ rexp x
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x)) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ rexp x) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- A bounded atom under an inverse is not dominated. -/
/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ (f x)⁻¹ * rexp (-x)) (Ioi 0) volume

case nhds0
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ (f x)⁻¹ * rexp (-x)) (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ (f x)⁻¹ * rexp (-x)) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ (f x)⁻¹ * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ (1 + f x)⁻¹ * rexp (-x)) (Ioi 0) volume

case nhds0
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ (1 + f x)⁻¹ * rexp (-x)) (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ (1 + f x)⁻¹ * rexp (-x)) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ (1 + f x)⁻¹ * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- The trace class reports a bounded atom which is not dominated. -/
/--
trace: [Tactic.endpoint_integrability] ❌️ case locallyIntegrableOn: not proved
  [Tactic.endpoint_integrability] the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
[Tactic.endpoint_integrability] ❌️ case nhds0: not proved
  [Tactic.endpoint_integrability] no rule bounds `rexp (f t)` as a function of `t`
[Tactic.endpoint_integrability] ❌️ case atTop: not proved
  [Tactic.endpoint_integrability] no rule bounds `rexp (f t)` as a function of `t`
[Tactic.endpoint_integrability] ❌️ with each bounded term replaced by its bound: not proved
  [Tactic.endpoint_integrability] a bounded term occurs in `rexp (f x)`, under a function through which it is not
      replaced by its bound: only products, sums, differences, negations, natural powers and
      numerators of quotients are
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ rexp (f x) * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- The trace class reports which obligation of the domination fails. -/
/--
trace: [Tactic.endpoint_integrability] ❌️ case locallyIntegrableOn: not proved
  [Tactic.endpoint_integrability] the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
[Tactic.endpoint_integrability] ❌️ case nhds0: not proved
  [Tactic.endpoint_integrability] no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
      continuous on `Ioi 0`
[Tactic.endpoint_integrability] ❌️ case atTop: not proved
  [Tactic.endpoint_integrability] no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
      continuous on `Ioi 0`
[Tactic.endpoint_integrability] ❌️ with each bounded term replaced by its bound: not proved
  [Tactic.endpoint_integrability] the majorant is `fun x ↦ 1 * ‖rexp (-x)‖`
  [Tactic.endpoint_integrability] the integrand is not proved measurable
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example (f : ℝ → ℝ) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/--
trace: [Tactic.endpoint_integrability] ❌️ case locallyIntegrableOn: not proved
  [Tactic.endpoint_integrability] the integrand is not proved continuous on `Ioi 1`, by a hypothesis or `fun_prop`
[Tactic.endpoint_integrability] ✅️ case nhds1: proved
  [Tactic.endpoint_integrability] with `x = 1 + t`, the integrand is `fun t ↦ Int.fract (1 + t) / (1 + t)`, at `𝓝[>] 0`
  [Tactic.endpoint_integrability] `Int.fract (1 + t) / (1 + t)` is in `O(1)`
    [Tactic.endpoint_integrability] `Int.fract (1 + t) * (1 + t)⁻¹` is in `O(1)`
      [Tactic.endpoint_integrability] `Int.fract (1 + t)` is in `O(1)`
      [Tactic.endpoint_integrability] `(1 + t)⁻¹` has the order of `1`
        [Tactic.endpoint_integrability] `1 + t` has the order of `1`
  [Tactic.endpoint_integrability] ✅️ which is integrable at `𝓝[>] 0`
[Tactic.endpoint_integrability] ❌️ case atTop: not proved
  [Tactic.endpoint_integrability] `Int.fract t / t` is in `O(t ^ (-1))`
    [Tactic.endpoint_integrability] `Int.fract t * t⁻¹` is in `O(t ^ (-1))`
      [Tactic.endpoint_integrability] `Int.fract t` is in `O(1)`
      [Tactic.endpoint_integrability] `t⁻¹` has the order of `t ^ (-1)`
  [Tactic.endpoint_integrability] the tactic only bounds the integrand `fun x ↦ Int.fract x / x` from above,
      up to a constant factor, by `fun t ↦ t ^ (-1)`, which is not proved integrable:
      ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`
[Tactic.endpoint_integrability] ❌️ with each bounded term replaced by its bound: not proved
  [Tactic.endpoint_integrability] the majorant is `fun x ↦ 1 * ‖x⁻¹‖`
  [Tactic.endpoint_integrability] ✅️ in the middle: the majorant is continuous on `Ici 1`
  [Tactic.endpoint_integrability] ❌️ case atTop: not proved
    [Tactic.endpoint_integrability] `1 * ‖t⁻¹‖` has the order of `t ^ (-1)`
      [Tactic.endpoint_integrability] `‖t⁻¹‖` has the order of `t ^ (-1)`
        [Tactic.endpoint_integrability] `t⁻¹` has the order of `t ^ (-1)`
    [Tactic.endpoint_integrability] the majorant `fun x ↦ 1 * ‖x⁻¹‖` has the order of `fun t ↦ t ^ (-1)`,
        which is not proved integrable:
        ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`
  [Tactic.endpoint_integrability] the majorant is not proved integrable
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) : IntegrableOn (fun x : ℝ ↦ Int.fract x / x) (Ioi 1) := by
  endpoint_integrability

/- Without the measurability of `f`, the statement is false. -/
/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) volume

case nhds0
f : ℝ → ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x)) (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x)) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ Int.fract x / x) (Ioi 1) volume

case atTop
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ IntegrableAtFilter (fun x ↦ Int.fract x / x) atTop volume
-/
#guard_msgs in
example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) : IntegrableOn (fun x : ℝ ↦ Int.fract x / x) (Ioi 1) := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ (Int.fract x)⁻¹ * rexp (-x)) (Ioi 0) volume

case nhds0
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ IntegrableAtFilter (fun x ↦ (Int.fract x)⁻¹ * rexp (-x)) (𝓝[>] 0) volume

case atTop
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ IntegrableAtFilter (fun x ↦ (Int.fract x)⁻¹ * rexp (-x)) atTop volume
-/
#guard_msgs in
example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) :
    IntegrableOn (fun x : ℝ ↦ (Int.fract x)⁻¹ * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-! ### Integrable factors -/

/- The factor `g x` is integrable, and its cofactor `sin x` is continuous on `ℝ` and bounded at
each end. -/
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ sin x * g x := by
  endpoint_integrability

example (g : ℝ → ℂ) (hg : Integrable g) : Integrable fun x : ℝ ↦ (sin x : ℂ) * g x := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ g x * sin x := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ -(sin x * (cos x * g x)) := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : Integrable g) :
    Integrable fun x : ℝ ↦ (sin x : ℂ) * ((g x : ℝ) : ℂ) := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ x / (1 + x ^ 2) * g x := by
  endpoint_integrability

example (g : ℝ → ℂ) (hg : Integrable g) :
    Integrable fun x : ℝ ↦ ((x / (1 + x ^ 2) : ℝ) : ℂ) * g x := by
  endpoint_integrability

/- The cofactor is the product of the other factors, `‖x‖ * ‖(1 + x ^ 2)⁻¹‖`: `x` alone is not
bounded, the product is. -/
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ x * g x * (1 + x ^ 2)⁻¹ := by
  endpoint_integrability

example (T : ℝ) (g : ℝ → ℂ) (hg : Integrable g) :
    Integrable fun x : ℝ ↦ Complex.exp (Complex.I * T * x) * g x * sin x := by
  endpoint_integrability

/- The cofactor `‖rexp x‖ * ‖rexp (-2 * x)‖` decays at `atTop`. -/
example (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun x ↦ rexp x * g x * rexp (-2 * x)) (Ioi 0) := by
  endpoint_integrability

/- A hypothesis on the interval of the goal, up to the closedness of its finite ends. -/
example (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun x ↦ sin x * g x) (Ioi 0) := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun x ↦ sin x * g x) (Ici 0) := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : Integrable g (volume.restrict (Icc 0 1))) :
    IntegrableOn (fun x ↦ sin x * g x) (Ioo 0 1) := by
  endpoint_integrability

/- An interval integrability hypothesis is given by the user as the integrability on `Ioc 0 1`. -/
example (g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun x ↦ sin x * g x) volume 0 1 := by
  have := hg.1
  endpoint_integrability

/- The integrability of a Schwartz function is given by the user. -/
example (b : SchwartzMap ℝ ℂ) :
    Integrable fun x : ℝ ↦ Complex.exp (2 * π * x * Complex.I) * b x := by
  have hb : Integrable b := b.integrable
  endpoint_integrability

/- The factor is found under the norm. -/
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ x / (1 + x ^ 2) * ‖g x‖ := by
  endpoint_integrability

example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ |x * g x / (1 + x ^ 2)| := by
  endpoint_integrability

/- Scalar multiplication of a vector-valued integrable function. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ℝ) (g : ℝ → E)
    (hg : Integrable g) :
    Integrable fun v : ℝ ↦ Complex.exp (-((T * v : ℝ) : ℂ) * Complex.I) • g v := by
  endpoint_integrability

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (g : ℝ → E)
    (hg : Integrable g) : Integrable fun x : ℝ ↦ c • (sin x • g x) := by
  endpoint_integrability

/- Composition with the domination: `φ x` is replaced by `C`, the measurability of the
integrand follows from `Measurable φ` and from the measurability of `g` given by `hg`, and the
majorant `C * ‖g x‖` is integrable through its integrable factor. -/
example (φ g : ℝ → ℝ) (C : ℝ) (hb : ∀ x, ‖φ x‖ ≤ C) (hφ : Measurable φ) (hg : Integrable g) :
    Integrable fun x ↦ φ x * g x := by
  endpoint_integrability

/- Each end uses the comparison which works: on `Ioi 0` the end `atTop` is proved by the
hypothesis `hO` and the end `0` by continuity; on `ℝ` the cofactor `x` of the integrable factor is
not bounded at `atBot`, where `hO` says nothing, and that end is left. -/
example (g : ℝ → ℝ) (_hg : Integrable g) (hO : g =O[atTop] fun x ↦ x ^ (-3 : ℝ))
    (hc : Continuous g) : IntegrableOn (fun x ↦ x * g x) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case atBot
g : ℝ → ℝ
hg : Integrable g volume
hO : g =O[atTop] fun x ↦ x ^ (-3)
hc : Continuous g
⊢ IntegrableAtFilter (fun x ↦ x * g x) atBot volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) (hO : g =O[atTop] fun x ↦ x ^ (-3 : ℝ))
    (hc : Continuous g) : Integrable fun x ↦ x * g x := by
  endpoint_integrability

/- The boundedness of `x ^ (-s)` at `atTop` leaves the condition `0 ≤ s`. -/
/--
error: unsolved goals
case atTop
g : ℝ → ℝ
hg : Integrable g volume
s : ℝ
⊢ 0 ≤ s
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) (s : ℝ) :
    IntegrableOn (fun x ↦ x ^ (-s) * g x) (Ioi 1) := by
  endpoint_integrability

/- The comparison is tried first, and a comparison which leaves a condition on a parameter
is a success: the condition `s < 2` of the hypothesis `hO` is left, not the condition `s ≤ 0` of
the integrable factor. -/
/--
error: unsolved goals
case atTop
g : ℝ → ℝ
hg : Integrable g volume
hO : g =O[atTop] fun x ↦ x ^ (-3)
hc : Continuous g
s : ℝ
⊢ s < 2
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) (hO : g =O[atTop] fun x ↦ x ^ (-3 : ℝ))
    (hc : Continuous g) (s : ℝ) : IntegrableOn (fun x ↦ x ^ s * g x) (Ioi 1) := by
  endpoint_integrability

/- The trace class reports the factor, the cofactor, and the obligation which fails: the cofactor
`‖x⁻¹‖` is not bounded at `0`. -/
/--
trace: [Tactic.endpoint_integrability] ✅️ case locallyIntegrableOn: proved
  [Tactic.endpoint_integrability] the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
  [Tactic.endpoint_integrability] `g` is an integrable factor, with the cofactor `fun x ↦ ‖x⁻¹‖`
  [Tactic.endpoint_integrability] ✅️ an integrable factor times a continuous cofactor: locally integrable
[Tactic.endpoint_integrability] ❌️ case nhds0: not proved
  [Tactic.endpoint_integrability] no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
      continuous on `Ioi 0`
  [Tactic.endpoint_integrability] `g` is an integrable factor, with the cofactor `fun x ↦ ‖x⁻¹‖`
  [Tactic.endpoint_integrability] `‖t⁻¹‖` has the order of `t ^ (-1)`
    [Tactic.endpoint_integrability] `t⁻¹` has the order of `t ^ (-1)`
  [Tactic.endpoint_integrability] the cofactor `fun x ↦ ‖x⁻¹‖` has the order of `fun t ↦ t ^ (-1)`,
      which is not proved bounded:
      ◦ the power `a = -1` of `t` does not satisfy `0 ≤ a`
[Tactic.endpoint_integrability] ✅️ case atTop: proved
  [Tactic.endpoint_integrability] no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
      continuous on `Ioi 0`
  [Tactic.endpoint_integrability] `g` is an integrable factor, with the cofactor `fun x ↦ ‖x⁻¹‖`
  [Tactic.endpoint_integrability] `‖t⁻¹‖` has the order of `t ^ (-1)`
    [Tactic.endpoint_integrability] `t⁻¹` has the order of `t ^ (-1)`
  [Tactic.endpoint_integrability] ✅️ which is bounded at `atTop`
  [Tactic.endpoint_integrability] ✅️ an integrable factor times a bounded cofactor: integrable
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example (g : ℝ → ℝ) (hg : Integrable g) : IntegrableOn (fun x ↦ x⁻¹ * g x) (Ioi 0) := by
  endpoint_integrability

/- The cofactor `x` is not bounded at either end. -/
/--
error: unsolved goals
case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x * g x) atBot volume

case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ x * g x := by
  endpoint_integrability

/--
error: unsolved goals
case nhds0
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x⁻¹ * g x) (𝓝[>] 0) volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : IntegrableOn (fun x ↦ x⁻¹ * g x) (Ioi 0) := by
  endpoint_integrability

/- A product of integrable functions need not be integrable: each factor is tried, the other one
being part of the cofactor, which is not known to be bounded or continuous. -/
/--
error: unsolved goals
case locallyIntegrableOn
g₁ g₂ : ℝ → ℝ
h₁ : Integrable g₁ volume
h₂ : Integrable g₂ volume
⊢ LocallyIntegrableOn (fun x ↦ g₁ x * g₂ x) univ volume

case atBot
g₁ g₂ : ℝ → ℝ
h₁ : Integrable g₁ volume
h₂ : Integrable g₂ volume
⊢ IntegrableAtFilter (fun x ↦ g₁ x * g₂ x) atBot volume

case atTop
g₁ g₂ : ℝ → ℝ
h₁ : Integrable g₁ volume
h₂ : Integrable g₂ volume
⊢ IntegrableAtFilter (fun x ↦ g₁ x * g₂ x) atTop volume
-/
#guard_msgs in
example (g₁ g₂ : ℝ → ℝ) (h₁ : Integrable g₁) (h₂ : Integrable g₂) :
    Integrable fun x ↦ g₁ x * g₂ x := by
  endpoint_integrability

/- An integrable factor is not looked for under an inverse, a power, an exponential, or at an
argument other than the variable. -/
/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : Integrable g volume
⊢ LocallyIntegrableOn (fun x ↦ (g x)⁻¹) univ volume

case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ (g x)⁻¹) atBot volume

case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ (g x)⁻¹) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ (g x)⁻¹ := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : Integrable g volume
⊢ LocallyIntegrableOn (fun x ↦ g x ^ 2) univ volume

case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ g x ^ 2) atBot volume

case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ g x ^ 2) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ g x ^ 2 := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : Integrable g volume
⊢ LocallyIntegrableOn (fun x ↦ rexp (g x)) univ volume

case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ rexp (g x)) atBot volume

case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ rexp (g x)) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ rexp (g x) := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : Integrable g volume
⊢ LocallyIntegrableOn (fun x ↦ g (x ^ 2)) univ volume

case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ g (x ^ 2)) atBot volume

case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ g (x ^ 2)) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ g (x ^ 2) := by
  endpoint_integrability

/- The cofactor is bounded at both ends, but its continuity on `ℝ` leaves the false side goal
`x - 1 ≠ 0`: the integrand has a nonintegrable singularity at `1`. -/
/--
error: unsolved goals
case continuity
g : ℝ → ℝ
hg : Integrable g volume
⊢ ∀ x ∈ univ, x - 1 ≠ 0
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ (x - 1)⁻¹ * g x := by
  endpoint_integrability

/- A hypothesis on another set is not used. -/
/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 5) volume
⊢ LocallyIntegrableOn (fun x ↦ sin x * g x) (Ioi 0) volume

case nhds0
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 5) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) (𝓝[>] 0) volume

case atTop
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 5) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 5)) :
    IntegrableOn (fun x ↦ sin x * g x) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 0) volume
⊢ LocallyIntegrableOn (fun x ↦ sin x * g x) univ volume

case atBot
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 0) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atBot volume

case atTop
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 0) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0)) : Integrable fun x ↦ sin x * g x := by
  endpoint_integrability

/- Local integrability is not a source. -/
/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : LocallyIntegrable g volume
⊢ LocallyIntegrableOn (fun x ↦ sin x * g x) univ volume

case atBot
g : ℝ → ℝ
hg : LocallyIntegrable g volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atBot volume

case atTop
g : ℝ → ℝ
hg : LocallyIntegrable g volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : LocallyIntegrable g) : Integrable fun x ↦ sin x * g x := by
  endpoint_integrability

/- The cofactor `‖rexp x‖ * ‖rexp (-2 * x)‖` is not bounded at `atBot`. -/
/--
error: unsolved goals
case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ rexp x * g x * rexp (-2 * x)) atBot volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ rexp x * g x * rexp (-2 * x) := by
  endpoint_integrability

/-! ### Compound integrable factors -/

/- The factor of an integrability hypothesis may be any factor of the integrand, here the vector of
the outer scalar multiplication. The ends need `a < T`, for `Ioo a T ∈ 𝓝[>] a`, and the reduction
of `IntervalIntegrable` to `Ioc a T` needs `a ≤ T`. -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (S : ℝ → F) (w t T a : ℝ)
    (h1 : IntervalIntegrable (fun s ↦ (((T - s) * Real.sinc (w * (T - s)) : ℝ) : ℂ) • S s)
      volume a T) (haT : a < T) :
    IntervalIntegrable (fun s ↦ (Real.cos (w * (t - T)) : ℂ) •
      ((((T - s) * Real.sinc (w * (T - s)) : ℝ) : ℂ) • S s)) volume a T := by
  have := h1.1
  endpoint_integrability

example (f : ℝ → ℝ) (x₀ : ℝ) (h : Integrable fun t ↦ f (x₀ - t)) :
    Integrable fun t ↦ Real.sin t * f (x₀ - t) := by
  endpoint_integrability

example (g : ℝ → ℝ) (h : Integrable fun x ↦ g x * rexp (-x)) :
    Integrable fun x : ℝ ↦ Real.cos x * (g x * rexp (-x)) := by
  endpoint_integrability

example (g : ℝ → ℝ) (h : IntegrableOn (fun x ↦ g (2 * x)) (Ioi 0)) :
    IntegrableOn (fun x : ℝ ↦ g (2 * x) / (1 + x)) (Ioi 0) := by
  endpoint_integrability

/- The factor is found under a norm, as the numerator of a quotient. -/
example (g : ℝ → ℝ) (h : Integrable fun x ↦ g x * rexp (-x)) :
    Integrable fun x : ℝ ↦ ‖g x * rexp (-x)‖ / (1 + x ^ 2) := by
  endpoint_integrability

/- The largest factor first: `g x * g x` is integrable, `g x` is not known to be. -/
example (g : ℝ → ℝ) (h : Integrable fun x ↦ g x * g x) :
    Integrable fun x : ℝ ↦ Real.sin x * (g x * g x) := by
  endpoint_integrability

/- The integrable factor `g x * rexp (-x)` has the cofactor `‖x‖`, continuous, so that the local
integrability is proved, but not bounded at `atBot` and `atTop`. -/
/--
error: unsolved goals
case atBot
g : ℝ → ℝ
h : Integrable (fun x ↦ g x * rexp (-x)) volume
⊢ IntegrableAtFilter (fun x ↦ g x * rexp (-x) * x) atBot volume

case atTop
g : ℝ → ℝ
h : Integrable (fun x ↦ g x * rexp (-x)) volume
⊢ IntegrableAtFilter (fun x ↦ g x * rexp (-x) * x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (h : Integrable fun x ↦ g x * rexp (-x)) :
    Integrable fun x : ℝ ↦ g x * rexp (-x) * x := by
  endpoint_integrability

/- A hypothesis about `g (2 * x)` says nothing of `g (3 * x)`. -/
/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
h : Integrable (fun x ↦ g (2 * x)) volume
⊢ LocallyIntegrableOn (fun x ↦ sin x * g (3 * x)) univ volume

case atBot
g : ℝ → ℝ
h : Integrable (fun x ↦ g (2 * x)) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g (3 * x)) atBot volume

case atTop
g : ℝ → ℝ
h : Integrable (fun x ↦ g (2 * x)) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g (3 * x)) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (h : Integrable fun x ↦ g (2 * x)) :
    Integrable fun x : ℝ ↦ Real.sin x * g (3 * x) := by
  endpoint_integrability

/- A hypothesis about the product `g x * rexp (-x)` says nothing of `g x`. -/
/--
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
h : Integrable (fun x ↦ g x * rexp (-x)) volume
⊢ LocallyIntegrableOn (fun x ↦ sin x * g x) univ volume

case atBot
g : ℝ → ℝ
h : Integrable (fun x ↦ g x * rexp (-x)) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atBot volume

case atTop
g : ℝ → ℝ
h : Integrable (fun x ↦ g x * rexp (-x)) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (h : Integrable fun x ↦ g x * rexp (-x)) :
    Integrable fun x : ℝ ↦ Real.sin x * g x := by
  endpoint_integrability

/-! ### Hypotheses with universal quantifiers -/

/- A hypothesis with a parameter is instantiated by the user. -/
example (φ : ℕ → ℝ → ℝ) (hm : ∀ k, Measurable (φ k)) (hb : ∀ k, ∀ x ∈ Ioi 0, |φ k x| ≤ 1)
    (k : ℕ) : IntegrableOn (fun x ↦ φ k x * rexp (-x)) (Ioi 0) := by
  have := hb k
  endpoint_integrability

/- A bound on `φ 0` says nothing of `φ 1`. -/
/--
error: unsolved goals
case locallyIntegrableOn
φ : ℕ → ℝ → ℝ
hm : ∀ (k : ℕ), Measurable (φ k)
hpoint : ∀ (t : ℝ), ‖φ 0 t‖ ≤ 1
⊢ LocallyIntegrableOn (fun t ↦ φ 1 t * rexp (-t ^ 2)) univ volume

case atBot
φ : ℕ → ℝ → ℝ
hm : ∀ (k : ℕ), Measurable (φ k)
hpoint : ∀ (t : ℝ), ‖φ 0 t‖ ≤ 1
⊢ IntegrableAtFilter (fun t ↦ φ 1 t * rexp (-t ^ 2)) atBot volume

case atTop
φ : ℕ → ℝ → ℝ
hm : ∀ (k : ℕ), Measurable (φ k)
hpoint : ∀ (t : ℝ), ‖φ 0 t‖ ≤ 1
⊢ IntegrableAtFilter (fun t ↦ φ 1 t * rexp (-t ^ 2)) atTop volume
-/
#guard_msgs in
example (φ : ℕ → ℝ → ℝ) (hm : ∀ k, Measurable (φ k)) (hpoint : ∀ t, ‖φ 0 t‖ ≤ 1) :
    Integrable fun t ↦ φ 1 t * rexp (-t ^ 2) := by
  endpoint_integrability

/-! ### Finite sums -/

/- A finite sum is split by the user, by `integrable_finsetSum`. -/
example (s : Finset ℕ) (c : ℕ → ℝ) :
    Integrable fun x : ℝ ↦ ∑ k ∈ s, c k * Real.cos (k * x) * rexp (-x ^ 2) := by
  refine integrable_finsetSum s fun k _ ↦ ?_
  endpoint_integrability

/-! ### `if … then … else` -/

/- A condition which does not depend on the variable is split by the user; the case `¬p` is
`Integrable fun x ↦ 0`. -/
example (p : Prop) [Decidable p] : Integrable fun x : ℝ ↦ if p then rexp (-x ^ 2) else 0 := by
  split_ifs <;> endpoint_integrability

open Classical in
example (N P : Set ℕ) (b : SchwartzMap ℝ ℂ) (hb : Integrable b) (R : ℝ → ℂ) (hR : Continuous R)
    (hRb : ∀ t, ‖R t‖ ≤ 1) : Integrable fun t : ℝ ↦ if Disjoint N P then b t * R t else 0 := by
  split_ifs <;> endpoint_integrability

/- A condition on the variable is a piecewise integrand, which is not supported. -/
/--
error: unsolved goals
case locallyIntegrableOn
⊢ LocallyIntegrableOn (fun x ↦ if x ≤ 0 then 0 else rexp (-x)) univ volume

case atBot
⊢ IntegrableAtFilter (fun x ↦ if x ≤ 0 then 0 else rexp (-x)) atBot volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ if x ≤ 0 then 0 else rexp (-x)) atTop volume
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ if x ≤ 0 then 0 else rexp (-x) := by
  endpoint_integrability

/-! ### Goals left to the user -/

/- The condition on the power is left as a side goal, with the case tag of the end. -/
/--
error: unsolved goals
case atTop
s : ℝ
⊢ s < -1
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioi 1) := by
  endpoint_integrability

/--
error: unsolved goals
case nhds0
s t : ℝ
_ht : 0 < t
⊢ -1 < s
-/
#guard_msgs in
example (s t : ℝ) (_ht : 0 < t) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioo 0 t) := by
  endpoint_integrability

/--
error: unsolved goals
case nhds0
s : ℝ
⊢ -1 < s
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioc 0 1) := by
  endpoint_integrability

/- The end `0` is singular: `fun_prop` must not prove the continuity on `Icc 0 1`, as an unsafe
discharger would by admitting `∀ x ∈ Icc 0 1, x ≠ 0` with `sorry`. -/
/--
error: unsolved goals
case nhds0
s : ℝ
⊢ -1 < s
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Icc 0 1) := by
  endpoint_integrability

/--
error: unsolved goals
case nhds0
s : ℝ
⊢ -1 < s
-/
#guard_msgs in
example (s : ℝ) : IntervalIntegrable (fun x : ℝ ↦ x ^ s) volume 0 1 := by
  endpoint_integrability

/- The sign of `k` is unknown: it is left, with the case tag of the end. -/
/--
error: unsolved goals
case atTop
k : ℝ
⊢ k < 0
-/
#guard_msgs in
example (k : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (k * x)) (Ioi 0) := by
  endpoint_integrability

/- The condition `-1 < -1` is false: the goal at `𝓝[>] 0` is left, not the false condition. -/
/--
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ x⁻¹) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioc 0 1) := by
  endpoint_integrability

/- The engine has no rule for the logarithm of anything but the variable. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ log (1 + x)) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ Real.log (1 + x)) (Ici 0) := by
  endpoint_integrability

/- The trace class reports why an end is not proved by comparison. -/
/--
trace: [Tactic.endpoint_integrability] ✅️ in the middle: the integrand is continuous on `Ici 0`
[Tactic.endpoint_integrability] ❌️ case atTop: not proved
  [Tactic.endpoint_integrability] no rule bounds `log (1 + t)` as a function of `t`
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example : IntegrableOn (fun x : ℝ ↦ Real.log (1 + x)) (Ici 0) := by
  endpoint_integrability

/- The rules for the product and the square root decline, and the message names the innermost
subexpression which no rule bounds, not `√(log (1 + t))`. -/
/--
trace: [Tactic.endpoint_integrability] ✅️ in the middle: the integrand is continuous on `Ici 2`
[Tactic.endpoint_integrability] ❌️ case atTop: not proved
  [Tactic.endpoint_integrability] no rule bounds `log (1 + t)` as a function of `t`
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example : IntegrableOn (fun x : ℝ ↦ √(Real.log (1 + x)) * x ^ (-2 : ℝ)) (Ioi 2) := by
  endpoint_integrability

/- `fun_prop` fails to prove the continuity on the open interval, and only the run leaving the side
goal `sin x ≠ 0` is tried after that: the default `maxHeartbeats` suffice. Both ends of the open
interval are then left: at `1`, the comparison does not prove that `(sin (1 - t))⁻¹` is continuous
at `0`. -/
/--
error: unsolved goals
case continuity
⊢ ∀ x ∈ Ioo 0 1, sin x ≠ 0

case nhds0
⊢ IntegrableAtFilter (fun x ↦ (sin x)⁻¹) (𝓝[>] 0) volume

case nhds1
⊢ IntegrableAtFilter (fun x ↦ (sin x)⁻¹) (𝓝[<] 1) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (Real.sin x)⁻¹) (Ioc 0 1) := by
  endpoint_integrability

/- At `𝓝[<] 0` the integrand becomes `(-(0 - t)) ^ (-1 / 2)`, normalised to `t ^ (-1 / 2)`, which
is integrable at `𝓝[>] 0`. At `atBot` it becomes `t ^ (-1 / 2)`, which is not integrable at
`atTop`: the condition `-1 / 2 < -1` is false, and the goal is left. -/
/--
error: unsolved goals
case atBot
⊢ IntegrableAtFilter (fun x ↦ (-x) ^ (-1 / 2)) atBot volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (-x) ^ (-1 / 2 : ℝ)) (Iio 0) := by
  endpoint_integrability

/- A real power of a negative variable is bounded only for a nonnegative exponent: along `atBot`,
`x ^ s` is not `|x| ^ s`. -/
/--
error: unsolved goals
case atBot
⊢ IntegrableAtFilter (fun x ↦ x ^ (-2)) atBot volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Iio (-1)) := by
  endpoint_integrability

/- The condition on the power at a reduced end is left, with the case tag of the end. -/
/--
error: unsolved goals
case nhdsa
a b s : ℝ
⊢ -1 < s
-/
#guard_msgs in
example (a b s : ℝ) : IntegrableOn (fun x : ℝ ↦ (x - a) ^ s) (Ioc a b) := by
  endpoint_integrability

/- The condition `-1 < -1` at `𝓝[>] 1` is false. -/
/--
error: unsolved goals
case nhds1
⊢ IntegrableAtFilter (fun x ↦ (x - 1) ^ (-1)) (𝓝[>] 1) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x - 1) ^ (-1 : ℝ)) (Ioc 1 2) := by
  endpoint_integrability

/- The local integrability is proved, with the side goal `∀ x ∈ Ioo 0 1, x ^ 2 ≠ 0` of `fun_prop`
proved after splitting the membership; the integrand is not integrable at `𝓝[>] 0`. -/
/--
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ 1 / x ^ 2) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ 1 / x ^ 2) (Ioc 0 1) := by
  endpoint_integrability

/--
trace: case atBot
h₁ : True → IntegrableAtFilter (fun x ↦ rexp (x ^ 2)) atBot volume
h₂ : True → IntegrableAtFilter (fun x ↦ rexp (x ^ 2)) atTop volume
⊢ IntegrableAtFilter (fun x ↦ rexp (x ^ 2)) atBot volume

case atTop
h₁ : True → IntegrableAtFilter (fun x ↦ rexp (x ^ 2)) atBot volume
h₂ : True → IntegrableAtFilter (fun x ↦ rexp (x ^ 2)) atTop volume
⊢ IntegrableAtFilter (fun x ↦ rexp (x ^ 2)) atTop volume
-/
#guard_msgs in
set_option linter.style.multiGoal false in
example (h₁ : True → IntegrableAtFilter (fun x : ℝ ↦ rexp (x ^ 2)) atBot)
    (h₂ : True → IntegrableAtFilter (fun x : ℝ ↦ rexp (x ^ 2)) atTop) :
    Integrable fun x : ℝ ↦ rexp (x ^ 2) := by
  endpoint_integrability
  trace_state
  case atBot => exact h₁ trivial
  case atTop => exact h₂ trivial

/--
trace: case atTop
f : ℝ → ℝ
hf : ContinuousOn f (Ici 0)
h : True → IntegrableAtFilter f atTop volume
⊢ IntegrableAtFilter f atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0)) (h : True → IntegrableAtFilter f atTop) :
    IntegrableOn f (Ici 0) := by
  endpoint_integrability
  trace_state
  exact h trivial

/--
trace: case locallyIntegrableOn
f : ℝ → ℝ
h₀ : True → LocallyIntegrableOn f (Ioi 0) volume
h₁ : True → IntegrableAtFilter f (𝓝[>] 0) volume
h₂ : True → IntegrableAtFilter f atTop volume
⊢ LocallyIntegrableOn f (Ioi 0) volume

case nhds0
f : ℝ → ℝ
h₀ : True → LocallyIntegrableOn f (Ioi 0) volume
h₁ : True → IntegrableAtFilter f (𝓝[>] 0) volume
h₂ : True → IntegrableAtFilter f atTop volume
⊢ IntegrableAtFilter f (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
h₀ : True → LocallyIntegrableOn f (Ioi 0) volume
h₁ : True → IntegrableAtFilter f (𝓝[>] 0) volume
h₂ : True → IntegrableAtFilter f atTop volume
⊢ IntegrableAtFilter f atTop volume
-/
#guard_msgs in
set_option linter.style.multiGoal false in
example (f : ℝ → ℝ) (h₀ : True → LocallyIntegrableOn f (Ioi 0))
    (h₁ : True → IntegrableAtFilter f (𝓝[>] 0)) (h₂ : True → IntegrableAtFilter f atTop) :
    IntegrableOn f (Ioi 0) := by
  endpoint_integrability
  trace_state
  exacts [h₀ trivial, h₁ trivial, h₂ trivial]

/-! ### The names of the goals at the finite ends

The goal at a finite end is named after the end, `nhds0` or `nhdsa`, when the end is a numeral or
a variable; otherwise it is `nhdsGT` at the lower end and `nhdsLT` at the upper end. -/

/--
error: unsolved goals
case nhdsa
a b : ℝ
hab : a < b
⊢ IntegrableAtFilter (fun x ↦ (x - a)⁻¹ + (b - x)⁻¹) (𝓝[>] a) volume

case nhdsb
a b : ℝ
hab : a < b
⊢ IntegrableAtFilter (fun x ↦ (x - a)⁻¹ + (b - x)⁻¹) (𝓝[<] b) volume
-/
#guard_msgs in
example (a b : ℝ) (hab : a < b) :
    IntegrableOn (fun x : ℝ ↦ (x - a)⁻¹ + (b - x)⁻¹) (Ioo a b) := by
  endpoint_integrability

/--
error: unsolved goals
case nhdsGT
⊢ IntegrableAtFilter (fun x ↦ (x + 1)⁻¹) (𝓝[>] (-1)) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (x + 1)⁻¹) (Ioc (-1) 0) := by
  endpoint_integrability

/-! ### Signs of the coefficients of the exponent left to the user -/

/- The coefficient `-1 * n` of the exponent is of unknown sign: the decay is needed, and `0 < n`,
the condition which makes the monomial its witness, is left. -/
/--
error: unsolved goals
case atTop
n : ℝ
⊢ 0 < n
-/
#guard_msgs in
example (n : ℝ) : IntegrableOn (fun t ↦ rexp (-t * n)) (Ioi (0 : ℝ)) := by
  endpoint_integrability

example (n : ℝ) (hn : 0 < n) : IntegrableOn (fun t ↦ rexp (-t * n)) (Ioi (0 : ℝ)) := by
  endpoint_integrability

/- The power `-2 < -1` decides the term when the exponent is bounded above: the weak condition
is left. -/
/--
error: unsolved goals
case atTop
n : ℝ
⊢ 0 ≤ n
-/
#guard_msgs in
example (n : ℝ) : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ) * rexp (-n * t)) (Ioi 1) := by
  endpoint_integrability

/- The cofactor of an integrable factor need only be bounded: the weak condition is left. -/
/--
error: unsolved goals
case atTop
n : ℝ
g : ℝ → ℝ
hg : Integrable g volume
⊢ 0 ≤ n
-/
#guard_msgs in
example (n : ℝ) (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun x ↦ g x * rexp (-n * x)) (Ioi 0) := by
  endpoint_integrability

/- The condition `0 < -1` is refuted: the goal at `atTop` is left, not the false condition. -/
/--
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun t ↦ rexp t) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun t : ℝ ↦ rexp t) (Ioi 0) := by
  endpoint_integrability

/- The monomial `t`, of positive coefficient, is absorbed by the witness `-a * t ^ 2`. -/
/--
error: unsolved goals
case atTop
a : ℝ
⊢ 0 < a
-/
#guard_msgs in
example (a : ℝ) : IntegrableOn (fun t : ℝ ↦ rexp (-a * t ^ 2 + t)) (Ioi 0) := by
  endpoint_integrability

/- The condition `0 < a` is left for the witness `-a * t`, then `1 ≤ 0`, for `t ^ 2`, of more
singular degree, is refuted: the goal at `atTop` is left, and not the condition `0 < a`. -/
/--
error: unsolved goals
case atTop
a : ℝ
⊢ IntegrableAtFilter (fun t ↦ rexp (-a * t + t ^ 2)) atTop volume
-/
#guard_msgs in
example (a : ℝ) : IntegrableOn (fun t : ℝ ↦ rexp (-a * t + t ^ 2)) (Ioi 0) := by
  endpoint_integrability

/- Two coefficients of unknown sign: `-a * t ^ 2` is the witness of the decay, and absorbs
`-b * t`, of less singular degree, whatever the sign of `b`. -/
/--
error: unsolved goals
case atTop
a b : ℝ
⊢ 0 < a
-/
#guard_msgs in
example (a b : ℝ) : IntegrableOn (fun t : ℝ ↦ rexp (-a * t ^ 2 - b * t)) (Ioi 0) := by
  endpoint_integrability

/- The witness is the candidate which absorbs the most monomials, `-a * t ^ 2`, not the first
one. -/
/--
error: unsolved goals
case atTop
a b : ℝ
⊢ 0 < a
-/
#guard_msgs in
example (a b : ℝ) : IntegrableOn (fun t : ℝ ↦ rexp (-b * t - a * t ^ 2)) (Ioi 0) := by
  endpoint_integrability

/- The witness `-x ^ 2` is proved to decay: it absorbs `a * x`, and the condition is left only for
`c * x ^ 3`, of more singular degree. -/
/--
error: unsolved goals
case atTop
a c : ℝ
⊢ c ≤ 0
-/
#guard_msgs in
example (a c : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (a * x + c * x ^ 3 - x ^ 2)) (Ioi 0) := by
  endpoint_integrability

/- At `𝓝[>] 0`, the decay is needed by the power `-3`: the witness `-a / t ^ 2` absorbs
`b / t`. -/
/--
error: unsolved goals
case nhds0
a b : ℝ
⊢ 0 < a
-/
#guard_msgs in
example (a b : ℝ) :
    IntegrableOn (fun t : ℝ ↦ rexp (-a / t ^ 2 + b / t) / t ^ 3) (Ioc 0 1) := by
  endpoint_integrability

/- At `𝓝[>] 0`, the power `0` decides the term when the exponent is bounded above: the weak
condition is left. -/
/--
error: unsolved goals
case nhds0
n : ℝ
⊢ 0 ≤ n
-/
#guard_msgs in
example (n : ℝ) : IntegrableOn (fun t : ℝ ↦ rexp (-n / t)) (Ioc 0 1) := by
  endpoint_integrability

/-! ### Pointwise operations on functions

The operations on functions of a real variable, such as `f * g`, are unfolded at the entry of the
tactic, in the goal and in the hypotheses: `f * g` becomes `fun x ↦ f x * g x` everywhere, so that
the factors are seen, and a hypothesis about `f * g` is read for the integrand whichever way each
is written. The goals left show the unfolded form. -/

/- The integrable factor `f` is seen in the product of functions, and `g` is bounded. -/
example (f g : ℝ → ℂ) (hC : ContinuousOn (f * g) (Ioi (0 : ℝ))) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hg : ∀ x, ‖g x‖ ≤ 1) : IntegrableOn (f * g) (Ioi (0 : ℝ)) := by
  endpoint_integrability

/- Without the bound of `g`, the two ends are left, with the product unfolded in the goal and in
the hypothesis. -/
/--
error: unsolved goals
case nhds0
f g : ℝ → ℂ
hC : ContinuousOn (fun x ↦ f x * g x) (Ioi 0)
hf : IntegrableOn f (Ioi 0) volume
⊢ IntegrableAtFilter (fun x ↦ f x * g x) (𝓝[>] 0) volume

case atTop
f g : ℝ → ℂ
hC : ContinuousOn (fun x ↦ f x * g x) (Ioi 0)
hf : IntegrableOn f (Ioi 0) volume
⊢ IntegrableAtFilter (fun x ↦ f x * g x) atTop volume
-/
#guard_msgs in
example (f g : ℝ → ℂ) (hC : ContinuousOn (f * g) (Ioi (0 : ℝ)))
    (hf : IntegrableOn f (Ioi (0 : ℝ))) : IntegrableOn (f * g) (Ioi (0 : ℝ)) := by
  endpoint_integrability

/- Hypotheses about the product: its continuity with an asymptotic bound, with its integrability
at the end, and its measurability with a pointwise bound. -/
example (f g : ℝ → ℝ) (hc : Continuous (f * g)) (h : (f * g) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn (f * g) (Ioi 1) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hc : Continuous (f * g)) (h : IntegrableAtFilter (f * g) atTop) :
    IntegrableOn (f * g) (Ioi 1) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hm : Measurable (f * g)) (h : ∀ x, ‖(f * g) x‖ ≤ rexp (-x)) :
    IntegrableOn (f * g) (Ioi 1) := by
  endpoint_integrability

/- The goal and the hypotheses need not be written the same way. -/
example (f g : ℝ → ℝ) (hc : Continuous (f * g)) (hf : Integrable f) (hg : ∀ x, ‖g x‖ ≤ 1) :
    IntegrableOn (fun x ↦ f x * g x) (Ioi 1) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hc : Continuous fun x ↦ f x * g x) (hf : Integrable f)
    (hg : ∀ x, ‖g x‖ ≤ 1) : IntegrableOn (f * g) (Ioi 1) := by
  endpoint_integrability

/- The product as a subterm, as an integrable factor, as a cofactor, and under a bound. -/
example (f g : ℝ → ℝ) (hc : Continuous (f * g)) :
    IntegrableOn (fun x ↦ (f * g) x / √(x - 1)) (Ioc 1 2) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hfg : Integrable (f * g)) :
    Integrable fun x ↦ Real.sin x * (f * g) x := by
  endpoint_integrability

example (f g h : ℝ → ℝ) (hf : Integrable f) (hc : Continuous (g * h))
    (hb : (g * h) =O[atTop] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (fun x ↦ (g * h) x * f x) (Ioi 1) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hm : Measurable (f * g)) (hb : ∀ x, ‖(f * g) x‖ ≤ 1) :
    IntegrableOn (fun x ↦ (f * g) x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- Explicit functions, a sum, a composition and a scalar multiple. -/
example : IntegrableOn ((fun x : ℝ ↦ rexp (-x)) * fun x ↦ x) (Ioi 0) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hc : Continuous (f + g)) (h : (f + g) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn (f + g) (Ioi 1) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hc : Continuous (f ∘ g)) (h : (f ∘ g) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn (f ∘ g) (Ioi 1) := by
  endpoint_integrability

example (c : ℝ) (f : ℝ → ℝ) (hc : Continuous (c • f))
    (h : (c • f) =O[atTop] fun x ↦ x ^ (-2 : ℝ)) : IntegrableOn (c • f) (Ioi 1) := by
  endpoint_integrability

/- The other goals. -/
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) : LocallyIntegrable (f * g) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hc : Continuous (f * g)) : LocallyIntegrableOn (f * g) (Ioi 0) := by
  endpoint_integrability

example (f g : ℝ → ℝ) (hc : Continuous (f * g)) :
    IntervalIntegrable (fun x ↦ (f * g) x / √x) volume 0 1 := by
  endpoint_integrability

example (f g : ℝ → ℝ) (h : Integrable (f * g)) : Integrable (f * g) := by
  endpoint_integrability

/- With the continuity of the product only, the end `atTop` is left, as for an opaque function. -/
/--
error: unsolved goals
case atTop
f g : ℝ → ℝ
hc : Continuous fun x ↦ f x * g x
⊢ IntegrableAtFilter (fun x ↦ f x * g x) atTop volume
-/
#guard_msgs in
example (f g : ℝ → ℝ) (hc : Continuous (f * g)) : IntegrableOn (f * g) (Ioi 1) := by
  endpoint_integrability

/- Every operation, nested: the bound variable is `x`. -/
/--
error: unsolved goals
case atTop
f g h k : ℝ → ℝ
c : ℝ
n : ℕ
h1 : Continuous fun x ↦ (f x * g x + -h x) / k x - c • f x ^ n + (f (g x))⁻¹ + 1 + 0 + f x • g x
⊢ IntegrableAtFilter (fun x ↦ (f x * g x + -h x) / k x - c • f x ^ n + (f (g x))⁻¹ + 1 + 0 + f x • g x) atTop volume
-/
#guard_msgs in
example (f g h k : ℝ → ℝ) (c : ℝ) (n : ℕ)
    (h1 : Continuous ((f * g + -h) / k - c • f ^ n + f⁻¹ ∘ g + 1 + 0 + f • g)) :
    IntegrableOn ((f * g + -h) / k - c • f ^ n + f⁻¹ ∘ g + 1 + 0 + f • g) (Ioi 1) := by
  endpoint_integrability

/- Nothing else is rewritten: the operations on functions of another variable, the beta-redexes
and the `let` of the hypotheses are left as they are, and the integrand keeps its variable `y`. -/
/--
error: unsolved goals
case atTop
f g : ℝ → ℝ
u v : ℕ → ℝ
hu : u * v = v * u
hb : (fun y ↦ y + 1) 2 = 3
hl :
  let z := 2;
  z = 2
hc : Continuous fun x ↦ f x * g x
⊢ IntegrableAtFilter (fun y ↦ f y * g y) atTop volume
-/
#guard_msgs in
example (f g : ℝ → ℝ) (u v : ℕ → ℝ) (hu : u * v = v * u)
    (hb : (fun y : ℝ ↦ y + 1) 2 = 3) (hl : let z := (2 : ℝ); z = 2)
    (hc : Continuous (f * g)) : IntegrableOn (fun y ↦ (f * g) y) (Ioi 1) := by
  endpoint_integrability

/-! ### The trace

With `set_option trace.Tactic.endpoint_integrability true`, the trace has one block per goal,
marked `✅️` if it is proved and `❌️` if it is left. A block gives what was established, the order
of each factor under that of their product, and why an attempt failed. Here the end `atTop` is
proved through the integrable factor `f`, whose cofactor is bounded by the hypothesis `hb`. -/

/--
trace: [Tactic.endpoint_integrability] ✅️ in the middle: the integrand is continuous on `Ioi 0`
[Tactic.endpoint_integrability] ❌️ case nhds0: not proved
  [Tactic.endpoint_integrability] no rule bounds `f t` as a function of `t`
  [Tactic.endpoint_integrability] `f` is an integrable factor, with the cofactor `fun x ↦ ‖g x‖`
  [Tactic.endpoint_integrability] no rule bounds `g t` as a function of `t`
[Tactic.endpoint_integrability] ✅️ case atTop: proved
  [Tactic.endpoint_integrability] no rule bounds `f t` as a function of `t`
  [Tactic.endpoint_integrability] `f` is an integrable factor, with the cofactor `fun x ↦ ‖g x‖`
  [Tactic.endpoint_integrability] `‖g t‖` is in `O(1)`
    [Tactic.endpoint_integrability] `g t` is in `O(1)`
  [Tactic.endpoint_integrability] ✅️ which is bounded at `atTop`
  [Tactic.endpoint_integrability] ✅️ an integrable factor times a bounded cofactor: integrable
-/
#guard_msgs (trace, drop error) in
set_option trace.Tactic.endpoint_integrability true in
example (f g : ℝ → ℂ) (hC : ContinuousOn (f * g) (Ioi (0 : ℝ))) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hg : Measurable g) (hb : g =O[atTop] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (f * g) (Ioi (0 : ℝ)) := by
  endpoint_integrability

/- An explicit integrand: the order of each factor, then that of the product, which is decided. -/
/--
trace: [Tactic.endpoint_integrability] ✅️ in the middle: the integrand is continuous on `Ioi 0`
[Tactic.endpoint_integrability] ✅️ case nhds0: proved
  [Tactic.endpoint_integrability] `t ^ (s - 1) * rexp (-t)` has the order of `t ^ (s - 1) * rexp (-t)`
    [Tactic.endpoint_integrability] `t ^ (s - 1)` has the order of `t ^ (s - 1)`
    [Tactic.endpoint_integrability] `rexp (-t)` has the order of `rexp (-t)`
  [Tactic.endpoint_integrability] ✅️ which is integrable at `𝓝[>] 0`
[Tactic.endpoint_integrability] ✅️ case atTop: proved
  [Tactic.endpoint_integrability] `t ^ (s - 1) * rexp (-t)` has the order of `t ^ (s - 1) * rexp (-t)`
    [Tactic.endpoint_integrability] `t ^ (s - 1)` has the order of `t ^ (s - 1)`
    [Tactic.endpoint_integrability] `rexp (-t)` has the order of `rexp (-t)`
  [Tactic.endpoint_integrability] ✅️ which is integrable at `atTop`
-/
#guard_msgs (trace) in
set_option trace.Tactic.endpoint_integrability true in
example (s : ℝ) (hs : 0 < s) : IntegrableOn (fun x : ℝ ↦ x ^ (s - 1) * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-! ### The explanation of the goals left

When `endpoint_integrability` leaves an integrability goal, it logs one `info` message which says,
for each goal left, why the tactic stopped there, and which forms of hypothesis it uses. The tests
below are a catalogue of these messages, in the order of the pipeline. The message gives the
number of goals left, then, under the case tag of each goal, its reasons, a summary followed by the
reasons for it as nested bullets; goals with the same reasons are given together. The option
`tactic.endpoint_integrability.explain`, off in the rest of this file, has here its default value,
`true`. -/

section Explanation

set_option tactic.endpoint_integrability.explain true

/-! #### The middle: the continuity of the integrand is not proved

Nothing is known about `f`: the middle is not proved continuous, and there is no asymptotic
comparison at the ends, since `f` is not proved measurable; the two ends, with the same reasons,
are given together. The remedy is a continuity hypothesis, and, at `atTop`, an asymptotic
bound. -/

/--
info: endpoint_integrability does not prove 3 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
case nhds0, case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 0`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
⊢ LocallyIntegrableOn f (Ioi 0) volume

case nhds0
f : ℝ → ℝ
⊢ IntegrableAtFilter f (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
⊢ IntegrableAtFilter f atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) : IntegrableOn f (Ioi 0) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Continuous f) (h : f =O[atTop] fun x ↦ x ^ (-2 : ℝ)) :
    IntegrableOn f (Ioi 0) := by
  endpoint_integrability

/-! #### An end: no asymptotic comparison

The asymptotic comparison needs the measure `volume`, values in `ℝ` or `ℂ`, and the measurability
of the integrand near the end. -/

/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no asymptotic comparison: it needs the measure `volume`, not `μ`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
μ : Measure ℝ
inst✝ : IsLocallyFiniteMeasure μ
⊢ IntegrableAtFilter (fun x ↦ x⁻¹) atTop μ
-/
#guard_msgs in
example (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioi 1) μ := by
  endpoint_integrability

/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no asymptotic comparison: it needs values in `ℝ` or `ℂ`, not in `ℝ × ℝ`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ (rexp (-x), rexp (-x))) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ (rexp (-x), rexp (-x))) (Ioi 0) := by
  endpoint_integrability

/- The continuity of `f` on `Ioo a b` gives its measurability near `a` only with
`Ioo a b ∈ 𝓝[>] a`, which needs `a < b`. -/
/--
info: endpoint_integrability does not prove 2 integrability goals:
case nhdsa:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, and
    its continuity on `Ioo a b` gives its measurability near this end only with
    `Ioo a b ∈ 𝓝[>] a`, which is not proved
case nhdsb:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, and
    its continuity on `Ioo a b` gives its measurability near this end only with
    `Ioo a b ∈ 𝓝[<] b`, which is not proved

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhdsa
a b : ℝ
f : ℝ → ℝ
hf : ContinuousOn f (Ioo a b)
⊢ IntegrableAtFilter f (𝓝[>] a) volume

case nhdsb
a b : ℝ
f : ℝ → ℝ
hf : ContinuousOn f (Ioo a b)
⊢ IntegrableAtFilter f (𝓝[<] b) volume
-/
#guard_msgs in
example (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo a b)) : IntegrableOn f (Ioo a b) := by
  endpoint_integrability

/-! #### An end: no rule bounds a term

At `atBot`, the engine sees the integrand after the change of variables `x = -t`, and has no
rule for the unknown function `f`. A pointwise bound on `f` lets the tactic replace it. -/

/--
info: endpoint_integrability does not prove 1 integrability goal:
case atBot:
  • with `x = -t`, the integrand is `fun t ↦ f (-t) * rexp (-t)`, at `atTop`
  • no rule bounds `f (-t)` as a function of `t`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atBot
f : ℝ → ℝ
hf : Continuous f
⊢ IntegrableAtFilter (fun x ↦ f x * rexp x) atBot volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Continuous f) : IntegrableOn (fun x ↦ f x * rexp x) (Iio 0) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Continuous f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp x) (Iio 0) := by
  endpoint_integrability

/- The rule for the inverse needs the exact order of the expression inverted, and the engine
only bounds `1 + t ^ 2 * cos t ^ 2` from above. -/
/--
info: endpoint_integrability does not prove 2 integrability goals:
case atBot:
  • with `x = -t`, the integrand is `fun t ↦ (1 + (-t) ^ 2 * cos (-t) ^ 2)⁻¹`, at `atTop`
  • no bound for the inverse `(1 + (-t) ^ 2 * cos (-t) ^ 2)⁻¹`: it needs the exact order
    of `1 + (-t) ^ 2 * cos (-t) ^ 2`, and the tactic has only the upper bound
    `fun t ↦ 1 + t ^ 2`
case atTop:
  • no bound for the inverse `(1 + t ^ 2 * cos t ^ 2)⁻¹`: it needs the exact order of
    `1 + t ^ 2 * cos t ^ 2`, and the tactic has only the upper bound `fun t ↦ 1 + t ^ 2`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atBot
⊢ IntegrableAtFilter (fun x ↦ (1 + x ^ 2 * cos x ^ 2)⁻¹) atBot volume

case atTop
⊢ IntegrableAtFilter (fun x ↦ (1 + x ^ 2 * cos x ^ 2)⁻¹) atTop volume
-/
#guard_msgs in
example : Integrable fun x : ℝ ↦ (1 + x ^ 2 * Real.cos x ^ 2)⁻¹ := by
  endpoint_integrability

/- A power of a sum whose exponent is not a numeral is not expanded. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no bound for the power `(cos t + sin t) ^ n` of a sum: its exponent is not a positive
    numeral

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
n : ℕ
⊢ IntegrableAtFilter (fun x ↦ (cos x + sin x) ^ n * rexp (-x)) atTop volume
-/
#guard_msgs in
example (n : ℕ) : IntegrableOn (fun x : ℝ ↦ (Real.cos x + Real.sin x) ^ n * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/-! #### An end: the integrability of the bound is not decided

The order `t ^ (-1)` of `x⁻¹` at `atTop` is not integrable: the power of the logarithm would have
to be less than `-1`. The message says "has the order of" when the comparison is exact, so that
the integrand is not integrable either, and "only bounds … from above" when it is not, in which
case nothing is known of the integrand (see `sin x / x ^ (3 / 2)` below). -/

/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • the integrand `fun x ↦ x⁻¹` has the order of `fun t ↦ t ^ (-1)`,
    which is not proved integrable:
    ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ x⁻¹) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioi 1) := by
  endpoint_integrability

/- An upper bound which is too crude: the function is integrable, but the engine bounds `sin x`
by `1` near `0`, so that it only bounds the integrand from above by `t ^ (-(3 / 2))`, which is
not integrable there (compare with `x⁻¹` above, whose order is exact). The remedy is a pointwise
bound of `sin`, `Real.abs_sin_le_abs`, with which the bounded term `sin x` is replaced by `|x|`. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case nhds0:
  • the tactic only bounds the integrand `fun x ↦ sin x / x ^ (3 / 2)` from above,
    up to a constant factor, by `fun t ↦ t ^ (-(3 / 2))`, which is not proved integrable:
    ◦ the power `a = -(3 / 2)` of `t` does not satisfy `-1 < a`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ sin x / x ^ (3 / 2)) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ Real.sin x / x ^ (3 / 2 : ℝ)) (Ioc 0 1) := by
  endpoint_integrability

example (h : ∀ x : ℝ, |Real.sin x| ≤ |x|) :
    IntegrableOn (fun x : ℝ ↦ Real.sin x / x ^ (3 / 2 : ℝ)) (Ioc 0 1) := by
  endpoint_integrability

/- The exponent `n * t ^ p` must decay, and the sign of `p` is unknown: state it. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • the integrand `fun x ↦ rexp (n * x ^ p)` has the order of `fun t ↦ rexp (n * t ^ p)`,
    which is not proved integrable:
    ◦ its exponent `fun t ↦ n * t ^ p` must decay, since the power `a = 0` of `t` does not
      satisfy `a < -1`
    ◦ the exponent is not proved to decay: no monomial `c * t ^ p` has `c` proved negative
      and `t ^ p` proved unbounded at this end; the degree of `fun t ↦ n * t ^ p` is not
      proved to satisfy `0 < p`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
n p : ℝ
⊢ IntegrableAtFilter (fun x ↦ rexp (n * x ^ p)) atTop volume
-/
#guard_msgs in
example (n p : ℝ) : IntegrableOn (fun x : ℝ ↦ rexp (n * x ^ p)) (Ioi 1) := by
  endpoint_integrability

/--
error: unsolved goals
case atTop
n p : ℝ
hp : 0 < p
⊢ n < 0
-/
#guard_msgs in
example (n p : ℝ) (hp : 0 < p) : IntegrableOn (fun x : ℝ ↦ rexp (n * x ^ p)) (Ioi 1) := by
  endpoint_integrability

/- The monomial `2 * t ^ p` of the exponent is bounded above, its degree being unknown, only if
its coefficient is nonpositive, which is false. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • the integrand `fun x ↦ x ^ (-2) * rexp (2 * x ^ p)` has the order of
    `fun t ↦ t ^ (-2) * rexp (2 * t ^ p)`, which is not proved integrable:
    ◦ the monomial `fun t ↦ 2 * t ^ p` of the exponent is bounded above if `2 ≤ 0`, which is
      false

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
p : ℝ
⊢ IntegrableAtFilter (fun x ↦ x ^ (-2) * rexp (2 * x ^ p)) atTop volume
-/
#guard_msgs in
example (p : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ) * rexp (2 * x ^ p)) (Ioi 1) := by
  endpoint_integrability

/- The bound is a sum, `1 + 1`: the message names its first term which is not decided. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • the tactic only bounds the integrand `fun x ↦ cos x + sin x` from above,
    up to a constant factor, by `fun t ↦ 1 + 1`, which is not proved integrable:
    ◦ the term `fun t ↦ 1` of the bound is not proved integrable:
      ◦ the power `a = 0` of `t` does not satisfy `a < -1`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ cos x + sin x) atTop volume
-/
#guard_msgs in
example : IntegrableOn (fun x ↦ Real.cos x + Real.sin x) (Ioi 0) := by
  endpoint_integrability

/- With `0 < p`, the monomial `2 * t ^ p` would make the exponent decay only with a negative
coefficient: the bound `rexp (2 * t ^ p)` is not integrable. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • the integrand `fun x ↦ rexp (2 * x ^ p)` has the order of `fun t ↦ rexp (2 * t ^ p)`,
    which is not proved integrable:
    ◦ its exponent `fun t ↦ 2 * t ^ p` must decay, since the power `a = 0` of `t` does not
      satisfy `a < -1`
    ◦ the monomial `fun t ↦ 2 * t ^ p` of the exponent makes the exponent decay if `2 < 0`,
      which is false

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
p : ℝ
hp : 0 < p
⊢ IntegrableAtFilter (fun x ↦ rexp (2 * x ^ p)) atTop volume
-/
#guard_msgs in
example (p : ℝ) (hp : 0 < p) : IntegrableOn (fun x : ℝ ↦ rexp (2 * x ^ p)) (Ioi 1) := by
  endpoint_integrability

/-! #### An integrable factor which is not used

A hypothesis of integrability on another set than an interval with the ends of the goal is not
used. -/

/--
info: endpoint_integrability does not prove 3 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
  • the hypothesis `IntegrableOn g (Ioi 1) volume` is not used: it is about a factor of
    the integrand, but not on an interval with the ends of `Ioi 0`
case nhds0, case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 0`
  • the hypothesis `IntegrableOn g (Ioi 1) volume` is not used: it is about a factor of
    the integrand, but not on an interval with the ends of `Ioi 0`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 1) volume
⊢ LocallyIntegrableOn g (Ioi 0) volume

case nhds0
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 1) volume
⊢ IntegrableAtFilter g (𝓝[>] 0) volume

case atTop
g : ℝ → ℝ
hg : IntegrableOn g (Ioi 1) volume
⊢ IntegrableAtFilter g atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 1)) : IntegrableOn g (Ioi 0) := by
  endpoint_integrability

/- At the end `a`, the integrable factor needs `Ioo a b ∈ 𝓝[>] a`, that is `a < b`. -/
/--
info: endpoint_integrability does not prove 2 integrability goals:
case nhdsa:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioo a b`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖sin x‖`
  • the integrable factor is not used: `Ioo a b ∈ 𝓝[>] a` is not proved (the discharger
    does not prove `a < b`)
case nhdsb:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioo a b`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖sin x‖`
  • the integrable factor is not used: `Ioo a b ∈ 𝓝[<] b` is not proved (the discharger
    does not prove `a < b`)

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhdsa
a b : ℝ
g : ℝ → ℝ
hg : IntegrableOn g (Ioo a b) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) (𝓝[>] a) volume

case nhdsb
a b : ℝ
g : ℝ → ℝ
hg : IntegrableOn g (Ioo a b) volume
⊢ IntegrableAtFilter (fun x ↦ sin x * g x) (𝓝[<] b) volume
-/
#guard_msgs in
example (a b : ℝ) (g : ℝ → ℝ) (hg : IntegrableOn g (Ioo a b)) :
    IntegrableOn (fun x ↦ Real.sin x * g x) (Ioo a b) := by
  endpoint_integrability

example (a b : ℝ) (hab : a < b) (g : ℝ → ℝ) (hg : IntegrableOn g (Ioo a b)) :
    IntegrableOn (fun x ↦ Real.sin x * g x) (Ioo a b) := by
  endpoint_integrability

/- The cofactor `‖x‖` of the integrable factor `g x` is not bounded at either end. -/
/--
info: endpoint_integrability does not prove 2 integrability goals:
case atBot:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `univ`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖x‖`
  • with `x = -t`, the cofactor is `fun t ↦ ‖-t‖`, at `atTop`
  • the cofactor `fun t ↦ ‖-t‖` has the order of `fun t ↦ t ^ 1`,
    which is not proved bounded:
    ◦ the power `a = 1` of `t` does not satisfy `a ≤ 0`
case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `univ`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖x‖`
  • the cofactor `fun x ↦ ‖x‖` has the order of `fun t ↦ t ^ 1`,
    which is not proved bounded:
    ◦ the power `a = 1` of `t` does not satisfy `a ≤ 0`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atBot
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x * g x) atBot volume

case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : Integrable fun x ↦ x * g x := by
  endpoint_integrability

/- The cofactor `x * rexp (n * x ^ p)` is bounded only if its exponent decays, which needs the
signs of `n` and `p`. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 1`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖x * rexp (n * x ^ p)‖`
  • the cofactor `fun x ↦ ‖x * rexp (n * x ^ p)‖` has the order of
    `fun t ↦ t ^ 1 * rexp (n * t ^ p)`, which is not proved bounded:
    ◦ its exponent `fun t ↦ n * t ^ p` must decay, since the power `a = 1` of `t` does not
      satisfy `a ≤ 0`
    ◦ the exponent is not proved to decay: no monomial `c * t ^ p` has `c` proved negative
      and `t ^ p` proved unbounded at this end; the degree of `fun t ↦ n * t ^ p` is not
      proved to satisfy `0 < p`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
n p : ℝ
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x * rexp (n * x ^ p) * g x) atTop volume
-/
#guard_msgs in
example (n p : ℝ) (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun x ↦ x * rexp (n * x ^ p) * g x) (Ioi 1) := by
  endpoint_integrability

/- With the signs of `n` and `p`, the goal is closed, without a message. -/
#guard_msgs in
example (n p : ℝ) (hn : n < 0) (hp : 0 < p) (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun x ↦ x * rexp (n * x ^ p) * g x) (Ioi 1) := by
  endpoint_integrability

/- The cofactor `‖log x‖` has the power `0` of `t`: it is bounded only if the power of the
logarithm is nonpositive. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 1`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖log x‖`
  • the cofactor `fun x ↦ ‖log x‖` has the order of `fun t ↦ |log t| ^ 1`,
    which is not proved bounded:
    ◦ the power of `t` is `0`, and the power `k = 1` of `|log t|` does not satisfy `k ≤ 0`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ log x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : IntegrableOn (fun x ↦ Real.log x * g x) (Ioi 1) := by
  endpoint_integrability

/- With a positive power of the logarithm, the cofactor is bounded only if the power of `t` is
negative. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 1`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖x * log x‖`
  • the cofactor `fun x ↦ ‖x * log x‖` has the order of `fun t ↦ t ^ 1 * |log t| ^ 1`,
    which is not proved bounded:
    ◦ the power `a = 1` of `t` does not satisfy `a < 0`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x * log x * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun x ↦ x * Real.log x * g x) (Ioi 1) := by
  endpoint_integrability

/- The bound of the cofactor is a sum, `1 + t ^ 1`: the message names its first term which is not
bounded. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 1`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖cos x + sin x * x‖`
  • the tactic only bounds the cofactor `fun x ↦ ‖cos x + sin x * x‖` from above,
    up to a constant factor, by `fun t ↦ 1 + t ^ 1`, which is not proved bounded:
    ◦ the term `fun t ↦ t ^ 1` of the bound is not proved bounded:
      ◦ the power `a = 1` of `t` does not satisfy `a ≤ 0`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ (cos x + sin x * x) * g x) atTop volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) :
    IntegrableOn (fun x ↦ (Real.cos x + Real.sin x * x) * g x) (Ioi 1) := by
  endpoint_integrability

/-! #### The middle through an integrable factor

Without the continuity of the integrand, the middle is proved through an integrable factor, whose
cofactor must be continuous, and the integrand measurable along the factorization. -/

/--
info: endpoint_integrability does not prove 3 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioo 0 1`, by a hypothesis or `fun_prop`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖Int.fract x‖`
  • the cofactor is not proved continuous on `Ioo 0 1`, by a hypothesis or `fun_prop`
case nhds0:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioo 0 1`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖Int.fract x‖`
  • no rule bounds `Int.fract t` as a function of `t`
case nhds1:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioo 0 1`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖Int.fract x‖`
  • with `x = 1 - t`, the cofactor is `fun t ↦ ‖Int.fract (1 - t)‖`, at `𝓝[>] 0`
  • no rule bounds `Int.fract (1 - t)` as a function of `t`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
g : ℝ → ℝ
hg : Integrable g volume
⊢ LocallyIntegrableOn (fun x ↦ Int.fract x * g x) (Ioo 0 1) volume

case nhds0
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ Int.fract x * g x) (𝓝[>] 0) volume

case nhds1
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ Int.fract x * g x) (𝓝[<] 1) volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : IntegrableOn (fun x ↦ Int.fract x * g x) (Ioo 0 1) := by
  endpoint_integrability

/- The norm of `h` is continuous, but `h` is not known to be measurable. -/
/--
info: endpoint_integrability does not prove 3 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖h x‖`
  • the integrand is not proved measurable
case nhds0:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 0`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖h x‖`
  • no rule bounds `h t` as a function of `t`
case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 0`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖h x‖`
  • the integrand is not proved measurable

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
h g : ℝ → ℝ
hg : Integrable g volume
hc : ContinuousOn (fun x ↦ ‖h x‖) (Ioi 0)
hb : (fun x ↦ ‖h x‖) =O[atTop] fun x ↦ 1
⊢ LocallyIntegrableOn (fun x ↦ h x * g x) (Ioi 0) volume

case nhds0
h g : ℝ → ℝ
hg : Integrable g volume
hc : ContinuousOn (fun x ↦ ‖h x‖) (Ioi 0)
hb : (fun x ↦ ‖h x‖) =O[atTop] fun x ↦ 1
⊢ IntegrableAtFilter (fun x ↦ h x * g x) (𝓝[>] 0) volume

case atTop
h g : ℝ → ℝ
hg : Integrable g volume
hc : ContinuousOn (fun x ↦ ‖h x‖) (Ioi 0)
hb : (fun x ↦ ‖h x‖) =O[atTop] fun x ↦ 1
⊢ IntegrableAtFilter (fun x ↦ h x * g x) atTop volume
-/
#guard_msgs in
example (h g : ℝ → ℝ) (hg : Integrable g) (hc : ContinuousOn (fun x ↦ ‖h x‖) (Ioi 0))
    (hb : (fun x ↦ ‖h x‖) =O[atTop] fun _ ↦ (1 : ℝ)) :
    IntegrableOn (fun x ↦ h x * g x) (Ioi 0) := by
  endpoint_integrability

/-! #### The majorant of the bounded terms

The majorant replaces each bounded term by its bound, and needs the measurability of the
integrand. -/

/--
info: endpoint_integrability does not prove 3 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
case nhds0, case atTop:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 0`
With each bounded term replaced by its bound:
  • the majorant is `fun x ↦ 1 * ‖rexp (-x)‖`
  • the integrand is not proved measurable

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) volume

case nhds0
f : ℝ → ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x)) (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ f x * rexp (-x)) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hb : ∀ x, |f x| ≤ 1) : IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ f x * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- A bounded term under an exponential is not replaced by its bound. -/
/--
info: endpoint_integrability does not prove 3 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioi 0`, by a hypothesis or `fun_prop`
case nhds0, case atTop:
  • no rule bounds `rexp (f t)` as a function of `t`
With each bounded term replaced by its bound:
  • a bounded term occurs in `rexp (f x)`, under a function through which it is not
    replaced by its bound: only products, sums, differences, negations, natural powers and
    numerators of quotients are

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ rexp (f x) * rexp (-x)) (Ioi 0) volume

case nhds0
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ rexp (f x) * rexp (-x)) (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
hf : Measurable f
hb : ∀ (x : ℝ), |f x| ≤ 1
⊢ IntegrableAtFilter (fun x ↦ rexp (f x) * rexp (-x)) atTop volume
-/
#guard_msgs in
example (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntegrableOn (fun x ↦ rexp (f x) * rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/- The majorant `1 * ‖x⁻¹‖` is not integrable at `atTop`: the message gives, under its header, the
piece of the majorant which is not proved. -/
/--
info: endpoint_integrability does not prove 2 integrability goals:
case locallyIntegrableOn:
  • the integrand is not proved continuous on `Ioi 1`, by a hypothesis or `fun_prop`
case atTop:
  • the tactic only bounds the integrand `fun x ↦ Int.fract x / x` from above,
    up to a constant factor, by `fun t ↦ t ^ (-1)`, which is not proved integrable:
    ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`
With each bounded term replaced by its bound:
  • the majorant is `fun x ↦ 1 * ‖x⁻¹‖`
  • case atTop:
    ◦ the majorant `fun x ↦ 1 * ‖x⁻¹‖` has the order of `fun t ↦ t ^ (-1)`,
      which is not proved integrable:
      ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`
  • the majorant is not proved integrable

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case locallyIntegrableOn
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ LocallyIntegrableOn (fun x ↦ Int.fract x / x) (Ioi 1) volume

case atTop
hb : ∀ (x : ℝ), ‖Int.fract x‖ ≤ 1
⊢ IntegrableAtFilter (fun x ↦ Int.fract x / x) atTop volume
-/
#guard_msgs in
example (hb : ∀ x : ℝ, ‖Int.fract x‖ ≤ 1) : IntegrableOn (fun x : ℝ ↦ Int.fract x / x) (Ioi 1) := by
  endpoint_integrability

/-! #### Several pieces

The end `atTop` is proved through the integrable factor `g x`, the cofactor `‖x⁻¹‖` being bounded
there: the message says nothing about it, and explains only the end `𝓝[>] 0`. -/

/--
info: endpoint_integrability does not prove 1 integrability goal:
case nhds0:
  • no asymptotic comparison: the integrand is not proved measurable by `fun_prop`, nor
    continuous on `Ioi 0`
  • `g` is an integrable factor, with the cofactor `fun x ↦ ‖x⁻¹‖`
  • the cofactor `fun x ↦ ‖x⁻¹‖` has the order of `fun t ↦ t ^ (-1)`,
    which is not proved bounded:
    ◦ the power `a = -1` of `t` does not satisfy `0 ≤ a`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhds0
g : ℝ → ℝ
hg : Integrable g volume
⊢ IntegrableAtFilter (fun x ↦ x⁻¹ * g x) (𝓝[>] 0) volume
-/
#guard_msgs in
example (g : ℝ → ℝ) (hg : Integrable g) : IntegrableOn (fun x ↦ x⁻¹ * g x) (Ioi 0) := by
  endpoint_integrability

/-! #### Pointwise operations on functions

The product of functions `f * g` is unfolded: the integrable factor `f` is found, and the message
says that the cofactor `g` is not bounded. A bound of `g` closes the goal. -/

/--
info: endpoint_integrability does not prove 2 integrability goals:
case nhds0, case atTop:
  • no rule bounds `f t` as a function of `t`
  • `f` is an integrable factor, with the cofactor `fun x ↦ ‖g x‖`
  • no rule bounds `g t` as a function of `t`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhds0
f g : ℝ → ℂ
hC : ContinuousOn (fun x ↦ f x * g x) (Ioi 0)
hf : IntegrableOn f (Ioi 0) volume
⊢ IntegrableAtFilter (fun x ↦ f x * g x) (𝓝[>] 0) volume

case atTop
f g : ℝ → ℂ
hC : ContinuousOn (fun x ↦ f x * g x) (Ioi 0)
hf : IntegrableOn f (Ioi 0) volume
⊢ IntegrableAtFilter (fun x ↦ f x * g x) atTop volume
-/
#guard_msgs in
example (f g : ℝ → ℂ) (hC : ContinuousOn (f * g) (Ioi (0 : ℝ)))
    (hf : IntegrableOn f (Ioi (0 : ℝ))) : IntegrableOn (f * g) (Ioi (0 : ℝ)) := by
  endpoint_integrability

example (f g : ℝ → ℂ) (hC : ContinuousOn (f * g) (Ioi (0 : ℝ)))
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (hg : ∀ x, ‖g x‖ ≤ 1) :
    IntegrableOn (f * g) (Ioi (0 : ℝ)) := by
  endpoint_integrability

/-! #### Other routes

An interval integrability goal is reduced to `IntegrableOn f (Ioc a b)`, and explained in the same
way. -/

/--
info: endpoint_integrability does not prove 1 integrability goal:
case nhds0:
  • the integrand `fun x ↦ x⁻¹` has the order of `fun t ↦ t ^ (-1)`,
    which is not proved integrable:
    ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhds0
⊢ IntegrableAtFilter (fun x ↦ x⁻¹) (𝓝[>] 0) volume
-/
#guard_msgs in
example : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 0 1 := by
  endpoint_integrability

/- A goal which leaves a side condition, `-1 < s` at `𝓝[>] 0`, and a piece, at `atTop`: only the
piece is explained. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • no rule bounds `log (1 + t)` as a function of `t`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case nhds0
s : ℝ
⊢ -1 < s

case atTop
s : ℝ
⊢ IntegrableAtFilter (fun x ↦ x ^ s * log (1 + x)) atTop volume
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ s * Real.log (1 + x)) (Ioi 0) := by
  endpoint_integrability

/- With the trace class enabled, the trace messages are kept, after the explanation. -/
/--
info: endpoint_integrability does not prove 1 integrability goal:
case atTop:
  • the integrand `fun x ↦ x⁻¹` has the order of `fun t ↦ t ^ (-1)`,
    which is not proved integrable:
    ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`

This tactic proves integrability by bounding a function by another integrable function at the ends of an interval. To achieve this, it requires some information (e.g. a bound) on all factors.
The tactic can interpret hypotheses such as: `ContinuousOn`, `Continuous`, `Measurable`, `Integrable`, `IntegrableOn`, a bound `∀ x, ‖g x‖ ≤ b x`, and `g =O[l] b` along the filter of an end.

To hide this message: `set_option tactic.endpoint_integrability.explain false`.
---
error: unsolved goals
case atTop
⊢ IntegrableAtFilter (fun x ↦ x⁻¹) atTop volume
---
trace: [Tactic.endpoint_integrability] ✅️ in the middle: the integrand is continuous on `Ici 1`
[Tactic.endpoint_integrability] ❌️ case atTop: not proved
  [Tactic.endpoint_integrability] `t⁻¹` has the order of `t ^ (-1)`
  [Tactic.endpoint_integrability] the integrand `fun x ↦ x⁻¹` has the order of `fun t ↦ t ^ (-1)`,
      which is not proved integrable:
      ◦ the power of `t` is `-1`, and the power `k = 0` of `|log t|` does not satisfy `k < -1`
-/
#guard_msgs in
set_option trace.Tactic.endpoint_integrability true in
example : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioi 1) := by
  endpoint_integrability

/-! #### No message

No message when only side conditions are left, when the goal is closed, or with the option
off. -/

/--
error: unsolved goals
case atTop
s : ℝ
⊢ s < -1
-/
#guard_msgs in
example (s : ℝ) : IntegrableOn (fun x : ℝ ↦ x ^ s) (Ioi 1) := by
  endpoint_integrability

#guard_msgs in
example : IntegrableOn (fun x : ℝ ↦ rexp (-x)) (Ioi 0) := by
  endpoint_integrability

/--
error: unsolved goals
case locallyIntegrableOn
f : ℝ → ℝ
⊢ LocallyIntegrableOn f (Ioi 0) volume

case nhds0
f : ℝ → ℝ
⊢ IntegrableAtFilter f (𝓝[>] 0) volume

case atTop
f : ℝ → ℝ
⊢ IntegrableAtFilter f atTop volume
-/
#guard_msgs in
set_option tactic.endpoint_integrability.explain false in
example (f : ℝ → ℝ) : IntegrableOn f (Ioi 0) := by
  endpoint_integrability

/- An error: no explanation, and no trace message is left behind. -/
/--
error: endpoint_integrability: unsupported set
  {x | 0 < x}
The supported sets are `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Ici a`, `Ioi a`,
`Iic b`, `Iio b` and `univ`.
-/
#guard_msgs (whitespace := lax) in
example : IntegrableOn (fun x : ℝ ↦ x) {x | 0 < x} := by
  endpoint_integrability

end Explanation

/-! ### Failures -/

/--
error: endpoint_integrability: unsupported set
  {x | 0 < x}
The supported sets are `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Ici a`, `Ioi a`,
`Iic b`, `Iio b` and `univ`.
-/
#guard_msgs (whitespace := lax) in
example : IntegrableOn (fun x : ℝ ↦ x) {x | 0 < x} := by
  endpoint_integrability

/--
error: endpoint_integrability: unsupported goal
  HasFiniteIntegral (fun x ↦ x) (volume.restrict (Icc 0 1))
The supported goals are `IntegrableOn f s μ`, `Integrable f (μ.restrict s)`, `Integrable f μ`,
`IntervalIntegrable f μ a b`, `LocallyIntegrableOn f s μ` and `LocallyIntegrable f μ`, for a
function `f : ℝ → E`.
-/
#guard_msgs (whitespace := lax) in
example : HasFiniteIntegral (fun x : ℝ ↦ x) (volume.restrict (Icc 0 1)) := by
  endpoint_integrability

/--
error: endpoint_integrability: failed to prove
  ContinuousOn (fun x ↦ x⁻¹) (uIcc a b)
by `assumption` or `fun_prop`, and failed to prove
  a ≤ b
by the discharger, which is needed to reduce the goal to `IntegrableOn f (Ioc a b) μ`.
-/
#guard_msgs in
example (a b : ℝ) : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume a b := by
  endpoint_integrability

/-! ### Rules registered outside the tactic -/

section Extension

open Lean Meta Asymptotics Mathlib.Tactic.EndpointIntegrability

/-- A function for which the engine has no rule. -/
noncomputable def bump (x : ℝ) : ℝ := rexp (-x)

@[fun_prop]
theorem continuous_bump : Continuous bump := by unfold bump; fun_prop

/-- The order of `bump`, in the form the engine consumes. -/
theorem isTheta_bump_powExp {l : Filter ℝ} (g : ℝ → ℝ) :
    (fun t ↦ bump (g t)) =Θ[l] powExp 0 0 fun t ↦ -g t :=
  isTheta_exp_powExp

/-- The rule for `bump`. -/
@[endpoint_compare bump _]
meta def bumpRule : Rule where
  eval e := do
    let_expr bump g := e | return none
    termResult e (← mkAppOptM ``isTheta_bump_powExp #[← filterExpr, ← lam g])

/- Without `bumpRule`, the goal `IntegrableAtFilter (fun x ↦ bump x / √x) atTop volume` is left;
the end `0` is closed by the continuity of `bump` at `0`. -/
example : IntegrableOn (fun x ↦ bump x / √x) (Ioi 0) := by
  endpoint_integrability

end Extension

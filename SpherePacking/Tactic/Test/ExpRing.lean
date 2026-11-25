/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import SpherePacking.Tactic.ExpRing

/-!
# Tests for the `exp_ring` tactic
-/

public section

open Complex Real

/-! ### Real exponentials -/

example (x y : ℝ) : rexp (x + y) = rexp x * rexp y := by exp_ring
example (x y : ℝ) : rexp (x - y) * rexp y = rexp x := by exp_ring
example (x : ℝ) : rexp (2 * x) = rexp x * rexp x := by exp_ring
example (x : ℝ) : rexp (-x) * rexp (3 * x) = rexp x ^ 2 := by exp_ring
example (a x f : ℝ) : f * rexp (-a * x) * rexp (a * x) = f := by exp_ring
example (x y : ℝ) : rexp (x / 2) * rexp y = rexp (y + x / 2) := by exp_ring
example (x y z : ℝ) : rexp (x * (y + z)) / rexp (x * z) = rexp (x * y) := by exp_ring

-- Exponentials need not be adjacent, and may occur in sums.
example (a b x y : ℝ) : a * rexp x * b * rexp y = a * b * rexp (x + y) := by exp_ring
example (x y : ℝ) : (rexp x + rexp y) ^ 2 = rexp (2 * x) + 2 * rexp (x + y) + rexp (2 * y) := by
  exp_ring

-- From `MagicFunction.a.IntegralEstimates.I₆.Bound_integrableOn`.
example (C r t : ℝ) :
    C * rexp (-(π * (r + 2)) * t) = C * rexp (-2 * π * t) * rexp (-π * r * t) := by
  exp_ring

/-! ### Complex exponentials, including `I ^ 2 = -1` -/

example (x y : ℂ) : cexp (x + y) = cexp x * cexp y := by exp_ring
example (x : ℂ) : cexp (2 * π * I * x) = cexp (π * I * x) ^ 2 := by exp_ring
example (z : ℂ) : cexp (I * (I * z)) = cexp (-z) := by exp_ring
example (z : ℂ) : cexp (I ^ 3 * z) * cexp (I * z) = 1 := by exp_ring

-- From `MagicFunction.a.RadialFunctions.I₂'_eq`.
example (r t : ℂ) : cexp (π * I * r * (-1 + t + I)) =
    cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r) := by
  exp_ring

-- From `MagicFunction.a.RadialFunctions.I₁'_eq`: `I ^ 2 = -1` is needed outside the exponent too.
example (r t : ℝ) (φ : ℂ) : I * φ * (I * t) ^ 2 * cexp (-π * r * (I + t)) =
    -I * φ * t ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
  exp_ring

-- From `MagicFunction.PolyFourierCoeffBound`.
example (c : ℂ) (n n₀ : ℕ) (z : ℂ) :
    c * cexp (π * I * (n + n₀) * z) = cexp (π * I * n₀ * z) * (c * cexp (π * I * n * z)) := by
  exp_ring
example (n₀ : ℕ) (z : ℂ) :
    cexp (π * I * n₀ * z) / cexp (2 * π * I * z) = cexp (π * I * (n₀ - 2) * z) := by
  exp_ring

-- Numeric coefficients are split off as powers, even when the rest of the goal is not closed
-- by the fallback.
example (x t : ℝ) (φ : ℂ → ℂ) :
    cexp (2 * π * I * x) * (-I * φ (-1 / (I * t)) * t ^ 2 * cexp (-π * I * x) * cexp (-π * x * t)) =
      -I * φ (-1 / (I * t)) * t ^ 2 * cexp (π * I * x) * cexp (-π * x * t) := by
  exp_ring

example (x : ℝ) (y : ℂ) (h : cexp (x * I * 3) = y) : cexp (x * I) ^ 3 = y := by
  exp_ring_nf at h
  exact h

/-! ### `exp_ring_nf` -/

example (x y : ℝ) (h : rexp (x + y) = 2) : rexp x * rexp y = 2 := by
  exp_ring_nf at h
  exact h

example (x y : ℝ) (h : rexp x * rexp y ≤ 2) : rexp (x + y) ≤ 2 := by
  exp_ring_nf
  exact h

/-! ### Failure

`exp_ring` is terminal: it fails rather than leaving a normalised goal behind. -/

-- Documented limitation: non-integer coefficients are not split.
example (x : ℝ) : rexp (x / 2) ^ 2 = rexp x := by
  fail_if_success exp_ring
  rw [← Real.exp_nat_mul]; ring_nf

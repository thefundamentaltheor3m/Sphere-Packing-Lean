/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic

/-! # Constructing Upper-Bounds for I₁, I₂, I₃ and I₄

The purpose of this file is to construct bounds on the integrals `I₁`, `I₂`, `I₃` and `I₄` that
make up the function `a`. We follow the proof of Proposition 7.8 in the blueprint.
-/

open MagicFunction Complex Real Set MeasureTheory

-- namespace MagicFunction

noncomputable section I₁

variable (r : ℝ)

/-! We begin by performing changes of variables. -/
#check intervalIntegral.integral_comp_smul_deriv

/- 1. (z + 1) ↦ -1 / (z + 1) -/
private def f : ℝ → ℝ := fun t ↦ 1 / (2 * t)

private def f' : ℝ → ℝ := fun t ↦ -1 / (2 * t ^ 2)

private def g : ℝ → ℝ → ℂ := fun r s ↦
    φ₀'' ((I + 1) * s) * ((I + 1) / (2 * s)) ^ 2 * (-1 / (2 * s)) ^ 2
      * cexp (I * π * r ^ 2 * (1 / (2 * s)) * (I - 1))

private lemma aux_measurable : MeasurableSet ((Ioo 0 1) : Set ℝ) := measurableSet_Ioo

private lemma hasDeriv {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt f (f' x) x := by
  sorry

private lemma injOn : InjOn f (Ioo 0 1) := by
  sorry

end I₁

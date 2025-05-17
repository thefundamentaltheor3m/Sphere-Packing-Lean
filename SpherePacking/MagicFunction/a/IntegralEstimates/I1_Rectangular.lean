/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta

M4R File
-/

import Mathlib

import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic_Rectangular

/-! # Constructing Upper-Bounds for I₁

The purpose of this file is to construct bounds on the integral `I₁` that is part of the definition
of the function `a`. We follow the proof of Proposition 7.8 in the blueprint.
-/

open MagicFunction.a.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function

namespace MagicFunction.a.IntegralEstimates.I1

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. -/
#check intervalIntegral.integral_comp_smul_deriv
-- #check MeasureTheory.integral_image_eq_integral_abs_deriv_smul

def f : ℝ → ℝ := fun t ↦ -1 / t

def f' : ℝ → ℝ := fun t ↦ 1 / t ^ 2

def g : ℝ → ℝ → ℂ := fun r s ↦
  φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (-π * I * r)
  * cexp (I * π * r / s)

end Change_of_Variables

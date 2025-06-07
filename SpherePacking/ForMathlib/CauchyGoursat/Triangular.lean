/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Basic

/-! # Deforming Paths of Integration for Triangular Contours

In this file, we prove that if a function satisfies the Cauchy-Goursat conditions for rectangular
contours, then the integral along the diagonal of the rectangle is equal to the integral along both
pairs of perpendicular sides of the rectangle.
-/

open Set Real Complex Metric Filter

open scoped Interval Topology

namespace Complex

section aux

-- WHY ARE THESE NOT JUST `exact?`????!!!!
theorem re_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).re = x := by simp
theorem im_of_real_add_real_mul_I (x y : ℝ) : (x + y * I).im = y := by simp

end aux

-- variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {x₁ x₂ : ℝ} (y : ℝ)

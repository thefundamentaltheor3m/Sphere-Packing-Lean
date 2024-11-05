/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ModularForms.Eisenstein
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex

noncomputable section Parametrisations

private def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 * t + I * (1 - t)

private def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t -- `by norm_num` also works

-- If there's a function that takes x : ℝ to 0 if x ≤ 0, x if x \in

private def z₂ (t : Icc (0 : ℝ) 1) : ℂ := t + I * (1 - t)

private def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t -- `by norm_num` also works

private def z₃ (t : Icc (0 : ℝ) 1) : ℂ := I * (1 - t)

private def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t -- `by norm_num` also works

private def z₄ (t : NNReal) : ℂ := I * t

private def z₄' (t : ℝ) : ℂ := IciExtend z₄ t -- `by norm_num` also works

end Parametrisations

section UpperHalfPlane

-- Show that the things that go into φ₀ are in the upper half plane

end UpperHalfPlane

noncomputable section Integrals

private noncomputable def I₁ (x : V) := ∫ t in Icc (0 : ℝ) 1, φ₀'' (-1 / ((z₁' t) + (1 : ℂ)))

end Integrals

#min_imports

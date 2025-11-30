/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open SchwartzMap Function RCLike

section SchwartzMap_multidimensional_of_schwartzMap_real

-- Credit to Heather for helping me golf these

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hasFDerivAt_norm_sq {x : F} :
  HasFDerivAt (fun x ↦ ‖x‖ ^ 2) (2 • ((innerSL ℝ) x)) x := (hasFDerivAt_id x).norm_sq

lemma differentiableAt_norm_sq {x : F} :
  DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2) x := hasFDerivAt_norm_sq.differentiableAt

lemma differentiable_norm_sq :
  Differentiable ℝ (fun (x : F) ↦ ‖x‖ ^ 2) := fun _ => differentiableAt_norm_sq

lemma hasTemperateGrowth_norm_sq :
    HasTemperateGrowth (fun (x :F) ↦ ‖x‖ ^ 2) := by
  refine Function.HasTemperateGrowth.of_fderiv ?_ differentiable_norm_sq (k := 2) (C := 1) ?_
  · convert (2 • (innerSL ℝ)).hasTemperateGrowth
    ext
    simp
  · intro x
    rw [norm_pow, norm_norm, one_mul, sq_le_sq, abs_norm, abs_of_nonneg (by positivity)]
    linear_combination

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

@[simps!]
noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ hasTemperateGrowth_norm_sq <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

end SchwartzMap_multidimensional_of_schwartzMap_real

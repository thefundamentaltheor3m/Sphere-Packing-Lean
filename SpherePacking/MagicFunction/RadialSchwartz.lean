import Mathlib

open SchwartzMap Function RCLike

section ForMathlib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hasFDerivAt_norm_sq {x : F} :
  HasFDerivAt (fun x ↦ ‖x‖ ^ 2) (2 • ((innerSL ℝ) x)) x := (hasFDerivAt_id x).norm_sq

lemma differentiableAt_norm_sq {x : F} :
  DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2) x := hasFDerivAt_norm_sq.differentiableAt

lemma differentiable_norm_sq :
  Differentiable ℝ (fun (x : F) ↦ ‖x‖ ^ 2) := fun _ => differentiableAt_norm_sq

lemma fderiv_norm_sq {x : F} :
  fderiv ℝ (fun x ↦ ‖x‖ ^ 2) x = 2 • ((innerSL ℝ) x) := hasFDerivAt_norm_sq.fderiv

lemma hasTemperateGrowth_norm_sq :
    HasTemperateGrowth (fun (x :F) ↦ ‖x‖ ^ 2) := by
  refine Function.HasTemperateGrowth.of_fderiv ?_ differentiable_norm_sq (k := 2) (C := 1) ?_
  · convert (2 • (innerSL ℝ)).hasTemperateGrowth
    ext
    simp [fderiv_norm_sq]
  · intro x
    rw [norm_pow, norm_norm, one_mul, sq_le_sq, abs_norm, abs_of_nonneg (by positivity)]
    linear_combination

end ForMathlib

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

@[simps!]
noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ hasTemperateGrowth_norm_sq <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

#check (schwartzMap_multidimensional_of_schwartzMap_real F f).toFun

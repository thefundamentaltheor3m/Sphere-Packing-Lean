/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Seewoo Lee
-/
module

public import Mathlib

/-! # Radial Schwartz Functions

The plan for this PR is to define a type of Radial Schwartz functions (as a `structure` extending
`SchwartzMap`) and prove some basic properties about the type.

The first goal will be to prove that we have a `StarModule` instance on it, where the `star`
operation will be nothing but the Fourier transform. One key result needed for this is the fact
that the Fourier transform of a radial Schwartz function is radial itself, which can be found in
Appendix A (specifically, (A.23)) of Dan Romik's book *Topics in Complex Analysis*.

The second goal will be to show that we can construct a radial Schwartz function from a smooth,
rapidly decaying function on the nonnegative reals by composing with the norm squared, using this
whole multiplying-by-a-smooth-transition-function trick.
-/

@[expose] public section

section Radial_Functions

variable {E F : Type*}

namespace Function

def IsRadial [Norm E] [Norm F] (f : E → F) : Prop :=
  ∀ {x y : E}, ‖x‖ = ‖y‖ → f x = f y

end Function

section Rotations

-- Do some work on rotations. See here: https://www.math.columbia.edu/~woit/fourier-analysis/higherdimensions.pdf

-- #check ContinuousLinearMap.rotation
-- #check Matrix.orthogonalGroup
-- #check Matrix.specialOrthogonalGroup

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma norm_eq_norm_iff {x y : E} (hfinrank : Module.finrank ℝ E ≠ 1) : ‖x‖ = ‖y‖ ↔ ∃ f : E ≃ₗᵢ[ℝ] E,
    f x = y ∧ f.det = 1 := by
  wlog h_ne_zero : x ≠ 0
  · simp only [ne_eq, not_not] at h_ne_zero
    simp only [h_ne_zero, norm_zero, map_zero, exists_and_left]
    constructor <;> intro h
    · simp only [norm_eq_zero.mp (id h.symm), true_and]
      use LinearIsometryEquiv.refl ℝ E
      sorry
    · exact (norm_eq_zero.mpr (h.1.symm)).symm
  constructor <;> intro h
  · have hy_ne_zero : y ≠ 0 := by
      by_contra hc
      rw [hc, norm_zero] at h
      grind [norm_eq_zero]
    have hspan : (ℝ ∙ y) ≠ ⊤ := fun htop ↦
      hfinrank (by rw [← finrank_span_singleton (K := ℝ) hy_ne_zero, htop, finrank_top])
    obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hspan)
    let u : E := w - (ℝ ∙ y).starProjection w
    refine ⟨((ℝ ∙ u)ᗮ).reflection * ((ℝ ∙ (x - y))ᗮ).reflection, ?_, ?_⟩
    · calc
      _ = ((ℝ ∙ u)ᗮ).reflection y := by
        simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
        exact Submodule.reflection_sub h
      _ = _ := by
        apply Submodule.reflection_mem_subspace_eq_self
        simp [Submodule.mem_orthogonal_singleton_iff_inner_right,
          Submodule.starProjection_inner_eq_zero, u]
    · rw [LinearIsometryEquiv.mul_def]
      simp only [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans,
        Submodule.linearEquiv_det_reflection]
      have (v : E) : Module.finrank ℝ (ℝ ∙ v) = 1 := by
        rw [@finrank_eq_one_iff']
        sorry
      sorry
  · obtain ⟨_, hf, _⟩ := h
    simp [← hf]

#check Submodule.reflection
#check Submodule.starProjection

end Rotations

end Radial_Functions

section RadialSchwartz

open SchwartzMap

@[simps]
def RadialSchwartzMap (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ 𝓢(E, F) where
  carrier := {f | Function.IsRadial f}
  add_mem' := by grind [Function.IsRadial]
  zero_mem' := by simp [Function.IsRadial]
  smul_mem' := by grind [Function.IsRadial]

section fourier

open SchwartzMap Real FourierTransform

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [NormedSpace ℂ F]

lemma radialSchwartzMap_map_le : (RadialSchwartzMap E F).map
    (fourierTransformCLM ℝ (V := E) (E := F)).toLinearMap ≤ RadialSchwartzMap E F := by
  intro f hf x y hxy
  simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe, fourierTransformCLM_apply] at hf
  obtain ⟨g, hg, hg_fourier⟩ := hf
  rw [← hg_fourier, SchwartzMap.fourier_coe, Real.fourier_eq g x, Real.fourier_eq g y]
  congr with v
  congr 1
  sorry

#check FourierTransform.fourier
#check SchwartzMap.instFourierTransform.fourier

end fourier

end RadialSchwartz

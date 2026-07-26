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

namespace Function

variable {E F : Type*}

/-- A function on a space with a norm is *radial* if its value at a point depends only on the norm
of that point. -/
def IsRadial [Norm E] (f : E → F) : Prop :=
  ∀ {x y : E}, ‖x‖ = ‖y‖ → f x = f y

namespace IsRadial

variable [SeminormedAddGroup E] {f : E → F} (hf : f.IsRadial)

include hf in
lemma even : f.Even := fun x ↦ hf (norm_neg x)

end IsRadial

section Isometries

lemma IsRadial.comp_isometry [SeminormedAddGroup E] {f : E → F} (hf : f.IsRadial) {g : E → E}
    (hg : Isometry g) (hg₀ : g 0 = 0) : f ∘ g = f :=
  funext fun x ↦ hf <| hg.norm_map_of_map_zero hg₀ x


lemma isRadial_iff_comp_linearIsometryEquiv [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → F) : f.IsRadial ↔ ∀ g : E ≃ₗᵢ[ℝ] E, f ∘ g = f := by
  refine ⟨fun hf g ↦ hf.comp_isometry g.isometry (by simp), fun h x y hxy ↦ ?_⟩
  specialize h (ℝ ∙ (x - y))ᗮ.reflection
  rw [← Submodule.reflection_sub hxy, ← f.comp_apply (g := (ℝ ∙ (x - y))ᗮ.reflection), h]

end Isometries

end Function

section RadialSchwartz

open Function SchwartzMap

/-- The submodule of radial Schwartz functions inside the Schwartz space `𝓢(E, F)`. -/
@[simps]
def RadialSchwartzMap (𝕜 E F : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
    Submodule 𝕜 𝓢(E, F) where
  carrier := {f | IsRadial f}
  add_mem' := by grind [IsRadial]
  zero_mem' := by simp [IsRadial]
  smul_mem' := by grind [IsRadial]

namespace RadialSchwartzMap

variable {𝕜 E F : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

section NormedSpace

variable [NormedSpace ℝ E]

instance instFunLike : FunLike (RadialSchwartzMap 𝕜 E F) E F where
  coe f := f.1
  coe_injective := DFunLike.coe_injective.comp Subtype.val_injective

@[simp, norm_cast]
lemma coe_coe (f : RadialSchwartzMap 𝕜 E F) : ⇑(f : 𝓢(E, F)) = f := rfl

lemma isRadial (f : RadialSchwartzMap 𝕜 E F) : IsRadial f := f.2

lemma _root_.SchwartzMap.mem_radialSchwartzMap_iff_isRadial (f : 𝓢(E, F)) :
    f ∈ RadialSchwartzMap 𝕜 E F ↔ IsRadial f := .rfl

end NormedSpace

lemma _root_.SchwartzMap.mem_radialSchwartzMap_iff_comp_linearIsometryEquiv
    [InnerProductSpace ℝ E] (f : 𝓢(E, F)) :
    f ∈ RadialSchwartzMap 𝕜 E F ↔ ∀ g : E ≃ₗᵢ[ℝ] E, ⇑f ∘ g = ⇑f :=
  isRadial_iff_comp_linearIsometryEquiv _

end RadialSchwartzMap

noncomputable section Fourier

open Real FourierTransform

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

/-- The Fourier transform of a radial function is radial. -/
lemma Function.IsRadial.fourier {f : E → F} (hf : f.IsRadial) : (𝓕 f).IsRadial := by
  rw [isRadial_iff_comp_linearIsometryEquiv] at hf ⊢
  intro g
  ext x
  rw [Function.comp_apply, ← Real.fourier_comp_linearIsometry g f x, hf g]

variable (𝕜) in
lemma SchwartzMap.fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap {f : 𝓢(E, F)}
    (hf : f ∈ RadialSchwartzMap 𝕜 E F) : 𝓕 f ∈ RadialSchwartzMap 𝕜 E F :=
  SchwartzMap.fourier_coe f ▸ hf.fourier

namespace RadialSchwartzMap

variable (𝕜 E F)

lemma map_fourierTransformCLM_le : (RadialSchwartzMap 𝕜 E F).map
    (SchwartzMap.fourierTransformCLM 𝕜 (V := E) (E := F)).toLinearMap ≤ RadialSchwartzMap 𝕜 E F :=
  Submodule.map_le_iff_le_comap.mpr fun _ ↦ fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

/-- The Fourier transform as a continuous linear map on radial Schwartz functions. -/
def fourierTransformCLM : RadialSchwartzMap 𝕜 E F →L[𝕜] RadialSchwartzMap 𝕜 E F :=
  (SchwartzMap.fourierTransformCLM 𝕜).restrict fun _ ↦
    fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

instance instFourierTransform :
    FourierTransform (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourier := fourierTransformCLM 𝕜 E F

variable {𝕜 E F}

@[simp]
lemma fourierTransformCLM_apply (f : RadialSchwartzMap 𝕜 E F) :
    fourierTransformCLM 𝕜 E F f = 𝓕 f := rfl

@[simp, norm_cast]
lemma coe_fourier (f : RadialSchwartzMap 𝕜 E F) :
    ((𝓕 f : RadialSchwartzMap 𝕜 E F) : 𝓢(E, F)) = 𝓕 (f : 𝓢(E, F)) := rfl

@[simp, norm_cast]
lemma DFunLike.coe_fourier (f : RadialSchwartzMap 𝕜 E F) :
    ((𝓕 f : RadialSchwartzMap 𝕜 E F) : E → F) = 𝓕 (f : E → F) := rfl

section inverse

-- TODO: Prove some fact about radial functions being even, then use this result somehow.
-- TODO: Trim down hypotheses for this result.
lemma _root_.Function.Even.fourierInv {f : E → F} (hf : (𝓕 f).Even) {w : E} :
    𝓕⁻ f w = 𝓕 f w := by
  rw [fourierInv_eq_fourier_neg]
  exact hf w

/-- The inverse Fourier transform of a radial Schwartz function equals its Fourier
transform. -/
lemma _root_.SchwartzMap.fourierInv_eq_fourier_of_isRadial {f : 𝓢(E, F)}
    (hf : f ∈ RadialSchwartzMap 𝕜 E F) : (𝓕⁻ f : 𝓢(E, F)) = 𝓕 f := by
  ext x
  rw [fourierInv_coe, fourier_coe]
  exact Function.Even.fourierInv <| IsRadial.even (hf.fourier)

instance instFourierInv :
    FourierTransformInv (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourierInv := fourierTransformCLM 𝕜 E F



variable [CompleteSpace F] (f : RadialSchwartzMap 𝕜 E F)

/-- The Fourier transform is an involution on radial Schwartz functions. -/
lemma fourierTransformCLM_apply_apply :
    𝓕 (𝓕 f) = f := by
  sorry
  -- Subtype.ext <| by simp [← SchwartzMap.fourierInv_eq_fourier_of_isRadial (isRadial f)]

end inverse

end RadialSchwartzMap

end Fourier

end RadialSchwartz

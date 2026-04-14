/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.ModularForms.FG

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

@[expose] public section

/-! # Complex integrands Φ₁'–Φ₆' are holomorphic on the upper half-plane

In this file, we prove that all the complex integrands Φ₁' through Φ₆' that appear in our integrals
`I₁`-`I₆` are holomorphic on the upper half-plane.

## Main Results

* `Φⱼ'_holo`: For j = 1…6, `Φⱼ'` is Complex-differentiable on the upper half-plane.
* `Φⱼ'_contDiffOn_ℂ`: For j = 1…6, `Φⱼ'` is Complex-smooth on the upper half-plane.
* `Φⱼ'_contDiffOn`: For j = 1…6, `Φⱼ'` is Real-smooth on the upper half-plane.
* `φ₀''_holo`: `φ₀''` is Complex-differentiable on the upper half-plane.
* `φ₀''_differentiable`: `φ₀''` is differentiable on `Set.univ ×ℂ Ioi 0`.
* `φ₀''_continuous`: `φ₀''` is continuous on the upper half-plane.
* `φ₀_continuous`: `φ₀ : ℍ → ℂ` is continuous.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.IntegralEstimates.I₁
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

open Complex Real Set Filter intervalIntegral ContDiff UpperHalfPlane

open scoped Function Manifold

local notation "ℍ₀" => upperHalfPlaneSet

local notation "Holo(" f ")" => DifferentiableOn ℂ f ℍ₀

local notation "MDiff(" f ")" => MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f ℍ₀

section Helpers

namespace UpperHalfPlane

theorem zero_not_mem_upperHalfPlaneSet : (0 : ℂ) ∉ ℍ₀ := by simp

end UpperHalfPlane

end Helpers

namespace MagicFunction.a.ComplexIntegrands

variable {r : ℝ} (hr : r ≥ 0)

section Holo_Lemmas

/-! # Complex Differentiability -/

theorem φ₀''_holo : Holo(φ₀'') := by
  have hF := UpperHalfPlane.mdifferentiable_iff.mp F_holo
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
  have h_eq :
      EqOn φ₀'' (fun z => (F ∘ UpperHalfPlane.ofComplex) z / (Δ ∘ UpperHalfPlane.ofComplex) z) ℍ₀ :=
    fun z hz => by simp [φ₀''_def hz, F, φ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ h_eq
  exact hF.div hΔ fun z hz => by
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Δ_ne_zero]

theorem Φ₁'_holo : Holo(Φ₁' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.add_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · rw [differentiableOn_add_const_iff]
      exact differentiableOn_id
    · intro z hz hcontra
      obtain ⟨hre, him⟩ := Complex.ext_iff.mp hcontra
      simp only [add_im, one_im, add_zero, zero_im] at him
      have : z.im > 0 := hz
      linarith
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 1]) (!![1, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / (z + 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ]
    refine MapsTo.congr ?_ this
    intro _ hz
    rw [mem_setOf_eq, smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) hz) (normSq_denom_pos _ (ne_of_gt hz))

theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ := Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₂'_holo : Holo(Φ₂' r) := Φ₁'_holo

theorem Φ₂'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₂' r) ℍ₀ := Φ₁'_contDiffOn_ℂ

theorem Φ₃'_holo : Holo(Φ₃' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.sub_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · simp only [sub_eq_add_neg, differentiableOn_add_const_iff]
      exact differentiableOn_id
    · intro z hz hcontra
      obtain ⟨hre, him⟩ := Complex.ext_iff.mp hcontra
      simp only [sub_im, one_im, sub_zero, zero_im] at him
      have : z.im > 0 := hz
      linarith
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, -1]) (!![-1, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / (z - 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    refine MapsTo.congr ?_ this
    intro _ hz
    rw [mem_setOf_eq, smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) hz) (normSq_denom_pos _ (ne_of_gt hz))

theorem Φ₃'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₃' r) ℍ₀ := Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₄'_holo : Holo(Φ₄' r) := Φ₃'_holo

theorem Φ₄'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₄' r) ℍ₀ := Φ₃'_contDiffOn_ℂ

theorem Φ₅'_holo : Holo(Φ₅' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| differentiableOn_pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div differentiableOn_id
    intro _ hz
    exact ne_of_mem_of_not_mem hz <| zero_not_mem_upperHalfPlaneSet
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 0]) (!![0, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / z := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    refine MapsTo.congr ?_ this
    intro _ hz
    rw [mem_setOf_eq, smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) hz) (normSq_denom_pos _ (ne_of_gt hz))

theorem Φ₅'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₅' r) ℍ₀ := Φ₅'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₆'_holo : Holo(Φ₆' r) := (φ₀''_holo.comp differentiableOn_id (mapsTo_id _)).mul
  (Complex.differentiable_exp.comp <| (differentiable_const _).mul
    differentiable_fun_id).differentiableOn

theorem Φ₆'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₆' r) ℍ₀ := Φ₆'_holo.contDiffOn isOpen_upperHalfPlaneSet

end Holo_Lemmas

section ContDiffOn_Real

/-! # Real Differentiability -/

theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) ℍ₀ := Φ₁'_contDiffOn_ℂ.restrict_scalars ℝ

theorem Φ₂'_contDiffOn : ContDiffOn ℝ ∞ (Φ₂' r) ℍ₀ := Φ₂'_contDiffOn_ℂ.restrict_scalars ℝ

theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) ℍ₀ := Φ₃'_contDiffOn_ℂ.restrict_scalars ℝ

theorem Φ₄'_contDiffOn : ContDiffOn ℝ ∞ (Φ₄' r) ℍ₀ := Φ₄'_contDiffOn_ℂ.restrict_scalars ℝ

theorem Φ₅'_contDiffOn : ContDiffOn ℝ ∞ (Φ₅' r) ℍ₀ := Φ₅'_contDiffOn_ℂ.restrict_scalars ℝ

theorem Φ₆'_contDiffOn : ContDiffOn ℝ ∞ (Φ₆' r) ℍ₀ := Φ₆'_contDiffOn_ℂ.restrict_scalars ℝ

end ContDiffOn_Real

section Corollaries

/-! # Corollaries using alternative set notation -/

/-- φ₀'' is holomorphic on the upper half-plane (using `Set.univ ×ℂ Ioi 0` notation).
    This is equivalent to `φ₀''_holo` since `Set.univ ×ℂ Ioi 0 = ℍ₀`. -/
theorem φ₀''_differentiable : DifferentiableOn ℂ φ₀'' (Set.univ ×ℂ Ioi 0) := by
  simpa [upperHalfPlaneSet, reProdIm] using φ₀''_holo

/-- φ₀'' is continuous on the upper half-plane. -/
theorem φ₀''_continuous : ContinuousOn φ₀'' (Set.univ ×ℂ Ioi 0) :=
  φ₀''_differentiable.continuousOn

/-- φ₀ : ℍ → ℂ is continuous. Follows from φ₀''_holo. -/
theorem φ₀_continuous : Continuous φ₀ := by
  have h_eq : φ₀ = φ₀'' ∘ (↑· : ℍ → ℂ) := funext fun z => (φ₀''_coe_upperHalfPlane z).symm
  rw [h_eq]
  exact φ₀''_holo.continuousOn.comp_continuous continuous_induced_dom fun z => z.2

end Corollaries

end MagicFunction.a.ComplexIntegrands

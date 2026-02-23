/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.ModularForms.FG.Basic

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import SpherePacking.ModularForms.Derivative

/-! # Complex integrands Φ₁'–Φ₆' are holomorphic on the upper half-plane

In this file, we prove that all the complex integrands Φ₁' through Φ₆' that appear in our integrals
`I₁`-`I₆` are holomorphic on the upper half-plane.

## Main Results:

This file includes the following (families of) theorems:

* [PROVED] `Φⱼ'_holo`: For j = 1…6, `Φⱼ'` is Complex-differentiable on the upper half-plane.
* [PROVED] `Φⱼ'_contDiffOn_ℂ`: For j = 1…6, `Φⱼ'` is Complex-smooth on the upper half-plane.
* [PROVED] `Φⱼ'_contDiffOn`: For j = 1…6, `Φⱼ'` is Real-smooth on the upper half-plane.
* [PROVED] `φ₀''_holo`: `φ₀''` is Complex-differentiable on the upper half-plane.
* [PROVED] `φ₀''_differentiable`: `φ₀''` is differentiable on `Set.univ ×ℂ Ioi 0`.
* [PROVED] `φ₀''_continuous`: `φ₀''` is continuous on `Set.univ ×ℂ Ioi 0`.
-/

open scoped Function Manifold

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

open Complex Real Set Filter intervalIntegral ContDiff UpperHalfPlane

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

private theorem differentiableOn_Delta_ofComplex :
    DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ℍ₀ := by
  refine (UpperHalfPlane.mdifferentiable_iff (f := (Δ : ℍ → ℂ))).1 ?_
  simpa [Delta_apply] using
    (Delta.holo' :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (Delta z : ℂ)))

private theorem Delta_ofComplex_ne_zero : ∀ z ∈ ℍ₀, Δ (UpperHalfPlane.ofComplex z) ≠ 0 := by
  intro z hz
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    Δ_ne_zero (UpperHalfPlane.ofComplex z)

section Holo_Lemmas

private lemma differentiableOn_E₂_E₄_E₆_Delta :
    DifferentiableOn ℂ (E₂ ∘ UpperHalfPlane.ofComplex) ℍ₀ ∧
      DifferentiableOn ℂ ((E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ℍ₀ ∧
        DifferentiableOn ℂ ((E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ℍ₀ ∧
          DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ℍ₀ := by
  refine ⟨(mdifferentiable_iff (f := E₂)).1 E₂_holo', ?_⟩
  refine ⟨(mdifferentiable_iff (f := (E₄ : ℍ → ℂ))).1 E₄.holo', ?_⟩
  exact ⟨(mdifferentiable_iff (f := (E₆ : ℍ → ℂ))).1 E₆.holo', differentiableOn_Delta_ofComplex⟩

private lemma mapsTo_smulAux' (g : GL (Fin 2) ℝ) : MapsTo (UpperHalfPlane.smulAux' g) ℍ₀ ℍ₀ := by
  intro z hz
  simpa [upperHalfPlaneSet, UpperHalfPlane.smulAux] using
    (UpperHalfPlane.smulAux g ⟨z, by simpa [upperHalfPlaneSet] using hz⟩).2

/-! # Complex Differentiability -/

/-- `φ₀''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₀''_holo : Holo(φ₀'') := by
  have hF := UpperHalfPlane.mdifferentiable_iff.mp F_holo
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
  have h_eq :
      EqOn φ₀'' (fun z => (F ∘ UpperHalfPlane.ofComplex) z / (Δ ∘ UpperHalfPlane.ofComplex) z) ℍ₀ :=
    fun z hz => by simp [φ₀''_def hz, F, φ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ h_eq
  exact hF.div hΔ fun z hz => by
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Δ_ne_zero]

/-- `φ₂''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₂''_holo : Holo(φ₂'') := by
  -- As for `φ₀''_holo`, work on `upperHalfPlaneSet` and transfer from the composite with
  -- `UpperHalfPlane.ofComplex`.
  rcases differentiableOn_E₂_E₄_E₆_Delta with ⟨hE₂, hE₄, hE₆, hΔ⟩
  have hNum :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (E₄ (UpperHalfPlane.ofComplex z)) *
            ((E₂ (UpperHalfPlane.ofComplex z)) * (E₄ (UpperHalfPlane.ofComplex z)) -
                E₆ (UpperHalfPlane.ofComplex z)))
        ℍ₀ :=
    hE₄.mul ((hE₂.mul hE₄).sub hE₆)
  have hQuot := hNum.div hΔ Delta_ofComplex_ne_zero
  refine hQuot.congr fun z hz => ?_
  have hz' : 0 < z.im := by simpa [upperHalfPlaneSet] using hz
  simp [φ₂'', φ₂', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- The integrand `Φ₁' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₁'_holo : Holo(Φ₁' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.add_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · exact differentiableOn_id.add_const 1
    · intro z hz h0
      exact (ne_of_gt hz) (by simpa using congrArg Complex.im h0)
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 1]) (!![1, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / (z + 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ]
    exact MapsTo.congr (mapsTo_smulAux' g) this

/-- The integrand `Φ₁' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn_ℂ :
    ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ :=
  Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₂'_holo : Holo(Φ₂' r) := Φ₁'_holo

theorem Φ₂'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₂' r) ℍ₀ := Φ₁'_contDiffOn_ℂ

/-- The integrand `Φ₃' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₃'_holo : Holo(Φ₃' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.sub_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · exact differentiableOn_id.sub_const 1
    · intro z hz h0
      exact (ne_of_gt hz) (by simpa using congrArg Complex.im h0)
  · let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, -1]) (!![-1, 1; -1, 0])
      (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ ℍ₀, UpperHalfPlane.smulAux' g z = -1 / (z - 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    exact MapsTo.congr (mapsTo_smulAux' g) this

/-- The integrand `Φ₃' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn_ℂ :
    ContDiffOn ℂ ∞ (Φ₃' r) ℍ₀ :=
  Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet

theorem Φ₄'_holo : Holo(Φ₄' r) := Φ₃'_holo

theorem Φ₄'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₄' r) ℍ₀ := Φ₃'_contDiffOn_ℂ

/-- The integrand `Φ₅' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₅'_holo : Holo(Φ₅' r) := by
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
    exact MapsTo.congr (mapsTo_smulAux' g) this

/-- The integrand `Φ₅' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₅'_contDiffOn_ℂ :
    ContDiffOn ℂ ∞ (Φ₅' r) ℍ₀ :=
  Φ₅'_holo.contDiffOn isOpen_upperHalfPlaneSet

/-- The integrand `Φ₆' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₆'_holo : Holo(Φ₆' r) := by
  have hExp : DifferentiableOn ℂ (fun z : ℂ => cexp (π * (Complex.I : ℂ) * r * z)) ℍ₀ := by fun_prop
  simpa [Φ₆'] using φ₀''_holo.mul hExp

/-- The integrand `Φ₆' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn_ℂ :
    ContDiffOn ℂ ∞ (Φ₆' r) ℍ₀ :=
  Φ₆'_holo.contDiffOn isOpen_upperHalfPlaneSet

end Holo_Lemmas

section ContDiffOn_Real

/-! ## Real differentiability -/

/-- The integrand `Φ₁' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) ℍ₀ :=
  (Φ₁'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

theorem Φ₂'_contDiffOn : ContDiffOn ℝ ∞ (Φ₂' r) ℍ₀ := Φ₂'_contDiffOn_ℂ.restrict_scalars ℝ

/-- The integrand `Φ₃' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) ℍ₀ :=
  (Φ₃'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

public theorem Φ₄'_contDiffOn : ContDiffOn ℝ ∞ (Φ₄' r) ℍ₀ := Φ₄'_contDiffOn_ℂ.restrict_scalars ℝ

/-- The integrand `Φ₅' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₅'_contDiffOn : ContDiffOn ℝ ∞ (Φ₅' r) ℍ₀ := Φ₅'_contDiffOn_ℂ.restrict_scalars ℝ

/-- The integrand `Φ₆' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn : ContDiffOn ℝ ∞ (Φ₆' r) ℍ₀ :=
  (Φ₆'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

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

end Corollaries

end MagicFunction.a.ComplexIntegrands

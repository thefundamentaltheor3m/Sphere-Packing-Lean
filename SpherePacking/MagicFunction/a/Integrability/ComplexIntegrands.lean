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

/-! # Complex integrands Φ₁'–Φ₆' are holomorphic on the upper half-plane. -/

open scoped Function Manifold
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Complex Real Set Filter intervalIntegral ContDiff UpperHalfPlane

local notation "ℍ₀" => upperHalfPlaneSet
local notation "Holo(" f ")" => DifferentiableOn ℂ f ℍ₀

namespace MagicFunction.a.ComplexIntegrands

variable {r : ℝ}

private theorem differentiableOn_Delta_ofComplex :
    DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) ℍ₀ :=
  (UpperHalfPlane.mdifferentiable_iff (f := (Δ : ℍ → ℂ))).1 <| by
    simpa [Delta_apply] using
      (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (Delta z : ℂ)))

private theorem Delta_ofComplex_ne_zero :
    ∀ z ∈ ℍ₀, Δ (UpperHalfPlane.ofComplex z) ≠ 0 := fun z hz => by
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    Δ_ne_zero (UpperHalfPlane.ofComplex z)

private lemma mapsTo_smulAux' (g : GL (Fin 2) ℝ) :
    MapsTo (UpperHalfPlane.smulAux' g) ℍ₀ ℍ₀ := fun z hz => by
  simpa [upperHalfPlaneSet, UpperHalfPlane.smulAux] using
    (UpperHalfPlane.smulAux g ⟨z, by simpa [upperHalfPlaneSet] using hz⟩).2

/-- `φ₀''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₀''_holo : Holo(φ₀'') := by
  have h_eq :
      EqOn φ₀'' (fun z => (F ∘ UpperHalfPlane.ofComplex) z / (Δ ∘ UpperHalfPlane.ofComplex) z) ℍ₀ :=
    fun z hz => by simp [φ₀''_def hz, F, φ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ h_eq
  exact (UpperHalfPlane.mdifferentiable_iff.mp F_holo).div
    (UpperHalfPlane.mdifferentiable_iff.mp Delta.holo') fun z hz => by
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Δ_ne_zero]

/-- `φ₂''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₂''_holo : Holo(φ₂'') := by
  have hE₄ := (mdifferentiable_iff (f := (E₄ : ℍ → ℂ))).1 E₄.holo'
  refine ((hE₄.mul (((mdifferentiable_iff (f := E₂)).1 E₂_holo').mul hE₄ |>.sub
      ((mdifferentiable_iff (f := (E₆ : ℍ → ℂ))).1 E₆.holo'))).div differentiableOn_Delta_ofComplex
    Delta_ofComplex_ne_zero).congr fun z hz => ?_
  have hz' : 0 < z.im := by simpa [upperHalfPlaneSet] using hz
  simp [φ₂'', φ₂', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- The integrand `Φ₁' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₁'_holo : Holo(Φ₁' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.add_const 1).pow 2
  refine φ₀''_holo.comp ((differentiableOn_const (-1)).div (differentiableOn_id.add_const 1)
    fun z hz h0 => (ne_of_gt hz) (by simpa using congrArg Complex.im h0)) ?_
  let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, 1]) (!![1, 1; -1, 0])
    (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
  exact MapsTo.congr (mapsTo_smulAux' g) fun _ _ ↦ by simp [smulAux', g, num, denom, σ]

/-- The integrand `Φ₁' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) ℍ₀ :=
  Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet

/-- The integrand `Φ₃' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₃'_holo : Holo(Φ₃' r) := by
  refine DifferentiableOn.mul ?_ ((Complex.differentiable_exp.comp <| (differentiable_const _).mul
      differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.sub_const 1).pow 2
  refine φ₀''_holo.comp ((differentiableOn_const (-1)).div (differentiableOn_id.sub_const 1)
    fun z hz h0 => (ne_of_gt hz) (by simpa using congrArg Complex.im h0)) ?_
  let g : GL (Fin 2) ℝ := Units.mk (!![0, -1; 1, -1]) (!![-1, 1; -1, 0])
    (by simp [Matrix.one_fin_two]) (by simp [Matrix.one_fin_two])
  exact MapsTo.congr (mapsTo_smulAux' g) fun _ _ ↦ by
    simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]

/-- The integrand `Φ₃' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₃' r) ℍ₀ :=
  Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet

/-- The integrand `Φ₆' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₆'_holo : Holo(Φ₆' r) := by
  simpa [Φ₆'] using φ₀''_holo.mul
    (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => cexp (π * (Complex.I : ℂ) * r * z)) ℍ₀)

/-- The integrand `Φ₆' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₆' r) ℍ₀ :=
  Φ₆'_holo.contDiffOn isOpen_upperHalfPlaneSet

/-- The integrand `Φ₁' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) ℍ₀ :=
  (Φ₁'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

/-- The integrand `Φ₃' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) ℍ₀ :=
  (Φ₃'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

/-- The integrand `Φ₆' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn : ContDiffOn ℝ ∞ (Φ₆' r) ℍ₀ :=
  (Φ₆'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ

/-- `φ₀''` is differentiable on `Set.univ ×ℂ Ioi 0` (equivalent to `φ₀''_holo`). -/
theorem φ₀''_differentiable : DifferentiableOn ℂ φ₀'' (Set.univ ×ℂ Ioi 0) := by
  simpa [upperHalfPlaneSet, reProdIm] using φ₀''_holo

end MagicFunction.a.ComplexIntegrands

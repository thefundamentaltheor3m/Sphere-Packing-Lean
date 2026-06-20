/-
Copyright (c) 2026 Auguste Poiroux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Auguste Poiroux
-/
module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Fourier transform under an invertible linear change of variables

For a linear automorphism `A` of a finite-dimensional real inner product space `V`, the Fourier
transform of the precomposition `f ∘ A` is the Fourier transform of `f`, rescaled by `|det A|⁻¹`
and reparametrised by the adjoint of `A⁻¹`:
`𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A⁻¹)^* w)`,
together with its inverse-transform companion. The scalar `|det A|⁻¹` is the Jacobian factor and the
adjoint appears because the Fourier pairing `⟪A x, w⟫ = ⟪x, A^* w⟫` moves `A` across the inner
product. This is the full-Jacobian generalisation of mathlib's isometry lemma
`Real.fourier_comp_linearIsometry`, valid for any codomain `E` with `[NormedSpace ℂ E]` over any
`[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]`.

Upstream target: `Mathlib/Analysis/Fourier/FourierTransform.lean`, beside
`Real.fourier_comp_linearIsometry`. Imports here are left as `public import Mathlib`; they are
narrowed at upstreaming time.
-/

open scoped FourierTransform Real
open MeasureTheory

namespace SpherePacking.ForMathlib.Fourier

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Change-of-variables for the Fourier transform under an invertible linear map. For
`A : V ≃ₗ[ℝ] V`, `𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A.symm)^* w)`. -/
public theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → E) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • 𝓕 f (LinearMap.adjoint (A.symm : V →ₗ[ℝ] V) w) := by
  have hmap : Measure.map (⇑A) (volume : Measure V) =
      ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (LinearEquiv.isUnit_det' A).ne_zero
  have hinner (y : V) :
      inner ℝ (A.symm y) w = inner ℝ y (LinearMap.adjoint (A.symm : V →ₗ[ℝ] V) w) :=
    (LinearMap.adjoint_inner_right _ y w).symm
  calc 𝓕 (fun x ↦ f (A x)) w
      = ∫ y, Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y
          ∂Measure.map (⇑A) (volume : Measure V) := by
        simpa [Real.fourier_eq] using
          (integral_map_equiv (μ := (volume : Measure V))
            A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
            fun y ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y).symm
    _ = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ •
          ∫ y, Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
    _ = _ := by simp only [Real.fourier_eq, hinner]

/-- Change-of-variables for the inverse Fourier transform under an invertible linear map; the
inverse-transform companion of `fourier_comp_linearEquiv`. -/
public theorem fourierInv_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → E) (w : V) :
    𝓕⁻ (fun x ↦ f (A x)) w =
      |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • 𝓕⁻ f (LinearMap.adjoint (A.symm : V →ₗ[ℝ] V) w) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_comp_linearEquiv, map_neg,
    ← Real.fourierInv_eq_fourier_neg]

end SpherePacking.ForMathlib.Fourier

/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1
public import SpherePacking.Integration.InvChangeOfVariables
public import SpherePacking.ModularForms.PhiTransform

import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Kernels for `perm_I₅`

We define the phase factor `permI5Phase` and the product kernel `permI5Kernel` used to rewrite
the Fourier transform of `I₅` as an iterated integral. We also record measurability and basic
unfolding lemmas for the functions `I₁`, ..., `I₆`. Includes the change-of-variables rewriting
`I₅' r` as an integral of `I₅.g r` over `Ici 1`.

## Main definitions
* `I₅.g`, `permI5Phase`, `permI5Kernel`

## Main statements
* `I₅.Complete_Change_of_Variables`, `aestronglyMeasurable_perm_I₅_kernel`
-/

namespace MagicFunction.a.IntegralEstimates.I₅

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open SpherePacking.Integration.InvChangeOfVariables

noncomputable section Change_of_Variables

/-- The integrand on `Ici 1` obtained from `I₅'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦
  -I * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * r / s)

/-- Rewrite `I₅' r` as an integral of `g r` over `Ici 1` (up to the factor `-2`). -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₅' r = -2 * ∫ s in Ici (1 : ℝ), g r s := by
  have hRecon : I₅' r = -2 * ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
    simp only [I₅'_eq_Ioc, g]
    congr 1
    refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht ↦ ?_)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r (1 : ℂ)
  refine hRecon.trans ?_
  simpa using congrArg (fun z : ℂ ↦ (-2 : ℂ) * z)
    (integral_Ici_one_eq_integral_abs_deriv_smul (g := g r)).symm

end Change_of_Variables

end MagicFunction.a.IntegralEstimates.I₅

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MeasureTheory Set Complex Real

/-- Continuity of the integrand `I₅.g` on the domain `univ ×ˢ Ici 1`. -/
public lemma continuousOn_I₅_g :
    ContinuousOn
      (fun p : ℝ⁸ × ℝ ↦ MagicFunction.a.IntegralEstimates.I₅.g (‖p.1‖ ^ 2) p.2)
      (univ ×ˢ Ici (1 : ℝ)) := by
  have hφ' : ContinuousOn (fun p : ℝ⁸ × ℝ ↦ φ₀'' (I * (p.2 : ℂ))) (univ ×ˢ Ici (1 : ℝ)) :=
    MagicFunction.a.Schwartz.I1Decay.φ₀''_I_mul_continuousOn.comp continuousOn_snd mapsTo_snd_prod
  have hzpow' : ContinuousOn (fun p : ℝ⁸ × ℝ ↦ (p.2 : ℂ) ^ (-4 : ℤ)) (univ ×ˢ Ici (1 : ℝ)) :=
    MagicFunction.a.Schwartz.I1Decay.zpow_neg_four_continuousOn.comp continuousOn_snd
      mapsTo_snd_prod
  refine ((((continuousOn_const (c := (-I : ℂ))).mul hφ').mul hzpow').mul
      (show ContinuousOn (fun p : ℝ⁸ × ℝ ↦
          cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ))) (univ ×ˢ Ici (1 : ℝ)) from
        fun p hp ↦ by
          have hp2 : (p.2 : ℂ) ≠ 0 := mod_cast (zero_lt_one.trans_le (by simpa using hp)).ne'
          fun_prop (disch := exact hp2))).congr fun p _ ↦ ?_
  simp [MagicFunction.a.IntegralEstimates.I₅.g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The phase factor `v ↦ exp(-2π i ⟪v, w⟫)` used in the kernel for `perm_I₅`. -/
@[expose] public def permI5Phase (w : ℝ⁸) : ℝ⁸ → ℂ :=
  fun v ↦ cexp ((↑(-2 * (π * ⟪v, w⟫)) : ℂ) * I)

/-- The product kernel used to rewrite the Fourier transform of `I₅` as an iterated integral. -/
@[expose] public def permI5Kernel (w : ℝ⁸) : ℝ⁸ × ℝ → ℂ :=
  fun p ↦ permI5Phase w p.1 * MagicFunction.a.IntegralEstimates.I₅.g (‖p.1‖ ^ 2) p.2

/-- Measurability of `permI5Kernel` w.r.t. `volume × (volume.restrict (Ici 1))`. -/
public lemma aestronglyMeasurable_perm_I₅_kernel (w : ℝ⁸) :
    AEStronglyMeasurable
      (permI5Kernel w)
      ((volume : Measure ℝ⁸).prod ((volume : Measure ℝ).restrict (Ici (1 : ℝ)))) := by
  have hphase : Continuous fun p : ℝ⁸ × ℝ ↦ permI5Phase w p.1 := by unfold permI5Phase; fun_prop
  have hkernel : ContinuousOn (permI5Kernel w) (univ ×ˢ Ici (1 : ℝ)) := by
    simpa [permI5Kernel] using hphase.continuousOn.mul continuousOn_I₅_g
  have hμ : (volume : Measure ℝ⁸).prod ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) =
      ((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ)) := by
    simpa [Measure.restrict_univ] using
      Measure.prod_restrict (μ := (volume : Measure ℝ⁸)) (ν := (volume : Measure ℝ))
        (s := univ) (t := Ici (1 : ℝ))
  simpa [hμ] using hkernel.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ici)

/-- Unfolding lemma for `I₅` as a radial function in terms of `I₅'`. -/
public lemma I₅_apply (x : ℝ⁸) :
    (I₅ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) := by simp [I₅]

/-- Unfolding lemma for `I₆` as a radial function in terms of `I₆'`. -/
public lemma I₆_apply (x : ℝ⁸) :
    (I₆ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₆' (‖x‖ ^ 2) := by simp [I₆]

/-- Unfolding lemma for `I₁` as a radial function in terms of `I₁'`. -/
public lemma I₁_apply (x : ℝ⁸) :
    (I₁ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₁' (‖x‖ ^ 2) := by simp [I₁]

/-- Unfolding lemma for `I₂` as a radial function in terms of `I₂'`. -/
public lemma I₂_apply (x : ℝ⁸) :
    (I₂ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₂' (‖x‖ ^ 2) := by simp [I₂]

/-- Unfolding lemma for `I₃` as a radial function in terms of `I₃'`. -/
public lemma I₃_apply (x : ℝ⁸) :
    (I₃ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₃' (‖x‖ ^ 2) := by simp [I₃]

/-- Unfolding lemma for `I₄` as a radial function in terms of `I₄'`. -/
public lemma I₄_apply (x : ℝ⁸) :
    (I₄ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₄' (‖x‖ ^ 2) := by simp [I₄]

end
end MagicFunction.a.Fourier

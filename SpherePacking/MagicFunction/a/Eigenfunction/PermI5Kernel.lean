/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.IntegralEstimates.I5
import SpherePacking.MagicFunction.a.IntegralEstimates.I1
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.MagicFunction.a.Schwartz.DecayI1
public import SpherePacking.ModularForms.PhiTransform
import SpherePacking.ForMathlib.ExpNormSqDiv
import SpherePacking.ForMathlib.GaussianFourierCommon

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
unfolding lemmas for the functions `I₁`, ..., `I₆`.

## Main definitions
* `permI5Phase`
* `permI5Kernel`

## Main statements
* `aestronglyMeasurable_perm_I₅_kernel`
-/


namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI5

open MeasureTheory Set Complex Real

/-- Continuity of the integrand `I₅.g` on the domain `univ ×ˢ Ici 1`. -/
public lemma continuousOn_I₅_g :
    ContinuousOn
      (fun p : ℝ⁸ × ℝ ↦ MagicFunction.a.IntegralEstimates.I₅.g (‖p.1‖ ^ 2) p.2)
      (univ ×ˢ Ici (1 : ℝ)) := by
  have hφ :
      ContinuousOn (fun s : ℝ ↦ φ₀'' (I * (s : ℂ))) (Ici (1 : ℝ)) :=
    MagicFunction.a.Schwartz.I1Decay.φ₀''_I_mul_continuousOn
  have hzpow :
      ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-4 : ℤ)) (Ici (1 : ℝ)) :=
    MagicFunction.a.Schwartz.I1Decay.zpow_neg_four_continuousOn
  have hφ' :
      ContinuousOn (fun p : ℝ⁸ × ℝ ↦ φ₀'' (I * (p.2 : ℂ))) (univ ×ˢ Ici (1 : ℝ)) := by
    refine hφ.comp continuousOn_snd ?_
    intro _ hp
    exact (Set.mem_prod.mp hp).2
  have hzpow' :
      ContinuousOn (fun p : ℝ⁸ × ℝ ↦ (p.2 : ℂ) ^ (-4 : ℤ)) (univ ×ˢ Ici (1 : ℝ)) := by
    refine hzpow.comp continuousOn_snd ?_
    intro _ hp
    exact (Set.mem_prod.mp hp).2
  have hconst : ContinuousOn (fun _ : ℝ⁸ × ℝ ↦ (-I : ℂ)) (univ ×ˢ Ici (1 : ℝ)) :=
    continuousOn_const
  refine
      (((hconst.mul hφ').mul hzpow').mul
            (SpherePacking.ForMathlib.continuousOn_exp_norm_sq_div (E := ℝ⁸))).congr ?_
  intro p hp
  simp [MagicFunction.a.IntegralEstimates.I₅.g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The phase factor `v ↦ exp(-2π i ⟪v, w⟫)` used in the kernel for `perm_I₅`. -/
@[expose] public def permI5Phase (w : ℝ⁸) : ℝ⁸ → ℂ :=
  fun v ↦ cexp ((↑(-2 * (π * ⟪v, w⟫)) : ℂ) * I)

/-- The product kernel used to rewrite the Fourier transform of `I₅` as an iterated integral. -/
@[expose] public def permI5Kernel (w : ℝ⁸) : ℝ⁸ × ℝ → ℂ :=
  fun p =>
    permI5Phase w p.1 * MagicFunction.a.IntegralEstimates.I₅.g (‖p.1‖ ^ 2) p.2

/-- Measurability of `permI5Kernel` with respect to the product measure
`volume × (volume.restrict (Ici 1))`. -/
public lemma aestronglyMeasurable_perm_I₅_kernel (w : ℝ⁸) :
    AEStronglyMeasurable
      (permI5Kernel w)
      ((volume : Measure ℝ⁸).prod ((volume : Measure ℝ).restrict (Ici (1 : ℝ)))) := by
  have hphase :
      ContinuousOn (fun p : ℝ⁸ × ℝ ↦ permI5Phase w p.1) (univ ×ˢ Ici (1 : ℝ)) := by
    have hinner : Continuous fun p : ℝ⁸ × ℝ => (⟪p.1, w⟫ : ℝ) := by
      simpa using (continuous_fst.inner continuous_const)
    have harg :
        Continuous fun p : ℝ⁸ × ℝ =>
            (↑(((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)))) : ℂ) * I :=
      (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.mul hinner))).mul
        continuous_const
    refine (harg.cexp.continuousOn).congr ?_
    intro p hp
    simp [permI5Phase]
  have hkernel : ContinuousOn (permI5Kernel w) (univ ×ˢ Ici (1 : ℝ)) := by
    simpa [permI5Kernel] using (hphase.mul continuousOn_I₅_g)
  have hmeas :
      AEStronglyMeasurable
        (permI5Kernel w)
        (((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    exact ContinuousOn.aestronglyMeasurable hkernel (MeasurableSet.univ.prod measurableSet_Ici)
  have hμ :
      (volume : Measure ℝ⁸).prod ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) =
        (((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    simpa [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ⁸)) (ν := (volume : Measure ℝ))
          (s := (univ : Set ℝ⁸)) (t := Ici (1 : ℝ)))
  simpa [hμ] using hmeas

/-- Unfolding lemma for `I₅` as a radial function in terms of `I₅'`. -/
public lemma I₅_apply (x : ℝ⁸) :
    (I₅ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) := by
  simp [I₅]

/-- Unfolding lemma for `I₆` as a radial function in terms of `I₆'`. -/
public lemma I₆_apply (x : ℝ⁸) :
    (I₆ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₆' (‖x‖ ^ 2) := by
  simp [I₆]

/-- Unfolding lemma for `I₁` as a radial function in terms of `I₁'`. -/
public lemma I₁_apply (x : ℝ⁸) :
    (I₁ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₁' (‖x‖ ^ 2) := by
  simp [I₁]

/-- Unfolding lemma for `I₂` as a radial function in terms of `I₂'`. -/
public lemma I₂_apply (x : ℝ⁸) :
    (I₂ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₂' (‖x‖ ^ 2) := by
  simp [I₂]

/-- Unfolding lemma for `I₃` as a radial function in terms of `I₃'`. -/
public lemma I₃_apply (x : ℝ⁸) :
    (I₃ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₃' (‖x‖ ^ 2) := by
  simp [I₃]

/-- Unfolding lemma for `I₄` as a radial function in terms of `I₄'`. -/
public lemma I₄_apply (x : ℝ⁸) :
    (I₄ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₄' (‖x‖ ^ 2) := by
  simp [I₄]

end Integral_Permutations.PermI5
end
end MagicFunction.a.Fourier

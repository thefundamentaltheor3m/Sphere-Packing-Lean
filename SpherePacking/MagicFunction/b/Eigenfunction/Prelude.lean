/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ5
public import SpherePacking.ModularForms.SlashActionAuxil
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.ExpDecay
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Change of variables for `J₅'`

The `t ↦ 1 / t` substitution rewrites `J₅'` as an integral over `Ici 1`, the form used in the
`J₅`/`J₆` Fourier permutation argument where `s ^ (-4)` and `s ^ 4` cancel.
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

/-- Unfold `Jⱼ` as the primed radial profile `Jⱼ'` evaluated at `‖x‖^2`. -/
public lemma J₃_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₃ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₃' (‖x‖ ^ 2) := by
  simp [J₃]
public lemma J₄_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₄ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₄' (‖x‖ ^ 2) := by
  simp [J₄]
public lemma J₅_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₅ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₅' (‖x‖ ^ 2) := by
  simp [J₅]
public lemma J₆_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₆ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₆' (‖x‖ ^ 2) := by
  simp [J₆]

namespace J5Change

open SpherePacking.Integration.InvChangeOfVariables

def f : ℝ → ℝ := fun t ↦ 1 / t
def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

/-- The integrand appearing after the `t ↦ 1 / t` substitution in `J₅'`. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * ψS' ((Complex.I : ℂ) * (s : ℂ))
  * (s ^ (-4 : ℤ))
  * cexp (-π * r / s)

lemma Reconciling_Change_of_Variables (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1, |f' t| • (g r (f t)) := by
  rw [show MagicFunction.b.RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1,
        (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * r * (z₅' t)) by
    simp [MagicFunction.b.RealIntegrals.J₅', intervalIntegral_eq_integral_uIoc, zero_le_one,
      uIoc_of_le, mul_assoc]]
  congr 1
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using z₅'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht)
  have hψS_inv : ψS' ((Complex.I : ℂ) * (t : ℂ)⁻¹) = ψS.resToImagAxis (t⁻¹) := by
    simpa [one_div] using
      (show ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) = ψS.resToImagAxis (1 / t) by
        simp [ψS', Function.resToImagAxis, ResToImagAxis, one_div, mul_comm])
  have hscalC : (1 / t ^ 2 : ℂ) * ((1 / t : ℝ) ^ (-4 : ℤ) : ℂ) = (t : ℂ) ^ (2 : ℕ) := by
    have : ((1 / t ^ 2) * ((1 / t : ℝ) ^ (-4 : ℤ)) : ℂ) = (t ^ 2 : ℂ) := by
      exact_mod_cast one_div_pow_two_mul_one_div_zpow
        (k := 4) (t := t) (hk := by decide) (ht := ne_of_gt ht.1)
    simpa [Complex.ofReal_mul] using this
  have hexp : cexp (π * (Complex.I : ℂ) * r * (z₅' t)) = cexp (-π * r * t) := by
    simpa [mul_assoc] using congrArg cexp
      (show (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * (z₅' t) = (-π : ℂ) * (r : ℂ) * (t : ℂ) by
        rw [hz5]; ring_nf; rw [Complex.I_sq]; ring)
  rw [show (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * r * (z₅' t)) =
        (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) by
      rw [MagicFunction.b.Schwartz.J5Smooth.ψI'_z₅'_eq t ht, hexp,
        show ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) = (-1 : ℂ) * (t : ℂ) ^ (2 : ℕ) by
          rw [mul_pow]; simp [Complex.I_sq]]
      ring,
    show |f' t| • g r (f t) =
        (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) by
      rw [show |f' t| = 1 / t ^ 2 by simp [f', neg_div, abs_neg]]
      calc (1 / t ^ 2) • g r (f t) = (1 / t ^ 2 : ℂ) * g r (f t) := by simp [real_smul]
        _ = (-I : ℂ) * ψS.resToImagAxis (1 / t) *
              ((1 / t ^ 2 : ℂ) * ((1 / t : ℝ) ^ (-4 : ℤ) : ℂ)) * cexp (-π * r * t) := by
            simp [g, f, hψS_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) := by
            rw [hscalC]]

/-- Change-of-variables formula expressing `J₅'` as an integral over `Ici (1 : ℝ)`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₅' r = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), (g r s) := by
  rw [Reconciling_Change_of_Variables (r := r)]
  simpa [f, f'] using
    congrArg (fun z : ℂ => (-2 : ℂ) * z)
      (integral_Ici_one_eq_integral_abs_deriv_smul (g := g r)).symm

end Integral_Permutations.J5Change
end

end MagicFunction.b.Fourier

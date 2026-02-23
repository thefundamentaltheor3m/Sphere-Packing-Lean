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

This file performs the `t ↦ 1 / t` substitution in the definition of `J₅'`, producing an integral
representation over `Ici 1`. This is the form used in the `J₅`/`J₆` Fourier permutation argument,
where the factors `s ^ (-4)` and `s ^ 4` cancel.

## Main definitions
* `J5Change.g`

## Main statement
* `J5Change.Complete_Change_of_Variables`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

/-- Unfold `J₅` as the primed radial profile `J₅'` evaluated at `‖x‖^2`. -/
public lemma J₅_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₅ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₅' (‖x‖ ^ 2) := by
  simp [J₅]

/-- Unfold `J₆` as the primed radial profile `J₆'` evaluated at `‖x‖^2`. -/
public lemma J₆_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₆ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₆' (‖x‖ ^ 2) := by
  simp [J₆]

/-- Unfold `J₁` as the primed radial profile `J₁'` evaluated at `‖x‖^2`. -/
public lemma J₁_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₁ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₁' (‖x‖ ^ 2) := by
  simp [J₁]

/-- Unfold `J₂` as the primed radial profile `J₂'` evaluated at `‖x‖^2`. -/
public lemma J₂_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₂ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ 2) := by
  simp [J₂]

/-- Unfold `J₃` as the primed radial profile `J₃'` evaluated at `‖x‖^2`. -/
public lemma J₃_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₃ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₃' (‖x‖ ^ 2) := by
  simp [J₃]

/-- Unfold `J₄` as the primed radial profile `J₄'` evaluated at `‖x‖^2`. -/
public lemma J₄_apply (x : EuclideanSpace ℝ (Fin 8)) :
    (J₄ : EuclideanSpace ℝ (Fin 8) → ℂ) x = MagicFunction.b.RealIntegrals.J₄' (‖x‖ ^ 2) := by
  simp [J₄]

namespace J5Change

open SpherePacking.Integration.InvChangeOfVariables


def f : ℝ → ℝ := fun t ↦ 1 / t

def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

/-- The integrand appearing after the `t ↦ 1 / t` substitution in `J₅'`. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * ψS' ((Complex.I : ℂ) * (s : ℂ))
  * (s ^ (-4 : ℤ))
  * cexp (-π * r / s)

lemma J₅'_eq_Ioc (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1,
        (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * r * (z₅' t)) := by
  simp [MagicFunction.b.RealIntegrals.J₅', intervalIntegral_eq_integral_uIoc, zero_le_one,
    uIoc_of_le, mul_assoc]

lemma Reconciling_Change_of_Variables (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1, |f' t| • (g r (f t)) := by
  rw [J₅'_eq_Ioc]
  congr 1
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht_ne0 : t ≠ 0 := ne_of_gt ht0
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using z₅'_eq_of_mem (t := t) htIcc
  have hψI :
      ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) :=
    MagicFunction.b.Schwartz.J5Smooth.ψI'_z₅'_eq t ht
  have hψS : ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) = ψS.resToImagAxis (1 / t) := by
    simp [ψS', Function.resToImagAxis, ResToImagAxis, one_div, mul_comm]
  have hψS_inv : ψS' ((Complex.I : ℂ) * (t : ℂ)⁻¹) = ψS.resToImagAxis (t⁻¹) := by
    simpa [one_div] using hψS
  have habs : |f' t| = 1 / t ^ 2 := by
    simp [f', neg_div, abs_neg]
  have hscal : (1 / t ^ 2) * ((1 / t : ℝ) ^ (-4 : ℤ)) = t ^ 2 := by
    simpa using
      (one_div_pow_two_mul_one_div_zpow (k := 4) (t := t) (hk := by decide) (ht := ht_ne0))
  have hscalC : (1 / t ^ 2 : ℂ) * ((1 / t : ℝ) ^ (-4 : ℤ) : ℂ) = (t : ℂ) ^ (2 : ℕ) := by
    have hscalC0 : ((1 / t ^ 2) * ((1 / t : ℝ) ^ (-4 : ℤ)) : ℂ) = (t ^ 2 : ℂ) := by
      exact_mod_cast hscal
    simpa [Complex.ofReal_mul] using hscalC0
  have hexp : cexp (π * (Complex.I : ℂ) * r * (z₅' t)) = cexp (-π * r * t) := by
    have :
        (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * (z₅' t) =
          (-π : ℂ) * (r : ℂ) * (t : ℂ) := by
      calc
        (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * (z₅' t) =
            (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) := by
              simp [hz5]
        _ = (π : ℂ) * (r : ℂ) * ((Complex.I : ℂ) * (Complex.I : ℂ)) * (t : ℂ) := by
              ring
        _ = (-π : ℂ) * (r : ℂ) * (t : ℂ) := by
              simp [Complex.I_mul_I, mul_left_comm, mul_comm]
    simpa [mul_assoc] using congrArg cexp this
  have hLHS :
      (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * r * (z₅' t)) =
        (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) := by
    have hPow : ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) = (-1 : ℂ) * (t : ℂ) ^ (2 : ℕ) := by
      calc
        ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) =
            ((Complex.I : ℂ) * (t : ℂ)) * ((Complex.I : ℂ) * (t : ℂ)) := by
              simp [pow_two]
        _ = ((Complex.I : ℂ) * (Complex.I : ℂ)) * ((t : ℂ) * (t : ℂ)) := by ac_rfl
        _ = (-1 : ℂ) * ((t : ℂ) * (t : ℂ)) := by simp [Complex.I_mul_I]
        _ = (-1 : ℂ) * (t : ℂ) ^ (2 : ℕ) := by simp [pow_two]
    rw [hψI, hexp, hPow]
    ring
  have hRHS :
      |f' t| • g r (f t) =
        (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) := by
    rw [habs]
    calc
      (1 / t ^ 2) • g r (f t) = (1 / t ^ 2 : ℂ) * g r (f t) := by simp [real_smul]
      _ =
          (-I : ℂ) * ψS.resToImagAxis (1 / t) * ((1 / t ^ 2 : ℂ) * ((1 / t : ℝ) ^ (-4 : ℤ) : ℂ)) *
            cexp (-π * r * t) := by
          simp [g, f, hψS_inv, mul_assoc, mul_left_comm, mul_comm]
      _ =
          (-I : ℂ) * ψS.resToImagAxis (1 / t) * (t : ℂ) ^ (2 : ℕ) * cexp (-π * r * t) := by
          simpa [mul_assoc] using
            congrArg (fun u : ℂ =>
              (-I : ℂ) * ψS.resToImagAxis (1 / t) * u * cexp (-π * r * t)) hscalC
  simp [hLHS, hRHS]

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

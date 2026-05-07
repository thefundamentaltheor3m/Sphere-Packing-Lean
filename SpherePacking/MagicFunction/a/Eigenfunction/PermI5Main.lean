/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Integrability

/-! # Fourier permutation for `I₅` and `I₆`: the identity `𝓕 I₅ = I₆`. -/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open SpherePacking.Integration (μIciOne)

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI5

open MeasureTheory Set Complex Real

/-- Fourier transform of `I₅` is `I₆`. -/
public theorem perm_I₅ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₅ = I₆ := by
  ext w
  simp only [FourierTransform.fourierCLE_apply, I₆_apply]
  change 𝓕 (I₅ : ℝ⁸ → ℂ) w = _
  rw [fourier_eq' (I₅ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₅_apply]
  simp only [show ∀ x : ℝ⁸, MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) =
        -2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s from
      fun x ↦ by simpa only [neg_mul] using
        MagicFunction.a.IntegralEstimates.I₅.Complete_Change_of_Variables (r := ‖x‖ ^ 2),
    mul_assoc]
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  let f : ℝ⁸ → ℝ → ℂ := fun x s => permI5Kernel w (x, s)
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ⁸).prod μs) := by
    simpa only [μIciOne] using integrable_perm_I₅_kernel (w := w)
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ⁸, f x s) =
      (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hfactor :
        (fun x : ℝ⁸ ↦ f x s) =
          fun x : ℝ⁸ ↦
            ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      simp [f, permI5Kernel, permI5Phase, MagicFunction.a.IntegralEstimates.I₅.g]
      ac_rfl
    rw [congrArg (fun F : ℝ⁸ → ℂ => ∫ x, F x) hfactor, integral_const_mul,
      integral_phase_gaussian (w := w) (s := s) hs0,
      ← mul_assoc, mul_assoc (-I * φ₀'' (I * ↑s)) _ _,
      zpow_neg_four_mul_pow_four (s := s) hs0.ne', mul_one]
  have hmain :
      (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)) =
        (-2 : ℂ) * ∫ s in Ici (1 : ℝ),
          (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hrew : (fun x : ℝ⁸ ↦
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)) =
        fun x : ℝ⁸ ↦ (-2 : ℂ) * ∫ s in Ici (1 : ℝ), f x s := by
      funext x
      rw [show (∫ s in Ici (1 : ℝ), f x s) =
            ∫ s in Ici (1 : ℝ), cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s
          from integral_congr_ae <| .of_forall fun _ ↦ by simp [f, permI5Kernel, permI5Phase],
        MeasureTheory.integral_const_mul (μ := μs)]
      ring
    rw [congrArg (fun F : ℝ⁸ → ℂ => ∫ x, F x) hrew, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ⁸)) (ν := μs) (f := f) hint]
    congr 1
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs ↦ ?_)
    simpa [f] using hinner s hs
  rw [hmain, show ((-2 : ℂ) * ∫ s in Ici (1 : ℝ),
            (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) =
          2 * ∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) by
    rw [show ((-2 : ℂ) * ∫ s in Ici (1 : ℝ),
              (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) =
        (-2 : ℂ) * -(∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) by
      congr 1
      rw [← MeasureTheory.integral_neg]
      exact integral_congr_ae <| .of_forall fun _ ↦ by ring]
    ring]
  simp only [neg_mul, mul_comm, mul_neg, mul_assoc,
    MagicFunction.a.RadialFunctions.I₆'_eq, ofReal_pow]

end Integral_Permutations.PermI5
end
end MagicFunction.a.Fourier

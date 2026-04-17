/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Integrability

/-!
# Fourier permutation for `I₅` and `I₆`

We compute the Fourier transform of `I₅` by rewriting it as an iterated integral with
`permI5Kernel` and evaluating the inner Gaussian integral. The result is the identity
`𝓕 I₅ = I₆` at the level of Schwartz maps.

## Main statements
* `perm_I₅`
-/

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
  -- Reduce to the underlying function equality `𝓕 I₅ = I₆`.
  simp only [FourierTransform.fourierCLE_apply, I₆_apply]
  -- Expand the Fourier transform as an integral and rewrite `I₅` using the change of variables.
  change 𝓕 (I₅ : ℝ⁸ → ℂ) w = _
  rw [fourier_eq' (I₅ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₅_apply]
  have hI5' (x : ℝ⁸) :
      MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) =
        -2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
    simpa only [neg_mul] using
      MagicFunction.a.IntegralEstimates.I₅.Complete_Change_of_Variables (r := ‖x‖ ^ 2)
  simp only [hI5', mul_assoc]
  -- Move the `x`-dependent phase factor inside the `s`-integral so we can use Fubini.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hmul :
      (fun x : ℝ⁸ ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s) =
        fun x : ℝ⁸ ↦
          ∫ s in Ici (1 : ℝ),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s :=
    funext fun _ => (integral_const_mul _ _).symm
  -- Apply Fubini to swap the order of integration.
  let f : ℝ⁸ → ℝ → ℂ := fun x s => permI5Kernel w (x, s)
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ⁸).prod μs) := by
    simpa only [μIciOne] using integrable_perm_I₅_kernel (w := w)
  -- Compute the inner integral using the Gaussian Fourier transform.
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)
        =
      (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hcancel : ((s : ℂ) ^ (-4 : ℤ)) * (s ^ 4 : ℂ) = 1 :=
      zpow_neg_four_mul_pow_four (s := s) hs0.ne'
    -- Factor constants from the integral, evaluate the Gaussian Fourier transform, then cancel.
    have hfactor :
        (fun x : ℝ⁸ ↦
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s) =
          fun x : ℝ⁸ ↦
            ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      -- Unfold `g`, turn `s ^ (-4 : ℤ)` into `((s : ℂ) ^ (-4 : ℤ))`, then reassociate/commute.
      simp [MagicFunction.a.IntegralEstimates.I₅.g]
      ac_rfl
    -- Evaluate the inner integral using the Gaussian Fourier transform, then cancel `s^(-4) * s^4`.
    calc
      (∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)
          =
          ∫ x : ℝ⁸,
            ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) :=
            congrArg (fun F : ℝ⁸ → ℂ => ∫ x : ℝ⁸, F x) hfactor
      _ =
          ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
            ∫ x : ℝ⁸,
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s) :=
            integral_const_mul _ _
      _ =
          ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
            ((s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) := by
            rw [integral_phase_gaussian (w := w) (s := s) hs0]
      _ = (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
            rw [← mul_assoc, mul_assoc (-I * φ₀'' (I * ↑s)) _ _, hcancel, mul_one]
  -- Put everything together and match the definition of `I₆'`.
  have hAE :
      (fun s : ℝ ↦ ∫ x : ℝ⁸, f x s) =ᵐ[μs]
        fun s : ℝ ↦ (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    simpa only [f, permI5Kernel, permI5Phase, neg_mul, ofReal_neg, ofReal_mul, ofReal_ofNat] using
      hinner s hs
  have hintEq :
      (∫ s in Ici (1 : ℝ), ∫ x : ℝ⁸, f x s) =
        ∫ s in Ici (1 : ℝ), (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    simpa only [neg_mul] using MeasureTheory.integral_congr_ae hAE
  calc
    (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s))
        =
        (-2 : ℂ) *
          ∫ x : ℝ⁸,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
          simp_rw [mul_left_comm _ (-2 : ℂ)]
          exact integral_const_mul _ _
    _ =
        (-2 : ℂ) *
          ∫ x : ℝ⁸,
            ∫ s in Ici (1 : ℝ),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s :=
          congrArg (fun z : ℂ => (-2 : ℂ) * z)
            (congrArg (fun F : ℝ⁸ → ℂ => ∫ x : ℝ⁸, F x) hmul)
    _ =
        (-2 : ℂ) *
          ∫ x : ℝ⁸, ∫ s in Ici (1 : ℝ), f x s := by
          simp only [neg_mul, ofReal_neg, ofReal_mul, ofReal_ofNat, permI5Kernel, permI5Phase, f]
    _ =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ), ∫ x : ℝ⁸, f x s :=
          congrArg (fun z : ℂ => (-2 : ℂ) * z)
            (MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ⁸))
              (ν := μs) (f := f) hint)
    _ =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ), (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) :=
          congrArg (fun z : ℂ => (-2 : ℂ) * z) hintEq
    _ = 2 * ∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
          simp only [neg_mul]
          rw [MeasureTheory.integral_neg]
          ring
    _ = MagicFunction.a.RealIntegrals.I₆' (‖w‖ ^ 2) := by
          simp only [neg_mul, mul_comm, mul_neg, mul_assoc,
            MagicFunction.a.RadialFunctions.I₆'_eq, ofReal_pow]

end Integral_Permutations.PermI5
end
end MagicFunction.a.Fourier

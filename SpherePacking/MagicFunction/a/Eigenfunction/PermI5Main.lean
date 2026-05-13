/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
public import SpherePacking.ForMathlib.GaussianRexpIntegral
public import SpherePacking.Integration.Measure
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.ForMathlib.IntegrablePowMulExp

/-! # Fourier permutation for `I₅` and `I₆`: the identity `𝓕 I₅ = I₆`. -/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open SpherePacking.ForMathlib SpherePacking.Integration
open MeasureTheory Set Complex Real

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

private instance : MeasureTheory.SFinite μIciOne := by dsimp [μIciOne]; infer_instance

/-- Cancellation lemma for the normalization factor `s ^ (-4)` appearing in `permI5Kernel`. -/
public lemma zpow_neg_four_mul_pow_four (s : ℝ) (hs : s ≠ 0) :
    ((s : ℂ) ^ (-4 : ℤ)) * (s ^ 4 : ℂ) = 1 := by
  simpa using zpow_neg_mul_zpow_self (a := (s : ℂ)) (n := (4 : ℤ)) (mod_cast hs)

private lemma norm_permI5Kernel_le (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) (x : ℝ⁸) :
    ‖permI5Kernel w (x, s)‖ ≤ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) := by
  have hπ' : ‖cexp ((((π * (‖x‖ ^ 2)) : ℝ) : ℂ) * I)‖ = (1 : ℝ) :=
    norm_exp_ofReal_mul_I (π * (‖x‖ ^ 2))
  have hπ : ‖cexp (π * I * (‖x‖ ^ 2))‖ = (1 : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hπ'
  have hnormg :
      ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ =
        ‖MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s‖ := by
    rw [show MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s =
        MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s * cexp (π * I * (‖x‖ ^ 2)) from by
      simp [MagicFunction.a.IntegralEstimates.I₃.g, MagicFunction.a.IntegralEstimates.I₅.g,
        mul_assoc, mul_left_comm, mul_comm], norm_mul, hπ, mul_one]
  refine (show ‖permI5Kernel w (x, s)‖ = ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖
    by simp [permI5Kernel, permI5Phase, norm_exp]).le.trans <| hnormg.le.trans <|
    MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := ‖x‖ ^ 2) s hs

lemma integral_norm_permI5Kernel_bound (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) :
    (∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) ≤ ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  calc (∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖)
      ≤ ∫ x : ℝ⁸, ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) :=
        MeasureTheory.integral_mono_of_nonneg (μ := (volume : Measure ℝ⁸))
          (.of_forall fun _ => norm_nonneg _)
          (by simpa [mul_assoc] using
            (integrable_gaussian_rexp (s := s) hs0).const_mul ‖φ₀'' (I * (s : ℂ))‖)
          (.of_forall (norm_permI5Kernel_le w s hs))
    _ = ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := by
      rw [integral_const_mul, SpherePacking.ForMathlib.integral_gaussian_rexp (s := s) hs0]

lemma integrable_integral_norm_permI5Kernel (w : ℝ⁸) :
    Integrable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) μIciOne := by
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) μIciOne := by
    simpa using ((by simpa [μIciOne] using aestronglyMeasurable_perm_I₅_kernel (w := w) :
      AEStronglyMeasurable (permI5Kernel w) ((volume : Measure ℝ⁸).prod μIciOne)
      ).norm.prod_swap.integral_prod_right'
        (μ := μIciOne) (ν := (volume : Measure ℝ⁸)))
  refine (show Integrable (fun s : ℝ ↦
        (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * s ^ 4 * rexp (-2 * π * s)) μIciOne by
      simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm,
          show ∀ s : ℝ, (-(2 * π) * s) = (-2 * π * s) from fun s => by ring] using
        ((SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 4) (b := (2 * π))
          (by positivity) : IntegrableOn (fun s : ℝ ↦ s ^ 4 * rexp (-(2 * π) * s))
            (Set.Ici (1 : ℝ)) volume)).const_mul
            (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ)).mono' hmeas <|
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => ?_
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)]
  linarith [(integral_norm_permI5Kernel_bound w s hs).trans <|
    mul_le_mul_of_nonneg_right (MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := s) hs)
      (pow_nonneg (le_trans (by norm_num) hs) 4)]

/-- Integrability of `permI5Kernel` on the product measure `volume × μIciOne`. -/
public lemma integrable_perm_I₅_kernel (w : ℝ⁸) :
    Integrable (permI5Kernel w) ((volume : Measure ℝ⁸).prod μIciOne) :=
  (MeasureTheory.integrable_prod_iff' (ν := μIciOne)
    (by simpa [μIciOne] using aestronglyMeasurable_perm_I₅_kernel (w := w))).2
    ⟨(ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => by
      have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
      have hphase : Continuous fun x : ℝ⁸ => permI5Phase w x := by unfold permI5Phase; fun_prop
      have hg : Continuous fun x : ℝ⁸ => MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
        simpa [continuousOn_univ] using continuousOn_I₅_g.comp
          (continuous_id.prodMk continuous_const).continuousOn
          (fun _ _ => ⟨Set.mem_univ _, hs⟩ :
            MapsTo (fun x : ℝ⁸ => (x, s)) (univ : Set ℝ⁸) (univ ×ˢ Ici (1 : ℝ)))
      exact (by simpa [mul_assoc] using
          (integrable_gaussian_rexp (s := s) hs0).const_mul ‖φ₀'' (I * (s : ℂ))‖ :
          Integrable (fun x : ℝ⁸ ↦ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s)) volume).mono'
        (by simpa [permI5Kernel] using hphase.mul hg : Continuous _).aestronglyMeasurable
        (.of_forall (norm_permI5Kernel_le w s hs)),
      integrable_integral_norm_permI5Kernel w⟩

/-- The phase-shifted Gaussian integral used in the computation of `𝓕 I₅`. -/
public lemma integral_phase_gaussian (w : ℝ⁸) (s : ℝ) (hs0 : 0 < s) :
    (∫ x : ℝ⁸, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) =
      (s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  have h := _root_.SpherePacking.ForMathlib.fourier_gaussian_norm_sq_div_even
    (k := 4) (s := s) hs0 (w := w)
  rw [fourier_eq' (fun v : ℝ⁸ ↦ cexp (-π * (‖v‖ ^ 2) / s)) w] at h
  simpa [smul_eq_mul, mul_assoc] using h

section Integral_Permutations

section PermI5

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

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
public import SpherePacking.MagicFunction.a.SpecialValues
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Contour.MobiusInv.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Contour.Segments

/-!
# Prelude for `perm_I₁_I₂` and `perm_I₅`

Defines the Fourier transform permutation for `I₅` (giving `I₆`), bridges `intervalIntegral`
definitions to `curveIntegral` along straight segments, and defines the auxiliary Fourier-side
integrand `Φ₁_fourier`.
-/

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

end PermI5
end Integral_Permutations

section Integral_Permutations

/-- For even Schwartz `f`, applying the Fourier transform twice gives back `f`. -/
public lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) (hf : Function.Even f) :
    FourierTransform.fourierCLE ℂ (SchwartzMap V E)
        (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f) = f := by
  ext x
  simpa [hf x, Real.fourierInv_eq_fourier_neg, neg_neg] using congrFun
    (f.continuous.fourierInv_fourier_eq f.integrable
      (by simpa using (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f).integrable)) (-x)

lemma φ₀''_inv_add_one_mul_sq' (w : ℂ) (hw : 0 < w.im) :
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 *
        (((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹) =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
  have hw0 : w ≠ 0 := fun h => absurd (show w.im = 0 by simp [h]) hw.ne'
  have hw' : 0 < (w - 1).im := by simpa using hw
  have hw1 : w - 1 ≠ 0 := fun h => absurd (show (w - 1).im = 0 by simp [h]) hw'.ne'
  have hzpos : 0 < (-1 / (w - 1)).im := by
    simpa [div_eq_mul_inv, sub_eq_add_neg, Complex.inv_im] using
      div_pos hw' (Complex.normSq_pos.2 hw1)
  have hbase : φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 * w ^ 2 =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
    rw [mul_assoc, show ((-1 / w + 1) ^ 2) * w ^ 2 = (w - 1) ^ 2 by field_simp [hw0]; ring,
      show (-1 / ((-1 / w) + 1) : ℂ) = (-1 / (w - 1)) - 1 by grind only,
      show φ₀'' ((-1 / (w - 1)) - 1) = φ₀'' (-1 / (w - 1)) by
        simpa using (MagicFunction.a.SpecialValues.φ₀''_add_one
          (z := -1 / (w - 1) - 1) (by simpa using hzpos)).symm]
  simpa [show ((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹ = w ^ (2 : ℕ) by
    field_simp; simp [Complex.I_pow_four]] using hbase

section CurveIntegral
open scoped Interval
open Complex MagicFunction.a.ComplexIntegrands SpherePacking.Contour
open MagicFunction.a.RealIntegrands (Φ₁_def Φ₂_def Φ₃_def Φ₄_def)

private lemma uIcc_aux {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht

/-- Rewrite `I₁'` as a curve integral of `Φ₁'` along the segment `-1 → -1 + i`. -/
public lemma I₁'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) (-1 + Complex.I), scalarOneForm (Φ₁' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' r)) (-1 : ℂ) (-1 + Complex.I)]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [Φ₁_def, scalarOneForm_apply,
      (lineMap_z₁line t).trans (z₁'_eq_z₁line t (uIcc_aux ht)).symm]

/-- Rewrite `I₂'` as a curve integral of `Φ₁'` along the segment `-1 + i → i`. -/
public lemma I₂'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Φ₁' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' r)) ((-1 : ℂ) + Complex.I) Complex.I]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [Φ₂_def, scalarOneForm_apply,
      (lineMap_z₂line t).trans (z₂'_eq_z₂line t (uIcc_aux ht)).symm, Φ₂']

/-- `I₃' + I₄'` as a sum of curve integrals of `Φ₃'` along `1 → 1 + i` and `1 + i → i`. -/
public lemma I₃'_add_I₄'_eq_curveIntegral_segments (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₃' r + MagicFunction.a.RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Φ₃' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Φ₃' r) z := by
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₃' r)) (1 : ℂ) ((1 : ℂ) + Complex.I),
    curveIntegral_segment (ω := scalarOneForm (Φ₃' r)) ((1 : ℂ) + Complex.I) Complex.I]
  refine congr_arg₂ _ (intervalIntegral.integral_congr fun t ht => ?_)
    (intervalIntegral.integral_congr fun t ht => ?_)
  · simp [Φ₃_def, scalarOneForm_apply, lineMap_z₃_eq_z₃' (t := t) (uIcc_aux ht)]
  · simp [Φ₄_def, scalarOneForm_apply, lineMap_z₄_eq_z₄' (t := t) (uIcc_aux ht), Φ₄']

/-- If `z` lies in the upper half-plane, then so does `-1 / z` (in terms of imaginary part). -/
public lemma neg_one_div_im_pos (z : ℂ) (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h => absurd (by simp [h] : z.im = 0) hz.ne'
  simpa [div_eq_mul_inv, Complex.inv_im] using div_pos hz (Complex.normSq_pos.2 hz0)

/-- The Fourier-side integrand corresponding to `Φ₁'`, including the Mobius inversion Jacobian. -/
@[expose] public def Φ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 *
    (((Complex.I : ℂ) / z) ^ (4 : ℕ)) *
      cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * (-1 / z))

/-- Modular identity relating `Φ₁_fourier` to `Φ₃'` via `mobiusInv` and its derivative. -/
public lemma Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃' (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z = (deriv SpherePacking.mobiusInv z) * Φ₃' r (SpherePacking.mobiusInv z) := by
  have hz0 : z ≠ 0 := fun h => absurd (show z.im = 0 by simp [h]) hz.ne'
  have hz2 : z ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hz0
  have hφ := φ₀''_inv_add_one_mul_sq' (w := -1 / z) (neg_one_div_im_pos z hz)
  have hrew : (-1 / (-1 / z) : ℂ) = z := by field_simp
  have h₁ : Φ₁_fourier r z = (1 / z ^ (2 : ℕ)) * Φ₃' r (-1 / z) := by
    simp [Φ₁_fourier, Φ₃',
      show φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * (((Complex.I : ℂ) / z) ^ (4 : ℕ)) =
        (1 / z ^ (2 : ℕ)) * (φ₀'' (-1 / ((-1 / z) - 1)) * ((-1 / z) - 1) ^ 2) from by grind only,
      mul_assoc, mul_left_comm, mul_comm]
  simpa [SpherePacking.mobiusInv, SpherePacking.deriv_mobiusInv (z := z), div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm] using h₁

end CurveIntegral

end Integral_Permutations

end
end MagicFunction.a.Fourier

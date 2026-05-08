/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Schwartz.Basic
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Lv1Lv2Identities
import SpherePacking.ModularForms.PhiTransformLemmas
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ForMathlib.SigmaBounds
import SpherePacking.ForMathlib.SigmaSummability
import SpherePacking.ForMathlib.SpecificLimits
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The special value `a 0`

This file proves the explicit special value of the magic function at the origin,
`a 0 = -8640 * I / π` (blueprint Proposition `prop:a0`).

## Main statements
* `φ₀_finite_difference`
* `φ₀''_add_one`
* `a_zero`
-/

namespace MagicFunction.a.SpecialValues

noncomputable section

open Real Complex UpperHalfPlane ModularGroup
open MagicFunction.FourierEigenfunctions RealIntegrals MagicFunction.a.RadialFunctions
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Zero

lemma a_zero_reduction :
    FourierEigenfunctions.a (0 : ℝ⁸) =
      I₁' (0 : ℝ) + I₂' 0 + I₃' 0 + I₄' 0 + I₅' 0 + I₆' 0 := by
  simpa using congrArg (fun f : ℝ⁸ → ℂ => f (0 : ℝ⁸))
    FourierEigenfunctions.a_eq_sum_integrals_RadialFunctions

/-- A second-order finite difference identity for `φ₀` obtained from its modular transformation
under `S`, together with periodicity. -/
public theorem φ₀_finite_difference (z : ℍ) :
    φ₀ (S • ((1 : ℝ) +ᵥ z)) * (((1 : ℝ) +ᵥ z : ℍ) : ℂ) ^ (2 : ℕ)
      - 2 * (φ₀ (S • z) * (z : ℂ) ^ (2 : ℕ))
      + φ₀ (S • ((-1 : ℝ) +ᵥ z)) * (((-1 : ℝ) +ᵥ z : ℍ) : ℂ) ^ (2 : ℕ)
      = 2 * φ₀ z := by
  rw [φ₀_S_transform_mul_sq ((1 : ℝ) +ᵥ z), φ₀_S_transform_mul_sq z,
    φ₀_S_transform_mul_sq ((-1 : ℝ) +ᵥ z)]
  simp [φ₀_periodic, φ₂'_periodic, φ₄'_periodic, φ₀_periodic_neg_one, φ₂'_periodic_neg_one,
    φ₄'_periodic_neg_one, pow_two]; ring_nf

/-! ## Evaluating `a(0)` via the strip contour. -/

section StripContour

open scoped Real Topology Interval BigOperators ArithmeticFunction.sigma
open Filter intervalIntegral

def zI (x : ℝ) : ℂ := (x : ℂ) + Complex.I

@[simp] lemma zI_im (x : ℝ) : (zI x).im = 1 := by simp [zI]

def F (z : ℂ) : ℂ := φ₀'' (-1 / z) * z ^ (2 : ℕ)

private lemma integral_neg_x_add_I_eq_integral_F_zI_sub_one :
    (∫ x in (0 : ℝ)..1,
        φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      ∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  have hrew : (fun x : ℝ =>
        φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      fun x : ℝ => F (zI (1 - x) - 1) :=
    funext fun x => by simp [F, zI, sub_eq_add_neg, add_assoc, add_comm]
  simpa [hrew] using intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => F (zI x - 1)) (a := (0 : ℝ)) (b := (1 : ℝ)) (d := (1 : ℝ))

lemma I₄'_zero :
    I₄' (0 : ℝ) = -∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  rw [show I₄' (0 : ℝ) = ∫ x in (0 : ℝ)..1, (-1 : ℂ) *
      (φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) from by
    simp [MagicFunction.a.RadialFunctions.I₄'_eq, pow_two],
    intervalIntegral.integral_const_mul, integral_neg_x_add_I_eq_integral_F_zI_sub_one]; ring

lemma φ₂''_def (z : ℂ) (hz : 0 < z.im) : φ₂'' z = φ₂' ⟨z, hz⟩ := by simp [φ₂'', hz]
lemma φ₄''_def (z : ℂ) (hz : 0 < z.im) : φ₄'' z = φ₄' ⟨z, hz⟩ := by simp [φ₄'', hz]

lemma F_eq_phi0_phi2_phi4 (z : ℂ) (hz : 0 < z.im) :
    F z =
      φ₀'' z * (z : ℂ) ^ (2 : ℕ) - (12 * Complex.I) / π * (z : ℂ) * φ₂'' z -
        36 / (π ^ 2) * φ₄'' z := by
  let zH : ℍ := ⟨z, hz⟩
  have hφ₀S : φ₀ (ModularGroup.S • zH) = φ₀'' (-1 / z) := by
    rw [← (φ₀''_coe_upperHalfPlane (ModularGroup.S • zH)),
      show ((ModularGroup.S • zH : ℍ) : ℂ) = -1 / (z : ℂ) by
        simpa [zH] using (ModularGroup.coe_S_smul (z := zH))]
  have h' := φ₀_S_transform_mul_sq zH
  rw [hφ₀S] at h'
  simpa [F, zH, φ₀''_def (z := z) hz, φ₂'', φ₄'', hz] using h'

private lemma vadd_neg_one_eq (z : ℂ) (hz : 0 < z.im) (hz1 : 0 < (z - 1).im) :
    ((-1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) : ℍ) = ⟨z - 1, hz1⟩ := by ext1; simp [sub_eq_add_neg, add_comm]

lemma F_sub_one (z : ℂ) (hz : 0 < z.im) :
    F z - F (z - 1) =
      φ₀'' z * ((2 : ℂ) * z - 1) - (12 * Complex.I) / π * φ₂'' z := by
  have hzm : 0 < (z - 1).im := by simpa using hz
  have hφ₀ : φ₀'' (z - 1) = φ₀'' z := by
    rw [φ₀''_def (z := z - 1) hzm, φ₀''_def (z := z) hz,
      ← vadd_neg_one_eq z hz hzm, φ₀_periodic_neg_one]
  have hφ₂ : φ₂'' (z - 1) = φ₂'' z := by
    rw [φ₂''_def (z := z - 1) hzm, φ₂''_def (z := z) hz,
      ← vadd_neg_one_eq z hz hzm, φ₂'_periodic_neg_one]
  have hφ₄ : φ₄'' (z - 1) = φ₄'' z := by
    rw [φ₄''_def (z := z - 1) hzm, φ₄''_def (z := z) hz,
      ← vadd_neg_one_eq z hz hzm, φ₄'_periodic_neg_one]
  simp [F_eq_phi0_phi2_phi4 (z := z) hz, F_eq_phi0_phi2_phi4 (z := z - 1) hzm,
    hφ₀, hφ₂, hφ₄, pow_two]
  ring_nf

lemma I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2 :
    IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 →
    IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 →
    I₂' (0 : ℝ) + I₄' 0 =
      ∫ x in (0 : ℝ)..1,
        (φ₀'' (zI x) * ((2 : ℂ) * (zI x) - 1) - (12 * Complex.I) / π * φ₂'' (zI x))
          ∂MeasureTheory.volume := fun hF hG => by
  have hI2 : I₂' (0 : ℝ) = ∫ x in (0 : ℝ)..1, F (zI x) := by
    simp [F, zI, MagicFunction.a.RadialFunctions.I₂'_eq]
  rw [show I₂' (0 : ℝ) + I₄' 0 =
      ∫ x in (0 : ℝ)..1, (F (zI x) - F (zI x - 1)) ∂MeasureTheory.volume from by
    simpa [hI2, I₄'_zero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) hF hG).symm]
  exact intervalIntegral.integral_congr (μ := MeasureTheory.volume) fun x _ => by
    simpa [zI] using F_sub_one (z := zI x) (by simp [zI])

def f0 (z : ℂ) : ℂ := φ₀'' z * ((2 : ℂ) * z - 1)

lemma f0_differentiableOn : DifferentiableOn ℂ f0 {z : ℂ | 0 < z.im} := by
  simpa [f0] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.mul
    (by fun_prop : Differentiable ℂ fun z : ℂ => (2:ℂ) * z - 1).differentiableOn
lemma f0_continuousOn : ContinuousOn f0 {z : ℂ | 0 < z.im} := f0_differentiableOn.continuousOn

lemma f0_norm_bound_on_strip :
    ∃ C₀ > 0, ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
      ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun {z} hzIm hzRe0 hzRe1 => ?_⟩
  have hzIm_pos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm
  have hφ : ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := by
    simpa [UpperHalfPlane.im, φ₀''_def (z := z) hzIm_pos] using hC₀ ⟨z, hzIm_pos⟩
      (by simpa [UpperHalfPlane.im] using lt_of_lt_of_le (by norm_num) hzIm)
  have hnorm : ‖(2 : ℂ) * z - 1‖ ≤ 2 * z.im + 1 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [show ((2:ℂ) * z - 1).re = 2 * z.re - 1 by simp,
      show ((2:ℂ) * z - 1).im = 2 * z.im by simp,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * z.im)]
    have : |2 * z.re - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  calc ‖f0 z‖
      = ‖φ₀'' z‖ * ‖(2 : ℂ) * z - 1‖ := by simp [f0]
    _ ≤ (C₀ * Real.exp (-2 * π * z.im)) * (2 * z.im + 1) := by gcongr
    _ = C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by ring_nf

private lemma vadd_one_eq (z : ℂ) (hz : 0 < z.im) (hz1 : 0 < (z + 1).im) :
    ((1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) : ℍ) = ⟨z + 1, hz1⟩ := by ext1; simp [add_comm]

/-- Periodicity of `φ₀''` under translation by `1`. -/
public lemma φ₀''_add_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z + 1) = φ₀'' z := by
  rw [φ₀''_def (z := z + 1) (by simpa using hz), φ₀''_def (z := z) hz,
    ← vadd_one_eq z hz (by simpa using hz), φ₀_periodic]

lemma f0_vertical_diff (y : ℝ) (hy : 0 < y) :
    f0 ((1 : ℂ) + (y : ℂ) * Complex.I) - f0 ((y : ℂ) * Complex.I) =
      (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
  simp [f0, show φ₀'' ((1 : ℂ) + (y : ℂ) * Complex.I) = φ₀'' ((y : ℂ) * Complex.I) from by
    simpa [add_assoc, add_comm, add_left_comm] using φ₀''_add_one ((y : ℂ) * Complex.I)
      (by simpa [mul_assoc] using hy)]
  ring

private lemma strip_uIcc_subset {m : ℝ} (hm : 1 ≤ m) :
    (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) ⊆ {z : ℂ | 0 < z.im} := fun _ hz =>
  lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (Set.uIcc_of_le hm ▸ (mem_reProdIm.1 hz).2).1

private lemma strip_Ioo_subset {m : ℝ} :
    (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) ⊆ {z : ℂ | 0 < z.im} :=
  fun _ hz => lt_trans (by norm_num) (mem_reProdIm.1 hz).2.1

lemma rect_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) = 0 := by
  simpa using Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (f := f0) (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I)
    (Hc := by simpa using f0_continuousOn.mono (strip_uIcc_subset hm))
    (Hd := by simpa [hm] using f0_differentiableOn.mono strip_Ioo_subset)

lemma integrableOn_phi0_imag :
    MeasureTheory.IntegrableOn (fun t : ℝ => φ₀'' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨C₀, _, hC₀⟩
  refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => C₀ * Real.exp (-2 * π * t))
    (by simpa [MeasureTheory.IntegrableOn, mul_assoc] using
      (exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (2 * Real.pi))
        (by positivity)).integrable.const_mul C₀)
    (((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
      (continuous_ofReal.mul continuous_const).continuousOn fun t ht => by
        simpa [mul_assoc] using
          (lt_of_lt_of_le (by norm_num) ht.le : (0:ℝ) < t)).aestronglyMeasurable measurableSet_Ioi)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa [mul_assoc] using lt_of_lt_of_le (by norm_num) ht.le⟩
  simpa [zH, UpperHalfPlane.im] using (show ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * zH.im) by
    simpa [φ₀''_coe_upperHalfPlane] using hC₀ zH
      (by simpa [zH, UpperHalfPlane.im] using lt_of_lt_of_le (by norm_num) ht.le))

private lemma norm_integral_f0_strip_le {C₀ : ℝ}
    (hC₀ : ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
              ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im)) :
    ∀ᶠ m : ℝ in atTop,
      ‖∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)‖ ≤
        C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (1 : ℝ)) fun x hx => by
      simpa using hC₀ (z := (x + m * Complex.I : ℂ)) (by simpa using hm)
        (by simpa using le_of_lt (by simpa using hx.1)) (by simpa using hx.2)

private lemma tendsto_two_m_plus_one_mul_exp_decay (C₀ : ℝ) :
    Tendsto (fun m : ℝ => C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m)) atTop (𝓝 (0 : ℝ)) := by
  have hmul : Tendsto (fun m : ℝ => m * Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by
    simpa [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (s := (1 : ℝ)) (b := (2 * Real.pi)) (by positivity)
  have hu : Tendsto (fun m : ℝ => (2 * Real.pi) * m) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hexp : Tendsto (fun m : ℝ => Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by simpa
  have hmain : Tendsto (fun m : ℝ => (2 * m + 1) * Real.exp (-2 * Real.pi * m))
      atTop (𝓝 (0 : ℝ)) := by
    have := (hmul.const_mul 2).add hexp
    simpa using this.congr' (Eventually.of_forall fun m => by ring_nf)
  simpa [mul_assoc] using hmain.const_mul C₀

private lemma intervalIntegrable_f0_vert {m : ℝ} (hm : 1 ≤ m) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => f0 ((x : ℝ) + y * Complex.I)) MeasureTheory.volume 1 m := by
  simpa using (f0_continuousOn.comp
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn)
    (fun y hy => by
      simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        ((Set.uIcc_of_le hm ▸ hy).1))).intervalIntegrable

private lemma integral_f0_vertical_diff_eq {m : ℝ} (hm : 1 ≤ m) :
    (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
        ∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I) =
      ∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
  rw [(integral_sub (intervalIntegrable_f0_vert hm 1) (intervalIntegrable_f0_vert hm 0)).symm]
  exact intervalIntegral.integral_congr (μ := MeasureTheory.volume) fun y hy => by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      f0_vertical_diff y (lt_of_lt_of_le (by norm_num) ((Set.uIcc_of_le hm ▸ hy).1))

lemma strip_identity_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I) := by
  have hVertTerm : Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) =
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) := by
    rw [← smul_sub, integral_f0_vertical_diff_eq hm]
  linear_combination rect_f0 m hm - hVertTerm

private lemma I6_zero_eq_I_smul_integral :
    I₆' (0 : ℝ) =
      Complex.I • (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
        ∂MeasureTheory.volume) := by
  rw [show I₆' (0 : ℝ) = 2 * ∫ t in Set.Ici (1 : ℝ),
      (Complex.I : ℂ) * φ₀'' ((t : ℂ) * Complex.I) ∂MeasureTheory.volume from by
    simp [MagicFunction.a.RadialFunctions.I₆'_eq (r := (0 : ℝ)), mul_comm],
    MeasureTheory.integral_Ici_eq_integral_Ioi]
  simp only [smul_eq_mul, MeasureTheory.integral_const_mul]; ring

lemma integral_f0_height_one_eq_neg_I6 :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) = -I₆' (0 : ℝ) := by
  set J : ℂ := ∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) ∂MeasureTheory.volume
  set bottom : ℂ := ∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)
  have hVert := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := MeasureTheory.volume)
    (f := fun y : ℝ => (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) (a := (1 : ℝ))
    (hfi := by simpa [MeasureTheory.IntegrableOn] using
      integrableOn_phi0_imag.const_mul (2 : ℂ)) (hb := tendsto_id)
  have hA0 : bottom + Complex.I • J = 0 := by
    obtain ⟨C₀, _, hC₀⟩ := f0_norm_bound_on_strip
    exact tendsto_nhds_unique
      ((tendsto_const_nhds.add (tendsto_const_nhds.smul hVert)).congr' <| by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm using strip_identity_f0 m hm)
      (squeeze_zero_norm' (norm_integral_f0_strip_le hC₀)
        (tendsto_two_m_plus_one_mul_exp_decay C₀))
  rw [I6_zero_eq_I_smul_integral]; linear_combination hA0

lemma rect_phi2 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I)) = 0 := by
  simpa using
    (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := φ₂'') (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I)
      (Hc := by
        simpa using MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn.mono
          (strip_uIcc_subset hm))
      (Hd := by
        simpa [hm] using
          (MagicFunction.a.ComplexIntegrands.φ₂''_holo :
              DifferentiableOn ℂ φ₂'' {z : ℂ | 0 < z.im}).mono strip_Ioo_subset))

lemma strip_identity_phi2 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + (1 : ℝ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I) := by
  have hVert : ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I) =
      ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I) :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) fun y hy => by
      have hyim : (0 : ℝ) < ((y : ℂ) * Complex.I).im := by
        simpa [mul_assoc] using
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((Set.uIcc_of_le hm ▸ hy).1)
      have hadd : φ₂'' ((y : ℂ) * Complex.I + 1) = φ₂'' ((y : ℂ) * Complex.I) := by
        rw [φ₂''_def (z := (y : ℂ) * Complex.I + 1) (by simpa using hyim),
          φ₂''_def (z := (y : ℂ) * Complex.I) hyim,
          ← vadd_one_eq ((y : ℂ) * Complex.I) hyim (by simpa using hyim), φ₂'_periodic]
      simpa [add_assoc, add_comm, add_left_comm, mul_assoc] using hadd
  have hrect := rect_phi2 m hm; grind only

lemma summable_coeff_A_over_q :
    Summable (fun n : ℕ =>
      ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) :=
  SpherePacking.ForMathlib.summable_norm_mul_sigma_shift_mul_exp (k := 3) (m := 4) (s := 1)
    fun n => by exact_mod_cast SpherePacking.ForMathlib.sigma_three_le_pow_four (n + 1)

private lemma tsum_pnat_div_q_eq_nat_tsum (z : ℍ) (a : ℕ → ℂ)
    (hrel : ∀ n : ℕ, a n = (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))) :
    (∑' (n : ℕ+),
        ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ))) =
      ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
  rw [show (∑' (n : ℕ+),
        ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ))) =
      ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
            cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ)) from by
    simpa using tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
      ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
        cexp (2 * π * Complex.I * (z : ℂ)))]
  refine tsum_congr fun n => ?_
  rw [show cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) =
      cexp (2 * π * Complex.I * (z : ℂ)) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) from by
    rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring,
      mul_add, mul_one, Complex.exp_add]; ring, hrel]
  field_simp

private lemma A_div_q_eq_nat_tsum (z : ℍ)
    (a : ℕ → ℂ) (hrel : ∀ n : ℕ, a n = (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))) :
    ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z) =
      (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n) := by
  rw [show (E₂ z) * (E₄ z) - (E₆ z) = (720 : ℂ) *
      ∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) from by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ z),
    mul_div_assoc, ← tsum_div_const, tsum_pnat_div_q_eq_nat_tsum z a hrel]

lemma tendsto_A_div_q :
    Tendsto (fun z : ℍ =>
        ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z))
      atImInfty (𝓝 (720 : ℂ)) := by
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using summable_coeff_A_over_q
  refine (tendsto_congr fun z => A_div_q_eq_nat_tsum z a fun _ => rfl).mpr ?_
  simpa [a] using tendsto_const_nhds.mul (QExp.tendsto_nat (a := a) (ha := ha))

private lemma tendsto_Delta_div_q :
    Tendsto (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) atImInfty (𝓝 (1 : ℂ)) := by
  have hrew : (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) =
      fun z : ℍ => ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 :=
    funext fun z => by simp [Δ, div_eq_mul_inv, mul_left_comm, mul_comm]
  simpa [hrew] using (Delta_boundedfactor : Tendsto _ atImInfty (𝓝 (1 : ℂ)))

private lemma tendsto_A_over_Delta :
    Tendsto (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z))
      atImInfty (𝓝 (720 : ℂ)) := by
  have hrew : (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)) =
      fun z : ℍ => (((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z)) /
        ((Δ z) / cexp (2 * π * Complex.I * z)) :=
    funext fun z => by
      field_simp [(by simp : (cexp (2 * π * Complex.I * z) : ℂ) ≠ 0), Δ_ne_zero z]
  rw [hrew]
  simpa using tendsto_A_div_q.div tendsto_Delta_div_q (by norm_num : (1 : ℂ) ≠ 0)

lemma tendsto_top_phi2 :
    Tendsto (fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) atTop (𝓝 (720 : ℂ)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  rcases (UpperHalfPlane.atImInfty_mem _).1
    ((show Tendsto (fun z : ℍ => φ₂' z) atImInfty (𝓝 (720 : ℂ)) by
      simpa [φ₂', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using
        SpherePacking.ModularForms.tendsto_E₄_atImInfty.mul tendsto_A_over_Delta)
      (Metric.ball_mem_nhds (720 : ℂ) (half_pos hε))) with ⟨A, hA⟩
  refine ⟨max A 1, fun m hm => ?_⟩
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hm)
  have hII : IntervalIntegrable (fun x : ℝ => φ₂'' (x + m * Complex.I))
      MeasureTheory.volume 0 1 := by
    simpa using (MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn.comp
      (continuous_ofReal.add continuous_const).continuousOn
      (fun x _ => by simpa [Complex.add_im] using hm0)).intervalIntegrable
  have hsub : (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ) =
      ∫ x : ℝ in (0 : ℝ)..1, (φ₂'' (x + m * Complex.I) - (720 : ℂ)) := by
    simpa using (intervalIntegral.integral_sub (μ := MeasureTheory.volume) hII
      (intervalIntegrable_const (c := (720 : ℂ)))).symm
  have hbound : ∀ x ∈ Ι (0 : ℝ) 1,
      ‖φ₂'' (x + m * Complex.I) - (720 : ℂ)‖ ≤ ε / 2 := fun x _ => by
    let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa using hm0⟩
    simpa [zH, mul_assoc, show φ₂'' ((x : ℂ) + (m : ℂ) * Complex.I) = φ₂' zH from by
      simpa [zH] using (φ₂''_def (z := (x : ℂ) + (m : ℂ) * Complex.I) (by simpa using hm0))]
      using le_of_lt (hA zH (by simpa [zH, UpperHalfPlane.im, Complex.add_im] using
        ((le_max_left _ _).trans hm)))
  simpa [Metric.ball, dist_eq_norm] using lt_of_le_of_lt
    (show ‖(∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ)‖ ≤ ε / 2 by
      simpa [hsub] using
        intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound)
    (half_lt_self hε)

lemma integral_phi2_height_one :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) = (720 : ℂ) := by
  simpa using tendsto_const_nhds_iff.mp (tendsto_top_phi2.congr' <| by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    simpa [zI] using (strip_identity_phi2 m hm).symm)

private lemma intervalIntegrable_F_comp
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1)) (hwim : ∀ x, 0 < (w x).im) :
    IntervalIntegrable (fun x : ℝ => F (w x)) MeasureTheory.volume (0 : ℝ) 1 := by
  have hwne : Set.MapsTo w (Set.uIcc (0 : ℝ) 1) ({0}ᶜ) := fun x _ h0 =>
    (ne_of_gt (hwim x)) (by simpa using congrArg Complex.im h0)
  have hinv : ContinuousOn (fun z : ℂ => (-1 : ℂ) / z) ({0}ᶜ) := by
    convert (continuousOn_const.mul (continuousOn_inv₀ (G₀ := ℂ)) :
      ContinuousOn ((fun _ : ℂ => (-1 : ℂ)) * (Inv.inv : ℂ → ℂ)) ({0}ᶜ)) using 1
  simpa [F] using ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
    (hinv.comp hw hwne) fun x _ => by
      simpa [div_eq_mul_inv] using UpperHalfPlane.im_inv_neg_coe_pos ⟨w x, hwim x⟩).mul
    (by simpa using hw.pow 2)).intervalIntegrable

private lemma intervalIntegrable_comp_zI {g : ℂ → ℂ} (hg : ContinuousOn g {z : ℂ | 0 < z.im}) :
    IntervalIntegrable (fun x : ℝ => g (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
  simpa using (hg.comp (continuous_ofReal.add continuous_const).continuousOn
    fun x _ => by simp).intervalIntegrable

private lemma hI246_eq :
    I₂' (0 : ℝ) + I₄' 0 + I₆' 0 = -8640 * Complex.I / π := by
  have hzI : IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [zI] using intervalIntegrable_F_comp (fun x : ℝ => zI x)
      (continuous_ofReal.add continuous_const).continuousOn fun x => by simp [zI]
  have hzIs : IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      intervalIntegrable_F_comp (fun x : ℝ => zI x - 1)
        ((continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
        fun x => by simp [zI]
  have hI24 := I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2 hzI hzIs
  have hIntf0 : IntervalIntegrable (fun x : ℝ => f0 (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [f0] using intervalIntegrable_comp_zI f0_continuousOn
  have hIntphi2 : IntervalIntegrable (fun x : ℝ => φ₂'' (zI x)) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_comp_zI MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn
  rw [show I₂' (0 : ℝ) + I₄' 0 =
      (∫ x : ℝ in (0 : ℝ)..1, (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) from by
    simpa [f0, zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_left_comm, mul_comm] using hI24,
    show (∫ x : ℝ in (0 : ℝ)..1, (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) =
        (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) -
          ∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x) from by
      simpa using (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
        hIntf0 (hIntphi2.const_mul _)),
    show (∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x)) =
        ((12 : ℂ) * Complex.I) / π * (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) from by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm],
    show (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) = -I₆' (0 : ℝ) by
      simpa [zI] using integral_f0_height_one_eq_neg_I6, integral_phi2_height_one]
  field_simp; ring

end StripContour

/-- The special value at the origin: `a 0 = -8640 * I / π`. -/
public theorem a_zero :
    FourierEigenfunctions.a (0 : ℝ⁸) = -8640 * Complex.I / π := by
  have h135 : (I₁' (0 : ℝ) + I₃' 0 + I₅' 0 : ℂ) = 0 := by
    simp [I₁'_eq, I₃'_eq, I₅'_eq]; ring
  linear_combination a_zero_reduction + h135 + hI246_eq

end Zero

end

end MagicFunction.a.SpecialValues

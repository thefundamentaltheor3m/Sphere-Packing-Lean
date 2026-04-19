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

open Real Complex
open UpperHalfPlane ModularGroup

open MagicFunction.FourierEigenfunctions RealIntegrals
open MagicFunction.a.RadialFunctions
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Zero

/-! At the origin, `a` reduces to the sum of the six defining integrals. -/

lemma a_zero_reduction :
    FourierEigenfunctions.a (0 : ℝ⁸) =
      I₁' (0 : ℝ) + I₂' 0 + I₃' 0 + I₄' 0 + I₅' 0 + I₆' 0 := by
  simpa using
    congrArg (fun f : ℝ⁸ → ℂ => f (0 : ℝ⁸))
      FourierEigenfunctions.a_eq_sum_integrals_RadialFunctions

/-! At `r = 0`, vertical pieces cancel, leaving `I₂' 0`, `I₄' 0`, `I₆' 0`. -/

lemma I₁'_zero_add_I₃'_zero_add_I₅'_zero :
    (I₁' (0 : ℝ) + I₃' 0 + I₅' 0 : ℂ) = 0 := by
  simp [I₁'_eq, I₃'_eq, I₅'_eq]; ring

lemma a_zero_reduction_I₂₄₆ :
    FourierEigenfunctions.a (0 : ℝ⁸) = I₂' (0 : ℝ) + I₄' 0 + I₆' 0 := by
  linear_combination a_zero_reduction + I₁'_zero_add_I₃'_zero_add_I₅'_zero

/--
A second-order finite difference identity for `φ₀` obtained from its modular transformation under
`S`, together with periodicity.
-/
public theorem φ₀_finite_difference (z : ℍ) :
    φ₀ (S • ((1 : ℝ) +ᵥ z)) * (((1 : ℝ) +ᵥ z : ℍ) : ℂ) ^ (2 : ℕ)
      - 2 * (φ₀ (S • z) * (z : ℂ) ^ (2 : ℕ))
      + φ₀ (S • ((-1 : ℝ) +ᵥ z)) * (((-1 : ℝ) +ᵥ z : ℍ) : ℂ) ^ (2 : ℕ)
      = 2 * φ₀ z := by
  rw [φ₀_S_transform_mul_sq ((1 : ℝ) +ᵥ z), φ₀_S_transform_mul_sq z,
    φ₀_S_transform_mul_sq ((-1 : ℝ) +ᵥ z)]
  simp [φ₀_periodic, φ₂'_periodic, φ₄'_periodic,
    φ₀_periodic_neg_one, φ₂'_periodic_neg_one, φ₄'_periodic_neg_one, pow_two]
  ring_nf

/-! ## Evaluating `a(0)` via the strip contour. -/

section StripContour

open scoped Real Topology Interval BigOperators ArithmeticFunction.sigma
open Filter intervalIntegral

def zI (x : ℝ) : ℂ := (x : ℂ) + Complex.I

@[simp] lemma zI_im (x : ℝ) : (zI x).im = 1 := by simp [zI]

def F (z : ℂ) : ℂ := φ₀'' (-1 / z) * z ^ (2 : ℕ)

lemma I₂'_zero :
    I₂' (0 : ℝ) = ∫ x in (0 : ℝ)..1, F (zI x) := by
  -- `I₂' 0` is the horizontal segment integral from `-1+i` to `i`.
  simp [F, zI, MagicFunction.a.RadialFunctions.I₂'_eq]

private lemma integral_neg_x_add_I_eq_integral_F_zI_sub_one :
    (∫ x in (0 : ℝ)..1,
        φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      ∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  have hrew :
      (fun x : ℝ =>
          φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
        fun x : ℝ => F (zI (1 - x) - 1) := by
    funext x
    simp [F, zI, sub_eq_add_neg, add_assoc, add_comm]
  simpa [hrew] using
    (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F (zI x - 1))
      (a := (0 : ℝ)) (b := (1 : ℝ)) (d := (1 : ℝ)))

lemma I₄'_zero :
    I₄' (0 : ℝ) = -∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  have h0 :
      I₄' (0 : ℝ) =
        ∫ x in (0 : ℝ)..1, (-1 : ℂ) *
          (φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) := by
    simp [MagicFunction.a.RadialFunctions.I₄'_eq, pow_two]
  rw [h0, intervalIntegral.integral_const_mul, integral_neg_x_add_I_eq_integral_F_zI_sub_one]
  ring

/-! ### S-transform identity for `F(z) - F(z-1)`. -/

lemma φ₂''_def (z : ℂ) (hz : 0 < z.im) : φ₂'' z = φ₂' ⟨z, hz⟩ := by
  simp [φ₂'', hz]

lemma φ₄''_def (z : ℂ) (hz : 0 < z.im) : φ₄'' z = φ₄' ⟨z, hz⟩ := by
  simp [φ₄'', hz]

lemma F_eq_phi0_phi2_phi4 (z : ℂ) (hz : 0 < z.im) :
    F z =
      φ₀'' z * (z : ℂ) ^ (2 : ℕ) - (12 * Complex.I) / π * (z : ℂ) * φ₂'' z -
        36 / (π ^ 2) * φ₄'' z := by
  let zH : ℍ := ⟨z, hz⟩
  have hSz : ((ModularGroup.S • zH : ℍ) : ℂ) = -1 / (z : ℂ) := by
    simpa [zH] using (ModularGroup.coe_S_smul (z := zH))
  have hφ₀S : φ₀ (ModularGroup.S • zH) = φ₀'' (-1 / z) := by
    rw [← (φ₀''_coe_upperHalfPlane (ModularGroup.S • zH)), hSz]
  have h' := φ₀_S_transform_mul_sq zH
  rw [hφ₀S] at h'
  simpa [F, zH, φ₀''_def (z := z) hz, φ₂'', φ₄'', hz] using h'

private lemma vadd_neg_one_eq (z : ℂ) (hz : 0 < z.im) (hz1 : 0 < (z - 1).im) :
    ((-1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) : ℍ) = ⟨z - 1, hz1⟩ := by
  ext1; simp [sub_eq_add_neg, add_comm]

private lemma φ₀''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z - 1) = φ₀'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  rw [φ₀''_def (z := z - 1) hz1, φ₀''_def (z := z) hz, ← vadd_neg_one_eq z hz hz1,
    φ₀_periodic_neg_one]

private lemma φ₂''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₂'' (z - 1) = φ₂'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  rw [φ₂''_def (z := z - 1) hz1, φ₂''_def (z := z) hz, ← vadd_neg_one_eq z hz hz1,
    φ₂'_periodic_neg_one]

private lemma φ₄''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₄'' (z - 1) = φ₄'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  rw [φ₄''_def (z := z - 1) hz1, φ₄''_def (z := z) hz, ← vadd_neg_one_eq z hz hz1,
    φ₄'_periodic_neg_one]

lemma F_sub_one (z : ℂ) (hz : 0 < z.im) :
    F z - F (z - 1) =
      φ₀'' z * ((2 : ℂ) * z - 1) - (12 * Complex.I) / π * φ₂'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  have hFz := F_eq_phi0_phi2_phi4 (z := z) hz
  have hFzm := F_eq_phi0_phi2_phi4 (z := z - 1) hz1
  simp [hFz, hFzm, φ₀''_sub_one (z := z) hz, φ₂''_sub_one (z := z) hz, φ₄''_sub_one (z := z) hz,
    pow_two]
  ring_nf

/-! ### Rewriting `I₂' 0 + I₄' 0` using `F_sub_one`. -/

lemma I₂'_zero_add_I₄'_zero :
    IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 →
    IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 →
    I₂' (0 : ℝ) + I₄' 0 =
      ∫ x in (0 : ℝ)..1, (F (zI x) - F (zI x - 1)) ∂MeasureTheory.volume := by
  intro hF hG
  simpa [I₂'_zero, I₄'_zero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ => F (zI x)) (g := fun x : ℝ => F (zI x - 1)) hF hG).symm

lemma I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2 :
    IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 →
    IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 →
    I₂' (0 : ℝ) + I₄' 0 =
      ∫ x in (0 : ℝ)..1,
        (φ₀'' (zI x) * ((2 : ℂ) * (zI x) - 1) - (12 * Complex.I) / π * φ₂'' (zI x))
          ∂MeasureTheory.volume := by
  intro hF hG
  rw [I₂'_zero_add_I₄'_zero hF hG]
  refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
  intro x hx
  simpa [zI] using (F_sub_one (z := zI x) (by simp [zI]))

/-! ### Cancelling the `φ₀''` strip integral against `I₆' 0`. -/

def f0 (z : ℂ) : ℂ := φ₀'' z * ((2 : ℂ) * z - 1)

lemma f0_differentiableOn : DifferentiableOn ℂ f0 {z : ℂ | 0 < z.im} := by
  simpa [f0] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.mul
    (by fun_prop : Differentiable ℂ fun z : ℂ => (2 : ℂ) * z - 1).differentiableOn

lemma f0_continuousOn : ContinuousOn f0 {z : ℂ | 0 < z.im} :=
  (f0_differentiableOn).continuousOn

private lemma norm_two_z_sub_one_le_two_im_add_one {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hzIm : 0 ≤ z.im) :
    ‖(2 : ℂ) * z - 1‖ ≤ 2 * z.im + 1 := by
  have hRe : |2 * z.re - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  calc
    ‖(2 : ℂ) * z - 1‖ ≤ |((2 : ℂ) * z - 1).re| + |((2 : ℂ) * z - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
    _ = |2 * z.re - 1| + |2 * z.im| := by simp
    _ ≤ 1 + 2 * z.im := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * z.im)]; linarith
    _ = 2 * z.im + 1 := by ring

lemma f0_norm_bound_on_strip :
    ∃ C₀ > 0, ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
      ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun {z} hzIm hzRe0 hzRe1 => ?_⟩
  have hzIm_pos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm
  have hφ : ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := by
    have hzHalf : (1 / 2 : ℝ) < (⟨z, hzIm_pos⟩ : ℍ).im := by
      simpa [UpperHalfPlane.im] using (lt_of_lt_of_le (by norm_num) hzIm)
    simpa [UpperHalfPlane.im, φ₀''_def (z := z) hzIm_pos] using hC₀ ⟨z, hzIm_pos⟩ hzHalf
  have hlin := norm_two_z_sub_one_le_two_im_add_one hzRe0 hzRe1 hzIm_pos.le
  calc
    ‖f0 z‖ = ‖φ₀'' z‖ * ‖(2 : ℂ) * z - 1‖ := by simp [f0]
    _ ≤ (C₀ * Real.exp (-2 * π * z.im)) * (2 * z.im + 1) := by gcongr
    _ = C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by ring_nf

/-! ### Rectangle identity for `f0` and cancellation with `I₆' 0`. -/

private lemma vadd_one_eq (z : ℂ) (hz : 0 < z.im) (hz1 : 0 < (z + 1).im) :
    ((1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) : ℍ) = ⟨z + 1, hz1⟩ := by
  ext1; simp [add_comm]

/-- Periodicity of `φ₀''` under translation by `1`. -/
public lemma φ₀''_add_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z + 1) = φ₀'' z := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  rw [φ₀''_def (z := z + 1) hz1, φ₀''_def (z := z) hz, ← vadd_one_eq z hz hz1, φ₀_periodic]

lemma f0_vertical_diff (y : ℝ) (hy : 0 < y) :
    f0 ((1 : ℂ) + (y : ℂ) * Complex.I) - f0 ((y : ℂ) * Complex.I) =
      (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
  have hyIm : 0 < (((y : ℂ) * Complex.I) : ℂ).im := by simpa [mul_assoc] using hy
  have hper : φ₀'' ((1 : ℂ) + (y : ℂ) * Complex.I) = φ₀'' ((y : ℂ) * Complex.I) := by
    simpa [add_assoc, add_comm, add_left_comm] using φ₀''_add_one (z := (y : ℂ) * Complex.I) hyIm
  simp [f0, hper]; ring

private lemma strip_uIcc_subset {m : ℝ} (hm : 1 ≤ m) :
    (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (Set.uIcc_of_le hm ▸ (mem_reProdIm.1 hz).2).1

private lemma strip_Ioo_subset {m : ℝ} :
    (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) ⊆ {z : ℂ | 0 < z.im} :=
  fun z hz => lt_trans (by norm_num) (mem_reProdIm.1 hz).2.1

lemma rect_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) = 0 := by
  simpa using
    (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := f0) (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I)
      (Hc := by simpa using f0_continuousOn.mono (strip_uIcc_subset hm))
      (Hd := by simpa [hm] using f0_differentiableOn.mono strip_Ioo_subset))

private lemma norm_phi0_imag_le {C₀ : ℝ}
    (hC₀ : ∀ z : ℍ, (1/2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    {t : ℝ} (ht : t ∈ Set.Ioi (1 : ℝ)) :
    ‖φ₀'' ((t : ℂ) * Complex.I)‖ ≤ C₀ * Real.exp (-2 * π * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa [mul_assoc] using ht0⟩
  have htHalf : (1 / 2 : ℝ) < zH.im := by
    simpa [zH, UpperHalfPlane.im] using (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
  have hφ0 : ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * zH.im) := by
    simpa [φ₀''_coe_upperHalfPlane] using hC₀ zH htHalf
  simpa [zH, UpperHalfPlane.im] using hφ0

private lemma integrable_const_mul_exp_on_Ioi (C₀ : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => C₀ * Real.exp (-2 * π * t))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hExp : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-2 * π * t)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
    simpa [mul_assoc] using
      exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (2 * Real.pi)) (by positivity)
  simpa [MeasureTheory.IntegrableOn, mul_assoc] using hExp.integrable.const_mul C₀

private lemma aestronglyMeasurable_phi0_imag :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => φ₀'' ((t : ℂ) * Complex.I))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
  ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
      (continuous_ofReal.mul continuous_const).continuousOn
      (fun t ht => by
        simpa [mul_assoc] using
          (lt_of_lt_of_le (by norm_num) (le_of_lt ht) :
            (0 : ℝ) < t))).aestronglyMeasurable measurableSet_Ioi

lemma integrableOn_phi0_imag :
    MeasureTheory.IntegrableOn (fun t : ℝ => φ₀'' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨C₀, _, hC₀⟩
  refine MeasureTheory.Integrable.mono' (integrable_const_mul_exp_on_Ioi C₀)
    aestronglyMeasurable_phi0_imag
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_)
  intro t ht
  simpa using norm_phi0_imag_le hC₀ ht

lemma integrableOn_two_mul_phi0_imag :
    MeasureTheory.IntegrableOn (fun t : ℝ => (2 : ℂ) * φ₀'' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  simpa [MeasureTheory.IntegrableOn] using (integrableOn_phi0_imag.const_mul (2 : ℂ))

private lemma norm_integral_f0_strip_le {C₀ : ℝ}
    (hC₀ : ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
              ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im)) :
    ∀ᶠ m : ℝ in atTop,
      ‖∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)‖ ≤
        C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
  have hC : ∀ x ∈ Ι (0 : ℝ) 1, ‖f0 (x + m * Complex.I)‖ ≤
        C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m) := fun x hx => by
    simpa using hC₀ (z := (x + m * Complex.I : ℂ))
      (by simpa using hm) (by simpa using le_of_lt (by simpa using hx.1))
      (by simpa using hx.2)
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun x : ℝ => f0 (x + m * Complex.I)) hC

private lemma tendsto_two_m_plus_one_mul_exp_decay (C₀ : ℝ) :
    Tendsto (fun m : ℝ => C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m)) atTop (𝓝 (0 : ℝ)) := by
  have hmul : Tendsto (fun m : ℝ => m * Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by
    simpa [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (1 : ℝ)) (b := (2 * Real.pi))
        (by positivity)
  have hu : Tendsto (fun m : ℝ => (2 * Real.pi) * m) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hexp : Tendsto (fun m : ℝ => Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by simpa
  have hmain :
      Tendsto (fun m : ℝ => (2 * m + 1) * Real.exp (-2 * Real.pi * m)) atTop (𝓝 (0 : ℝ)) := by
    have := (hmul.const_mul 2).add hexp
    simp only [mul_zero, add_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by ring_nf)
  simpa [mul_assoc] using hmain.const_mul C₀

lemma tendsto_top_f0 :
    Tendsto (fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) atTop (𝓝 (0 : ℂ)) := by
  rcases f0_norm_bound_on_strip with ⟨C₀, _, hC₀⟩
  exact squeeze_zero_norm' (norm_integral_f0_strip_le hC₀) (tendsto_two_m_plus_one_mul_exp_decay C₀)

private lemma intervalIntegrable_f0_vert {m : ℝ} (hm : 1 ≤ m) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => f0 ((x : ℝ) + y * Complex.I)) MeasureTheory.volume 1 m := by
  have hconty : ContinuousOn (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) (Set.uIcc (1 : ℝ) m) :=
    (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
  have hmaps :
      Set.MapsTo (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) (Set.uIcc (1 : ℝ) m)
        {z : ℂ | 0 < z.im} := by
    intro y hy
    have hy1 : (1 : ℝ) ≤ y := (Set.uIcc_of_le hm ▸ hy).1
    simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy1
  simpa using (f0_continuousOn.comp hconty hmaps).intervalIntegrable

private lemma integral_f0_vertical_diff_eq {m : ℝ} (hm : 1 ≤ m) :
    (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
        ∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I) =
      ∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
  rw [(integral_sub (intervalIntegrable_f0_vert hm 1) (intervalIntegrable_f0_vert hm 0)).symm]
  refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) (fun y hy => ?_)
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num)
    ((Set.uIcc_of_le hm ▸ hy).1)
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (f0_vertical_diff y hy0)

lemma strip_identity_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I) := by
  have hrect := rect_f0 m hm
  have hVertTerm :
      Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) =
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) := by
    rw [← smul_sub, integral_f0_vertical_diff_eq hm]
  linear_combination hrect - hVertTerm

private lemma I6_zero_eq_I_smul_integral :
    I₆' (0 : ℝ) =
      Complex.I • (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
        ∂MeasureTheory.volume) := by
  have h0' :
      I₆' (0 : ℝ) =
        2 * ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * φ₀'' ((t : ℂ) * Complex.I)
          ∂MeasureTheory.volume := by
    simp [MagicFunction.a.RadialFunctions.I₆'_eq (r := (0 : ℝ)), mul_comm]
  rw [h0', MeasureTheory.integral_Ici_eq_integral_Ioi]
  simp only [smul_eq_mul, MeasureTheory.integral_const_mul]; ring

lemma integral_f0_height_one_eq_neg_I6 :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) = -I₆' (0 : ℝ) := by
  set J : ℂ := ∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) ∂MeasureTheory.volume
  set bottom : ℂ := ∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)
  have hVert := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := MeasureTheory.volume)
    (f := fun y : ℝ => (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) (a := (1 : ℝ))
    (hfi := integrableOn_two_mul_phi0_imag) (hb := tendsto_id)
  have hEq : (fun m : ℝ => bottom + Complex.I •
      (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I))) =ᶠ[atTop]
      fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm using strip_identity_f0 m hm
  have hA0 : bottom + Complex.I • J = 0 :=
    tendsto_nhds_unique
      ((tendsto_const_nhds.add (tendsto_const_nhds.smul hVert)).congr' hEq) tendsto_top_f0
  rw [I6_zero_eq_I_smul_integral]; linear_combination hA0

/-! ### Evaluating the remaining `φ₂''` term. -/

lemma φ₂''_add_one (z : ℂ) (hz : 0 < z.im) : φ₂'' (z + 1) = φ₂'' z := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  rw [φ₂''_def (z := z + 1) hz1, φ₂''_def (z := z) hz, ← vadd_one_eq z hz hz1, φ₂'_periodic]

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
  have hrect := rect_phi2 m hm
  have hVert :
      ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I) =
        ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro y hy
    have hy1 : (1 : ℝ) ≤ y := (Set.uIcc_of_le hm ▸ hy).1
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
    have hyIm : 0 < (((y : ℂ) * Complex.I) : ℂ).im := by simpa [mul_assoc] using hy0
    simpa [add_assoc, add_comm, add_left_comm, mul_assoc] using
      φ₂''_add_one (z := (y : ℂ) * Complex.I) hyIm
  grind only

lemma summable_coeff_A_over_q :
    Summable (fun n : ℕ =>
      ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) := by
  refine
    SpherePacking.ForMathlib.summable_norm_mul_sigma_shift_mul_exp (k := 3) (m := 4) (s := 1) ?_
  intro n
  exact_mod_cast (SpherePacking.ForMathlib.sigma_three_le_pow_four (n + 1))

private lemma cexp_pnat_succ_factor (z : ℂ) (n : ℕ) :
    cexp (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) =
      cexp (2 * π * Complex.I * z) * cexp (2 * π * Complex.I * z * (n : ℂ)) := by
  rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring, mul_add, mul_one, Complex.exp_add]
  ring

private lemma tsum_pnat_div_q_eq_nat_tsum (z : ℍ) (a : ℕ → ℂ)
    (hrel : ∀ n : ℕ, a n = (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))) :
    (∑' (n : ℕ+),
        ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
          cexp (2 * π * Complex.I * (z : ℂ))) =
      ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
  have hpnat :
      (∑' (n : ℕ+),
          ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
            cexp (2 * π * Complex.I * (z : ℂ))) =
        ∑' n : ℕ,
          (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ) *
                cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) /
            cexp (2 * π * Complex.I * (z : ℂ)) := by
    simpa using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ =>
          ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
            cexp (2 * π * Complex.I * (z : ℂ))))
  rw [hpnat]
  refine tsum_congr fun n => ?_
  rw [cexp_pnat_succ_factor, hrel]
  field_simp

private lemma A_div_q_eq_nat_tsum (z : ℍ)
    (a : ℕ → ℂ) (hrel : ∀ n : ℕ, a n = (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))) :
    ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z) =
      (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n) := by
  have hA :
      (E₂ z) * (E₄ z) - (E₆ z) =
        (720 : ℂ) *
          ∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ z)
  rw [hA, mul_div_assoc, ← tsum_div_const, tsum_pnat_div_q_eq_nat_tsum z a hrel]

lemma tendsto_A_div_q :
    Tendsto (fun z : ℍ =>
        ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z))
      atImInfty (𝓝 (720 : ℂ)) := by
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using summable_coeff_A_over_q
  have hseries'' :
      Tendsto (fun z : ℍ => (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (720 : ℂ)) := by
    simpa [a] using (tendsto_const_nhds.mul (QExp.tendsto_nat (a := a) (ha := ha)))
  exact (tendsto_congr (fun z => A_div_q_eq_nat_tsum z a (fun _ => rfl))).mpr hseries''

private lemma tendsto_Delta_div_q :
    Tendsto (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) atImInfty (𝓝 (1 : ℂ)) := by
  have hrew :
      (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) =
        fun z : ℍ => ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 := by
    funext z
    simp [Δ, div_eq_mul_inv, mul_left_comm, mul_comm]
  simpa [hrew] using (Delta_boundedfactor : Tendsto _ atImInfty (𝓝 (1 : ℂ)))

private lemma tendsto_A_over_Delta :
    Tendsto (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z))
      atImInfty (𝓝 (720 : ℂ)) := by
  have hq_ne : ∀ z : ℍ, (cexp (2 * π * Complex.I * z) : ℂ) ≠ 0 := fun _ => by simp
  have hrew :
      (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)) =
        fun z : ℍ =>
          (((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z)) /
            ((Δ z) / cexp (2 * π * Complex.I * z)) := by
    funext z; field_simp [hq_ne z, Δ_ne_zero z]
  rw [hrew]
  simpa using tendsto_A_div_q.div tendsto_Delta_div_q (by norm_num : (1 : ℂ) ≠ 0)

lemma tendsto_phi2'_atImInfty :
    Tendsto (fun z : ℍ => φ₂' z) atImInfty (𝓝 (720 : ℂ)) := by
  have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₄_atImInfty
  simpa [φ₂', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using
    hE4.mul tendsto_A_over_Delta

private lemma norm_phi2_strip_bound_le {ε : ℝ} {A m : ℝ}
    (hA : ∀ z : ℍ, A ≤ z.im → ‖φ₂' z - (720 : ℂ)‖ < ε / 2) (hmA : A ≤ m) (hm0 : 0 < m) :
    ∀ x ∈ Ι (0 : ℝ) 1, ‖φ₂'' (x + m * Complex.I) - (720 : ℂ)‖ ≤ ε / 2 := fun x _ => by
  let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa using hm0⟩
  have hdef : φ₂'' ((x : ℂ) + (m : ℂ) * Complex.I) = φ₂' zH := by
    simpa [zH] using (φ₂''_def (z := (x : ℂ) + (m : ℂ) * Complex.I) (by simpa using hm0))
  simpa [zH, hdef, mul_assoc] using le_of_lt (hA zH
    (by simpa [zH, UpperHalfPlane.im, Complex.add_im] using hmA))

private lemma intervalIntegrable_phi2_strip {m : ℝ} (hm : 0 < m) :
    IntervalIntegrable (fun x : ℝ => φ₂'' (x + m * Complex.I)) MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (fun x : ℝ => φ₂'' (x + m * Complex.I)) (Set.uIcc (0 : ℝ) 1) :=
    MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn.comp
      (continuous_ofReal.add continuous_const).continuousOn
      (fun x _ => by simpa [Complex.add_im] using hm)
  simpa using hcont.intervalIntegrable

private lemma integral_phi2_sub_720 {m : ℝ} (hm : 0 < m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ) =
      ∫ x : ℝ in (0 : ℝ)..1, (φ₂'' (x + m * Complex.I) - (720 : ℂ)) := by
  simpa using
    (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun x : ℝ => φ₂'' (x + m * Complex.I)) (g := fun _x : ℝ => (720 : ℂ))
      (intervalIntegrable_phi2_strip hm) intervalIntegrable_const).symm

lemma tendsto_top_phi2 :
    Tendsto (fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) atTop (𝓝 (720 : ℂ)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  rcases (UpperHalfPlane.atImInfty_mem _).1
    (tendsto_phi2'_atImInfty (Metric.ball_mem_nhds (720 : ℂ) (half_pos hε))) with ⟨A, hA⟩
  refine ⟨max A 1, fun m hm => ?_⟩
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hm)
  have hbound := norm_phi2_strip_bound_le hA (le_trans (le_max_left _ _) hm) hm0
  have hle : ‖(∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ)‖ ≤ ε / 2 := by
    simpa [integral_phi2_sub_720 hm0] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound
  simpa [Metric.ball, dist_eq_norm] using lt_of_le_of_lt hle (half_lt_self hε)

lemma integral_phi2_height_one :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) = (720 : ℂ) := by
  have hEq :
      (fun _m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) =ᶠ[atTop]
        fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    simpa [zI] using strip_identity_phi2 m hm
  simpa using tendsto_const_nhds_iff.mp (tendsto_top_phi2.congr' hEq.symm)

private lemma intervalIntegrable_F_comp
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1)) (hwim : ∀ x, 0 < (w x).im) :
    IntervalIntegrable (fun x : ℝ => F (w x)) MeasureTheory.volume (0 : ℝ) 1 := by
  have hwne : Set.MapsTo w (Set.uIcc (0 : ℝ) 1) ({0}ᶜ) := fun x _ h0 =>
    (ne_of_gt (hwim x)) (by simpa using congrArg Complex.im h0)
  have hinv : ContinuousOn (fun z : ℂ => (-1 : ℂ) / z) ({0}ᶜ) := by
    have h : ContinuousOn ((fun _ : ℂ => (-1 : ℂ)) * (Inv.inv : ℂ → ℂ)) ({0}ᶜ) :=
      continuousOn_const.mul (continuousOn_inv₀ (G₀ := ℂ))
    convert h using 1
  have himap :
      Set.MapsTo (fun x : ℝ => (-1 : ℂ) / (w x)) (Set.uIcc (0 : ℝ) 1) {z : ℂ | 0 < z.im} :=
    fun x _ => by
      simpa [div_eq_mul_inv] using UpperHalfPlane.im_inv_neg_coe_pos ⟨w x, hwim x⟩
  have hφcomp :
      ContinuousOn (fun x : ℝ => φ₀'' ((-1 : ℂ) / (w x))) (Set.uIcc (0 : ℝ) 1) :=
    MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp (hinv.comp hw hwne) himap
  simpa [F] using (hφcomp.mul (by simpa using hw.pow 2)).intervalIntegrable

private lemma intervalIntegrable_comp_zI {g : ℂ → ℂ} (hg : ContinuousOn g {z : ℂ | 0 < z.im}) :
    IntervalIntegrable (fun x : ℝ => g (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
  have hx : ContinuousOn (fun x : ℝ => (zI x : ℂ)) (Set.uIcc (0 : ℝ) 1) :=
    (continuous_ofReal.add continuous_const).continuousOn
  simpa using (hg.comp hx (fun x hx => by simp [zI])).intervalIntegrable

private lemma intervalIntegrable_F_zI :
    IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
  simpa [zI] using
    intervalIntegrable_F_comp (w := fun x : ℝ => zI x)
      ((continuous_ofReal.add continuous_const).continuousOn) (by intro x; simp [zI])

private lemma intervalIntegrable_F_zI_sub_one :
    IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 := by
  simpa [zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    intervalIntegrable_F_comp (w := fun x : ℝ => zI x - 1)
      ((continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
      (by intro x; simp [zI])

private lemma hI246_eq :
    I₂' (0 : ℝ) + I₄' 0 + I₆' 0 = -8640 * Complex.I / π := by
  have hI24 := I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2
    intervalIntegrable_F_zI intervalIntegrable_F_zI_sub_one
  have hf0 : (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) = -I₆' (0 : ℝ) := by
    simpa [zI] using integral_f0_height_one_eq_neg_I6
  have hphi2 : (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) = (720 : ℂ) := integral_phi2_height_one
  have hIntf0 : IntervalIntegrable (fun x : ℝ => f0 (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [f0] using intervalIntegrable_comp_zI f0_continuousOn
  have hIntphi2 : IntervalIntegrable (fun x : ℝ => φ₂'' (zI x)) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_comp_zI MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn
  have hsplit :
      (∫ x : ℝ in (0 : ℝ)..1, (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) =
        (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) -
          ∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x) := by
    simpa using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ => f0 (zI x))
        (g := fun x : ℝ => (12 * Complex.I) / π * φ₂'' (zI x)) hIntf0 (hIntphi2.const_mul _))
  have hI24' : I₂' (0 : ℝ) + I₄' 0 =
      (∫ x : ℝ in (0 : ℝ)..1, (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) := by
    simpa [f0, zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_left_comm, mul_comm] using hI24
  have hconstmul :
      (∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x)) =
        ((12 : ℂ) * Complex.I) / π * (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) := by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hI24', hsplit, hconstmul, hf0, hphi2]
  field_simp
  ring

end StripContour

/-- The special value at the origin: `a 0 = -8640 * I / π`. -/
public theorem a_zero :
    FourierEigenfunctions.a (0 : ℝ⁸) = -8640 * Complex.I / π := by
  rw [a_zero_reduction_I₂₄₆, hI246_eq]

end Zero

end

end MagicFunction.a.SpecialValues

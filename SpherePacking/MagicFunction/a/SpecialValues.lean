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
  simp [I₁'_eq, I₃'_eq, I₅'_eq]
  ring

lemma a_zero_reduction_I₂₄₆ :
    FourierEigenfunctions.a (0 : ℝ⁸) = I₂' (0 : ℝ) + I₄' 0 + I₆' 0 := by
  rw [a_zero_reduction]
  linear_combination I₁'_zero_add_I₃'_zero_add_I₅'_zero

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

lemma I₄'_zero :
    I₄' (0 : ℝ) = -∫ x in (0 : ℝ)..1, F (zI x - 1) := by
  have h0 : I₄' (0 : ℝ) =
      ∫ x in (0 : ℝ)..1, (-1 : ℂ) *
        (φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) := by
    simp [MagicFunction.a.RadialFunctions.I₄'_eq, pow_two]
  have hrew : (fun x : ℝ =>
      φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      fun x : ℝ => F (zI (1 - x) - 1) := by
    funext x; simp [F, zI, sub_eq_add_neg, add_assoc, add_comm]
  have hsub : (∫ x in (0 : ℝ)..1,
      φ₀'' (-1 / ((-(x : ℂ)) + Complex.I)) * ((-(x : ℂ)) + Complex.I) ^ (2 : ℕ)) =
      ∫ x in (0 : ℝ)..1, F (zI x - 1) := by
    simpa [hrew] using (intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => F (zI x - 1)) (a := 0) (b := 1) (d := 1))
  simp [h0, hsub]

/-! ### S-transform identity for `F(z) - F(z-1)`. -/

lemma φ₂''_def (z : ℂ) (hz : 0 < z.im) : φ₂'' z = φ₂' ⟨z, hz⟩ := by simp [φ₂'', hz]

lemma φ₄''_def (z : ℂ) (hz : 0 < z.im) : φ₄'' z = φ₄' ⟨z, hz⟩ := by simp [φ₄'', hz]

lemma F_eq_phi0_phi2_phi4 (z : ℂ) (hz : 0 < z.im) :
    F z =
      φ₀'' z * (z : ℂ) ^ (2 : ℕ) - (12 * Complex.I) / π * (z : ℂ) * φ₂'' z -
        36 / (π ^ 2) * φ₄'' z := by
  -- Work in `ℍ` and use the previously proved `φ₀_S_transform_mul_sq`.
  let zH : ℍ := ⟨z, hz⟩
  have hSz : ((ModularGroup.S • zH : ℍ) : ℂ) = -1 / (z : ℂ) := by
    simpa [zH] using ModularGroup.coe_S_smul (z := zH)
  have hφ₀S : φ₀ (ModularGroup.S • zH) = φ₀'' (-1 / z) := by rw [← hSz, φ₀''_coe_upperHalfPlane]
  have hφ₀ : φ₀ zH = φ₀'' z := by simpa [zH] using (φ₀''_def (z := z) hz).symm
  have hφ₂ : φ₂' zH = φ₂'' z := by simp [φ₂'', hz, zH]
  have hφ₄ : φ₄' zH = φ₄'' z := by simp [φ₄'', hz, zH]
  have h' := φ₀_S_transform_mul_sq zH
  rw [hφ₀S, hφ₀, hφ₂, hφ₄] at h'
  simpa [F, zH] using h'

private lemma φ₀''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z - 1) = φ₀'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  let zH : ℍ := ⟨z, hz⟩
  have hvneg : ((-1 : ℝ) +ᵥ zH : ℍ) = ⟨z - 1, hz1⟩ := by ext1; simp [zH, sub_eq_add_neg, add_comm]
  have h1 : φ₀'' (z - 1) = φ₀ (⟨z - 1, hz1⟩ : ℍ) := by simpa using φ₀''_def (z := z - 1) hz1
  have h2 : φ₀ zH = φ₀'' z := by simpa [zH] using (φ₀''_def (z := z) hz).symm
  rw [h1, ← hvneg, φ₀_periodic_neg_one, h2]

private lemma φ₂''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₂'' (z - 1) = φ₂'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  let zH : ℍ := ⟨z, hz⟩
  have hvneg : ((-1 : ℝ) +ᵥ zH : ℍ) = ⟨z - 1, hz1⟩ := by ext1; simp [zH, sub_eq_add_neg, add_comm]
  have h1 : φ₂'' (z - 1) = φ₂' (⟨z - 1, hz1⟩ : ℍ) := by simpa using φ₂''_def (z := z - 1) hz1
  have h2 : φ₂' zH = φ₂'' z := by simpa [zH] using (φ₂''_def (z := z) hz).symm
  rw [h1, ← hvneg, φ₂'_periodic_neg_one, h2]

private lemma φ₄''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₄'' (z - 1) = φ₄'' z := by
  have hz1 : 0 < (z - 1).im := by simpa using hz
  let zH : ℍ := ⟨z, hz⟩
  have hvneg : ((-1 : ℝ) +ᵥ zH : ℍ) = ⟨z - 1, hz1⟩ := by
    ext1; simpa [zH, sub_eq_add_neg] using (add_comm (-1 : ℂ) z)
  have h1 : φ₄'' (z - 1) = φ₄' (⟨z - 1, hz1⟩ : ℍ) := by simpa using φ₄''_def (z := z - 1) hz1
  have h2 : φ₄' zH = φ₄'' z := by simpa [zH] using (φ₄''_def (z := z) hz).symm
  rw [h1, ← hvneg, φ₄'_periodic_neg_one, h2]

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
  have hzI : 0 < (zI x).im := by simp [zI]
  simpa [zI] using F_sub_one (z := zI x) hzI

/-! ### Cancelling the `φ₀''` strip integral against `I₆' 0`. -/

def f0 (z : ℂ) : ℂ := φ₀'' z * ((2 : ℂ) * z - 1)

lemma f0_differentiableOn : DifferentiableOn ℂ f0 {z : ℂ | 0 < z.im} := by
  have hlin : Differentiable ℂ fun z : ℂ => (2 : ℂ) * z - 1 := by fun_prop
  simpa [f0] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.mul hlin.differentiableOn

lemma f0_continuousOn : ContinuousOn f0 {z : ℂ | 0 < z.im} :=
  (f0_differentiableOn).continuousOn

lemma f0_norm_bound_on_strip :
    ∃ C₀ > 0, ∀ {z : ℂ}, 1 ≤ z.im → 0 ≤ z.re → z.re ≤ 1 →
      ‖f0 z‖ ≤ C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro z hzIm hzRe0 hzRe1
  have hzIm_pos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm
  have hφ : ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) := by
    let zH : ℍ := ⟨z, hzIm_pos⟩
    have hzHalf : (1 / 2 : ℝ) < zH.im := by
      simpa [zH, UpperHalfPlane.im] using (lt_of_lt_of_le (by norm_num) hzIm)
    simpa [zH, UpperHalfPlane.im, φ₀''_def (z := z) hzIm_pos] using hC₀ zH hzHalf
  have hlin : ‖(2 : ℂ) * z - 1‖ ≤ 2 * z.im + 1 := by
    have hRe : |2 * z.re - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have hIm : |2 * z.im| = 2 * z.im := abs_of_nonneg (by positivity)
    calc ‖(2 : ℂ) * z - 1‖
        ≤ |((2 : ℂ) * z - 1).re| + |((2 : ℂ) * z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |2 * z.re - 1| + |2 * z.im| := by simp
      _ ≤ 1 + |2 * z.im| := add_le_add hRe le_rfl
      _ = 2 * z.im + 1 := by simp [hIm, add_comm]
  calc
    ‖f0 z‖ = ‖φ₀'' z * ((2 : ℂ) * z - 1)‖ := by simp [f0]
    _ = ‖φ₀'' z‖ * ‖(2 : ℂ) * z - 1‖ := by simp
    _ ≤ (C₀ * Real.exp (-2 * π * z.im)) * (2 * z.im + 1) := by gcongr
    _ = C₀ * (2 * z.im + 1) * Real.exp (-2 * π * z.im) := by ring_nf

/-! ### Rectangle identity for `f0` and cancellation with `I₆' 0`. -/

/-- Periodicity of `φ₀''` under translation by `1`. -/
public lemma φ₀''_add_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z + 1) = φ₀'' z := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  let zH : ℍ := ⟨z, hz⟩
  have hvadd : ((1 : ℝ) +ᵥ zH : ℍ) = ⟨z + 1, hz1⟩ := by ext1; simp [zH, add_comm]
  have h1 : φ₀'' (z + 1) = φ₀ (⟨z + 1, hz1⟩ : ℍ) := by simpa using φ₀''_def (z := z + 1) hz1
  have h2 : φ₀ zH = φ₀'' z := by simpa [zH] using (φ₀''_def (z := z) hz).symm
  rw [h1, ← hvadd, φ₀_periodic, h2]

lemma f0_vertical_diff (y : ℝ) (hy : 0 < y) :
    f0 ((1 : ℂ) + (y : ℂ) * Complex.I) - f0 ((y : ℂ) * Complex.I) =
      (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
  have hyIm : 0 < (((y : ℂ) * Complex.I) : ℂ).im := by simpa [mul_assoc] using hy
  have hper :
      φ₀'' ((1 : ℂ) + (y : ℂ) * Complex.I) = φ₀'' ((y : ℂ) * Complex.I) := by
    simpa [add_assoc, add_comm, add_left_comm] using φ₀''_add_one (z := (y : ℂ) * Complex.I) hyIm
  simp [f0, hper]
  ring

lemma rect_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I)) = 0 := by
  -- Cauchy-Goursat on the rectangle with corners `i` and `1 + m i`.
  have hC :
      ContinuousOn f0 (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) := by
    refine f0_continuousOn.mono ?_
    intro z hz
    have hzIm' : (1 : ℝ) ≤ z.im :=
      (by simpa [Set.uIcc_of_le hm] using (mem_reProdIm.1 hz).2 : z.im ∈ Set.Icc (1 : ℝ) m).1
    exact lt_of_lt_of_le (by norm_num) hzIm'
  have hD :
      DifferentiableOn ℂ f0 (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) := by
    refine f0_differentiableOn.mono ?_
    intro z hz
    have hzIm : z.im ∈ Set.Ioo (1 : ℝ) m := (mem_reProdIm.1 hz).2
    exact lt_trans (by norm_num) hzIm.1
  -- Apply the rectangle theorem with `z = i`, `w = 1 + m i`.
  simpa using
    (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := f0) (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I) (Hc := by
        simpa using hC) (Hd := by simpa [hm] using hD))

lemma integrableOn_phi0_imag :
    MeasureTheory.IntegrableOn (fun t : ℝ => φ₀'' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨C₀, _, hC₀⟩
  have hbound :
      ∀ t : ℝ, t ∈ Set.Ioi (1 : ℝ) → ‖φ₀'' ((t : ℂ) * Complex.I)‖ ≤ C₀ * Real.exp (-2 * π * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
    let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa [mul_assoc] using ht0⟩
    have htHalf : (1 / 2 : ℝ) < zH.im := by
      have : (1 / 2 : ℝ) < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      simpa [zH, UpperHalfPlane.im] using this
    have hφ0 : ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * zH.im) := by
      simpa [φ₀''_coe_upperHalfPlane] using hC₀ zH htHalf
    simpa [zH, UpperHalfPlane.im] using hφ0
  have hgi :
      MeasureTheory.Integrable (fun t : ℝ => C₀ * Real.exp (-2 * π * t))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hExp :
        MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-2 * π * t)) (Set.Ioi (1 : ℝ))
          MeasureTheory.volume := by
      simpa [mul_assoc] using
        (exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (2 * Real.pi)) (by positivity))
    simpa [MeasureTheory.IntegrableOn, mul_assoc] using hExp.integrable.const_mul C₀
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => φ₀'' ((t : ℂ) * Complex.I))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
        (continuous_ofReal.mul continuous_const).continuousOn
        (by
          intro t ht
          have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
          simpa [mul_assoc] using ht0)).aestronglyMeasurable measurableSet_Ioi
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
    hgi hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  simpa using hbound t ht

lemma integrableOn_two_mul_phi0_imag :
    MeasureTheory.IntegrableOn (fun t : ℝ => (2 : ℂ) * φ₀'' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
      MeasureTheory.volume := by
  simpa [MeasureTheory.IntegrableOn] using (integrableOn_phi0_imag.const_mul (2 : ℂ))

lemma tendsto_top_f0 :
    Tendsto (fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) atTop (𝓝 (0 : ℂ)) := by
  rcases f0_norm_bound_on_strip with ⟨C₀, hC₀_pos, hC₀⟩
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)‖ ≤
          C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have hC :
        ∀ x ∈ Ι (0 : ℝ) 1, ‖f0 (x + m * Complex.I)‖ ≤
          C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m) := by
      intro x hx
      have hx0 : 0 ≤ x := le_of_lt (by simpa using hx.1)
      have hx1 : x ≤ 1 := by simpa using hx.2
      have hzIm : 1 ≤ (x + m * Complex.I : ℂ).im := by simpa using hm
      have hzRe0 : 0 ≤ (x + m * Complex.I : ℂ).re := by simpa using hx0
      have hzRe1 : (x + m * Complex.I : ℂ).re ≤ 1 := by simpa using hx1
      simpa using hC₀ (z := (x + m * Complex.I : ℂ)) hzIm hzRe0 hzRe1
    have hN :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun x : ℝ => f0 (x + m * Complex.I)) hC
    simpa using hN
  have hdecay :
      Tendsto (fun m : ℝ => C₀ * (2 * m + 1) * Real.exp (-2 * Real.pi * m)) atTop (𝓝 (0 : ℝ)) := by
    have hu : Tendsto (fun m : ℝ => (2 * Real.pi) * m) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    have hmul :
        Tendsto (fun m : ℝ => m * Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by
      simpa [Real.rpow_one] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := 1) (b := 2 * π) (by positivity)
    have hexp :
        Tendsto (fun m : ℝ => Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by simpa
    have hmain :
        Tendsto (fun m : ℝ => (2 * m + 1) * Real.exp (-2 * Real.pi * m)) atTop (𝓝 (0 : ℝ)) := by
      have hsum : Tendsto (fun m : ℝ => 2 * (m * Real.exp (-(2 * Real.pi) * m)) +
          Real.exp (-(2 * Real.pi) * m)) atTop (𝓝 (0 : ℝ)) := by
        simpa using (hmul.const_mul 2).add hexp
      exact hsum.congr' (Eventually.of_forall fun m => by ring_nf)
    simpa [mul_assoc] using hmain.const_mul C₀
  -- squeeze the norm to `0`
  exact squeeze_zero_norm' hbound hdecay

lemma strip_identity_f0 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I) := by
  -- Start from the rectangle identity,
  -- then rewrite the vertical contribution using `f0_vertical_diff`.
  have hrect := rect_f0 m hm
  have hInt (x : ℝ) :
      IntervalIntegrable (fun y : ℝ => f0 ((x : ℝ) + y * Complex.I))
        MeasureTheory.volume (1 : ℝ) m := by
    have hconty :
        ContinuousOn (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) (Set.uIcc (1 : ℝ) m) :=
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    have hmaps :
        Set.MapsTo (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) (Set.uIcc (1 : ℝ) m)
          {z : ℂ | 0 < z.im} := by
      intro y hy
      have hy1 : (1 : ℝ) ≤ y := by
        have hy' : y ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le hm] using hy
        exact hy'.1
      have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
      simpa using hy0
    have hcomp :
        ContinuousOn (fun y : ℝ => f0 ((x : ℂ) + (y : ℂ) * Complex.I)) (Set.uIcc (1 : ℝ) m) :=
      f0_continuousOn.comp hconty hmaps
    simpa using hcomp.intervalIntegrable
  have hIntR :
      IntervalIntegrable (fun y : ℝ => f0 ((1 : ℝ) + y * Complex.I)) MeasureTheory.volume
        (1 : ℝ) m := by simpa using hInt (x := (1 : ℝ))
  have hIntL :
      IntervalIntegrable (fun y : ℝ => f0 ((0 : ℝ) + y * Complex.I)) MeasureTheory.volume
        (1 : ℝ) m := by simpa using hInt (x := (0 : ℝ))
  have hSub :
      (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
          ∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I) =
        ∫ y : ℝ in (1 : ℝ)..m, (f0 ((1 : ℝ) + y * Complex.I) - f0 ((0 : ℝ) + y * Complex.I)) := by
    exact Eq.symm (integral_sub (hInt 1) (hInt 0))
  have hVert :
      (∫ y : ℝ in (1 : ℝ)..m, (f0 ((1 : ℝ) + y * Complex.I) - f0 ((0 : ℝ) + y * Complex.I))) =
        ∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro y hy
    have hy1 : (1 : ℝ) ≤ y := by
      have hy' : y ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le hm] using hy
      exact hy'.1
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
    -- rewrite the left integrand using `f0_vertical_diff`
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (f0_vertical_diff y hy0)
  -- Rearrange the rectangle identity.
  have hrect' :
      (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) -
          (∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) +
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) = 0 := by
    have hrect₁ :
        (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) -
            (∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)) +
            (Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((1 : ℝ) + y * Complex.I)) -
              Complex.I • (∫ y : ℝ in (1 : ℝ)..m, f0 ((0 : ℝ) + y * Complex.I))) =
          0 := by simpa [add_sub_assoc] using hrect
    rwa [← smul_sub, hSub, hVert] at hrect₁
  exact sub_eq_zero.mp (by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrect')

lemma integral_f0_height_one_eq_neg_I6 :
    (∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)) = -I₆' (0 : ℝ) := by
  -- Take `m → ∞` in the strip identity.
  let bottom : ℂ := ∫ x : ℝ in (0 : ℝ)..1, f0 (x + (1 : ℝ) * Complex.I)
  let vert : ℝ → ℂ :=
    fun m : ℝ => ∫ y : ℝ in (1 : ℝ)..m, (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
  let top : ℝ → ℂ := fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f0 (x + m * Complex.I)
  have hEq : (fun m : ℝ => bottom + Complex.I • vert m) =ᶠ[atTop] top := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have h := strip_identity_f0 m hm
    simpa [bottom, vert, top] using h
  have hVert :
      Tendsto vert atTop
        (𝓝
          (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
            ∂MeasureTheory.volume)) := by
    simpa [vert] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := MeasureTheory.volume)
        (f := fun y : ℝ => (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)) (a := (1 : ℝ))
        (b := fun m : ℝ => m) (l := atTop) (hfi := integrableOn_two_mul_phi0_imag)
        (hb := tendsto_id))
  have hL :
      Tendsto (fun m : ℝ => bottom + Complex.I • vert m) atTop
        (𝓝
          (bottom +
            Complex.I •
              (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
                ∂MeasureTheory.volume))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.smul hVert))
  have hTopA :
      Tendsto top atTop
        (𝓝
          (bottom +
            Complex.I •
              (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
                ∂MeasureTheory.volume))) :=
    hL.congr' hEq
  have hTop0 : Tendsto top atTop (𝓝 (0 : ℂ)) := by simpa [top] using tendsto_top_f0
  have hA0 :
      bottom +
          Complex.I •
            (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
              ∂MeasureTheory.volume) =
        0 :=
    tendsto_nhds_unique hTopA hTop0
  -- Identify the vertical limit with `I₆' 0`.
  have hI6 :
      I₆' (0 : ℝ) =
        Complex.I •
          (∫ y in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((y : ℂ) * Complex.I)
            ∂MeasureTheory.volume) := by
    -- Use the explicit `I₆'` formula at `r = 0` and `Ici = Ioi` up to measure zero.
    have h0 := (MagicFunction.a.RadialFunctions.I₆'_eq (r := (0 : ℝ)))
    -- simplify the exponential factor at `r = 0`
    have h0' :
        I₆' (0 : ℝ) =
          2 * ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * φ₀'' ((t : ℂ) * Complex.I)
            ∂MeasureTheory.volume := by simp [h0, mul_comm]
    -- switch to `Ioi` and pull out scalars
    calc
      I₆' (0 : ℝ)
          = 2 * ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * φ₀'' ((t : ℂ) * Complex.I)
              ∂MeasureTheory.volume := by simp [h0', MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = Complex.I •
            (∫ t in Set.Ioi (1 : ℝ), (2 : ℂ) * φ₀'' ((t : ℂ) * Complex.I)
              ∂MeasureTheory.volume) := by
            simp only [MeasureTheory.integral_const_mul, smul_eq_mul]
            ring
  -- Solve for `bottom`.
  grind only

/-! ### Evaluating the remaining `φ₂''` term. -/

lemma φ₂''_add_one (z : ℂ) (hz : 0 < z.im) : φ₂'' (z + 1) = φ₂'' z := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  let zH : ℍ := ⟨z, hz⟩
  have hvadd : ((1 : ℝ) +ᵥ zH : ℍ) = ⟨z + 1, hz1⟩ := by ext1; simp [zH, add_comm]
  have h1 : φ₂'' (z + 1) = φ₂' (⟨z + 1, hz1⟩ : ℍ) := by simpa using φ₂''_def (z := z + 1) hz1
  have h2 : φ₂' zH = φ₂'' z := by simpa [zH] using (φ₂''_def (z := z) hz).symm
  rw [h1, ← hvadd, φ₂'_periodic, h2]

lemma rect_phi2 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + (1 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) +
        Complex.I • (∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I)) -
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I)) = 0 := by
  have hC :
      ContinuousOn φ₂'' (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) := by
    refine (MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn).mono ?_
    intro z hz
    have hzIm : z.im ∈ Set.uIcc (1 : ℝ) m := (mem_reProdIm.1 hz).2
    have hzIm' : (1 : ℝ) ≤ z.im := by
      have : z.im ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le hm] using hzIm
      exact this.1
    exact lt_of_lt_of_le (by norm_num) hzIm'
  have hD :
      DifferentiableOn ℂ φ₂'' (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) := by
    refine
      (MagicFunction.a.ComplexIntegrands.φ₂''_holo :
          DifferentiableOn ℂ φ₂'' {z : ℂ | 0 < z.im}).mono ?_
    intro z hz
    have hzIm : z.im ∈ Set.Ioo (1 : ℝ) m := (mem_reProdIm.1 hz).2
    exact lt_trans (by norm_num) hzIm.1
  simpa using
    (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := φ₂'') (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I) (Hc := by simpa using hC)
      (Hd := by simpa [hm] using hD))

lemma strip_identity_phi2 (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + (1 : ℝ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I) := by
  have hrect := rect_phi2 m hm
  have hVert :
      ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((1 : ℝ) + y * Complex.I) =
        ∫ y : ℝ in (1 : ℝ)..m, φ₂'' ((0 : ℝ) + y * Complex.I) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro y hy
    have hy1 : (1 : ℝ) ≤ y := by
      have hy' : y ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le hm] using hy
      exact hy'.1
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
    have hyIm : 0 < (((y : ℂ) * Complex.I) : ℂ).im := by simpa [mul_assoc] using hy0
    have hper : φ₂'' (((y : ℂ) * Complex.I) + 1) = φ₂'' ((y : ℂ) * Complex.I) :=
      φ₂''_add_one (z := (y : ℂ) * Complex.I) hyIm
    have hper' : φ₂'' ((1 : ℂ) + (y : ℂ) * Complex.I) = φ₂'' ((y : ℂ) * Complex.I) := by
      simpa [add_assoc, add_comm, add_left_comm] using hper
    simpa [hper', add_assoc, add_comm, add_left_comm, mul_assoc]
  grind only

lemma summable_coeff_A_over_q :
    Summable (fun n : ℕ =>
      ‖(((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) := by
  refine
    SpherePacking.ForMathlib.summable_norm_mul_sigma_shift_mul_exp (k := 3) (m := 4) (s := 1) ?_
  intro n
  exact_mod_cast (SpherePacking.ForMathlib.sigma_three_le_pow_four (n + 1))

lemma tendsto_A_div_q :
    Tendsto (fun z : ℍ =>
        ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z))
      atImInfty (𝓝 (720 : ℂ)) := by
  -- Write `A / q` as a `q`-series with constant term `720`.
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 3 (n + 1) : ℂ))
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using summable_coeff_A_over_q
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hseries'' :
      Tendsto (fun z : ℍ => (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (720 : ℂ)) := by simpa [a] using (tendsto_const_nhds.mul hseries)
  have hA_eq (z : ℍ) :
      ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z) =
        (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n) := by
    have hz : cexp (2 * π * Complex.I * (z : ℂ)) ≠ 0 := by simp
    have hA :
        (E₂ z) * (E₄ z) - (E₆ z) =
          (720 : ℂ) *
            ∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₄_sub_E₆ z)
    -- Shift the `ℕ+` series to an `ℕ` series and cancel one `q` factor in each exponential.
    have hshift :
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
      have hexp :
          cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) =
            cexp (2 * π * Complex.I * (z : ℂ)) *
              cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
        have harg :
            (2 * π * Complex.I * (z : ℂ) * ((n : ℂ) + 1)) =
              (2 * π * Complex.I * (z : ℂ)) + (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by ring_nf
        calc
          cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) =
              cexp (2 * π * Complex.I * (z : ℂ) * ((n : ℂ) + 1)) := by
                simp [Nat.cast_add, Nat.cast_one]
          _ = cexp ((2 * π * Complex.I * (z : ℂ)) + (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) := by
                simp [harg]
          _ = cexp (2 * π * Complex.I * (z : ℂ)) *
                cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
                simp [Complex.exp_add, mul_left_comm, mul_comm]
      grind only
    calc
      ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z)
          = (720 : ℂ) *
              ((∑' (n : ℕ+), (n : ℂ) * (σ 3 n : ℂ) *
                    cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
                cexp (2 * π * Complex.I * (z : ℂ))) := by
              -- Use `hA` and pull the constant factor outside the division.
              rw [hA]
              simp [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm]
      _ = (720 : ℂ) *
            ∑' (n : ℕ+),
              ((n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
                cexp (2 * π * Complex.I * (z : ℂ)) := by
            -- Move the division by `q` inside the `tsum`.
            simpa using
              congrArg (fun t : ℂ => (720 : ℂ) * t)
                (tsum_div_const (f := fun n : ℕ+ =>
                      (n : ℂ) * (σ 3 n : ℂ) *
                        cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))
                    (a := cexp (2 * π * Complex.I * (z : ℂ)))).symm
      _ = (720 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            simp [hshift]
  -- Conclude by comparing with the `q`-series limit.
  exact (tendsto_congr hA_eq).mpr hseries''

lemma tendsto_phi2'_atImInfty :
    Tendsto (fun z : ℍ => φ₂' z) atImInfty (𝓝 (720 : ℂ)) := by
  -- Factor `φ₂'` into `E₄ * (A / Δ)` and use `Δ = q * boundedfactor`.
  have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₄_atImInfty
  have hAq :
      Tendsto (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z))
        atImInfty (𝓝 (720 : ℂ)) :=
    tendsto_A_div_q
  have hΔq :
      Tendsto (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) atImInfty (𝓝 (1 : ℂ)) := by
    -- `Δ z / q =` the bounded product factor.
    have hrew :
        (fun z : ℍ => (Δ z) / cexp (2 * π * Complex.I * z)) =
          fun z : ℍ =>
            ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 := by
      funext z
      simp [Δ, div_eq_mul_inv, mul_left_comm, mul_comm]
    simpa [hrew] using (Delta_boundedfactor : Tendsto _ atImInfty (𝓝 (1 : ℂ)))
  have hΔq_ne : ∀ᶠ z in atImInfty, (Δ z) / cexp (2 * π * Complex.I * z) ≠ (0 : ℂ) := by
    have hne0 : {w : ℂ | w ≠ 0} ∈ 𝓝 (1 : ℂ) := by
      refine Filter.mem_of_superset
        (Metric.ball_mem_nhds (1 : ℂ) (ε := (1 / 2 : ℝ)) (by norm_num)) ?_
      intro w hw h0
      have hdist : dist (0 : ℂ) (1 : ℂ) < (1 / 2 : ℝ) := by
        simpa [Metric.mem_ball, h0, dist_comm] using hw
      have hdist' : (1 : ℝ) < (1 / 2 : ℝ) := by simpa [dist_eq_norm] using hdist
      norm_num at hdist'
    simpa [Set.mem_setOf_eq] using (hΔq.eventually hne0)
  have hA_over_Δ :
      Tendsto (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)) atImInfty (𝓝 (720 : ℂ)) := by
    have hq_ne : ∀ z : ℍ, (cexp (2 * π * Complex.I * z) : ℂ) ≠ 0 := fun z =>
      by simp
    -- Rewrite `A/Δ` as `(A/q) / (Δ/q)`.
    have hrew :
        (fun z : ℍ => ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)) =
          fun z : ℍ =>
            (((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z)) /
              ((Δ z) / cexp (2 * π * Complex.I * z)) := by
      funext z
      field_simp [hq_ne z, Δ_ne_zero z]
    -- Apply `tendsto_div` to the rewritten form.
    have hdiv' :
        Tendsto (fun z : ℍ =>
            (((E₂ z) * (E₄ z) - (E₆ z)) / cexp (2 * π * Complex.I * z)) /
              ((Δ z) / cexp (2 * π * Complex.I * z))) atImInfty (𝓝 (720 : ℂ)) := by
      simpa using hAq.div hΔq (by norm_num : (1 : ℂ) ≠ 0)
    rw [hrew]
    exact hdiv'
  -- Combine `E₄ → 1` and `A/Δ → 720`.
  simpa [φ₂', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hE4.mul hA_over_Δ

lemma tendsto_top_phi2 :
    Tendsto (fun m : ℝ => ∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) atTop (𝓝 (720 : ℂ)) := by
  -- Use the `atImInfty` limit uniformly in `re z` to control the integral.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hBall :
      {z : ℍ | ‖φ₂' z - (720 : ℂ)‖ < ε / 2} ∈ atImInfty :=
    tendsto_phi2'_atImInfty (Metric.ball_mem_nhds (720 : ℂ) (half_pos hε))
  rcases (UpperHalfPlane.atImInfty_mem _).1 hBall with ⟨A, hA⟩
  -- Take `m` large enough so that `A ≤ m` and `1 ≤ m`.
  refine ⟨max A 1, ?_⟩
  intro m hm
  have hmA : A ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  -- Pointwise bound on the integrand on `x ∈ [0,1]`.
  have hbound :
      ∀ x ∈ Ι (0 : ℝ) 1, ‖φ₂'' (x + m * Complex.I) - (720 : ℂ)‖ ≤ ε / 2 := by
    intro x hx
    let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa using hm0⟩
    have hz : A ≤ zH.im := by simpa [zH, UpperHalfPlane.im, zI, Complex.add_im] using hmA
    have hmem : ‖φ₂' zH - (720 : ℂ)‖ < ε / 2 := by simpa using hA zH hz
    have him : 0 < ((x : ℂ) + (m : ℂ) * Complex.I).im := by simpa using hm0
    have hdef : φ₂'' ((x : ℂ) + (m : ℂ) * Complex.I) = φ₂' zH := by
      simpa [zH] using φ₂''_def (z := (x : ℂ) + (m : ℂ) * Complex.I) him
    simpa [zH, hdef, mul_assoc] using le_of_lt hmem
  -- Rewrite the difference of integrals as the integral of the difference.
  have hInt :
      IntervalIntegrable (fun x : ℝ => φ₂'' (x + m * Complex.I)) MeasureTheory.volume (0 : ℝ)
        1 := by
    have hcont : ContinuousOn (fun x : ℝ => φ₂'' (x + m * Complex.I)) (Set.uIcc (0 : ℝ) 1) := by
      have hφ : ContinuousOn φ₂'' {z : ℂ | 0 < z.im} :=
        MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn
      have hx : ContinuousOn (fun x : ℝ => (x : ℂ) + (m : ℂ) * Complex.I) (Set.uIcc (0 : ℝ) 1) :=
        (continuous_ofReal.add continuous_const).continuousOn
      have hmaps :
          Set.MapsTo (fun x : ℝ => (x : ℂ) + (m : ℂ) * Complex.I) (Set.uIcc (0 : ℝ) 1)
            {z : ℂ | 0 < z.im} := by
        intro x hx'
        simpa [Complex.add_im] using hm0
      exact hφ.comp hx hmaps
    simpa using hcont.intervalIntegrable
  have hIntConst :
      IntervalIntegrable (fun _x : ℝ => (720 : ℂ)) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hsub :
      (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ) =
        ∫ x : ℝ in (0 : ℝ)..1, (φ₂'' (x + m * Complex.I) - (720 : ℂ)) := by
    -- Use `∫ f - ∫ c = ∫ (f - c)` and `∫ c = c` on `[0,1]`.
    simpa using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ => φ₂'' (x + m * Complex.I)) (g := fun _x : ℝ => (720 : ℂ)) hInt
        hIntConst).symm
  have hdist :
      dist (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) (720 : ℂ) < ε := by
    have hnorm :
        ‖(∫ x : ℝ in (0 : ℝ)..1, (φ₂'' (x + m * Complex.I) - (720 : ℂ)))‖ ≤
          (ε / 2) * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound
    have hnorm' :
        ‖(∫ x : ℝ in (0 : ℝ)..1, (φ₂'' (x + m * Complex.I) - (720 : ℂ)))‖ ≤ ε / 2 := by
      simpa using hnorm
    -- `dist` is the norm of the difference.
    have : ‖(∫ x : ℝ in (0 : ℝ)..1, φ₂'' (x + m * Complex.I)) - (720 : ℂ)‖ ≤ ε / 2 := by
      simpa [hsub] using hnorm'
    exact lt_of_le_of_lt this (half_lt_self hε)
  simpa [Metric.ball, dist_eq_norm] using hdist

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
  have hφ : ContinuousOn φ₀'' {z : ℂ | 0 < z.im} :=
    MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
  have hwne : Set.MapsTo w (Set.uIcc (0 : ℝ) 1) ({0}ᶜ) := by
    intro x hx
    exact fun h0 => (ne_of_gt (hwim x)) (by simpa using congrArg Complex.im h0)
  have hinv : ContinuousOn (fun z : ℂ => (-1 : ℂ) / z) ({0}ᶜ) := by
    have h :
        ContinuousOn ((fun _ : ℂ => (-1 : ℂ)) * (Inv.inv : ℂ → ℂ)) ({0}ᶜ) :=
      (continuousOn_const.mul (continuousOn_inv₀ (G₀ := ℂ)))
    convert h using 1
  have hinvcomp : ContinuousOn (fun x : ℝ => (-1 : ℂ) / (w x)) (Set.uIcc (0 : ℝ) 1) :=
    hinv.comp hw hwne
  have himap :
      Set.MapsTo (fun x : ℝ => (-1 : ℂ) / (w x)) (Set.uIcc (0 : ℝ) 1) {z : ℂ | 0 < z.im} := by
    intro x hx
    have hpos : 0 < ((-(⟨w x, hwim x⟩ : ℍ) : ℂ)⁻¹).im :=
      UpperHalfPlane.im_inv_neg_coe_pos ⟨w x, hwim x⟩
    simpa [div_eq_mul_inv] using hpos
  have hφcomp :
      ContinuousOn (fun x : ℝ => φ₀'' ((-1 : ℂ) / (w x))) (Set.uIcc (0 : ℝ) 1) :=
    hφ.comp hinvcomp himap
  have hwpow : ContinuousOn (fun x => w x ^ (2 : ℕ)) (Set.uIcc 0 1) := by simpa using hw.pow 2
  simpa [F] using (hφcomp.mul hwpow).intervalIntegrable

private lemma intervalIntegrable_comp_zI {g : ℂ → ℂ} (hg : ContinuousOn g {z : ℂ | 0 < z.im}) :
    IntervalIntegrable (fun x : ℝ => g (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
  have hx : ContinuousOn (fun x : ℝ => (zI x : ℂ)) (Set.uIcc (0 : ℝ) 1) :=
    (continuous_ofReal.add continuous_const).continuousOn
  simpa using (hg.comp hx (fun x hx => by simp [zI])).intervalIntegrable

theorem a_zero_value : FourierEigenfunctions.a (0 : ℝ⁸) = -8640 * Complex.I / π := by
  -- Reduce to `I₂' 0 + I₄' 0 + I₆' 0`.
  have ha : FourierEigenfunctions.a (0 : ℝ⁸) = I₂' (0 : ℝ) + I₄' 0 + I₆' 0 :=
    a_zero_reduction_I₂₄₆
  -- Establish interval integrability of the `F`-integrands (continuity on a compact interval).
  have hFInt :
      IntervalIntegrable (fun x : ℝ => F (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [zI] using
      intervalIntegrable_F_comp (w := fun x : ℝ => zI x)
        ((continuous_ofReal.add continuous_const).continuousOn) (by intro x; simp [zI])
  have hGInt :
      IntervalIntegrable (fun x : ℝ => F (zI x - 1)) MeasureTheory.volume (0 : ℝ) 1 := by
    -- same argument, since `im(zI x - 1) = 1`.
    simpa [zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      intervalIntegrable_F_comp (w := fun x : ℝ => zI x - 1)
        ((continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
        (by intro x; simp [zI])
  -- Express `I₂' 0 + I₄' 0` as the integral of `f0 - (12i/π) φ₂''`.
  have hI24 := I₂'_zero_add_I₄'_zero_eq_integral_phi0_phi2 hFInt hGInt
  -- Split the integral and substitute the `f0` strip computation.
  have hf0 :
      (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) = -I₆' (0 : ℝ) := by
    simpa [zI] using integral_f0_height_one_eq_neg_I6
  have hphi2 : (∫ x : ℝ in (0 : ℝ)..1, φ₂'' (zI x)) = (720 : ℂ) :=
    integral_phi2_height_one
  have hIntf0 : IntervalIntegrable (fun x : ℝ => f0 (zI x)) MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [f0] using intervalIntegrable_comp_zI f0_continuousOn
  have hIntphi2 : IntervalIntegrable (fun x : ℝ => φ₂'' (zI x)) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_comp_zI MagicFunction.a.ComplexIntegrands.φ₂''_holo.continuousOn
  have hsplit :
      (∫ x : ℝ in (0 : ℝ)..1,
            (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x))) =
        (∫ x : ℝ in (0 : ℝ)..1, f0 (zI x)) -
          ∫ x : ℝ in (0 : ℝ)..1, (12 * Complex.I) / π * φ₂'' (zI x) := by
    simpa using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ => f0 (zI x))
        (g := fun x : ℝ => (12 * Complex.I) / π * φ₂'' (zI x)) hIntf0 (hIntphi2.const_mul _))
  have hI246 :
      I₂' (0 : ℝ) + I₄' 0 + I₆' 0 = -8640 * Complex.I / π := by
    have hI24' : I₂' (0 : ℝ) + I₄' 0 =
        -I₆' 0 - (12 * Complex.I) / π * 720 := by
      have : I₂' (0 : ℝ) + I₄' 0 =
          ∫ x : ℝ in (0 : ℝ)..1,
            (f0 (zI x) - (12 * Complex.I) / π * φ₂'' (zI x)) := by
        simpa [f0, zI, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
          mul_assoc, mul_left_comm, mul_comm] using hI24
      rw [this, hsplit, hf0]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hphi2]
    rw [hI24']
    ring
  simp [ha, hI246]

end StripContour

/-- The special value at the origin: `a 0 = -8640 * I / π`. -/
public theorem a_zero :
    FourierEigenfunctions.a (0 : ℝ⁸) = -8640 * Complex.I / π := a_zero_value

end Zero

end

end MagicFunction.a.SpecialValues

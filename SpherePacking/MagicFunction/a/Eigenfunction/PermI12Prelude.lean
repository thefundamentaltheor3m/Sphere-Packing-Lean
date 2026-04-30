/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Main
public import SpherePacking.MagicFunction.a.SpecialValues
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Contour.MobiusInv.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

import SpherePacking.Contour.Segments

/-!
# Prelude for `perm_I₁_I₂`

The identity `perm_I₁_I₂` is proved by rewriting `I₁ + I₂` and `I₃ + I₄` as curve integrals of the
same holomorphic `1`-form and applying the Poincare lemma (contour deformation in the upper
half-plane).

This file bridges the existing `intervalIntegral` definitions to `curveIntegral` along straight
segments, and defines the auxiliary Fourier-side integrand `Φ₁_fourier`.

## Main definitions
* `Φ₁_fourier`

## Main statements
* `I₁'_eq_curveIntegral_segment`
* `I₂'_eq_curveIntegral_segment`
* `I₃'_add_I₄'_eq_curveIntegral_segments`
* `Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃'`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

/-- If `f` is an even Schwartz function, then applying the Fourier transform twice gives back `f`.

This is used to invert permutation identities for radial (hence even) functions. -/
public lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) (hf : Function.Even f) :
    FourierTransform.fourierCLE ℂ (SchwartzMap V E)
        (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f) = f := by
  ext x
  simpa [hf x, Real.fourierInv_eq_fourier_neg, neg_neg] using congrFun
    (f.continuous.fourierInv_fourier_eq f.integrable
      (by simpa using (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f).integrable)) (-x)

lemma φ₀''_inv_add_one_mul_sq (w : ℂ) (hw : 0 < w.im) :
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 * w ^ 2 =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
  have hw0 : w ≠ 0 := fun h => absurd (show w.im = 0 by simp [h]) hw.ne'
  have hw' : 0 < (w - 1).im := by simpa using hw
  have hw1 : w - 1 ≠ 0 := fun h => absurd (show (w - 1).im = 0 by simp [h]) hw'.ne'
  have hzpos : 0 < (-1 / (w - 1)).im := by
    simpa [div_eq_mul_inv, sub_eq_add_neg, Complex.inv_im] using
      div_pos hw' (Complex.normSq_pos.2 hw1)
  rw [mul_assoc, show ((-1 / w + 1) ^ 2) * w ^ 2 = (w - 1) ^ 2 by field_simp [hw0]; ring,
    show (-1 / ((-1 / w) + 1) : ℂ) = (-1 / (w - 1)) - 1 by grind only,
    show φ₀'' ((-1 / (w - 1)) - 1) = φ₀'' (-1 / (w - 1)) by
      simpa using (MagicFunction.a.SpecialValues.φ₀''_add_one
        (z := -1 / (w - 1) - 1) (by simpa using hzpos)).symm]

lemma φ₀''_inv_add_one_mul_sq' (w : ℂ) (hw : 0 < w.im) :
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 *
        (((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹) =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
  simpa [show ((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹ = w ^ (2 : ℕ) by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · field_simp; simp [Complex.I_pow_four]] using φ₀''_inv_add_one_mul_sq (w := w) hw

section CurveIntegral
open scoped Interval
open Complex

private lemma uIcc_aux {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht

/-- Rewrite `I₁'` as a curve integral of `Φ₁'` along the segment `-1 → -1 + i`. -/
public lemma I₁'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) (-1 + Complex.I),
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r))
    (-1 : ℂ) (-1 + Complex.I)]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [MagicFunction.a.RealIntegrands.Φ₁_def, scalarOneForm_apply,
      SpherePacking.Contour.lineMap_z₁_eq_z₁' (t := t) (uIcc_aux ht)]

/-- Rewrite `I₂'` as a curve integral of `Φ₁'` along the segment `-1 + i → i`. -/
public lemma I₂'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r))
    ((-1 : ℂ) + Complex.I) Complex.I]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [MagicFunction.a.RealIntegrands.Φ₂_def, scalarOneForm_apply,
      SpherePacking.Contour.lineMap_z₂_eq_z₂' (t := t) (uIcc_aux ht),
      MagicFunction.a.ComplexIntegrands.Φ₂']

lemma I₃'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₃' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
    (1 : ℂ) ((1 : ℂ) + Complex.I)]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [MagicFunction.a.RealIntegrands.Φ₃_def, scalarOneForm_apply,
      SpherePacking.Contour.lineMap_z₃_eq_z₃' (t := t) (uIcc_aux ht)]

lemma I₄'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
    ((1 : ℂ) + Complex.I) Complex.I]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [MagicFunction.a.RealIntegrands.Φ₄_def, scalarOneForm_apply,
      SpherePacking.Contour.lineMap_z₄_eq_z₄' (t := t) (uIcc_aux ht),
      MagicFunction.a.ComplexIntegrands.Φ₄']

/-- Rewrite `I₃' + I₄'` as a sum of curve integrals of `Φ₃'` along the two segments
`1 → 1 + i` and `1 + i → i`. -/
public lemma I₃'_add_I₄'_eq_curveIntegral_segments (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₃' r + MagicFunction.a.RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
          scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z := by
  simp [I₃'_eq_curveIntegral_segment, I₄'_eq_curveIntegral_segment]

/-- If `z` lies in the upper half-plane, then so does `-1 / z` (in terms of imaginary part). -/
public lemma neg_one_div_im_pos (z : ℂ) (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h => absurd (by simp [h] : z.im = 0) hz.ne'
  simpa [div_eq_mul_inv, Complex.inv_im] using div_pos hz (Complex.normSq_pos.2 hz0)

/-- The Fourier-side integrand corresponding to `Φ₁'`, including the Mobius inversion Jacobian.

This is the holomorphic function whose curve integral appears in `fourier_I₁_eq_curveIntegral` and
`fourier_I₂_eq_curveIntegral`. -/
@[expose] public def Φ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 *
    (((Complex.I : ℂ) / z) ^ (4 : ℕ)) *
      cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * (-1 / z))

lemma Φ₁_fourier_eq_one_div_sq_mul_Φ₃' (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z = (1 / z ^ (2 : ℕ)) * MagicFunction.a.ComplexIntegrands.Φ₃' r (-1 / z) := by
  have hz0 : z ≠ 0 := fun h => absurd (show z.im = 0 by simp [h]) hz.ne'
  have hz2 : z ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hz0
  have hφ := φ₀''_inv_add_one_mul_sq' (w := -1 / z) (neg_one_div_im_pos z hz)
  have hrew : (-1 / (-1 / z) : ℂ) = z := by field_simp
  simp [Φ₁_fourier, MagicFunction.a.ComplexIntegrands.Φ₃',
    show φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * (((Complex.I : ℂ) / z) ^ (4 : ℕ)) =
      (1 / z ^ (2 : ℕ)) * (φ₀'' (-1 / ((-1 / z) - 1)) * ((-1 / z) - 1) ^ 2) from by grind only,
    mul_assoc, mul_left_comm, mul_comm]

/-- Modular identity relating `Φ₁_fourier` to `Φ₃'` via `mobiusInv` and its derivative.

The prime at the end of the name comes from the integrand `Φ₃'`. -/
public lemma Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃' (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z = (deriv SpherePacking.mobiusInv z) *
      MagicFunction.a.ComplexIntegrands.Φ₃' r (SpherePacking.mobiusInv z) := by
  simpa [SpherePacking.mobiusInv, SpherePacking.deriv_mobiusInv (z := z), div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm] using Φ₁_fourier_eq_one_div_sq_mul_Φ₃' r z hz

end CurveIntegral

end Integral_Permutations

end
end MagicFunction.a.Fourier

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

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

lemma fourier_involution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) :
    FourierTransform.fourierCLE ℂ (SchwartzMap V E)
        (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f) = fun x => f (-x) :=
by
  ext x; change 𝓕 (𝓕 f) x = f (-x)
  simpa [Real.fourierInv_eq_fourier_neg, neg_neg] using
    congrArg (fun g : V → E => g (-x)) (f.continuous.fourierInv_fourier_eq f.integrable
      (by simpa using (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f).integrable))

/-- If `f` is an even Schwartz function, then applying the Fourier transform twice gives back `f`.

This is used to invert permutation identities for radial (hence even) functions. -/
public lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) (hf : Function.Even f) :
    FourierTransform.fourierCLE ℂ (SchwartzMap V E)
        (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f) = f :=
by
  ext x; simpa [hf x] using congrArg (fun g => g x) (fourier_involution (V:=V) (E:=E) f)

lemma φ₀''_add_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z + 1) = φ₀'' z := by
  simpa using (MagicFunction.a.SpecialValues.φ₀''_add_one (z := z) hz)

lemma φ₀''_sub_one (z : ℂ) (hz : 0 < z.im) : φ₀'' (z - 1) = φ₀'' z := by
  simpa using (φ₀''_add_one (z := z - 1) (by simpa using hz)).symm

lemma neg_one_div_sub_one_im_pos (w : ℂ) (hw : 0 < w.im) :
    0 < (-1 / (w - 1)).im := by
  have hw' : 0 < (w - 1).im := by simpa using hw
  have hne : w - 1 ≠ 0 := by
    intro h
    have : (w - 1).im = 0 := by simp [h]
    exact (lt_irrefl (0 : ℝ)) (this ▸ hw')
  have hnormSq_pos : 0 < Complex.normSq (w - 1) := (Complex.normSq_pos).2 hne
  have : 0 < (w - 1).im / Complex.normSq (w - 1) := div_pos hw' hnormSq_pos
  simpa [div_eq_mul_inv, sub_eq_add_neg, Complex.inv_im] using this

lemma one_sub_inv_sq_mul_sq (w : ℂ) (hw : w ≠ 0) :
    ((-1 / w + 1) ^ 2) * w ^ 2 = (w - 1) ^ 2 := by
  field_simp [hw]
  ring

lemma φ₀''_inv_add_one_mul_sq (w : ℂ) (hw : 0 < w.im) :
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 * w ^ 2 =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
  have hw0 : w ≠ 0 := by intro hw0; simpa [hw0] using hw.ne'
  have harg :
      (-1 / ((-1 / w) + 1)) = (-1 / (w - 1)) - 1 := by
    have hw1 : w - 1 ≠ 0 := by
      intro h
      have him0 : (w - 1).im = 0 := by simp [h]
      have hw' : 0 < (w - 1).im := by simpa using hw
      exact (lt_irrefl (0 : ℝ)) (him0 ▸ hw')
    have hden : (-1 / w + 1) = (w - 1) / w := by
      field_simp [hw0]
      ring
    -- Both sides simplify to `-w / (w - 1)`.
    calc
      (-1 / ((-1 / w) + 1))
          = (-1 : ℂ) / ((w - 1) / w) := by
              simp [hden]
      _ = (-1 : ℂ) * ((w - 1) / w)⁻¹ := by simp [div_eq_mul_inv]
      _ = (-1 : ℂ) * (w / (w - 1)) := by
              simp [inv_div]
      _ = (-w) / (w - 1) := by ring
      _ = (-1 / (w - 1)) - 1 := by
              field_simp [hw1]
              ring
  have hφ :
      φ₀'' (-1 / ((-1 / w) + 1)) = φ₀'' (-1 / (w - 1)) := by
    have him : 0 < (-1 / (w - 1)).im := neg_one_div_sub_one_im_pos w hw
    -- `-1/((-1/w)+1)` is `(-1/(w-1)) - 1`
    simpa [harg] using (φ₀''_sub_one (z := -1 / (w - 1)) him)
  have hsq : ((-1 / w + 1) ^ 2) * w ^ 2 = (w - 1) ^ 2 := one_sub_inv_sq_mul_sq w hw0
  -- Combine the two simplifications.
  calc
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 * w ^ 2
        = φ₀'' (-1 / ((-1 / w) + 1)) * (((-1 / w) + 1) ^ 2 * w ^ 2) := by ring
    _ = φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
          simp [hφ, hsq]

lemma I_div_neg_one_div_pow_four_mul_one_div_sq (w : ℂ) :
    ((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (1 / w ^ (2 : ℕ)) = w ^ (2 : ℕ) := by
  by_cases hw : w = 0
  · subst hw; simp
  · field_simp [hw]
    simp [Complex.I_pow_four]

lemma φ₀''_inv_add_one_mul_sq' (w : ℂ) (hw : 0 < w.im) :
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 *
        (((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹) =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
  -- Replace the extra Fourier/Jacobian factor by `w^2`, then apply the main simplification lemma.
  have hfac :
      ((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹ = w ^ (2 : ℕ) :=
    by simpa [div_eq_mul_inv] using (I_div_neg_one_div_pow_four_mul_one_div_sq (w := w))
  simpa [hfac] using (φ₀''_inv_add_one_mul_sq (w := w) hw)


section CurveIntegral
open scoped Interval
open Complex

/-- Rewrite `I₁'` as a curve integral of `Φ₁'` along the segment `-1 → -1 + i`. -/
public lemma I₁'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) (-1 + Complex.I),
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r) z) := by
  -- Unfold the curve integral along a segment.
  rw [curveIntegral_segment
    (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r))
    (-1 : ℂ) (-1 + Complex.I)]
  -- Unfold `I₁'` and the real integrand `Φ₁`.
  simp only [MagicFunction.a.RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁_def]
  -- Reduce to pointwise equality of the integrands on `[0,1]`.
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hzlin :
      AffineMap.lineMap (-1 : ℂ) (-1 + Complex.I) t = MagicFunction.Parametrisations.z₁' t :=
    SpherePacking.Contour.lineMap_z₁_eq_z₁' (t := t) ht'
  simp [scalarOneForm_apply, hzlin]

/-- Rewrite `I₂'` as a curve integral of `Φ₁'` along the segment `-1 + i → i`. -/
public lemma I₂'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r) z) := by
  rw [curveIntegral_segment
    (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₁' r))
    ((-1 : ℂ) + Complex.I) Complex.I]
  simp only [MagicFunction.a.RealIntegrals.I₂', MagicFunction.a.RealIntegrands.Φ₂_def]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hzlin :
      AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t = MagicFunction.Parametrisations.z₂' t :=
    SpherePacking.Contour.lineMap_z₂_eq_z₂' (t := t) ht'
  simp [scalarOneForm_apply, hzlin, MagicFunction.a.ComplexIntegrands.Φ₂']

lemma I₃'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₃' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) := by
  rw [curveIntegral_segment
    (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
    (1 : ℂ) ((1 : ℂ) + Complex.I)]
  simp only [MagicFunction.a.RealIntegrals.I₃', MagicFunction.a.RealIntegrands.Φ₃_def]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hzlin :
      AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) t = MagicFunction.Parametrisations.z₃' t :=
    SpherePacking.Contour.lineMap_z₃_eq_z₃' (t := t) ht'
  simp [scalarOneForm_apply, hzlin]

lemma I₄'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) := by
  rw [curveIntegral_segment
    (ω := scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
    ((1 : ℂ) + Complex.I) Complex.I]
  simp only [MagicFunction.a.RealIntegrals.I₄', MagicFunction.a.RealIntegrands.Φ₄_def]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hzlin :
      AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I t = MagicFunction.Parametrisations.z₄' t :=
    SpherePacking.Contour.lineMap_z₄_eq_z₄' (t := t) ht'
  simp [scalarOneForm_apply, hzlin, MagicFunction.a.ComplexIntegrands.Φ₄']

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
  have hz0 : z ≠ 0 := by
    intro hz0
    have : z.im = 0 := by simp [hz0]
    exact (lt_irrefl (0 : ℝ)) (this ▸ hz)
  have hnormSq_pos : 0 < Complex.normSq z := (Complex.normSq_pos).2 hz0
  have : 0 < z.im / Complex.normSq z := div_pos hz hnormSq_pos
  simpa [div_eq_mul_inv, Complex.inv_im] using this

/-- The Fourier-side integrand corresponding to `Φ₁'`, including the Mobius inversion Jacobian.

This is the holomorphic function whose curve integral appears in `fourier_I₁_eq_curveIntegral` and
`fourier_I₂_eq_curveIntegral`. -/
@[expose] public def Φ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 *
    (((Complex.I : ℂ) / z) ^ (4 : ℕ)) *
      cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * (-1 / z))

lemma Φ₁_fourier_eq_one_div_sq_mul_Φ₃' (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z = (1 / z ^ (2 : ℕ)) * MagicFunction.a.ComplexIntegrands.Φ₃' r (-1 / z) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    simpa [hz0] using hz.ne'
  have hw : 0 < (-1 / z).im := neg_one_div_im_pos z hz
  have hφ :=
    (φ₀''_inv_add_one_mul_sq' (w := (-1 / z)) hw)
  have hrew : (-1 / (-1 / z) : ℂ) = z := by
    field_simp [hz0]
  have hsq : (((-1 / z) ^ (2 : ℕ) : ℂ)⁻¹) = z ^ (2 : ℕ) := by
    simp [div_eq_mul_inv, pow_two]
  have hφz :
      φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 *
          (((Complex.I : ℂ) / z) ^ (4 : ℕ) * (z ^ (2 : ℕ))) =
        φ₀'' (-1 / ((-1 / z) - 1)) * ((-1 / z) - 1) ^ 2 := by
    simpa [hrew, hsq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hφ
  have hz2 : z ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hz0
  have hcoef :
      φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * (((Complex.I : ℂ) / z) ^ (4 : ℕ)) =
        (1 / z ^ (2 : ℕ)) * (φ₀'' (-1 / ((-1 / z) - 1)) * ((-1 / z) - 1) ^ 2) := by
    -- Multiply `hφz` by `1 / z^2` and cancel.
    have h := congrArg (fun t : ℂ => (1 / z ^ (2 : ℕ)) * t) hφz
    -- simplify the left-hand side
    -- `1/z^2 * (A * (B * z^2)) = A * B` by commutativity and `inv_mul_cancel`.
    simpa [div_eq_mul_inv, hz2, mul_assoc, mul_left_comm, mul_comm] using h
  -- Reattach the exponential; it matches the definition of `Φ₃'`.
  simp [Φ₁_fourier, MagicFunction.a.ComplexIntegrands.Φ₃', hcoef,
    mul_assoc, mul_left_comm, mul_comm]

/-- Modular identity relating `Φ₁_fourier` to `Φ₃'` via `mobiusInv` and its derivative.

The prime at the end of the name comes from the integrand `Φ₃'`. -/
public lemma Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃' (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z =
      (deriv SpherePacking.mobiusInv z) *
        MagicFunction.a.ComplexIntegrands.Φ₃' r (SpherePacking.mobiusInv z) := by
  -- Rewrite both sides using the previously established modular identity
  -- and the derivative formula.
  -- `SpherePacking.mobiusInv z = -1 / z`.
  simpa [SpherePacking.mobiusInv, div_eq_mul_inv, SpherePacking.deriv_mobiusInv (z := z),
    mul_assoc, mul_left_comm,
    mul_comm] using
    (Φ₁_fourier_eq_one_div_sq_mul_Φ₃' (r := r) (z := z) hz)

end CurveIntegral

end Integral_Permutations

end
end MagicFunction.a.Fourier

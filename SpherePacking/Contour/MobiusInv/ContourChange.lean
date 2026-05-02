module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import SpherePacking.ForMathlib.ScalarOneForm

public import SpherePacking.Contour.MobiusInv.Basic
public import SpherePacking.Contour.MobiusInv.Segments
import SpherePacking.Contour.Segments
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Mobius inversion: contour change on segments

This file proves change-of-variables lemmas for curve integrals on straight segments under
`SpherePacking.mobiusInv`.

The key ingredients are:
- evaluation and derivative identities for `Path.segment.map'`;
- a generic lemma rewriting a segment integral in terms of the mapped segment; and
- a small typeclass `SegmentHyp` packaging the hypotheses needed for the Mobius inversion map.
-/

open scoped Interval
open MeasureTheory
open MagicFunction

namespace SpherePacking.Contour

noncomputable section

/--
Change-of-variables lemma for curve integrals on a straight segment.

Given a relation between `Ψ` and `Ψ'` involving the derivative of a map `f`, we can rewrite the
curve integral on `Path.segment a b` in terms of the mapped path `(Path.segment a b).map' f`.
-/
public lemma curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of
    {Ψ Ψ' : ℝ → ℂ → ℂ} (a b : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range (Path.segment a b)))
    (hΨ :
      ∀ r : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
        (b - a) * Ψ r (AffineMap.lineMap a b t) =
          -(deriv (fun s : ℝ => f (AffineMap.lineMap a b s)) t) *
            Ψ' r (f (AffineMap.lineMap a b t)))
    (r : ℝ) :
    (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ r) z) =
      -∫ᶜ z in (Path.segment a b).map' (f := f) hf, scalarOneForm (Ψ' r) z := by
  let γw : Path (f a) (f b) := (Path.segment a b).map' (f := f) hf
  have hExt : ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 →
      γw.extend t = f (AffineMap.lineMap a b t) :=
    fun {t} ht => by simpa [γw] using γw.extend_apply ⟨ht.1.le, ht.2.le⟩
  rw [curveIntegral_segment (ω := scalarOneForm (Ψ r)) a b,
    curveIntegral_eq_intervalIntegral_deriv (ω := scalarOneForm (Ψ' r)) γw,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae_restrict (μ := (volume : Measure ℝ)) ?_
  simpa [Set.uIoc_of_le zero_le_one] using show
      (fun t : ℝ =>
          scalarOneForm (Ψ r) (AffineMap.lineMap a b t) (b - a)) =ᵐ[
        (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)] fun t : ℝ =>
          -(scalarOneForm (Ψ' r) (γw.extend t) (deriv γw.extend t)) by
    filter_upwards [show ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
        t ∈ Set.Ioo (0 : ℝ) 1 by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        Measure.ae_ne (volume.restrict (Set.Ioc 0 1)) 1] with t ht htne1
      exact ⟨ht.1, lt_of_le_of_ne ht.2 htne1⟩] with t ht
    simp [scalarOneForm_apply, hExt ht,
      show deriv γw.extend t = deriv (fun s : ℝ => f (AffineMap.lineMap a b s)) t by
        simpa using
          (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs => hExt hs).deriv_eq,
      hΨ r t ht]

end

end SpherePacking.Contour

namespace SpherePacking.MobiusInv

/--
Hypotheses for applying the Mobius inversion contour-change lemma on a segment `a → b`.

We require:
- the segment stays in the upper half-plane (so `mobiusInv` is well-behaved), and
- `mobiusInv` is continuous on the segment.
-/
public class SegmentHyp (a b : ℂ) : Prop where
  lineMap_im_pos : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → 0 < (AffineMap.lineMap a b t).im
  continuousOn_mobiusInv_segment : ContinuousOn mobiusInv (Set.range (Path.segment a b))

/-- `SegmentHyp` for the segment `-1 → -1 + I`. -/
public instance segmentHyp_z₁ :
    SegmentHyp (-1 : ℂ) ((-1 : ℂ) + Complex.I) where
  lineMap_im_pos := fun t ht => by
    simpa [SpherePacking.Contour.lineMap_z₁line, SpherePacking.Contour.z₁line_im] using ht.1
  continuousOn_mobiusInv_segment := continuousOn_mobiusInv_segment_z₁

/-- `SegmentHyp` for the segment `-1 + I → I`. -/
public instance segmentHyp_z₂ :
    SegmentHyp ((-1 : ℂ) + Complex.I) Complex.I where
  lineMap_im_pos := fun _ _ => by simp [SpherePacking.Contour.lineMap_z₂line]
  continuousOn_mobiusInv_segment := continuousOn_mobiusInv_segment_z₂

/--
Specialize `curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of` to `mobiusInv`,
in the "minus derivative" form used in `perm_J12` contour changes.
-/
public lemma curveIntegral_segment_neg_inv
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (a b : ℂ)
    [hs : SegmentHyp (a := a) (b := b)]
    (Ψ₁_fourier_eq_neg_deriv_mul :
      ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (r : ℝ) :
    (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ₁_fourier r) z) =
      -∫ᶜ z in
        (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
        scalarOneForm (Ψ₁' r) z := by
  refine
    SpherePacking.Contour.curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of
      (Ψ := Ψ₁_fourier) (Ψ' := Ψ₁') a b (f := mobiusInv) (hf := hs.continuousOn_mobiusInv_segment)
      (hΨ := fun r t ht => ?_) (r := r)
  have hz_im : 0 < (AffineMap.lineMap a b t).im := hs.lineMap_im_pos t ht
  have hz0 : AffineMap.lineMap a b t ≠ 0 :=
    fun hz0 => (ne_of_gt hz_im) (by simp [hz0])
  have hderiv :=
    (SpherePacking.hasDerivAt_mobiusInv_comp_lineMap (a := a) (b := b) (t := t) hz0).deriv
  simpa [hderiv, _root_.SpherePacking.deriv_mobiusInv, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using
    congrArg (fun z => (b - a) * z)
      (Ψ₁_fourier_eq_neg_deriv_mul (r := r) (z := AffineMap.lineMap a b t) hz_im)

/--
Variant of `curveIntegral_segment_neg_inv` where the Fourier-side identity uses
`+(deriv mobiusInv)`.
-/
public lemma curveIntegral_segment_pos_inv
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (a b : ℂ)
    [hs : SegmentHyp (a := a) (b := b)]
    (Ψ₁_fourier_eq_deriv_mul :
      ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = (deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (r : ℝ) :
    (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ₁_fourier r) z) =
      ∫ᶜ z in
        (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
        scalarOneForm (Ψ₁' r) z := by
  have hω : (fun z : ℂ => scalarOneForm (fun z : ℂ => -Ψ₁' r z) z) =
      fun z : ℂ => -scalarOneForm (Ψ₁' r) z := by
    funext z; ext; simp [scalarOneForm_apply, mul_neg]
  have hneg := curveIntegral_segment_neg_inv (Ψ₁_fourier := Ψ₁_fourier)
    (Ψ₁' := fun r z => -Ψ₁' r z) a b
    (Ψ₁_fourier_eq_neg_deriv_mul := fun r z hz => by
      simpa [neg_mul, mul_neg, neg_neg] using (Ψ₁_fourier_eq_deriv_mul (r := r) (z := z) hz)) r
  simp_all

end SpherePacking.MobiusInv

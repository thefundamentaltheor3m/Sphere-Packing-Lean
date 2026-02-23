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
On the interior of the parameter interval, the `extend` of a mapped segment evaluates pointwise as
expected.
-/
public lemma segment_map'_extend_eq (a b : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range (Path.segment a b))) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ((Path.segment a b).map' (f := f) hf).extend t = f (AffineMap.lineMap a b t) := by
  simpa using ((Path.segment a b).map' (f := f) hf).extend_apply ⟨ht.1.le, ht.2.le⟩

/--
The derivative of a mapped segment agrees with the derivative of its explicit parametrization.
-/
public lemma deriv_segment_map'_extend_eq (a b : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range (Path.segment a b))) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (((Path.segment a b).map' (f := f) hf).extend) t =
      deriv (fun s : ℝ => f (AffineMap.lineMap a b s)) t := by
  simpa using
    (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
        segment_map'_extend_eq (a := a) (b := b) (f := f) hf (t := s) hs).deriv_eq

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
  rw [curveIntegral_segment (ω := scalarOneForm (Ψ r)) a b,
    curveIntegral_eq_intervalIntegral_deriv (ω := scalarOneForm (Ψ' r)) γw,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae_restrict (μ := (volume : Measure ℝ)) ?_
  have hEqAE :
      (fun t : ℝ =>
          scalarOneForm (Ψ r) (AffineMap.lineMap a b t) (b - a)) =ᵐ[
        (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)] fun t : ℝ =>
          -(scalarOneForm (Ψ' r) (γw.extend t) (deriv γw.extend t)) := by
    have htIoo :
        ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
          t ∈ Set.Ioo (0 : ℝ) 1 := by
      have hne1 :
          ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)), t ≠ 1 := by
        have : ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) ({(1 : ℝ)} : Set ℝ) = 0 := by
          simp
        simpa [Set.mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.1 this)
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with t ht htne1
      exact ⟨ht.1, lt_of_le_of_ne ht.2 htne1⟩
    filter_upwards [htIoo] with t ht
    have hγw_val : γw.extend t = f (AffineMap.lineMap a b t) :=
      segment_map'_extend_eq (a := a) (b := b) (f := f) hf (t := t) ht
    have hderiv_w :
        deriv γw.extend t = deriv (fun s : ℝ => f (AffineMap.lineMap a b s)) t := by
      simpa [γw] using deriv_segment_map'_extend_eq (a := a) (b := b) (f := f) hf (t := t) ht
    simp [scalarOneForm_apply, hγw_val, hderiv_w, hΨ r t ht]
  simpa [Set.uIoc_of_le zero_le_one] using hEqAE

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

/-- Imaginary part positivity along the segment `-1 → -1 + I`. -/
public lemma lineMap_im_pos_z₁
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t).im := by
  simpa [SpherePacking.Contour.lineMap_z₁line, SpherePacking.Contour.z₁line_im] using ht.1

/-- Imaginary part positivity along the segment `-1 + I → I`. -/
public lemma lineMap_im_pos_z₂ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t).im := by
  -- Here the imaginary part is constantly `1`.
  simp [SpherePacking.Contour.lineMap_z₂line]

/-- `SegmentHyp` for the segment `-1 → -1 + I`. -/
public instance segmentHyp_z₁ :
    SegmentHyp (-1 : ℂ) ((-1 : ℂ) + Complex.I) where
  lineMap_im_pos := fun t ht => lineMap_im_pos_z₁ t ht
  continuousOn_mobiusInv_segment := continuousOn_mobiusInv_segment_z₁

/-- `SegmentHyp` for the segment `-1 + I → I`. -/
public instance segmentHyp_z₂ :
    SegmentHyp ((-1 : ℂ) + Complex.I) Complex.I where
  lineMap_im_pos := fun t ht => lineMap_im_pos_z₂ t ht
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
      (hΨ := ?_) (r := r)
  intro r t ht
  have hz_im : 0 < (AffineMap.lineMap a b t).im := hs.lineMap_im_pos t ht
  have hz0 : AffineMap.lineMap a b t ≠ 0 := by
    intro hz
    have : (AffineMap.lineMap a b t).im = 0 := by simpa using congrArg Complex.im hz
    exact (ne_of_gt hz_im) this
  have hderiv :
      deriv (fun s : ℝ => mobiusInv (AffineMap.lineMap a b s)) t =
        (b - a) / (AffineMap.lineMap a b t) ^ (2 : ℕ) := by
    simpa using
      (SpherePacking.hasDerivAt_mobiusInv_comp_lineMap (a := a) (b := b) (t := t) hz0).deriv
  have hderiv' :
      deriv (fun s : ℝ => mobiusInv (AffineMap.lineMap a b s)) t =
        (b - a) * deriv mobiusInv (AffineMap.lineMap a b t) := by
    simp [hderiv, _root_.SpherePacking.deriv_mobiusInv, div_eq_mul_inv]
  rw [hderiv']
  simpa [mul_assoc, mul_left_comm, mul_comm] using
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
  have hneg :
      (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ₁_fourier r) z) =
        -∫ᶜ z in
          (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
          scalarOneForm (fun z : ℂ => -Ψ₁' r z) z := by
    simpa [neg_mul, mul_neg, neg_neg] using
      (curveIntegral_segment_neg_inv (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := fun r z => -Ψ₁' r z) a b
        (Ψ₁_fourier_eq_neg_deriv_mul := by
          intro r z hz
          simpa [neg_mul, mul_neg, neg_neg] using (Ψ₁_fourier_eq_deriv_mul (r := r) (z := z) hz))
        r)
  have hinner :
      (∫ᶜ z in
            (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
          scalarOneForm (fun z : ℂ => -Ψ₁' r z) z) =
        -∫ᶜ z in
            (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
          scalarOneForm (Ψ₁' r) z := by
    have hω :
        (fun z : ℂ => scalarOneForm (fun z : ℂ => -Ψ₁' r z) z) =
          fun z : ℂ => -scalarOneForm (Ψ₁' r) z := by
      funext z
      ext
      simp [scalarOneForm_apply]
    simp [hω]
  calc
    (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ₁_fourier r) z) =
        -∫ᶜ z in
          (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
          scalarOneForm (fun z : ℂ => -Ψ₁' r z) z := hneg
    _ = _ := by simp [hinner]

end SpherePacking.MobiusInv

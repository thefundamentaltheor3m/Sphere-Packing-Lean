module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.Contour.MobiusInv.Basic
import SpherePacking.Contour.Segments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Order.LatticeIntervals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Contour identities for `mobiusInv` on `wedgeSet`.

Contains the shared contour deformation lemmas (`perm_J12_contour_h1` / `perm_J12_contour_h2`,
together with `ClosedOneFormOn` and the `PermJ12ContourH1/2Hyp` structures) and the assembled
`perm_J12` / `perm_I12` identities specialized to `mobiusInv` and `wedgeSet`. Also includes
the underlying continuity, mapped paths, and change-of-variables lemmas for curve integrals
on segments under `mobiusInv` (via the `SegmentHyp` typeclass).
-/

namespace SpherePacking

noncomputable section

open Complex

private lemma continuousOn_mobiusInv_segment_of_ne_zero (a b : ℂ)
    (segment_ne_zero : ∀ t : Set.Icc (0 : ℝ) 1, Path.segment a b t ≠ 0) :
    ContinuousOn mobiusInv (Set.range (Path.segment a b)) := by
  rintro _ ⟨t, rfl⟩
  simpa [mobiusInv] using (continuousAt_inv₀ (segment_ne_zero t)).neg.continuousWithinAt

/-- `mobiusInv` is continuous on the segment `-1 → -1 + I`. -/
public lemma continuousOn_mobiusInv_segment_z₁ :
    ContinuousOn mobiusInv (Set.range (Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I))) := by
  simpa using continuousOn_mobiusInv_segment_of_ne_zero (-1) (-1 + I) segment_z₁_ne_zero

/-- `mobiusInv` is continuous on the segment `-1 + I → I`. -/
public lemma continuousOn_mobiusInv_segment_z₂ :
    ContinuousOn mobiusInv (Set.range (Path.segment ((-1 : ℂ) + Complex.I) Complex.I)) := by
  simpa using continuousOn_mobiusInv_segment_of_ne_zero (-1 + I) I segment_z₂_ne_zero

/-- The segment `-1 → -1 + I` mapped by `mobiusInv`, bundled as a path. -/
public abbrev mobiusInv_segment_z₁ :
    Path (mobiusInv (-1 : ℂ)) (mobiusInv ((-1 : ℂ) + Complex.I)) :=
  (Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I)).map'
    (f := mobiusInv) (by simpa using continuousOn_mobiusInv_segment_z₁)

/-- The segment `-1 + I → I` mapped by `mobiusInv`, bundled as a path. -/
public abbrev mobiusInv_segment_z₂ :
    Path (mobiusInv ((-1 : ℂ) + Complex.I)) (mobiusInv Complex.I) :=
  (Path.segment ((-1 : ℂ) + Complex.I) Complex.I).map'
    (f := mobiusInv) (by simpa using continuousOn_mobiusInv_segment_z₂)

end

end SpherePacking

namespace SpherePacking.Contour

noncomputable section

open MeasureTheory MagicFunction

/-- Change-of-variables for curve integrals on a straight segment: given a relation between `Ψ`
and `Ψ'` involving the derivative of `f`, rewrite the curve integral on `Path.segment a b` via
the mapped path `(Path.segment a b).map' f`. -/
public lemma curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of
    {Ψ Ψ' : ℝ → ℂ → ℂ} (a b : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range (Path.segment a b)))
    (hΨ : ∀ r : ℝ, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
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
      (fun t : ℝ => scalarOneForm (Ψ r) (AffineMap.lineMap a b t) (b - a)) =ᵐ[
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

open Complex MagicFunction

/-- Hypotheses for applying the Mobius inversion contour-change lemma on a segment `a → b`:
the segment stays in the upper half-plane, and `mobiusInv` is continuous on it. -/
public class SegmentHyp (a b : ℂ) : Prop where
  lineMap_im_pos : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → 0 < (AffineMap.lineMap a b t).im
  continuousOn_mobiusInv_segment : ContinuousOn mobiusInv (Set.range (Path.segment a b))

/-- `SegmentHyp` for the segment `-1 → -1 + I`. -/
public instance segmentHyp_z₁ : SegmentHyp (-1 : ℂ) ((-1 : ℂ) + Complex.I) where
  lineMap_im_pos := fun t ht => by
    simpa [SpherePacking.Contour.lineMap_z₁line, SpherePacking.Contour.z₁line_im] using ht.1
  continuousOn_mobiusInv_segment := continuousOn_mobiusInv_segment_z₁

/-- `SegmentHyp` for the segment `-1 + I → I`. -/
public instance segmentHyp_z₂ : SegmentHyp ((-1 : ℂ) + Complex.I) Complex.I where
  lineMap_im_pos := fun _ _ => by simp [SpherePacking.Contour.lineMap_z₂line]
  continuousOn_mobiusInv_segment := continuousOn_mobiusInv_segment_z₂

/-- Specialize `curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of` to `mobiusInv`,
in the "minus derivative" form used in `perm_J12` contour changes. -/
public lemma curveIntegral_segment_neg_inv
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ} (a b : ℂ) [hs : SegmentHyp (a := a) (b := b)]
    (Ψ₁_fourier_eq_neg_deriv_mul : ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (r : ℝ) :
    (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ₁_fourier r) z) =
      -∫ᶜ z in (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
        scalarOneForm (Ψ₁' r) z := by
  refine
    SpherePacking.Contour.curveIntegral_segment_eq_neg_curveIntegral_segment_map'_of
      (Ψ := Ψ₁_fourier) (Ψ' := Ψ₁') a b (f := mobiusInv) (hf := hs.continuousOn_mobiusInv_segment)
      (hΨ := fun r t ht => ?_) (r := r)
  have hz_im : 0 < (AffineMap.lineMap a b t).im := hs.lineMap_im_pos t ht
  have hz0 : AffineMap.lineMap a b t ≠ 0 := fun hz0 => (ne_of_gt hz_im) (by simp [hz0])
  have hderiv :=
    (show HasDerivAt (fun s : ℝ => mobiusInv (AffineMap.lineMap a b s))
        ((b - a) / (AffineMap.lineMap a b t) ^ (2 : ℕ)) t by
      simpa [mobiusInv, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        ((by simpa [mobiusInv] using (hasFDerivAt_inv' (𝕜 := ℝ) (R := ℂ) hz0).neg :
          HasFDerivAt (𝕜 := ℝ) mobiusInv
            (ContinuousLinearMap.mulLeftRight ℝ ℂ (AffineMap.lineMap a b t)⁻¹
              (AffineMap.lineMap a b t)⁻¹) (AffineMap.lineMap a b t)).comp_hasDerivAt t
          (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t)))).deriv
  simpa [hderiv, _root_.SpherePacking.deriv_mobiusInv, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using
    congrArg (fun z => (b - a) * z)
      (Ψ₁_fourier_eq_neg_deriv_mul (r := r) (z := AffineMap.lineMap a b t) hz_im)

/-- Variant of `curveIntegral_segment_neg_inv` where the Fourier-side identity uses
`+(deriv mobiusInv)`. -/
public lemma curveIntegral_segment_pos_inv
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ} (a b : ℂ) [hs : SegmentHyp (a := a) (b := b)]
    (Ψ₁_fourier_eq_deriv_mul : ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = (deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (r : ℝ) :
    (∫ᶜ z in Path.segment a b, scalarOneForm (Ψ₁_fourier r) z) =
      ∫ᶜ z in (Path.segment a b).map' (f := mobiusInv) (hs.continuousOn_mobiusInv_segment),
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

open MeasureTheory
open MagicFunction

namespace SpherePacking.Contour

/-- `ClosedOneFormOn ω s` packages the hypotheses needed to apply the Poincaré lemma for curve
integrals on `s`: regularity (`DiffContOnCl`) plus symmetry of the `fderivWithin`. -/
public structure ClosedOneFormOn (ω : ℂ → ℂ →L[ℂ] ℂ) (s : Set ℂ) : Prop where
  diffContOnCl : DiffContOnCl ℝ ω s
  fderivWithin_symm :
    ∀ x ∈ s, ∀ u ∈ tangentConeAt ℝ s x, ∀ v ∈ tangentConeAt ℝ s x,
      fderivWithin ℝ ω s x u v = fderivWithin ℝ ω s x v u

/-- Hypotheses for `perm_J12_contour_h1` independent of the specific 1-form `scalarOneForm`:
the homotopy stays inside `wedgeSet` and is `C²` on `Icc (0,1)²`. -/
public structure PermJ12ContourH1Hyp (mobiusInv : ℂ → ℂ) (wedgeSet : Set ℂ) : Prop where
  continuousOn_mobiusInv_segment_z₁ :
    ContinuousOn mobiusInv (Set.range (Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I)))
  mobiusInv_neg_one : mobiusInv (-1 : ℂ) = 1
  homotopy_mem_wedgeSet :
    ∀ {x y : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      (AffineMap.lineMap (k := ℝ)
            (mobiusInv (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) y))
            (AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) y)) x ∈ wedgeSet
  contDiffOn_homotopy :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ =>
        (AffineMap.lineMap (k := ℝ)
          (mobiusInv (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) xy.2))
          (AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) xy.2)) xy.1)
      (Set.Icc (0 : ℝ × ℝ) 1)

/-- Hypotheses for `perm_J12_contour_h2` (analogue of `PermJ12ContourH1Hyp`). -/
public structure PermJ12ContourH2Hyp (mobiusInv : ℂ → ℂ) (wedgeSet : Set ℂ) : Prop where
  continuousOn_mobiusInv_segment_z₂ :
    ContinuousOn mobiusInv (Set.range (Path.segment ((-1 : ℂ) + Complex.I) Complex.I))
  mobiusInv_I : mobiusInv Complex.I = Complex.I
  homotopy_mem_wedgeSet :
    ∀ {x y : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      (AffineMap.lineMap (k := ℝ)
            (mobiusInv (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I y))
            (AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I y)) x ∈ wedgeSet
  contDiffOn_homotopy :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ =>
        (AffineMap.lineMap (k := ℝ)
          (mobiusInv (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I xy.2))
          (AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I xy.2)) xy.1)
      (Set.Icc (0 : ℝ × ℝ) 1)

/-- Bundled inputs to `perm_J12_contour_h1` (excluding the parameter `r`). -/
public structure PermJ12ContourH1Args (mobiusInv : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ)
    (wedgeSet : Set ℂ) : Prop where
  closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet
  hyp : PermJ12ContourH1Hyp mobiusInv wedgeSet

/-- Bundled inputs to `perm_J12_contour_h2` (excluding the parameter `r`). -/
public structure PermJ12ContourH2Args (mobiusInv : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ)
    (wedgeSet : Set ℂ) : Prop where
  closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet
  hyp : PermJ12ContourH2Hyp mobiusInv wedgeSet

private lemma perm_J12_contour_h_aux {mobiusInv : ℂ → ℂ} {Ψ₁' : ℝ → ℂ → ℂ} {wedgeSet : Set ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (p0 p1 q0 q1 : ℂ)
    (continuousOn_mobiusInv_segment :
      ContinuousOn mobiusInv (Set.range (Path.segment p0 p1)))
    (homotopy_mem_wedgeSet : ∀ {x y : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      (AffineMap.lineMap (k := ℝ) (mobiusInv (AffineMap.lineMap p0 p1 y))
        (AffineMap.lineMap q0 q1 y)) x ∈ wedgeSet)
    (contDiffOn_homotopy : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => (AffineMap.lineMap (k := ℝ) (mobiusInv (AffineMap.lineMap p0 p1 xy.2))
        (AffineMap.lineMap q0 q1 xy.2)) xy.1)
      (Set.Icc (0 : ℝ × ℝ) 1))
    (r : ℝ) :
    (∫ᶜ z in (Path.segment p0 p1).map' continuousOn_mobiusInv_segment,
          scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv p1) q1,
          scalarOneForm (Ψ₁' r) z =
      (∫ᶜ z in Path.segment (mobiusInv p0) q0,
            scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment q0 q1, scalarOneForm (Ψ₁' r) z := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := scalarOneForm (Ψ₁' r)
  let γ : Path (mobiusInv p0) (mobiusInv p1) :=
    (Path.segment p0 p1).map' continuousOn_mobiusInv_segment
  let δ : Path q0 q1 := Path.segment q0 q1
  let I01 : Set ℝ := unitInterval
  let φ : (γ : C(I01, ℂ)).Homotopy δ := .affine ..
  have hφt : ∀ a ∈ Set.Ioo 0 1, ∀ b ∈ Set.Ioo 0 1, φ (a, b) ∈ wedgeSet := fun a ha b hb => by
    simpa [φ, γ, δ, Path.map', Path.segment_apply] using
      (homotopy_mem_wedgeSet (x := (a : ℝ)) (y := (b : ℝ)) ha hb)
  have hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
      (Set.Icc (0 : ℝ × ℝ) 1) := by
    refine (contDiffOn_congr ?_).2 contDiffOn_homotopy
    rintro ⟨x, y⟩ ⟨h0, h1⟩
    let xI : I01 := ⟨x, h0.1, h1.1⟩
    let yI : I01 := ⟨y, h0.2, h1.2⟩
    calc Set.IccExtend (h := (zero_le_one : (0 : ℝ) ≤ 1)) (φ.extend x) y = (φ.extend x) yI := by
          simpa [yI] using
            (Set.IccExtend_of_mem (h := (zero_le_one : (0 : ℝ) ≤ 1)) (f := φ.extend x) ⟨h0.2, h1.2⟩)
      _ = φ (xI, yI) := by
          simpa [xI, yI] using
            (ContinuousMap.Homotopy.extend_apply_of_mem_I (F := φ) (ht := ⟨h0.1, h1.1⟩) (x := yI))
      _ = (Path.segment (γ yI) (δ yI) xI : ℂ) := rfl
      _ = _ := by simp [γ, δ, yI, Path.map', Path.segment_apply, xI]
  have h :
      (∫ᶜ z in γ, ω z) + ∫ᶜ z in Path.segment (γ (1 : I01)) (δ (1 : I01)), ω z =
        (∫ᶜ z in δ, ω z) + ∫ᶜ z in Path.segment (γ (0 : I01)) (δ (0 : I01)), ω z := by
    simpa [show φ.evalAt (0 : I01) = Path.segment (γ (0 : I01)) (δ (0 : I01)) from rfl,
      show φ.evalAt (1 : I01) = Path.segment (γ (1 : I01)) (δ (1 : I01)) from rfl] using
      ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl
        (𝕜 := ℂ) (E := ℂ) (F := ℂ) (γ₁ := γ) (γ₂ := δ) (t := wedgeSet) (ω := ω) (φ := φ)
        hφt (by simpa [ω] using (closed_ω_wedgeSet (r := r)).diffContOnCl)
        (by simpa [ω] using (closed_ω_wedgeSet (r := r)).fderivWithin_symm) hcontdiff
  rw [show (∫ᶜ z in Path.segment (mobiusInv p0) q0, ω z) =
        ∫ᶜ z in Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (0 : ℝ)))
            ((AffineMap.lineMap q0 q1) (0 : ℝ)), ω z by
      rw [← Path.cast_segment (by simp [AffineMap.lineMap_apply_zero] :
        mobiusInv p0 = mobiusInv ((AffineMap.lineMap p0 p1) (0 : ℝ)))
        (by simp [AffineMap.lineMap_apply_zero] : q0 = (AffineMap.lineMap q0 q1) (0 : ℝ))]
      exact curveIntegral_cast ω _ _ _,
    show (∫ᶜ z in Path.segment (mobiusInv p1) q1, ω z) =
        ∫ᶜ z in Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (1 : ℝ)))
            ((AffineMap.lineMap q0 q1) (1 : ℝ)), ω z by
      rw [← Path.cast_segment (by simp [AffineMap.lineMap_apply_one] :
        mobiusInv p1 = mobiusInv ((AffineMap.lineMap p0 p1) (1 : ℝ)))
        (by simp [AffineMap.lineMap_apply_one] : q1 = (AffineMap.lineMap q0 q1) (1 : ℝ))]
      exact curveIntegral_cast ω _ _ _]
  simpa [ω, γ, δ, Path.map', Path.segment_apply, add_assoc, add_left_comm, add_comm] using h

/-- Contour deformation `h1`: from mapped segment `(-1 → -1 + I)` to vertical segment
`(1 → 1 + I)` inside `wedgeSet`. -/
public lemma perm_J12_contour_h1 {mobiusInv : ℂ → ℂ} {Ψ₁' : ℝ → ℂ → ℂ} {wedgeSet : Set ℂ}
    (h : PermJ12ContourH1Args mobiusInv Ψ₁' wedgeSet) (r : ℝ) :
    (∫ᶜ z in
          (Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I)).map'
            (h.hyp.continuousOn_mobiusInv_segment_z₁),
          scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z =
      ∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z := by
  simpa [add_assoc, show (∫ᶜ z in Path.segment (mobiusInv (-1 : ℂ)) (1 : ℂ),
      scalarOneForm (Ψ₁' r) z) = 0 by rw [h.hyp.mobiusInv_neg_one]; simp [Path.segment_same]] using
    perm_J12_contour_h_aux h.closed_ω_wedgeSet
      (-1 : ℂ) ((-1 : ℂ) + Complex.I) (1 : ℂ) ((1 : ℂ) + Complex.I)
      h.hyp.continuousOn_mobiusInv_segment_z₁ (@h.hyp.homotopy_mem_wedgeSet)
      h.hyp.contDiffOn_homotopy r

/-- Contour deformation `h2`: from mapped segment `(-1 + I → I)` to vertical segment
`(1 + I → I)` inside `wedgeSet`. -/
public lemma perm_J12_contour_h2 {mobiusInv : ℂ → ℂ} {Ψ₁' : ℝ → ℂ → ℂ} {wedgeSet : Set ℂ}
    (h : PermJ12ContourH2Args mobiusInv Ψ₁' wedgeSet) (r : ℝ) :
    ∫ᶜ z in
          (Path.segment ((-1 : ℂ) + Complex.I) Complex.I).map'
            (h.hyp.continuousOn_mobiusInv_segment_z₂),
          scalarOneForm (Ψ₁' r) z =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z := by
  simpa [add_assoc, add_left_comm, add_comm, show (∫ᶜ z in Path.segment (mobiusInv Complex.I)
      Complex.I, scalarOneForm (Ψ₁' r) z) = 0 by rw [h.hyp.mobiusInv_I]; simp [Path.segment_same]]
    using perm_J12_contour_h_aux h.closed_ω_wedgeSet
      (((-1 : ℂ) + Complex.I)) Complex.I (((1 : ℂ) + Complex.I)) Complex.I
      h.hyp.continuousOn_mobiusInv_segment_z₂ (@h.hyp.homotopy_mem_wedgeSet)
      h.hyp.contDiffOn_homotopy r

end SpherePacking.Contour

namespace SpherePacking

noncomputable section

open SpherePacking.Contour

private lemma mobiusInv_re_im (x y : ℝ) :
    (-( ((x : ℂ) + Complex.I * (y : ℂ)) )⁻¹ : ℂ).re = (-x) / (x ^ 2 + y ^ 2) ∧
      (-( ((x : ℂ) + Complex.I * (y : ℂ)) )⁻¹ : ℂ).im = y / (x ^ 2 + y ^ 2) := by
  constructor <;>
    simp [Complex.inv_re, Complex.inv_im, Complex.normSq, pow_two, neg_div]

/-- Along `-1 → -1 + I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₁_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t) ∈ wedgeSet := by
  rw [Contour.lineMap_z₁line]
  obtain ⟨hre, him⟩ := mobiusInv_re_im (-1) t
  rw [show mobiusInv (Contour.z₁line t) = -(↑(-1 : ℝ) + Complex.I * ↑t)⁻¹ from by
    simp [mobiusInv, Contour.z₁line]] at *
  refine wedgeSet_iff.mpr ⟨by rw [him]; positivity, ?_⟩
  rw [hre, him]; simp only [fieldLt]
  constructor <;> nlinarith only [ht0, ht1]

/-- Along `-1 + I → I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₂_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t) ∈ wedgeSet := by
  rw [Contour.lineMap_z₂line]
  obtain ⟨hre, him⟩ := mobiusInv_re_im (t - 1) 1
  rw [show mobiusInv (Contour.z₂line t) = -(↑(t - 1) + Complex.I * ↑(1 : ℝ))⁻¹ from by
    simp [sub_eq_add_neg, add_comm, mobiusInv, Contour.z₂line], one_pow] at *
  refine wedgeSet_iff.mpr ⟨by rw [him]; positivity, ?_⟩
  rw [hre, him]; simp only [fieldLt]
  constructor <;> nlinarith only [ht0, ht1]

/-- `C^2` smoothness of the homotopy map
`(x,y) ↦ lineMap (mobiusInv (lineMap p0 p1 y)) (lineMap q0 q1 y) x`
on the unit square, assuming `lineMap p0 p1 y ≠ 0` throughout. -/
private lemma contDiffOn_lineMap_mobiusInv_lineMap (p0 p1 q0 q1 : ℂ)
    (hne : ∀ xy ∈ Set.Icc (0 : ℝ × ℝ) 1, (AffineMap.lineMap p0 p1 xy.2) ≠ 0) :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ =>
        (AffineMap.lineMap (k := ℝ)
            (mobiusInv (AffineMap.lineMap p0 p1 xy.2))
            (AffineMap.lineMap q0 q1 xy.2)) xy.1)
      (Set.Icc (0 : ℝ × ℝ) 1) := by
  have hline (a b : ℂ) :
      ContDiffOn ℝ 2 (fun xy => AffineMap.lineMap a b xy.2) (Set.Icc (0 : ℝ × ℝ) 1) := by
    simpa [AffineMap.lineMap_apply_module] using (by
      fun_prop :
        ContDiffOn ℝ 2 (fun xy => (1 - xy.2) • a + xy.2 • b) (Set.Icc (0 : ℝ × ℝ) 1))
  have hA : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => mobiusInv (AffineMap.lineMap p0 p1 xy.2))
      (Set.Icc (0 : ℝ × ℝ) 1) := by simpa [mobiusInv] using ((hline p0 p1).inv hne).neg
  simpa [AffineMap.lineMap_apply_module] using
    ((by fun_prop : ContDiffOn ℝ 2 (fun xy => (1 : ℝ) - xy.1) (Set.Icc (0 : ℝ × ℝ) 1)).smul hA).add
      ((by fun_prop : ContDiffOn ℝ 2 (fun xy => xy.1) (Set.Icc (0 : ℝ × ℝ) 1)).smul (hline q0 q1))

lemma perm_J12_contour_h1_mobiusInv_wedgeSet {Ψ₁' : ℝ → ℂ → ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet) (r : ℝ) :
    (∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z =
      ∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z :=
  perm_J12_contour_h1 (mobiusInv := mobiusInv) (Ψ₁' := Ψ₁') (wedgeSet := wedgeSet)
    ⟨closed_ω_wedgeSet,
      { continuousOn_mobiusInv_segment_z₁ := continuousOn_mobiusInv_segment_z₁
        mobiusInv_neg_one := by simp [mobiusInv]
        homotopy_mem_wedgeSet := fun hx hy => convex_wedgeSet.lineMap_mem
          (mobiusInv_lineMap_z₁_mem_wedgeSet hy.1 hy.2)
          (lineMap_z₃line_mem_wedgeSet hy.1) ⟨hx.1.le, hx.2.le⟩
        contDiffOn_homotopy := by
          refine contDiffOn_lineMap_mobiusInv_lineMap (-1) (-1 + Complex.I) 1 (1 + Complex.I) ?_
          rintro ⟨_x, y⟩ ⟨h0, h1⟩
          exact segment_z₁_ne_zero ⟨y, ⟨h0.2, h1.2⟩⟩ }⟩ r

lemma perm_J12_contour_h2_mobiusInv_wedgeSet {Ψ₁' : ℝ → ℂ → ℂ}
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet) (r : ℝ) :
    ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment (mobiusInv ((-1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z :=
  perm_J12_contour_h2 (mobiusInv := mobiusInv) (Ψ₁' := Ψ₁') (wedgeSet := wedgeSet)
    ⟨closed_ω_wedgeSet,
      { continuousOn_mobiusInv_segment_z₂ := continuousOn_mobiusInv_segment_z₂
        mobiusInv_I := by simp [mobiusInv]
        homotopy_mem_wedgeSet := fun hx hy => convex_wedgeSet.lineMap_mem
          (mobiusInv_lineMap_z₂_mem_wedgeSet hy.1 hy.2)
          (lineMap_z₄line_mem_wedgeSet hy.1 hy.2) ⟨hx.1.le, hx.2.le⟩
        contDiffOn_homotopy := by
          refine contDiffOn_lineMap_mobiusInv_lineMap
            (-1 + Complex.I) Complex.I (1 + Complex.I) Complex.I ?_
          rintro ⟨_x, y⟩ ⟨h0, h1⟩
          exact segment_z₂_ne_zero ⟨y, ⟨h0.2, h1.2⟩⟩ }⟩ r

private lemma perm_12_contour_mobiusInv_wedgeSet_aux
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ} (s : ℂ)
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet) (r : ℝ)
    (hseg1 : (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) =
        s * ∫ᶜ z in mobiusInv_segment_z₁, scalarOneForm (Ψ₁' r) z)
    (hseg2 : (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z) =
        s * ∫ᶜ z in mobiusInv_segment_z₂, scalarOneForm (Ψ₁' r) z) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      s * ((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Ψ₁' r) z) := by
  have := perm_J12_contour_h1_mobiusInv_wedgeSet closed_ω_wedgeSet r
  have := perm_J12_contour_h2_mobiusInv_wedgeSet closed_ω_wedgeSet r
  grind only

/-- Assembled `perm_J12` contour identity for `mobiusInv` and `wedgeSet`. -/
public lemma perm_J12_contour_mobiusInv_wedgeSet
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (Ψ₁_fourier_eq_neg_deriv_mul :
      ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      -((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
  simpa using
    perm_12_contour_mobiusInv_wedgeSet_aux (s := (-1 : ℂ)) closed_ω_wedgeSet r
      (hseg1 := by
        simpa [neg_one_mul] using SpherePacking.MobiusInv.curveIntegral_segment_neg_inv
          (Ψ₁' := Ψ₁') (-1 : ℂ) ((-1 : ℂ) + Complex.I) Ψ₁_fourier_eq_neg_deriv_mul r)
      (hseg2 := by
        simpa [neg_one_mul] using SpherePacking.MobiusInv.curveIntegral_segment_neg_inv
          (Ψ₁' := Ψ₁') ((-1 : ℂ) + Complex.I) Complex.I Ψ₁_fourier_eq_neg_deriv_mul r)

/-- Assembled `perm_I12` contour identity for `mobiusInv` and `wedgeSet`. -/
public lemma perm_I12_contour_mobiusInv_wedgeSet
    {Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ}
    (Ψ₁_fourier_eq_deriv_mul :
      ∀ r : ℝ, ∀ z : ℂ, 0 < z.im →
        Ψ₁_fourier r z = (deriv mobiusInv z) * Ψ₁' r (mobiusInv z))
    (closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z := by
  simpa using
    perm_12_contour_mobiusInv_wedgeSet_aux (s := (1 : ℂ)) closed_ω_wedgeSet r
      (hseg1 := by
        simpa using SpherePacking.MobiusInv.curveIntegral_segment_pos_inv (Ψ₁' := Ψ₁')
          (-1 : ℂ) ((-1 : ℂ) + Complex.I) Ψ₁_fourier_eq_deriv_mul r)
      (hseg2 := by
        simpa using SpherePacking.MobiusInv.curveIntegral_segment_pos_inv (Ψ₁' := Ψ₁')
          ((-1 : ℂ) + Complex.I) Complex.I Ψ₁_fourier_eq_deriv_mul r)

end

end SpherePacking

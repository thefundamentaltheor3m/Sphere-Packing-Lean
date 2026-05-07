module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Topology.Homotopy.Affine
public import SpherePacking.ForMathlib.ScalarOneForm

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Shared contour deformation lemmas for `J₁/J₂`

Underlies `perm_J12_contour_h1` and `perm_J12_contour_h2` in the `b`-eigenfunction Fourier
permutation proof. Topological hypotheses are factored through `ClosedOneFormOn`. -/

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
public structure PermJ12ContourH1Args
    (mobiusInv : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ) (wedgeSet : Set ℂ) : Prop where
  closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet
  hyp : PermJ12ContourH1Hyp mobiusInv wedgeSet

/-- Bundled inputs to `perm_J12_contour_h2` (excluding the parameter `r`). -/
public structure PermJ12ContourH2Args
    (mobiusInv : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ) (wedgeSet : Set ℂ) : Prop where
  closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet
  hyp : PermJ12ContourH2Hyp mobiusInv wedgeSet

private lemma perm_J12_contour_h_aux
    {mobiusInv : ℂ → ℂ}
    {Ψ₁' : ℝ → ℂ → ℂ}
    {wedgeSet : Set ℂ}
    (closed_ω_wedgeSet :
      ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet)
    (p0 p1 q0 q1 : ℂ)
    (continuousOn_mobiusInv_segment :
      ContinuousOn mobiusInv (Set.range (Path.segment p0 p1)))
    (homotopy_mem_wedgeSet :
      ∀ {x y : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
        (AffineMap.lineMap (k := ℝ)
              (mobiusInv (AffineMap.lineMap p0 p1 y))
              (AffineMap.lineMap q0 q1 y)) x ∈ wedgeSet)
    (contDiffOn_homotopy :
      ContDiffOn ℝ 2
        (fun xy : ℝ × ℝ =>
          (AffineMap.lineMap (k := ℝ)
            (mobiusInv (AffineMap.lineMap p0 p1 xy.2))
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
  let φ : (γ : C(I01, ℂ)).Homotopy δ := .affine (γ : C(I01, ℂ)) δ
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

/-- Contour deformation `h1`: from mapped segment `(-1 → -1 + I)` to vertical
segment `(1 → 1 + I)` inside `wedgeSet`. -/
public lemma perm_J12_contour_h1
    {mobiusInv : ℂ → ℂ}
    {Ψ₁' : ℝ → ℂ → ℂ}
    {wedgeSet : Set ℂ}
    (h : PermJ12ContourH1Args mobiusInv Ψ₁' wedgeSet)
    (r : ℝ) :
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

/-- Contour deformation `h2`: from mapped segment `(-1 + I → I)` to vertical
segment `(1 + I → I)` inside `wedgeSet`. -/
public lemma perm_J12_contour_h2
    {mobiusInv : ℂ → ℂ}
    {Ψ₁' : ℝ → ℂ → ℂ}
    {wedgeSet : Set ℂ}
    (h : PermJ12ContourH2Args mobiusInv Ψ₁' wedgeSet)
    (r : ℝ) :
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

/-
Shared contour deformation lemmas for the `perm_J12_contour_h1` / `perm_J12_contour_h2` identities.
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Topology.Homotopy.Affine
public import SpherePacking.ForMathlib.ScalarOneForm

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open MagicFunction

namespace SpherePacking.Contour

/--
`ClosedOneFormOn ω s` packages the hypotheses needed to apply the Poincaré lemma for curve
integrals on a set `s`: regularity (`DiffContOnCl`) plus symmetry of the `fderivWithin`
(`dω = 0`).

This is a convenience wrapper to keep lemma statements readable (and to avoid repeating the long
`fderivWithin` symmetry predicate at every call site).
-/
public structure ClosedOneFormOn (ω : ℂ → ℂ →L[ℂ] ℂ) (s : Set ℂ) : Prop where
  diffContOnCl : DiffContOnCl ℝ ω s
  fderivWithin_symm :
    ∀ x ∈ s, ∀ u ∈ tangentConeAt ℝ s x, ∀ v ∈ tangentConeAt ℝ s x,
      fderivWithin ℝ ω s x u v = fderivWithin ℝ ω s x v u

/--
Hypotheses for `perm_J12_contour_h1` that are independent of the specific 1-form `scalarOneForm`.

Callers are expected to provide the two "geometric" facts needed to apply the Poincaré lemma:
1) the homotopy stays inside `wedgeSet`; and
2) the homotopy map is `C²` on `Icc (0,1)²`.
-/
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

/--
Hypotheses for `perm_J12_contour_h2` that are independent of the specific 1-form `scalarOneForm`.

See `PermJ12ContourH1Hyp` for the guiding principle.
-/
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

/--
All inputs to `perm_J12_contour_h1` except for the parameter `r`.

This is a convenience wrapper so call sites can pass a single structured argument.
-/
public structure PermJ12ContourH1Args
    (mobiusInv : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ) (wedgeSet : Set ℂ) : Prop where
  closed_ω_wedgeSet : ∀ r : ℝ, ClosedOneFormOn (scalarOneForm (Ψ₁' r)) wedgeSet
  hyp : PermJ12ContourH1Hyp mobiusInv wedgeSet

/--
All inputs to `perm_J12_contour_h2` except for the parameter `r`.
-/
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
  let γ :
      Path (mobiusInv p0) (mobiusInv p1) :=
    (Path.segment p0 p1).map' continuousOn_mobiusInv_segment
  let δ : Path q0 q1 := Path.segment q0 q1
  let I01 : Set ℝ := unitInterval
  let φ : (γ : C(I01, ℂ)).Homotopy δ := ContinuousMap.Homotopy.affine (γ : C(I01, ℂ)) δ
  have hω : DiffContOnCl ℝ ω wedgeSet := by
    simpa [ω] using (closed_ω_wedgeSet (r := r)).diffContOnCl
  have hdω :
      ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
        fderivWithin ℝ ω wedgeSet x u v = fderivWithin ℝ ω wedgeSet x v u := by
    simpa [ω] using (closed_ω_wedgeSet (r := r)).fderivWithin_symm
  have hφt : ∀ a ∈ Set.Ioo 0 1, ∀ b ∈ Set.Ioo 0 1, φ (a, b) ∈ wedgeSet := by
    intro a ha b hb
    simpa [φ, γ, δ, Path.map', Path.segment_apply] using
      (homotopy_mem_wedgeSet (x := (a : ℝ)) (y := (b : ℝ)) ha hb)
  have hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
      (Set.Icc (0 : ℝ × ℝ) 1) := by
    let F : ℝ × ℝ → ℂ := fun xy =>
      ((AffineMap.lineMap (k := ℝ)
            (mobiusInv ((AffineMap.lineMap (k := ℝ) p0 p1) xy.2))
            ((AffineMap.lineMap (k := ℝ) q0 q1) xy.2)) xy.1)
    have hF : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => F xy) (Set.Icc (0 : ℝ × ℝ) 1) := by
      simpa [F] using contDiffOn_homotopy
    refine (contDiffOn_congr ?_).2 hF
    intro xy hxy
    rcases xy with ⟨x, y⟩
    rcases hxy with ⟨h0, h1⟩
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨h0.1, h1.1⟩
    have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨h0.2, h1.2⟩
    let xI : I01 := ⟨x, hx⟩
    let yI : I01 := ⟨y, hy⟩
    calc
      Set.IccExtend (h := (zero_le_one : (0 : ℝ) ≤ 1)) (φ.extend x) y = (φ.extend x) yI := by
        simpa [yI] using
          (Set.IccExtend_of_mem (h := (zero_le_one : (0 : ℝ) ≤ 1)) (f := φ.extend x) hy)
      _ = φ (xI, yI) := by
        simpa [xI, yI] using
          (ContinuousMap.Homotopy.extend_apply_of_mem_I (F := φ) (ht := hx) (x := yI))
      _ = (Path.segment (γ yI) (δ yI) xI : ℂ) := by
        rfl
      _ = (AffineMap.lineMap (γ yI) (δ yI) x : ℂ) := by
        simp [Path.segment_apply, xI]
      _ = (F (x, y) : ℂ) := by
        simp [F, γ, δ, yI, Path.map', Path.segment_apply]
  have hmain :=
    ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl
      (𝕜 := ℂ) (E := ℂ) (F := ℂ) (γ₁ := γ) (γ₂ := δ) (t := wedgeSet) (ω := ω) (φ := φ)
      hφt hω hdω hcontdiff
  have hφ0 : φ.evalAt (0 : I01) = Path.segment (γ (0 : I01)) (δ (0 : I01)) := by
    rfl
  have hφ1 : φ.evalAt (1 : I01) = Path.segment (γ (1 : I01)) (δ (1 : I01)) := by
    rfl
  have h :
      (∫ᶜ z in γ, ω z) + ∫ᶜ z in Path.segment (γ (1 : I01)) (δ (1 : I01)), ω z =
        (∫ᶜ z in δ, ω z) + ∫ᶜ z in Path.segment (γ (0 : I01)) (δ (0 : I01)), ω z := by
    simpa [hφ0, hφ1] using hmain
  have hflat :
      (∫ᶜ z in (Path.segment p0 p1).map' continuousOn_mobiusInv_segment, ω z) +
          ∫ᶜ z in Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (1 : ℝ)))
              ((AffineMap.lineMap q0 q1) (1 : ℝ)),
            ω z =
        (∫ᶜ z in Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (0 : ℝ)))
                ((AffineMap.lineMap q0 q1) (0 : ℝ)),
              ω z) +
          ∫ᶜ z in Path.segment q0 q1, ω z := by
    simpa [ω, γ, δ, Path.map', Path.segment_apply, add_assoc, add_left_comm, add_comm] using h
  have hseg1 :
      (∫ᶜ z in Path.segment (mobiusInv p1) q1, ω z) =
        ∫ᶜ z in Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (1 : ℝ)))
            ((AffineMap.lineMap q0 q1) (1 : ℝ)),
          ω z := by
    have hac : mobiusInv p1 = mobiusInv ((AffineMap.lineMap p0 p1) (1 : ℝ)) := by
      simp [AffineMap.lineMap_apply_one]
    have hbd : q1 = (AffineMap.lineMap q0 q1) (1 : ℝ) := by
      simp [AffineMap.lineMap_apply_one]
    rw [← Path.cast_segment hac hbd]
    simpa using
      (curveIntegral_cast (ω := ω)
        (γ := Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (1 : ℝ)))
          ((AffineMap.lineMap q0 q1) (1 : ℝ))) hac hbd)
  have hseg0 :
      (∫ᶜ z in Path.segment (mobiusInv p0) q0, ω z) =
        ∫ᶜ z in Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (0 : ℝ)))
            ((AffineMap.lineMap q0 q1) (0 : ℝ)),
          ω z := by
    have hac : mobiusInv p0 = mobiusInv ((AffineMap.lineMap p0 p1) (0 : ℝ)) := by
      simp [AffineMap.lineMap_apply_zero]
    have hbd : q0 = (AffineMap.lineMap q0 q1) (0 : ℝ) := by
      simp [AffineMap.lineMap_apply_zero]
    rw [← Path.cast_segment hac hbd]
    simpa using
      (curveIntegral_cast (ω := ω)
        (γ := Path.segment (mobiusInv ((AffineMap.lineMap p0 p1) (0 : ℝ)))
          ((AffineMap.lineMap q0 q1) (0 : ℝ))) hac hbd)
  -- Rewrite the endpoint segments via casting and finish.
  have hfinal := hflat
  -- LHS endpoint segment
  rw [← hseg1] at hfinal
  -- RHS endpoint segment
  rw [← hseg0] at hfinal
  simpa [ω, add_assoc] using hfinal

/--
Contour deformation identity for the first segment in the `perm_J12` argument.

This is the `h1` step in the assembled contour identity, moving from the mapped segment
`(-1 → -1 + I)` to the vertical segment `(1 → 1 + I)` inside `wedgeSet`.
-/
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
  -- The start-segment term is a trivial curve integral (`mobiusInv (-1) = 1`).
  have hstart :
      (∫ᶜ z in Path.segment (mobiusInv (-1 : ℂ)) (1 : ℂ), scalarOneForm (Ψ₁' r) z) = 0 := by
    rw [h.hyp.mobiusInv_neg_one]
    simp [Path.segment_same]
  simpa [add_assoc, hstart] using
    perm_J12_contour_h_aux (mobiusInv := mobiusInv) (Ψ₁' := Ψ₁')
      (wedgeSet := wedgeSet) h.closed_ω_wedgeSet
      (-1 : ℂ) ((-1 : ℂ) + Complex.I) (1 : ℂ) ((1 : ℂ) + Complex.I)
      (continuousOn_mobiusInv_segment :=
        h.hyp.continuousOn_mobiusInv_segment_z₁)
      (homotopy_mem_wedgeSet := by
        intro x y hx hy
        simpa using h.hyp.homotopy_mem_wedgeSet (x := x) (y := y) hx hy)
      (contDiffOn_homotopy := by
        simpa using h.hyp.contDiffOn_homotopy)
      (r := r)

/--
Contour deformation identity for the second segment in the `perm_J12` argument.

This is the `h2` step in the assembled contour identity, relating the mapped segment
`(-1 + I → I)` to the vertical segment `((1 + I) → I)` inside `wedgeSet`.
-/
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
  -- The end-segment term is a trivial curve integral (`mobiusInv I = I`).
  have hend :
      (∫ᶜ z in Path.segment (mobiusInv Complex.I) Complex.I,
          scalarOneForm (Ψ₁' r) z) = 0 := by
    rw [h.hyp.mobiusInv_I]
    simp [Path.segment_same]
  simpa [add_assoc, add_left_comm, add_comm, hend] using
    perm_J12_contour_h_aux (mobiusInv := mobiusInv) (Ψ₁' := Ψ₁')
      (wedgeSet := wedgeSet) h.closed_ω_wedgeSet
      (((-1 : ℂ) + Complex.I)) Complex.I (((1 : ℂ) + Complex.I)) Complex.I
      (continuousOn_mobiusInv_segment :=
        h.hyp.continuousOn_mobiusInv_segment_z₂)
      (homotopy_mem_wedgeSet := by
        intro x y hx hy
        simpa using h.hyp.homotopy_mem_wedgeSet (x := x) (y := y) hx hy)
      (contDiffOn_homotopy := by
        simpa using h.hyp.contDiffOn_homotopy)
      (r := r)

end SpherePacking.Contour

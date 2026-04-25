module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Path
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A wedge domain for contour deformation

This file defines `wedgeSet : Set ℂ`, an open convex wedge in the upper half-plane.
Its closure meets the real axis only at `1`.
This domain is used throughout the contour deformation arguments.

We also record basic topological/convexity properties, convenient closure bounds,
and membership lemmas for the line segments used in the constructions.
-/

namespace SpherePacking

noncomputable section

open Complex

/-! ## Main definition -/

/--
The wedge region used for the contour deformation.

Its closure meets the real axis only at `1`.
-/
public def wedgeSet : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im}

/-- Unfolding lemma for `wedgeSet`. -/
@[simp] public lemma wedgeSet_iff {z : ℂ} :
    wedgeSet z ↔ 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im := Iff.rfl

/-- The wedge set is an open subset of `ℂ`. -/
public lemma isOpen_wedgeSet : IsOpen wedgeSet := by
  simpa [wedgeSet, and_left_comm, and_assoc, and_comm, Set.setOf_and] using
    (isOpen_lt continuous_const continuous_im).inter
      ((isOpen_lt (continuous_re.sub continuous_const) continuous_im).inter
        (isOpen_lt (continuous_const.sub continuous_re) continuous_im))

/-- The wedge set is convex. -/
public lemma convex_wedgeSet : Convex ℝ wedgeSet := by
  have hEq :
      wedgeSet =
        {z : ℂ | (0 : ℝ) < z.im} ∩
          ({z : ℂ | z.re - z.im < (1 : ℝ)} ∩ {z : ℂ | (1 : ℝ) < z.re + z.im}) := by
    ext z
    refine ⟨fun hz => ⟨hz.1, by simp; linarith [hz.2.1], by simp; linarith [hz.2.2]⟩, ?_⟩
    rintro ⟨hA, hB, hC⟩
    exact ⟨hA, by simp at hB hC; constructor <;> linarith⟩
  have hA : Convex ℝ {z : ℂ | (0 : ℝ) < z.im} := by
    simpa using (convex_halfSpace_gt (f := fun z : ℂ => z.im) (.mk add_im smul_im) (0 : ℝ))
  have hB : Convex ℝ {z : ℂ | z.re - z.im < (1 : ℝ)} := by
    refine convex_halfSpace_lt (f := fun z : ℂ => z.re - z.im)
      (.mk (fun z w => by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm])
        (fun c z => by simp [sub_eq_add_neg, mul_add, mul_comm])) (1 : ℝ)
  have hC : Convex ℝ {z : ℂ | (1 : ℝ) < z.re + z.im} := by
    refine convex_halfSpace_gt (f := fun z : ℂ => z.re + z.im)
      (.mk (fun z w => by simp [add_left_comm, add_comm])
        (fun c z => by simp [mul_add, mul_comm])) (1 : ℝ)
  simpa [hEq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hA.inter (hB.inter hC)

public lemma wedgeSet_subset_upperHalfPlaneSet :
    wedgeSet ⊆ UpperHalfPlane.upperHalfPlaneSet := fun _ hz => hz.1

private lemma closure_wedgeSet_subset_im_nonneg :
    closure wedgeSet ⊆ {z : ℂ | 0 ≤ z.im} :=
  closure_minimal (fun _ hz => le_of_lt hz.1) (isClosed_le continuous_const continuous_im)

/-- A point in `closure wedgeSet` satisfies `|z.re - 1| ≤ z.im`. -/
public lemma closure_wedgeSet_subset_abs_re_sub_one_le_im :
    closure wedgeSet ⊆ {z : ℂ | |z.re - 1| ≤ z.im} := by
  refine closure_minimal (fun z hz => ?_)
    (isClosed_le (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_im)
  exact abs_le.2 ⟨by linarith [hz.2.2], le_of_lt hz.2.1⟩

/-- If `z ∈ closure wedgeSet` and `z ≠ 1`, then `z` lies in the open upper half-plane. -/
public lemma mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one
    {z : ℂ} (hz : z ∈ closure wedgeSet) (hne : z ≠ (1 : ℂ)) :
    z ∈ UpperHalfPlane.upperHalfPlaneSet := by
  have hzIm_pos : 0 < z.im := by
    refine lt_of_le_of_ne (closure_wedgeSet_subset_im_nonneg hz) fun hzIm => hne ?_
    have habs0 : |z.re - 1| = 0 :=
      le_antisymm (by simpa [hzIm] using closure_wedgeSet_subset_abs_re_sub_one_le_im hz)
        (abs_nonneg _)
    have hre : z.re = 1 := sub_eq_zero.mp (abs_eq_zero.mp habs0)
    exact Complex.ext (by simp [hre]) (by simp [hzIm])
  simpa [UpperHalfPlane.upperHalfPlaneSet] using hzIm_pos

/-- Membership in `wedgeSet` for the vertical line segment from `1` to `1 + I`. -/
public lemma lineMap_z₃line_mem_wedgeSet {t : ℝ} (ht0 : 0 < t) :
    AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) t ∈ wedgeSet := by
  simp [wedgeSet, AffineMap.lineMap_apply_module', Algebra.smul_def, ht0, add_comm, mul_comm]

/-- Membership in `wedgeSet` for the line segment from `1 + I` to `I`, for `t ∈ (0, 1)`. -/
public lemma lineMap_z₄line_mem_wedgeSet {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I t ∈ wedgeSet := by
  simp [wedgeSet, AffineMap.lineMap_apply_module', Algebra.smul_def,
    (by linarith [ht0] : (-t : ℝ) < 1), ht1, sub_eq_add_neg, add_left_comm, add_comm]

end

end SpherePacking

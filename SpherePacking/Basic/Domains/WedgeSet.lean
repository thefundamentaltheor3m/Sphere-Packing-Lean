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
  let A : Set ℂ := {z : ℂ | (0 : ℝ) < z.im}
  let B : Set ℂ := {z : ℂ | z.re - z.im < (1 : ℝ)}
  let C : Set ℂ := {z : ℂ | (1 : ℝ) < z.re + z.im}
  have hlin_re_sub_im : IsLinearMap ℝ (fun z : ℂ => z.re - z.im) := by
    refine .mk ?_ ?_
    · intro z w
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    · intro c z
      simp [sub_eq_add_neg, mul_add, mul_comm]
  have hlin_re_add_im : IsLinearMap ℝ (fun z : ℂ => z.re + z.im) := by
    refine .mk ?_ ?_
    · intro z w
      simp [add_comm, add_left_comm]
    · intro c z
      simp [mul_add, mul_comm]
  have hEq : wedgeSet = A ∩ (B ∩ C) := by
    ext z
    constructor
    · intro hz
      refine ⟨hz.1, ?_⟩
      refine ⟨?_, ?_⟩
      · dsimp [B]
        linarith [hz.2.1]
      · dsimp [C]
        linarith [hz.2.2]
    · rintro ⟨hA, hBC⟩
      rcases hBC with ⟨hB, hC⟩
      refine ⟨hA, ?_, ?_⟩
      · dsimp [B] at hB
        linarith [hB]
      · dsimp [C] at hC
        linarith [hC]
  have hAconv : Convex ℝ A := by
    simpa [A] using (convex_halfSpace_gt (f := fun z : ℂ => z.im) (.mk add_im smul_im) (0 : ℝ))
  have hBconv : Convex ℝ B := by
    have : Convex ℝ {z : ℂ | z.re - z.im < (1 : ℝ)} :=
      convex_halfSpace_lt (f := fun z : ℂ => z.re - z.im) hlin_re_sub_im (1 : ℝ)
    simpa [B] using this
  have hCconv : Convex ℝ C := by
    have : Convex ℝ {z : ℂ | (1 : ℝ) < z.re + z.im} :=
      convex_halfSpace_gt (f := fun z : ℂ => z.re + z.im) hlin_re_add_im (1 : ℝ)
    simpa [C] using this
  simpa [hEq, A, B, C] using hAconv.inter (hBconv.inter hCconv)

public lemma wedgeSet_subset_upperHalfPlaneSet :
    wedgeSet ⊆ UpperHalfPlane.upperHalfPlaneSet := fun _ hz => hz.1

private lemma closure_wedgeSet_subset_im_nonneg :
    closure wedgeSet ⊆ {z : ℂ | 0 ≤ z.im} := by
  exact closure_minimal (fun z hz => le_of_lt hz.1) (isClosed_le continuous_const continuous_im)

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
  have him_nonneg : 0 ≤ z.im := closure_wedgeSet_subset_im_nonneg hz
  have habs : |z.re - 1| ≤ z.im := closure_wedgeSet_subset_abs_re_sub_one_le_im hz
  have hzIm_ne : z.im ≠ 0 := by
    intro hzIm
    apply hne
    have hre : z.re = 1 := by
      have habs0 : |z.re - 1| = 0 :=
        le_antisymm (by simpa [hzIm] using habs) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs0)
    apply Complex.ext <;> simp [hre, hzIm]
  have hzIm_pos : 0 < z.im := lt_of_le_of_ne him_nonneg (Ne.symm hzIm_ne)
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

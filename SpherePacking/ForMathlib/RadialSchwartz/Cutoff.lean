module
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Basic


/-!
# Smooth cutoff for radial Schwartz constructions

`cutoff : ℝ → ℝ` is a smooth function with
* `cutoff r = 0` for `r ≤ -1`;
* `cutoff r = 1` for `0 ≤ r`.

We use it to upgrade one-sided (i.e. `r ≥ 0`) decay bounds for radial profiles `f : ℝ → ℂ` into
global Schwartz bounds for `r ↦ cutoff r * f r`, without changing the induced function on
`F` via `r = ‖x‖^2`.
-/

namespace RadialSchwartz

noncomputable section

open Complex Real

-- We choose a transition region contained in `[-1/2, 0]`. This ensures the cutoff is identically
-- zero on a neighborhood of `(-1 : ℝ)`, which is convenient for profiles that are only naturally
-- smooth for `r > -1`.
/-- A smooth cutoff function on `ℝ` with `cutoff r = 0` for `r ≤ -1/2` and `cutoff r = 1` for
`0 ≤ r`. -/
@[expose] public def cutoff (r : ℝ) : ℝ := Real.smoothTransition (2 * r + 1)

/-- `cutoff r = 0` for `r ≤ -1/2`. -/
@[simp] public lemma cutoff_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoff r = 0 := by
  simpa [cutoff] using
    (Real.smoothTransition.zero_of_nonpos (x := 2 * r + 1) (by linarith))

/-- `cutoff r = 0` for `r ≤ -1`. -/
@[simp] public lemma cutoff_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoff r = 0 := by
  exact cutoff_eq_zero_of_le_neg_half (r := r) (by linarith [hr])

/-- `cutoff r = 1` for `0 ≤ r`. -/
@[simp] public lemma cutoff_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoff r = 1 := by
  simpa [cutoff] using
    (Real.smoothTransition.one_of_one_le (x := 2 * r + 1) (by linarith))

/-- The cutoff function is smooth. -/
@[fun_prop]
public lemma cutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoff := by
  simpa [cutoff] using
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- Complex-valued version of `cutoff`. -/
@[expose] public def cutoffC (r : ℝ) : ℂ := (cutoff r : ℂ)

/-- `cutoffC r = 0` for `r ≤ -1/2`. -/
@[simp] public lemma cutoffC_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoffC r = 0 := by
  simp [cutoffC, cutoff_eq_zero_of_le_neg_half hr]

/-- `cutoffC r = 0` for `r ≤ -1`. -/
@[simp] public lemma cutoffC_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoffC r = 0 := by
  simp [cutoffC, cutoff_eq_zero_of_le hr]

/-- `cutoffC r = 1` for `0 ≤ r`. -/
@[simp] public lemma cutoffC_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoffC r = 1 := by
  simp [cutoffC, cutoff_eq_one_of_nonneg hr]

/-- The complex cutoff function is smooth. -/
@[fun_prop]
public lemma cutoffC_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffC := by
  simpa [cutoffC] using ofRealCLM.contDiff.comp cutoff_contDiff

/-- `cutoff (‖x‖^2) = 1` for all `x`. -/
@[simp] public lemma cutoff_norm_sq_eq_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) : cutoff (‖x‖ ^ 2) = 1 := by
  exact cutoff_eq_one_of_nonneg (r := ‖x‖ ^ 2) (sq_nonneg ‖x‖)

/-- `cutoffC (‖x‖^2) = 1` for all `x`. -/
@[simp] public lemma cutoffC_norm_sq_eq_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) : cutoffC (‖x‖ ^ 2) = 1 := by
  simp [cutoffC]

/-- If `f` is smooth on `(-1, ∞)` then `r ↦ cutoffC r * f r` is smooth on all of `ℝ`. -/
public lemma contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi (-1 : ℝ))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ cutoffC r * f r) := by
  refine (contDiff_iff_contDiffAt (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (f := fun r ↦ cutoffC r * f r)).2 ?_
  intro x
  by_cases hx : x < (-1 / 2 : ℝ)
  · have hEq : (fun r ↦ cutoffC r * f r) =ᶠ[nhds x] fun _ ↦ (0 : ℂ) := by
      refine Filter.eventuallyEq_of_mem (Iio_mem_nhds hx) fun y hy => ?_
      simp [cutoffC_eq_zero_of_le_neg_half (r := y) (le_of_lt hy)]
    simpa using
      (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ ↦ (0 : ℂ)) x).congr_of_eventuallyEq hEq
  · have hx' : (-1 : ℝ) < x := by linarith [le_of_not_gt hx]
    exact (cutoffC_contDiff.contDiffAt (x := x)).mul (hf.contDiffAt (isOpen_Ioi.mem_nhds hx'))

end

end RadialSchwartz

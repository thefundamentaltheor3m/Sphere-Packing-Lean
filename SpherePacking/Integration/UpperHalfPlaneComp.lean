module
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Order
public import SpherePacking.ForMathlib.BoundsOnIcc


/-!
# Helpers for real parametrisations in `ℍ`

This file provides continuity and boundedness helpers for functions defined on `ℍ` and evaluated
along real parametrisations.
-/

namespace SpherePacking.Integration

open scoped Interval
open Set

/-- Imaginary part of `-1 / (t + i)` as a real function of `t`. -/
public lemma im_neg_one_div_ofReal_add_I (t : ℝ) :
    (-1 / ((t : ℂ) + Complex.I)).im = 1 / (t ^ 2 + 1) := by
  simp [div_eq_mul_inv, Complex.normSq, pow_two]

/-- Imaginary part of `-1 / (-t + i)` as a real function of `t`. -/
public lemma im_neg_one_div_neg_ofReal_add_I (t : ℝ) :
    (-1 / (-(t : ℂ) + Complex.I)).im = 1 / (t ^ 2 + 1) := by
  simpa using (im_neg_one_div_ofReal_add_I (t := -t))

/-- For `t ∈ (0,1)`, we have `1/2 < 1 / (t^2 + 1)`. -/
public lemma one_half_lt_one_div_sq_add_one_of_mem_Ioo01 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) < 1 / (t ^ 2 + 1) := by
  have hlt : t ^ 2 + 1 < 2 := by
    have ht2 : t ^ 2 < 1 := (sq_lt_one_iff₀ (le_of_lt ht.1)).2 ht.2
    linarith
  have hpos : 0 < t ^ 2 + 1 := by positivity
  -- `t^2 + 1 < 2` implies `1/2 < 1/(t^2 + 1)`.
  simpa using (one_div_lt_one_div_of_lt hpos hlt)

/-- A continuity helper for expressions that pass through `UpperHalfPlane.mk`.

This is useful when a function is stated on `ℍ`, but a computation is carried out on `ℂ` with an
explicit proof of positivity of the imaginary part.
-/
public lemma continuous_comp_upperHalfPlane_mk {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {ψT : UpperHalfPlane → β} (hψT : Continuous ψT) {z : α → ℂ}
    (hz : Continuous z) (him : ∀ a : α, 0 < (z a).im) {ψT' : ℂ → β}
    (hEq : ∀ a : α, ψT' (z a) = ψT (⟨z a, him a⟩ : UpperHalfPlane)) :
    Continuous fun a : α => ψT' (z a) :=
  by simpa [hEq] using hψT.comp (hz.upperHalfPlaneMk him)

/-- A continuous function on `[0,1]` is bounded on `Ι (0,1)`. -/
public lemma exists_bound_norm_uIoc_zero_one_of_continuous (f : ℝ → ℂ) (hf : Continuous f) :
    ∃ M : ℝ, ∀ t ∈ (Ι (0 : ℝ) 1), ‖f t‖ ≤ M := by
  simpa using
    (SpherePacking.ForMathlib.exists_upper_bound_on_uIoc (g := fun t : ℝ => ‖f t‖)
      (a := (0 : ℝ)) (b := 1) (zero_le_one : (0 : ℝ) ≤ 1) (hg := (hf.norm).continuousOn))

end SpherePacking.Integration

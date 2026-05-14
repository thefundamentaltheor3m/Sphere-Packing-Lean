module
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Topology.Order
public import SpherePacking.ForMathlib.DerivHelpers

/-!
# Helpers for real parametrisations in `ℍ`

Continuity and boundedness helpers for functions on `ℍ` along real parametrisations.
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
  simpa using im_neg_one_div_ofReal_add_I (t := -t)

/-- For `t ∈ (0,1)`, we have `1/2 < 1 / (t^2 + 1)`. -/
public lemma one_half_lt_one_div_sq_add_one_of_mem_Ioo01 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) < 1 / (t ^ 2 + 1) := by
  simpa using one_div_lt_one_div_of_lt (by positivity)
    (by linarith [(sq_lt_one_iff₀ ht.1.le).2 ht.2] : t ^ 2 + 1 < 2)

/-- Continuity helper for expressions that pass through `UpperHalfPlane.mk`, when a function on
`ℍ` is computed on `ℂ` with an explicit proof of positivity of the imaginary part. -/
public lemma continuous_comp_upperHalfPlane_mk {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {ψT : UpperHalfPlane → β} (hψT : Continuous ψT) {z : α → ℂ}
    (hz : Continuous z) (him : ∀ a : α, 0 < (z a).im) {ψT' : ℂ → β}
    (hEq : ∀ a : α, ψT' (z a) = ψT (⟨z a, him a⟩ : UpperHalfPlane)) :
    Continuous fun a : α => ψT' (z a) := by
  simpa [hEq] using hψT.comp (hz.upperHalfPlaneMk him)

/-- A continuous function on `[0,1]` is bounded on `Ι (0,1)`. -/
public lemma exists_bound_norm_uIoc_zero_one_of_continuous (f : ℝ → ℂ) (hf : Continuous f) :
    ∃ M : ℝ, ∀ t ∈ (Ι (0 : ℝ) 1), ‖f t‖ ≤ M :=
  let ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc (g := fun t : ℝ => ‖f t‖)
    (a := (0 : ℝ)) (b := 1) zero_le_one hf.norm.continuousOn
  ⟨C, fun x hx => hC x (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le zero_le_one] using hx))⟩

end SpherePacking.Integration

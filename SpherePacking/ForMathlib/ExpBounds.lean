module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential bounds

Uniform bounds of the form `x ^ k * exp (-b * x)` on `0 ≤ x`, and a few closely related variants.
-/

namespace SpherePacking.ForMathlib

open Filter Real

/-- Uniform bound for `x ^ k * exp (-b * x)` on `0 ≤ x` when `0 < b`. -/
public lemma exists_bound_pow_mul_exp_neg_mul (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * x) ≤ C := by
  let f : ℝ → ℝ := fun x ↦ x ^ k * Real.exp (-b * x)
  have ht : Tendsto f atTop (nhds (0 : ℝ)) := by
    simpa [f, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := b) hb)
  rcases (eventually_atTop.1 <| ht.eventually (Iio_mem_nhds zero_lt_one)) with ⟨A, hA⟩
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (max A 0))).exists_isMaxOn
      (Set.nonempty_Icc.2 (le_max_right A 0)) (by fun_prop : Continuous f).continuousOn
    with ⟨x0, hx0, hxmax⟩
  refine ⟨max (f x0) 1, fun x hx => ?_⟩
  by_cases hxA : x ≤ max A 0
  · exact (hxmax ⟨hx, hxA⟩).trans (le_max_left _ _)
  · exact (le_of_lt (hA x ((le_max_left _ _).trans (le_of_not_ge hxA)))).trans (le_max_right _ _)

/-- Uniform bound for `x ^ k * exp (-b * sqrt x)` on `0 ≤ x`. -/
public lemma exists_bound_pow_mul_exp_neg_mul_sqrt (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-b * Real.sqrt x) ≤ C := by
  rcases exists_bound_pow_mul_exp_neg_mul (k := 2 * k) (b := b) hb with ⟨C, hC⟩
  exact ⟨C, fun x hx => by
    simpa [pow_mul, Real.sq_sqrt hx] using hC (Real.sqrt x) (Real.sqrt_nonneg _)⟩

/-- AM-GM style inequality for the exponential weight: for `0 ≤ x`, `0 < t`,
`exp (-π / t) * exp (-π * x * t) ≤ exp (-2 * π * sqrt x)`. -/
public lemma exp_neg_pi_div_mul_exp_neg_pi_mul_le (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
      Real.exp (-2 * Real.pi * Real.sqrt x) := by
  have hAMGM : 2 * Real.sqrt (x * t) * (Real.sqrt t)⁻¹ ≤ x * t + 1 / t := by
    have h := two_mul_le_add_sq (Real.sqrt (x * t)) ((Real.sqrt t)⁻¹)
    have hinv : ((Real.sqrt t)⁻¹ : ℝ) ^ 2 = (1 / t : ℝ) := by simp [one_div, Real.sq_sqrt ht.le]
    simpa [Real.sq_sqrt (mul_nonneg hx ht.le), hinv, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_sqrt : Real.sqrt (x * t) * (Real.sqrt t)⁻¹ = Real.sqrt x := by
    have hsqrt : Real.sqrt (x * t) = Real.sqrt x * Real.sqrt t := by
      simpa [mul_comm] using Real.sqrt_mul hx t
    grind
  have hIneq : 2 * Real.sqrt x ≤ x * t + 1 / t := by
    simpa [hmul_sqrt, mul_assoc] using hAMGM
  refine (Real.exp_add _ _).symm.trans_le (Real.exp_le_exp.2 ?_)
  rw [show (-Real.pi / t) + (-Real.pi * x * t) = -(Real.pi * (x * t + 1 / t)) from by ring,
    show -2 * Real.pi * Real.sqrt x = -(Real.pi * (2 * Real.sqrt x)) from by ring]
  exact neg_le_neg (mul_le_mul_of_nonneg_left hIneq Real.pi_pos.le)

end SpherePacking.ForMathlib

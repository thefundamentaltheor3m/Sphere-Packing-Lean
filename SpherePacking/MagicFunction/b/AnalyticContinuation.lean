/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.b.Schwartz

/-!
# Double zeroes of `b`

For `s > 2`, `b(s) = -4i sin(π s / 2)² ∫₀^∞ ψ_I(it) e^{-π s t} dt`, where `s` is the squared
radius `‖x‖²`. We also state the behaviour of `ψ_I(it)` as `t → 0` and `t → ∞`, and write the
expansion of `ψ_I(it)` at `t → ∞` via `expPoly`, so that the analytic continuation of Laplace
transforms applies to `ψ_I`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Real Complex MagicFunction.DoubleZeroes Finset

namespace MagicFunction

/-- `ψ_I(it) = O(t² e^{-π/t})` as `t → 0`. -/
theorem ψI'_I_mul_isBigO_nhdsGT_zero :
    (fun t : ℝ ↦ ψI' (I * t)) =O[𝓝[>] 0] fun t ↦ t ^ 2 * rexp (-π / t) := by
  sorry

/-- `ψ_I(it) = O(e^{2πt})` as `t → ∞`. -/
theorem ψI'_I_mul_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t)) =O[atTop] fun t ↦ rexp (2 * π * t) := by
  sorry

theorem integrableOn_ψI'_mul_cexp {s : ℝ} (hr : 2 < s) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * s * t)) (Ioi 0) := by
  sorry

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {s : ℝ} (hr : 2 < s) :
    b.RealIntegrals.b' s = -4 * I * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t) := by
  sorry

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  rw [FourierEigenfunctions.b_apply,
    b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (lt_sq_of_sqrt_lt hx)]
  norm_num

/-- `ψ_I(it) = e^{2πt} + 144 + O(e^{-πt})` as `t → ∞`. -/
theorem ψI'_I_mul_sub_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t) - (cexp (2 * π * t) + 144)) =O[atTop] fun t ↦ rexp (-π * t) := by
  sorry

theorem expPoly_ψI' (t : ℝ) :
    expPoly 1 (fun k ↦ if k = 0 then 144 else 1) 0 t = cexp (2 * π * t) + 144 := by
  simp [sum_range_succ, add_comm]

theorem ψI'_I_mul_sub_expPoly_isBigO_atTop :
    (fun t : ℝ ↦ ψI' (I * t) - expPoly 1 (fun k ↦ if k = 0 then 144 else 1) 0 t) =O[atTop]
      fun t ↦ rexp (-π * t) :=
  /- We could add `gcongr` to `IsBigO` and `IsLittleO`, after we do that,
    we could use `grw` here. -/
  ψI'_I_mul_sub_isBigO_atTop.congr_left fun t ↦ by rw [expPoly_ψI']

end MagicFunction

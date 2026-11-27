/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.AnalyticContinuation
public import SpherePacking.MagicFunction.a.Schwartz

/-!
# Analytic continuation of `a`

The asymptotic expansion of `φ₀(i/t) t²` as `t → ∞`, and the identity `ψ(it) = t² φ₀(i/t)` for
`ψ(z) = -z² φ₀(-1/z)`, the function to which the analytic continuation of Laplace transforms is
applied.
-/

@[expose] public section

open Set Filter MeasureTheory Real Complex MagicFunction.DoubleZeroes Finset

namespace MagicFunction

/-- `φ₀(i/t) t² = 36/π² e^{2πt} - 8640/π t + 18144/π² + O(t² e^{-2πt})` as `t → ∞`. -/
theorem φ₀''_I_div_mul_sq_sub_isBigO_atTop :
    (fun t : ℝ ↦ φ₀'' (I / t) * t ^ 2 -
      (36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2)) =O[atTop]
        fun t ↦ t ^ 2 * rexp (-2 * π * t) := by
  sorry

/-- `ψ(it) = t² φ₀(i/t)` for `ψ(z) = -z² φ₀(-1/z)`. -/
theorem neg_sq_mul_φ₀''_neg_inv_I_mul (t : ℝ) :
    -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) = φ₀'' (I / t) * t ^ 2 := by
  /- This is used to rewrite `φ₀(i/t) t²` as `ψ(it)`, in order to apply the analytic continuation
    of Laplace transforms (FGH Proposition 2.1, see `MagicFunction.DoubleZeroes`) to `a`. -/
  have h : -1 / (I * t) = I / t := by simp [div_eq_mul_inv, Complex.inv_I, mul_comm]
  rw [h, mul_pow, I_sq]
  ring

/-- `t ↦ ψ(it)` is locally integrable on `[0, ∞)`, for `ψ(z) = -z² φ₀(-1/z)`. -/
theorem locallyIntegrableOn_φ₀'' :
    LocallyIntegrableOn (fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t))) (Ici 0) := by
  sorry

theorem expPoly_φ₀'' (t : ℝ) :
    expPoly 1 (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
      (fun k ↦ if k = 0 then -8640 / π else 0) t =
        36 / π ^ 2 * cexp (2 * π * t) - 8640 / π * t + 18144 / π ^ 2 := by
  simp [sum_range_succ]
  ring

theorem φ₀''_sub_expPoly_isBigO_atTop :
    (fun t : ℝ ↦ -(I * t) ^ 2 * φ₀'' (-1 / (I * t)) -
      expPoly 1 (fun k ↦ if k = 0 then 18144 / π ^ 2 else 36 / π ^ 2)
        (fun k ↦ if k = 0 then -8640 / π else 0) t) =O[atTop] fun t ↦ rexp (-π * t) := by
  have h : (fun t : ℝ ↦ t ^ 2 * rexp (-2 * π * t)) =O[atTop] fun t ↦ rexp (-π * t) :=
    ((isLittleO_pow_exp_pos_mul_atTop 2 pi_pos).isBigO.mul
      (Asymptotics.isBigO_refl _ _)).congr_right fun t ↦ by rw [← Real.exp_add]; ring_nf
  refine (φ₀''_I_div_mul_sq_sub_isBigO_atTop.trans h).congr_left fun t ↦ ?_
  rw [neg_sq_mul_φ₀''_neg_inv_I_mul, expPoly_φ₀'']

end MagicFunction

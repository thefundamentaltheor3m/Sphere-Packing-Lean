/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module
import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAuxIci
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Bounds for `I₃'`

This file rewrites the auxiliary integral `I₃'` as an integral over `Ici 1` and proves the
exponential bound used in Proposition 7.8 of the blueprint.

## Main definitions
* `g`

## Main statements
* `inv_integrand_eq_integrand`
* `I₃'_bounding`
-/

namespace MagicFunction.a.IntegralEstimates.I₃

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

noncomputable section Change_of_Variables

variable (r : ℝ)

/-! We begin by performing changes of variables. We use `Ioc` intervals everywhere because of the
way `intervalIntegral` is defined. -/

section Setup

/-- The integrand on `Ici 1` obtained from `I₃'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ -I
  * φ₀'' (I * s)
  * (s ^ (-4 : ℤ))
  * cexp (π * I * r)
  * cexp (-π * r / s)

end Setup

section Change

/-- Algebraic identity relating the `I₃'` integrand under the inversion `t ↦ 1 / t`. -/
public lemma inv_integrand_eq_integrand {t : ℝ} (ht₀ : 0 < t) (r : ℝ) (phase : ℂ) :
    (-I : ℂ) * φ₀'' (-1 / (I * t)) * t ^ 2 * phase * cexp (-π * r * t) =
      |(-1 / t ^ 2)| •
        ((-I : ℂ) * φ₀'' (I * (1 / t)) * (1 / t) ^ (-4 : ℤ) * phase * cexp (-π * r / (1 / t))) := by
  simp only [Int.reduceNeg, zpow_neg, real_smul]
  have h₃ : -1 / (I * t) = I / t := by
    rw [div_mul_eq_div_div_swap, div_I, neg_div, neg_mul, neg_neg, mul_comm, mul_div, mul_one]
  have h₁ : |-1 / t ^ 2| = 1 / t ^ 2 := by simp [neg_div]
  rw [h₁, h₃]
  simp only [neg_mul, ofReal_div, ofReal_one, ofReal_pow, mul_div_assoc', mul_one, div_zpow,
    one_zpow, inv_div, div_one, div_div_eq_mul_div, mul_neg, div_mul_eq_mul_div, one_mul, neg_div']
  rw [eq_div_iff (pow_ne_zero 2 (by exact_mod_cast (ne_of_gt ht₀))), neg_mul, neg_inj]
  ring_nf; ac_rfl

end Change_of_Variables.Change
----------------------------------------------------------------

section Bounding

section Bounding_Integrand

/-- Pointwise bound on `‖g r s‖` on `Ici 1` in terms of `‖φ₀'' (I * s)‖`. -/
public lemma I₃'_bounding_aux_1 (r : ℝ) :
    ∀ x ∈ Ici 1, ‖g r x‖ ≤ ‖φ₀'' (I * ↑x)‖ * rexp (-π * r / x) := by
  intro s hs
  simp only [
    g, neg_mul, Int.reduceNeg, zpow_neg, norm_neg, norm_mul, norm_I, one_mul, norm_inv, norm_zpow,
    norm_real, norm_eq_abs, norm_exp, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, zero_mul, mul_im, add_zero, Real.exp_zero, div_ofReal_re, sub_zero
  ]
  conv_rhs => rw [← mul_one ‖φ₀'' (I * ↑s)‖]
  gcongr
  have hs1 : (1 : ℝ) ≤ s := by simpa [mem_Ici] using hs
  simpa [abs_of_nonneg (zero_le_one.trans hs1)] using
    (inv_le_one_of_one_le₀ (one_le_zpow₀ hs1 <| Int.zero_le_ofNat 4))

end Bounding_Integrand

section Integrability

/-- The model bound integrand is integrable on `Ici 1`. -/
public lemma Bound_integrableOn (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  simpa using (MagicFunction.a.IntegralEstimates.bound_integrableOn_Ici (r := r) (C₀ := C₀))

end Integrability
end Bounding
end I₃

end MagicFunction.a.IntegralEstimates
----------------------------------------------------------------

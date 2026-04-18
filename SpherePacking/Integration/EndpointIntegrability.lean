module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.NormNum
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.InvChangeOfVariables

/-!
# Endpoint integrability

This file provides endpoint integrability lemmas used in contour-change and permutation arguments.

The main lemma `integrableOn_one_div_sq_mul_exp_neg_div` proves integrability on `Ioc (0, 1]` of
the standard endpoint weight `(1 / t ^ 2) * exp (-c / t)`.
-/

namespace SpherePacking.Integration

noncomputable section

open scoped Interval
open Set MeasureTheory Real

/-- Integrability of the endpoint weight `(1 / t ^ 2) * exp (-c / t)` on `Ioc (0, 1]` for `c > 0`.
-/
public lemma integrableOn_one_div_sq_mul_exp_neg_div (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-c / t)) (Ioc (0 : ℝ) 1) volume := by
  let s : Set ℝ := Ioc (0 : ℝ) 1
  let f : ℝ → ℝ := fun t ↦ (1 : ℝ) / t
  let f' : ℝ → ℝ := fun t ↦ -(1 : ℝ) / t ^ 2
  have hs : MeasurableSet s := measurableSet_Ioc
  have hf' : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t := fun t ht => by
    simpa [f, f', one_div, div_eq_mul_inv, pow_two, ne_of_gt ht.1] using
      (hasDerivAt_inv (ne_of_gt ht.1)).hasDerivWithinAt
  have hfinj : InjOn f s := fun a _ b _ hab =>
    inv_injective (by simpa [f, one_div] using hab)
  have himage : f '' s = Ici (1 : ℝ) := by
    simpa [f, s] using (InvChangeOfVariables.Ici_one_eq_image_inv_Ioc).symm
  have hmain : IntegrableOn (fun t : ℝ ↦ |f' t| * rexp (-(c * f t))) s volume := by
    have : IntegrableOn (fun y : ℝ ↦ rexp (-(c * y))) (f '' s) volume := by
      simpa [himage, pow_zero, one_mul] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := c) hc)
    simpa [smul_eq_mul] using
      (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (hs := hs) (hf' := hf')
        (hf := hfinj) (g := fun y : ℝ ↦ rexp (-(c * y)))).1 this
  refine hmain.congr_fun (hs := hs) fun t _ => ?_
  simp [f', f, abs_div, abs_of_nonneg (pow_two_nonneg t), div_eq_mul_inv]

end

end SpherePacking.Integration

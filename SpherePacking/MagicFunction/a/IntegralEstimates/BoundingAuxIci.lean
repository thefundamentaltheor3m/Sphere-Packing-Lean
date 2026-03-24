module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability on `Ici 1`

This file provides a single integrability lemma for the model bound integrand
`s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)` on `Ici 1`, used in the
`IntegralEstimates` development.

## Main statement
* `bound_integrableOn_Ici`
-/

open Real Set MeasureTheory

namespace MagicFunction.a.IntegralEstimates

/-- The model bound integrand is integrable on `Ici 1`. -/
public lemma bound_integrableOn_Ici (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  set μ := volume.restrict (Ici (1 : ℝ))
  have h_g : Integrable (fun s ↦ C₀ * rexp (-2 * π * s)) μ :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith [pi_pos]) 1)).const_mul C₀
  have hφ : AEStronglyMeasurable (fun s ↦ rexp (-π * r / s)) μ :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_inv)).aestronglyMeasurable
  have hb : ∀ᵐ s ∂μ, ‖rexp (-π * r / s)‖ ≤ rexp (π * |r|) :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s (hs : 1 ≤ s) ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
      refine exp_le_exp.mpr <| (le_abs_self _).trans ?_
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg pi_pos.le, abs_of_nonneg (by linarith : 0 ≤ s)]
      exact div_le_self (by positivity) hs
  simpa [IntegrableOn, μ, mul_assoc] using h_g.mul_bdd hφ hb

end MagicFunction.a.IntegralEstimates

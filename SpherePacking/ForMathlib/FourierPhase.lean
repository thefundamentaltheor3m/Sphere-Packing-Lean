module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE

import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Fourier phase factor

Many permutation and integrability arguments multiply an integrable Gaussian-type function by the
bounded phase `x ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)`.

This file collects boilerplate measurability and norm facts about that phase so dimension-specific
developments do not duplicate them.
-/

namespace SpherePacking.ForMathlib

open scoped RealInnerProductSpace Topology

open MeasureTheory Complex Real Filter

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The phase factor `exp (i * real)` has norm `1`. -/
public lemma norm_phase_eq_one (w x : V) :
    ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)‖ = (1 : ℝ) := by
  simpa using (Complex.norm_exp_ofReal_mul_I (-2 * (π * ⟪x, w⟫)))

/-- Multiplying by the phase factor preserves the norm. -/
public lemma norm_phase_mul (w : V) (x : V) (z : ℂ) :
    ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) * z‖ = ‖z‖ := by
  simpa [norm_mul] using congrArg (fun r : ℝ => r * ‖z‖) (norm_phase_eq_one w x)

section

variable [MeasureSpace V] [BorelSpace V]

/-- The phase factor is a.e. strongly measurable with respect to Lebesgue measure. -/
public lemma aestronglyMeasurable_phase (w : V) :
    AEStronglyMeasurable (fun x : V ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I))
      (volume : Measure V) := by
  have hcont : Continuous fun x : V => cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) := by continuity
  simpa using hcont.aestronglyMeasurable

end

section

variable [MeasureSpace V]

/-- Almost everywhere, the phase factor has norm at most `1`. -/
public lemma ae_norm_phase_le_one (w : V) :
    (∀ᵐ x : V ∂(volume : Measure V),
      ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)‖ ≤ (1 : ℝ)) := by
  exact Filter.Eventually.of_forall (fun x => (norm_phase_eq_one (w := w) (x := x)).le)

end

end

end SpherePacking.ForMathlib

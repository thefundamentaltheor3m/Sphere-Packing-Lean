module

public import SpherePacking.Integration.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini on `Ioc (0, 1]`

A small wrapper around `integral_integral_swap` for the repo-local measure `μIoc01` on `Ioc (0, 1]`.
-/

namespace SpherePacking.Integration

noncomputable section

open MeasureTheory

/-- Swap order of integration over `volume × μIoc01` and rewrite the inner integral using `g`. -/
public lemma integral_integral_swap_muIoc01
    {V : Type*} [MeasureSpace V] [MeasureTheory.SFinite (volume : Measure V)]
    {f : V → ℝ → ℂ} {g : ℝ → ℂ}
    (hint : Integrable (Function.uncurry f) ((volume : Measure V).prod μIoc01))
    (hfg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (∫ x : V, f x t) = g t) :
    (∫ x : V, ∫ t : ℝ, f x t ∂μIoc01) = ∫ t : ℝ, g t ∂μIoc01 := by
  rw [show (∫ x : V, ∫ t : ℝ, f x t ∂μIoc01) =
      ∫ t : ℝ, ∫ x : V, f x t ∂(volume : Measure V) ∂μIoc01 from by
    simpa using (MeasureTheory.integral_integral_swap (μ := volume) (ν := μIoc01) hint)]
  refine MeasureTheory.integral_congr_ae <|
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ioc).2 <|
      Filter.Eventually.of_forall fun t ht => by simp [hfg t ht]

end

end SpherePacking.Integration

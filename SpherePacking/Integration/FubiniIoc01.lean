module

public import SpherePacking.Integration.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini on `Ioc (0, 1]`

This file provides a small wrapper around `integral_integral_swap` for the repo-local measure
`μIoc01` on `Ioc (0, 1]`.
-/

namespace SpherePacking.Integration

noncomputable section

open MeasureTheory

/-- Swap the order of integration over `volume × μIoc01`, and rewrite the inner integral using `g`.

This is a convenience lemma specialized to the measure `μIoc01`.
-/
public lemma integral_integral_swap_muIoc01
    {V : Type*} [MeasureSpace V] [MeasureTheory.SFinite (volume : Measure V)]
    {f : V → ℝ → ℂ} {g : ℝ → ℂ}
    (hint : Integrable (Function.uncurry f) ((volume : Measure V).prod μIoc01))
    (hfg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (∫ x : V, f x t) = g t) :
    (∫ x : V, ∫ t : ℝ, f x t ∂μIoc01) = ∫ t : ℝ, g t ∂μIoc01 := by
  calc
    (∫ x : V, ∫ t : ℝ, f x t ∂μIoc01) =
        ∫ t : ℝ, ∫ x : V, f x t ∂(volume : Measure V) ∂μIoc01 := by
          simpa using
            (MeasureTheory.integral_integral_swap (μ := (volume : Measure V)) (ν := μIoc01) hint)
    _ = ∫ t : ℝ, g t ∂μIoc01 := by
          refine MeasureTheory.integral_congr_ae ?_
          refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ioc).2 <|
            Filter.Eventually.of_forall fun t ht => by simp [hfg t ht]

/-- Version of `integral_integral_swap_muIoc01` written with `∫ t in Ioc (0,1], ...`. -/
public lemma integral_integral_swap_Ioc01
    {V : Type*} [MeasureSpace V] [MeasureTheory.SFinite (volume : Measure V)]
    {f : V → ℝ → ℂ} {g : ℝ → ℂ}
    (hint : Integrable (Function.uncurry f) ((volume : Measure V).prod μIoc01))
    (hfg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (∫ x : V, f x t) = g t) :
    (∫ x : V, ∫ t in Set.Ioc (0 : ℝ) 1, f x t) = ∫ t in Set.Ioc (0 : ℝ) 1, g t := by
  simpa [μIoc01] using
    (integral_integral_swap_muIoc01 (V := V) (f := f) (g := g) hint hfg)

end

end SpherePacking.Integration

module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Small helpers for integrals on product measures

This file contains small wrapper lemmas around `MeasureTheory` facts about integrals on product
measures, extracted to reduce proof duplication across the project.
-/

namespace SpherePacking.ForMathlib

open MeasureTheory

/--
If `f` is ae-strongly measurable on `ν.prod μ`, then `b ↦ ∫ a, ‖f (a, b)‖ ∂ν` is
ae-strongly measurable.

The prime indicates this is a small wrapper around Mathlib's `integral_prod_right'`, obtained by
swapping the product coordinates.
-/
public lemma aestronglyMeasurable_integral_norm_prod_right'
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure β} {ν : Measure α} [SFinite μ] [SFinite ν] {f : α × β → E}
    (hf : AEStronglyMeasurable f (ν.prod μ)) :
    AEStronglyMeasurable (fun b : β => ∫ a : α, ‖f (a, b)‖ ∂ν) μ := by
  simpa using
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μ) (ν := ν) (f := fun p : β × α => ‖f (p.2, p.1)‖)
      (by simpa using (hf.norm.prod_swap (μ := μ) (ν := ν))))

end SpherePacking.ForMathlib

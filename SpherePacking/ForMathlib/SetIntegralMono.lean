/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bounding a set integral by a pointwise bound on the set

To bound `∫ x in s, f x ∂μ` above by `∫ x in s, g x ∂μ`, Mathlib's `setIntegral_mono_on` (which is
also what `gcongr` uses) asks for integrability of *both* `f` and `g`. When `f` is non-negative,
integrability of `f` is not needed: if `f` is not integrable its integral is `0` by convention, and
the bound holds trivially. Without a lemma saying so, every use starts with the same case split

```
wlog hint : IntegrableOn f s μ
· rw [integral_undef hint]; positivity
```

The lemmas below package that case split. They are the set-integral, pointwise-on-the-set forms of
`MeasureTheory.integral_mono_of_nonneg` and `MeasureTheory.norm_integral_le_of_norm_le`, and are
candidates for upstreaming to Mathlib.
-/

public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- If `0 ≤ f ≤ g` on a measurable set `s` and `g` is integrable on `s`, then
`∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ`. No integrability assumption on `f` is needed. -/
theorem setIntegral_mono_on_of_nonneg {f g : α → ℝ} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : IntegrableOn g s μ) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  integral_mono_of_nonneg ((ae_restrict_iff' hs).2 (.of_forall hf)) hg
    ((ae_restrict_iff' hs).2 (.of_forall h))

/-- If `‖f x‖ ≤ g x` on a measurable set `s` and `g` is integrable on `s`, then
`‖∫ x in s, f x ∂μ‖ ≤ ∫ x in s, g x ∂μ`. No integrability assumption on `f` is needed. -/
theorem norm_setIntegral_le_of_norm_le_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → E} {g : α → ℝ} (hs : MeasurableSet s) (hg : IntegrableOn g s μ)
    (h : ∀ x ∈ s, ‖f x‖ ≤ g x) : ‖∫ x in s, f x ∂μ‖ ≤ ∫ x in s, g x ∂μ :=
  norm_integral_le_of_norm_le hg ((ae_restrict_iff' hs).2 (.of_forall h))

end MeasureTheory

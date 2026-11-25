/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Congruence lemmas for integrals that remember the domain of integration

When rewriting an integrand one almost always needs to know that the variable of integration
lies in the domain: `t ∈ Set.Ioc 0 1`, `1 ≤ t`, and so on. Mathlib's lemmas for this
(`MeasureTheory.setIntegral_congr_fun`, `intervalIntegral.integral_congr`,
`MeasureTheory.setIntegral_congr_ae₀`, ...) are stated in terms of `Set.EqOn` or `∀ᵐ`, so neither
`simp` nor `congr!` can use them, and every use is preceded by a few lines of boilerplate
(`apply`, unfold `EqOn`, `ae_of_all`, `intro`, rewrite `uIcc_of_le`, ...).

This file restates them in the shape that `@[congr]` accepts, in the same way that
`Finset.sum_congr` is a `@[congr]` lemma for finite sums. No new tactic is involved; the effect is
that the following *existing* tactics learn about the domain of integration.

* `simp` rewrites under `∫ x in s, _` and `∫ x in a..b, _` with `x ∈ s` available to discharge
  side conditions of conditional rewrite rules. With the default discharger, pass `+contextual`.
  With a custom discharger the hypothesis is simply in the local context, so
  `simp (disch := grind) only [foo]` works whenever `grind` can derive the side condition of `foo`
  from membership in the interval.
* `congr! 1 with t ht` on `∫ t in s, f t = ∫ t in s, g t` produces `ht : t ∈ s ⊢ f t = g t`.

## Main statements

* `intervalIntegral.integral_congr_uIoc`: interval integrals, with `x ∈ Set.uIoc a b`.
* `MeasureTheory.integral_Icc_congr` and its seven siblings for the other kinds of interval. These
  have no measurability side condition, so they fire under any discharger.
* `MeasureTheory.setIntegral_congr_of_mem` and `MeasureTheory.setLIntegral_congr_of_mem`: an
  arbitrary measurable set. `simp` has to discharge `MeasurableSet s`; the default discharger does
  this for sets built out of intervals, balls, and so on.

All of these are candidates for upstreaming to Mathlib.
-/

public section

open MeasureTheory Set

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}

/-- Congruence for set integrals in a form usable by `simp` and `congr!`: the integrands only need
to agree on the domain of integration. -/
@[congr]
theorem setIntegral_congr_of_mem {s : Set α} {f g : α → E} (hs : MeasurableSet s)
    (h : ∀ x, x ∈ s → f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_fun hs h

/-- Congruence for set Lebesgue integrals in a form usable by `simp` and `congr!`. -/
@[congr]
theorem setLIntegral_congr_of_mem {s : Set α} {f g : α → ENNReal} (hs : MeasurableSet s)
    (h : ∀ x, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
  setLIntegral_congr_fun hs h

section Interval

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : α} {f g : α → E}

/-! The following eight lemmas are the instances of `setIntegral_congr_of_mem` for intervals. They
are stated separately so that no measurability side condition is left for `simp` to discharge. -/

@[congr]
theorem integral_Icc_congr (h : ∀ x, x ∈ Icc a b → f x = g x) :
    ∫ x in Icc a b, f x ∂μ = ∫ x in Icc a b, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Icc h

@[congr]
theorem integral_Ioc_congr (h : ∀ x, x ∈ Ioc a b → f x = g x) :
    ∫ x in Ioc a b, f x ∂μ = ∫ x in Ioc a b, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Ioc h

@[congr]
theorem integral_Ico_congr (h : ∀ x, x ∈ Ico a b → f x = g x) :
    ∫ x in Ico a b, f x ∂μ = ∫ x in Ico a b, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Ico h

@[congr]
theorem integral_Ioo_congr (h : ∀ x, x ∈ Ioo a b → f x = g x) :
    ∫ x in Ioo a b, f x ∂μ = ∫ x in Ioo a b, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Ioo h

@[congr]
theorem integral_Ici_congr (h : ∀ x, x ∈ Ici a → f x = g x) :
    ∫ x in Ici a, f x ∂μ = ∫ x in Ici a, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Ici h

@[congr]
theorem integral_Ioi_congr (h : ∀ x, x ∈ Ioi a → f x = g x) :
    ∫ x in Ioi a, f x ∂μ = ∫ x in Ioi a, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Ioi h

@[congr]
theorem integral_Iic_congr (h : ∀ x, x ∈ Iic b → f x = g x) :
    ∫ x in Iic b, f x ∂μ = ∫ x in Iic b, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Iic h

@[congr]
theorem integral_Iio_congr (h : ∀ x, x ∈ Iio b → f x = g x) :
    ∫ x in Iio b, f x ∂μ = ∫ x in Iio b, g x ∂μ :=
  setIntegral_congr_fun measurableSet_Iio h

end Interval

end MeasureTheory

namespace intervalIntegral

/-- Congruence for interval integrals in a form usable by `simp` and `congr!`: the integrands only
need to agree on `Set.uIoc a b`. When `a ≤ b` this is `Set.Ioc a b`, which `grind` and
`simp [Set.uIoc_of_le]` both know. -/
@[congr]
theorem integral_congr_uIoc {μ : Measure ℝ} {a b : ℝ} {f g : ℝ → E}
    (h : ∀ x, x ∈ uIoc a b → f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall h)

end intervalIntegral

/-! ### Unordered intervals and `grind`

Mathlib tags `Set.uIoc_of_le` and `Set.uIoc_of_ge` with `@[grind =]`, so `grind` can turn the
hypothesis `x ∈ Set.uIoc 0 1` produced by `intervalIntegral.integral_congr_uIoc` into
`0 < x ∧ x ≤ 1`. The corresponding lemmas for `Set.uIcc` are not tagged; we do so here, so that the
same works for hypotheses coming from `intervalIntegral.integral_congr` and
`intervalIntegral.integral_mono_on`. -/

attribute [grind =] Set.uIcc_of_le Set.uIcc_of_ge

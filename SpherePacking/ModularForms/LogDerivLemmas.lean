module
public import SpherePacking.ModularForms.TendstoLemmas
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Lemmas about `logDeriv`

This file collects auxiliary lemmas about the logarithmic derivative `logDeriv`, including
formulas for `logDeriv` of exponential expressions and a basic summability statement.

## Main statements
* `logDeriv_one_sub_exp_comp`
* `logDeriv_q_expo_summable`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  simp [logDeriv]

/-- A chain rule computation for `logDeriv` of `(fun z => 1 - r * cexp z) ∘ g`. -/
public lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw [logDeriv_comp _ (hg y), logDeriv_one_sub_exp]
  · ring
  · fun_prop

/-- If `‖r‖ < 1`, then the series `∑ n, n * r^n / (1 - r^n)` is summable. -/
public lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  simpa [pow_one] using (summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 (r := r) hr)


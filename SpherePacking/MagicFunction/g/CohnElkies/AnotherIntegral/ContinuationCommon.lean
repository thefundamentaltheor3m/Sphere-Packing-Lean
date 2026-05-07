module

public import Mathlib.Analysis.Complex.Basic

import Mathlib.Tactic

/-!
# Helper lemma for analytic continuation (`AnotherIntegral`)

To apply
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, we need an accumulation point for the set
where we know equality (typically real `u > 2`, accumulating at the complex point `3`).

## Main statement
* `frequently_eq_near_three`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Topology

open MeasureTheory Real Complex

/-- If `f` and `g` agree on all real `u > 2`, then `f = g` holds frequently near `3`. -/
public lemma frequently_eq_near_three
    {f g : ℂ → ℂ} (hf : ∀ u : ℝ, 2 < u → f (u : ℂ) = g (u : ℂ)) :
    (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = g z) := by
  refine Filter.frequently_iff.2 ?_
  intro U hU
  obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.1 hVnhds
  refine ⟨((3 + ε / 2 : ℝ) : ℂ), hVsub ⟨hball ?_, ?_⟩, by
    simpa using hf (3 + ε / 2) (by nlinarith [hεpos])⟩
  · simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2),
      abs_of_nonneg hεpos.le] using half_lt_self hεpos
  · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (show ((3 + ε / 2 : ℝ) : ℂ) ≠ 3 by exact_mod_cast (by nlinarith [hεpos.ne'] :
        (3 + ε / 2 : ℝ) ≠ 3))

end MagicFunction.g.CohnElkies.IntegralReps

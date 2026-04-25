/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationCommon
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Generic analytic continuation wrapper

This module provides a shared "wrapper" theorem for analytic continuation on `ACDomain`.
Both the `a'` and `b'` continuation arguments follow the identical pattern:

1. We have a function `value : ℝ → ℂ` (either `a'` or `b'`) with an analytic extension to `ACDomain`.
2. We have a complex-analytic RHS `rhsC : ℂ → ℂ` that restricts to `rhsR : ℝ → ℂ` on real inputs.
3. We know `value r = rhsR r` for all `r > 2`.
4. We conclude `value u = rhsR u` for all `0 < u`, `u ≠ 2` by analytic continuation.

## Main statement
* `MagicFunction.g.CohnElkies.IntegralReps.analytic_continuation_of_gt2`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Topology
open Real Complex Filter SpherePacking

/-- Generic analytic continuation on `ACDomain = {Re u > 0} \ {2}`.

Given:
- `value : ℝ → ℂ` with an analytic extension `f` to `ACDomain`
- A complex-analytic RHS `rhsC` on `ACDomain` restricting to `rhsR` on reals
- Agreement `value r = rhsR r` for `r > 2`

Conclude `value u = rhsR u` for all `0 < u`, `u ≠ 2`. -/
public theorem analytic_continuation_of_gt2
    {value : ℝ → ℂ}
    {rhsC : ℂ → ℂ}
    {rhsR : ℝ → ℂ}
    (h_extension :
      ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
        ∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = value u)
    (h_rhs_analytic : AnalyticOnNhd ℂ rhsC ACDomain)
    (h_rhs_ofReal : ∀ u : ℝ, rhsC (u : ℂ) = rhsR u)
    (h_gt2 : ∀ r : ℝ, 2 < r → value r = rhsR r)
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    value u = rhsR u := by
  have h3_mem : (3 : ℂ) ∈ ACDomain := by
    simp [ACDomain, rightHalfPlane]
  rcases h_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = rhsC (r : ℂ) := by
    intro r hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    have hr2 : r ≠ 2 := by linarith
    exact (hf_ofReal r hr0 hr2).trans ((h_gt2 r hr).trans (h_rhs_ofReal r).symm)
  have hfreq : ∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = rhsC z :=
    frequently_eq_near_three hf_gt2
  have hEqOn : Set.EqOn f rhsC ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic h_rhs_analytic
      ACDomain_isPreconnected h3_mem hfreq
  have hu_mem : (u : ℂ) ∈ ACDomain := by
    refine ⟨by simpa [rightHalfPlane] using hu,
      by simpa [ACDomain, Set.mem_singleton_iff] using (show (u : ℂ) ≠ 2 by exact_mod_cast hu2)⟩
  exact (hf_ofReal u hu hu2).symm.trans ((hEqOn hu_mem).trans (h_rhs_ofReal u))

end MagicFunction.g.CohnElkies.IntegralReps

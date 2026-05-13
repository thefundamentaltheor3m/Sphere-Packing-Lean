/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

/-!
# Generic analytic continuation wrapper

Shared wrapper theorem `analytic_continuation_of_gt2` for analytic continuation on `ACDomain`,
shared by the `a'` and `b'` continuation arguments.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Topology
open Real Complex Filter SpherePacking

/-- Generic analytic continuation on `ACDomain = {Re u > 0} \ {2}`. -/
public theorem analytic_continuation_of_gt2
    {value : ℝ → ℂ} {rhsC : ℂ → ℂ} {rhsR : ℝ → ℂ}
    (h_extension : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      ∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = value u)
    (h_rhs_analytic : AnalyticOnNhd ℂ rhsC ACDomain)
    (h_rhs_ofReal : ∀ u : ℝ, rhsC (u : ℂ) = rhsR u)
    (h_gt2 : ∀ r : ℝ, 2 < r → value r = rhsR r)
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    value u = rhsR u := by
  rcases h_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = rhsC (r : ℂ) := fun r hr =>
    (hf_ofReal r (lt_trans (by norm_num) hr) (by linarith)).trans
      ((h_gt2 r hr).trans (h_rhs_ofReal r).symm)
  have hFreq : (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = rhsC z) := Filter.frequently_iff.2 <| by
    intro U hU
    obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.1 hVnhds
    refine ⟨((3 + ε / 2 : ℝ) : ℂ), hVsub ⟨hball ?_, ?_⟩, by
      simpa using hf_gt2 (3 + ε / 2) (by nlinarith [hεpos])⟩
    · simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2),
        abs_of_nonneg hεpos.le] using half_lt_self hεpos
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show ((3 + ε / 2 : ℝ) : ℂ) ≠ 3 by exact_mod_cast
          (by nlinarith [hεpos.ne'] : (3 + ε / 2 : ℝ) ≠ 3))
  have hEqOn : Set.EqOn f rhsC ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic h_rhs_analytic
      ACDomain_isPreconnected (by simp [ACDomain, rightHalfPlane]) hFreq
  have hu_mem : (u : ℂ) ∈ ACDomain :=
    ⟨by simpa [rightHalfPlane] using hu,
      by simpa [ACDomain, Set.mem_singleton_iff] using (show (u : ℂ) ≠ 2 by exact_mod_cast hu2)⟩
  exact (hf_ofReal u hu hu2).symm.trans ((hEqOn hu_mem).trans (h_rhs_ofReal u))

end MagicFunction.g.CohnElkies.IntegralReps

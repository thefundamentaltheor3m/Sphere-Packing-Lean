module
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Shared analyticity helpers for `AnotherRHS`

Both `aAnotherRHS_analyticOnNhd` (in `A/Continuation.lean`) and
`bAnotherRHS_analyticOnNhd` (in `B/Continuation.lean`) have the same structure:
an explicit prefactor of `sign * (sin (π u / 2))^2` times an inner analytic function
(the pole terms plus the complex integral). This file extracts the common prefactor
part into a single lemma.

## Main statements
* `analyticOnNhd_sinSqHalfPi`
* `analyticOnNhd_sinSq_prefactor_mul`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open Real Complex SpherePacking

noncomputable section

/-- The function `u ↦ (sin (π u / 2))^2` is analytic on `ACDomain`. -/
public lemma analyticOnNhd_sinSqHalfPi :
    AnalyticOnNhd ℂ (fun u : ℂ => (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ)) ACDomain := by
  have hsin_arg : AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain :=
    AnalyticOnNhd.div_const (analyticOnNhd_const.mul analyticOnNhd_id)
  have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
    have hsin_univ : AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ) := by
      simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))
    simpa [Function.comp] using hsin_univ.comp hsin_arg (by intro _ _; simp)
  exact hsin.pow 2

/-- If `inner` is analytic on `ACDomain`, then so is
`u ↦ sign * (sin (π u / 2))^2 * inner u` for any constant `sign : ℂ`. -/
public lemma analyticOnNhd_sinSq_prefactor_mul
    (sign : ℂ) {inner : ℂ → ℂ} (hinner : AnalyticOnNhd ℂ inner ACDomain) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => sign * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) * inner u) ACDomain := by
  exact (analyticOnNhd_const.mul analyticOnNhd_sinSqHalfPi).mul hinner

end

end MagicFunction.g.CohnElkies.IntegralReps

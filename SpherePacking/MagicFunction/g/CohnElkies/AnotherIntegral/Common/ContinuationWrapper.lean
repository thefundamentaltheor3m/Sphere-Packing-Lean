module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationGeneric
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Shared analyticity helpers for `AnotherRHS`

Extracts the common `sign * (sin (π u / 2))^2 * inner` prefactor used by `aAnotherRHS_analyticOnNhd`
and `bAnotherRHS_analyticOnNhd`.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open Real Complex SpherePacking

noncomputable section

/-- If `inner` is analytic on `ACDomain`, then so is
`u ↦ sign * (sin (π u / 2))^2 * inner u` for any constant `sign : ℂ`. -/
public lemma analyticOnNhd_sinSq_prefactor_mul
    (sign : ℂ) {inner : ℂ → ℂ} (hinner : AnalyticOnNhd ℂ inner ACDomain) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => sign * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) * inner u) ACDomain :=
  (analyticOnNhd_const.mul (by
    have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
      simpa [Function.comp] using ((by simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))) :
          AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ)).comp
        (AnalyticOnNhd.div_const (analyticOnNhd_const.mul analyticOnNhd_id) :
          AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain) (by intro _ _; simp)
    exact hsin.pow 2)).mul hinner

end

end MagicFunction.g.CohnElkies.IntegralReps

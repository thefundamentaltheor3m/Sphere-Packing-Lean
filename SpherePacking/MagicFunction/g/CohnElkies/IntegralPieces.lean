module
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.b.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul


/-!
# Trigonometric helper lemmas for the `g` integrals

These isolate the algebraic and trigonometric manipulations needed to factor out the term
`sin(π u / 2)^2` from the vertical-segment pieces of the defining integrals of `a'` and `b'`.

## Main statements
* `MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I`
* `MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq`
-/

namespace MagicFunction.g.CohnElkies

open scoped BigOperators
open MeasureTheory Real Complex intervalIntegral

noncomputable section

namespace Trig

/-- Rewrite `2 - exp(π u i) - exp(-π u i)` as `2 - 2 cos(π u)`. -/
public lemma two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I (u : ℝ) :
    (2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) =
      ((2 - 2 * Real.cos (π * u) : ℝ) : ℂ) := by
  set z : ℂ := ((π * u : ℝ) : ℂ)
  have hcos : Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) =
      (2 : ℂ) * Complex.cos z := by
    simpa [neg_mul] using (Complex.two_cos (x := z)).symm
  calc
    (2 : ℂ) - Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) =
        (2 : ℂ) - (Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))) := by
          simpa using sub_sub (2 : ℂ) (Complex.exp (z * Complex.I)) (Complex.exp (-(z * Complex.I)))
    _ = (2 : ℂ) - (2 : ℂ) * Complex.cos z := by simp [hcos]
    _ = ((2 - 2 * Real.cos (π * u) : ℝ) : ℂ) := by simp [z, sub_eq_add_neg]

/-- Rewrite `2 - 2 cos(π u)` as `4 sin(π u / 2)^2`. -/
public lemma two_sub_two_cos_eq_four_sin_sq (u : ℝ) :
    (2 - 2 * Real.cos (π * u) : ℝ) = 4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by
  have hsin : (Real.sin (π * u / 2)) ^ (2 : ℕ) = 1 / 2 - Real.cos (π * u) / 2 := by
    have : (2 : ℝ) * (π * u / 2) = π * u := by ring
    simpa [pow_two, this] using (Real.sin_sq_eq_half_sub (x := π * u / 2))
  calc
    (2 - 2 * Real.cos (π * u) : ℝ) = 4 * (1 / 2 - Real.cos (π * u) / 2) := by ring
    _ = 4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by simp [hsin]

end Trig

end

end MagicFunction.g.CohnElkies

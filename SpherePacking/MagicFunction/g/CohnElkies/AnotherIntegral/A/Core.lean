module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# Core definitions for `AnotherIntegral.A`

This file defines the integrand and integral used in the "another integral" representation of
`a'`. It is kept small to avoid import cycles: analytic-continuation files can depend on these
definitions without importing the full representation proof.

## Main definitions
* `aAnotherIntegrand`
* `aAnotherIntegral`

## Main statement
* `aAnotherIntegral_eq`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open MeasureTheory Real Complex

noncomputable section

/-- The integrand used in the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrand (u t : ℝ) : ℂ :=
  ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
      Real.exp (-π * u * t))

/-- The "another integral" associated to `a'`, defined as `∫_{t>0} aAnotherIntegrand u t`. -/
@[expose] public def aAnotherIntegral (u : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t

end

end MagicFunction.g.CohnElkies.IntegralReps

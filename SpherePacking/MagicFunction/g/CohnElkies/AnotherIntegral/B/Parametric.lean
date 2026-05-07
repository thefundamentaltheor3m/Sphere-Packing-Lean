module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
public import SpherePacking.Basic.Domains.RightHalfPlane
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.AnalyticityWrapper

/-!
# Complex-parameter "another integral" for `b'`

This file defines a complex-parameter integrand and integral for the "another integral"
representation of `b'`, obtained by replacing `Real.exp (-π * u * t)` with
`Complex.exp (-(π : ℂ) * u * (t : ℂ))`. We prove analyticity of the resulting function on the
right half-plane and record its restriction to real parameters.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open MeasureTheory Real Complex

noncomputable section

open SpherePacking

/-- Complex-parameter integrand for the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  bAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" associated to `b'`. -/
@[expose] public def bAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrandC u t

/-- Restriction of `bAnotherIntegrandC` to real parameters. -/
public lemma bAnotherIntegrandC_ofReal (u t : ℝ) :
    bAnotherIntegrandC (u : ℂ) t = bAnotherBase t * (Real.exp (-π * u * t) : ℂ) := by
  simp [bAnotherIntegrandC, mul_assoc]

/-- Restriction of `bAnotherIntegralC` to real parameters. -/
public lemma bAnotherIntegralC_ofReal (u : ℝ) :
    bAnotherIntegralC (u : ℂ) =
      ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ) :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t _ ↦ bAnotherIntegrandC_ofReal u t)

/-- `bAnotherIntegralC` is analytic on the right half-plane. -/
public lemma bAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherIntegralC rightHalfPlane := by
  convert analyticOnNhd_integral_base_exp (base := bAnotherBase) continuousOn_bAnotherBase
    (fun u hu ↦ bAnotherBase_integrable_exp (u := u) hu) using 1

end

end MagicFunction.g.CohnElkies.IntegralReps

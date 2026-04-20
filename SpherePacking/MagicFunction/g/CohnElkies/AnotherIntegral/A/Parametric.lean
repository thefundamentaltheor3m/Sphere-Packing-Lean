module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.ImagAxis
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.LargeImagApprox
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
public import SpherePacking.Basic.Domains.RightHalfPlane
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.AnalyticityWrapper
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.Integration.Measure


/-!
# Complex-parameter "another integral" for `a'`

This file defines a complex-parameter integrand and integral by replacing the real factor
`Real.exp (-π * u * t)` with the holomorphic exponential `Complex.exp (-(π : ℂ) * u * (t : ℂ))`.
We prove analyticity of the resulting function on the right half-plane and record its restriction
to real parameters.

## Main definitions
* `aAnotherBase`
* `aAnotherIntegrandC`
* `aAnotherIntegralC`

## Main statements
* `aAnotherIntegralC_ofReal`
* `aAnotherIntegralC_analyticOnNhd`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped UpperHalfPlane

open MeasureTheory Real Complex
open SpherePacking.Integration (μIoi0)
open UpperHalfPlane

open SpherePacking

noncomputable section


/-- The `u`-independent bracket in the "another integral" integrand for `a'`. -/
@[expose] public def aAnotherBase (t : ℝ) : ℂ :=
  (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
      ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
      ((8640 / π : ℝ) : ℂ) * t -
      ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))

/-- Complex-parameter integrand for the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" for `a'`. -/
@[expose] public def aAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrandC u t

@[simp]
lemma aAnotherIntegrandC_eq (u : ℂ) (t : ℝ) :
    aAnotherIntegrandC u t = aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ)) := rfl

lemma aAnotherIntegrand_eq (u t : ℝ) :
    aAnotherIntegrand u t = aAnotherBase t * Real.exp (-π * u * t) := by
  simp [aAnotherIntegrand, aAnotherBase, mul_assoc]

lemma aAnotherIntegrandC_ofReal (u t : ℝ) :
    aAnotherIntegrandC (u : ℂ) t = aAnotherIntegrand u t := by
  simp [aAnotherIntegrandC, aAnotherBase, aAnotherIntegrand]

/-- On real parameters, `aAnotherIntegralC` agrees with
the real "another integral". -/
public lemma aAnotherIntegralC_ofReal (u : ℝ) :
    aAnotherIntegralC (u : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t :=
  MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
    measurableSet_Ioi (fun t _ => by simpa using aAnotherIntegrandC_ofReal u t)

/-- Continuity of `aAnotherBase` on `(0, ∞)`. -/
lemma continuousOn_aAnotherBase : ContinuousOn aAnotherBase (Set.Ioi (0 : ℝ)) := by
  have hcontφ : ContinuousOn (fun z : ℂ => φ₀'' z) upperHalfPlaneSet := by
    simpa using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn
  have hden0 : ∀ t ∈ Set.Ioi (0 : ℝ), (t : ℂ) ≠ 0 :=
    fun t ht => by exact_mod_cast ne_of_gt ht
  have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
    continuous_const.continuousOn.div continuous_ofReal.continuousOn hden0
  have hmaps :
      Set.MapsTo (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ))
        upperHalfPlaneSet := fun t ht => by
    change 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im
    rw [imag_I_div t]; exact inv_pos.2 (by simpa using ht)
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
    hcontφ.comp hcontIdiv hmaps
  have hpowC : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
  have hexp2C : Continuous fun t : ℝ => ((Real.exp (2 * π * t)) : ℂ) := by fun_prop
  exact (((hpowC.continuousOn.mul hφcomp).sub (continuousOn_const.mul hexp2C.continuousOn)).add
    (continuousOn_const.mul continuous_ofReal.continuousOn)).sub continuousOn_const

/-- Integrability of `t ↦ aAnotherBase t * exp (-π u t)` on `t > 0`, for `u > 0`. -/
lemma aAnotherBase_integrable_exp {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherBase t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
  (aAnotherIntegrand_integrable_of_pos hu).congr <|
    Filter.Eventually.of_forall fun t => by simp [aAnotherIntegrand_eq]

/-- `aAnotherIntegralC` is analytic on the right half-plane. -/
public lemma aAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherIntegralC rightHalfPlane := by
  convert analyticOnNhd_integral_base_exp (base := aAnotherBase)
    continuousOn_aAnotherBase (fun u hu => aAnotherBase_integrable_exp (u := u) hu) using 1

end

end MagicFunction.g.CohnElkies.IntegralReps

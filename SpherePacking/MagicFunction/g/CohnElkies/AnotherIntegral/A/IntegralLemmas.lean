module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Complex.Basic
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Core
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.ImagAxis
public import
  SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
public import SpherePacking.Basic.Domains.RightHalfPlane
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.AnalyticityWrapper
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.APrimeExtension
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationGeneric
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation


/-!
# Laplace-type integrals and analytic continuation for `AnotherIntegral.A`

Explicit evaluations and integrability facts for basic Laplace-type integrals on `t > 0`,
in the complex-valued form used by the "another integral" representation of `a'`. Also includes
the analytic-continuation step that extends the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`.

## Main definitions
* `aAnotherBase`, `aAnotherIntegrandC`, `aAnotherIntegralC`, `aAnotherRHS`

## Main statements
* `aRadial_eq_another_integral_analytic_continuation_of_gt2`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology UpperHalfPlane

open MeasureTheory Real Complex UpperHalfPlane
open SpherePacking
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

noncomputable section

/-- The `u`-independent bracket in the "another integral" integrand for `a'`. -/
@[expose] public def aAnotherBase (t : ℝ) : ℂ :=
  (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
    ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))

/-- Complex-parameter integrand for the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" for `a'`. -/
@[expose] public def aAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrandC u t

/-- `aAnotherIntegralC` is analytic on the right half-plane. -/
public lemma aAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherIntegralC rightHalfPlane := by
  have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
    continuous_const.continuousOn.div continuous_ofReal.continuousOn fun t ht => by
      exact_mod_cast ne_of_gt ht
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
    (by simpa using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
      ContinuousOn (fun z : ℂ => φ₀'' z) upperHalfPlaneSet).comp hcontIdiv fun t ht => by
        change 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im
        rw [imag_I_div t]; exact inv_pos.2 (by simpa using ht)
  have hbase : ContinuousOn aAnotherBase (Set.Ioi (0 : ℝ)) :=
    ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
      hφcomp).sub (continuousOn_const.mul (by fun_prop : Continuous fun t : ℝ =>
      ((Real.exp (2 * π * t)) : ℂ)).continuousOn)).add
      (continuousOn_const.mul continuous_ofReal.continuousOn)).sub continuousOn_const
  convert analyticOnNhd_integral_base_exp (base := aAnotherBase)
    hbase (fun u hu => (aAnotherIntegrand_integrable_of_pos hu).congr <|
      Filter.Eventually.of_forall fun t => by
        simp [aAnotherIntegrand, aAnotherBase, mul_assoc]) using 1

/-!
## Analytic RHS function on `ℂ`

This is the complex-analytic function whose restriction to the real axis is the blueprint RHS.
-/

def aAnotherRHS (u : ℂ) : ℂ :=
  (4 * Complex.I) * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
    ((36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
      (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)

lemma aAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := fun u hu h0 =>
    absurd (by simpa [rightHalfPlane] using hu.1) (by simp [h0])
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (sub_ne_zero.2 (by simpa using hu.2))
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (pow_ne_zero _ (hu_ne0 u hu))
  have hterm3 :
      AnalyticOnNhd ℂ (fun u : ℂ => (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id)
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (hu_ne0 u hu)
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)
        ACDomain := by
    simpa [sub_eq_add_neg, add_assoc] using (hterm1.sub hterm2).add
      (hterm3.add (aAnotherIntegralC_analyticOnNhd.mono fun u hu => hu.1))
  simpa [aAnotherRHS] using
    analyticOnNhd_sinSq_prefactor_mul (sign := 4 * Complex.I) hinner

/-- Analytic-continuation step: extend the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`. -/
public theorem aRadial_eq_another_integral_analytic_continuation_of_gt2
  (h_gt2 :
      ∀ r : ℝ, 2 < r →
        a' r =
          (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
                ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * Complex.I) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  refine analytic_continuation_of_gt2
    ⟨aPrimeC, aPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.a.RealIntegrals.a' u = a' u by
        simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) (hu := hu.le)).symm]
        using aPrimeC_ofReal u⟩
    aAnotherRHS_analyticOnNhd
    (rhsR := fun r : ℝ =>
      (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    (fun r => by
      simp only [aAnotherRHS, show (Complex.sin ((π : ℂ) * (r : ℂ) / 2)) ^ (2 : ℕ) =
        ((Real.sin (π * r / 2)) ^ (2 : ℕ) : ℂ) by simp,
        show aAnotherIntegralC (r : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t from
          MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
            measurableSet_Ioi (fun t _ => by
              simp [aAnotherIntegrandC, aAnotherBase, aAnotherIntegrand])])
    h_gt2 hu hu2

/-- Integral of a triple sum is the sum of the integrals, under integrability assumptions. -/
public lemma integral_add_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ((f x + g x) + h x) ∂ μ) =
      (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) + (∫ x, h x ∂ μ) := by
  simpa [add_assoc, MeasureTheory.integral_add (μ := μ) hf hg] using
    MeasureTheory.integral_add (μ := μ) (hf.add hg) hh

/-- `∫_{t > 0} exp (-π u t) dt = 1 / (π u)` as a complex-valued integral, for `u > 0`. -/
public lemma integral_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi (u := u) hu]
  exact integral_ofReal (μ := μIoi0) (𝕜 := ℂ)

/-- `∫_{t > 0} t * exp (-π u t) dt = 1 / (π u)^2` as a complex-valued integral, for `u > 0`. -/
public lemma integral_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using
    integral_ofReal (μ := μIoi0) (𝕜 := ℂ) (f := fun t : ℝ => t * Real.exp (-π * u * t))

/-- `∫_{t > 0} exp (2π t) * exp (-π u t) dt = 1 / (π (u - 2))` as a complex-valued integral,
for `u > 2`. -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ)
  rw [← MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using integral_ofReal (μ := μIoi0) (𝕜 := ℂ)
    (f := fun t : ℝ => Real.exp (2 * π * t) * Real.exp (-π * u * t))

/-- Integrability of `t ↦ exp (-π u t)` on `t > 0` as a complex-valued function, for `u > 0`. -/
public lemma integrableOn_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hne : (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (mul_ne_zero Real.pi_ne_zero hu.ne')
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

/-- Integrability of `t ↦ t * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 0`. -/
public lemma integrableOn_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hne : (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (pow_ne_zero 2 (mul_ne_zero Real.pi_ne_zero hu.ne'))
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

/-- Integrability of `t ↦ exp (2π t) * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 2`. -/
public lemma integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hne :
      (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [show (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ) from by
      simpa [μIoi0] using integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    exact_mod_cast one_div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_pos.2 hu).ne')
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0) hne

end

end MagicFunction.g.CohnElkies.IntegralReps

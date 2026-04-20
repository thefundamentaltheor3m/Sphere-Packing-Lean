module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Parametric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.APrimeExtension
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationGeneric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.ContinuationWrapper


/-!
# Analytic continuation for `AnotherIntegral.A`

Assuming the "another integral" formula for `a'` holds for all real `u > 2`, this file extends the
equality to all real `0 < u` with `u ≠ 2` by comparing analytic functions on the punctured
right half-plane `ACDomain = {u : ℂ | 0 < Re u} \\ {2}` and applying an identity theorem.

## Main definition
* `aAnotherRHS`

## Main statement
* `aRadial_eq_another_integral_analytic_continuation_of_gt2`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology

open MeasureTheory Real Complex
open SpherePacking
open MagicFunction.FourierEigenfunctions

noncomputable section

/-!
## Analytic RHS function on `ℂ`

This is the complex-analytic function whose restriction to the real axis is the blueprint RHS.
-/

def aAnotherRHS (u : ℂ) : ℂ :=
  (4 * (Complex.I : ℂ)) *
    (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
      ((36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
        (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) +
          aAnotherIntegralC u)

lemma aAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := fun u hu h0 =>
    absurd (by simpa [rightHalfPlane] using hu.1) (by simp [h0])
  have hI : AnalyticOnNhd ℂ aAnotherIntegralC ACDomain :=
    aAnotherIntegralC_analyticOnNhd.mono fun u hu => hu.1
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
    simpa [sub_eq_add_neg, add_assoc] using (hterm1.sub hterm2).add (hterm3.add hI)
  simpa [aAnotherRHS] using
    analyticOnNhd_sinSq_prefactor_mul (sign := (4 * (Complex.I : ℂ))) hinner

/-!
## Analytic extension of `a'`
-/

lemma exists_a'_analytic_extension :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      (∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = a' u) := by
  refine ⟨aPrimeC, aPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => ?_⟩
  have ha' : MagicFunction.a.RealIntegrals.a' u = a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) (hu := hu.le)).symm
  simpa [ha'] using aPrimeC_ofReal u

/-!
## Final wrapper theorem
-/

/--
Analytic-continuation step: extend the "another integral" identity for `a'` from `u > 2` to all
real `0 < u` with `u ≠ 2`.
-/
public theorem aRadial_eq_another_integral_analytic_continuation_of_gt2
  (h_gt2 :
      ∀ r : ℝ, 2 < r →
        a' r =
          (4 * (Complex.I : ℂ)) *
            (Real.sin (π * r / 2)) ^ (2 : ℕ) *
              ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
                (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
                (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
                  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  let rhsR := fun r : ℝ =>
    (4 * (Complex.I : ℂ)) *
      (Real.sin (π * r / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t)
  have h_rhs_eq : ∀ r : ℝ, aAnotherRHS (r : ℂ) = rhsR r := fun r => by
    have hsin :
        (Complex.sin ((π : ℂ) * (r : ℂ) / 2)) ^ (2 : ℕ) =
          ((Real.sin (π * r / 2)) ^ (2 : ℕ) : ℂ) := by simp
    simp only [aAnotherRHS, hsin, by simpa using aAnotherIntegralC_ofReal r, rhsR]
  exact analytic_continuation_of_gt2 exists_a'_analytic_extension aAnotherRHS_analyticOnNhd
    h_rhs_eq h_gt2 hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

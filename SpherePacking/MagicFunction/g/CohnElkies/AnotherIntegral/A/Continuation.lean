module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Parametric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.APrimeExtension
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationGeneric
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv


/-!
# Analytic continuation for `AnotherIntegral.A`

Assuming the "another integral" formula for `a'` holds for all real `u > 2`, this file extends the
equality to all real `0 < u` with `u ≠ 2` by comparing analytic functions on the punctured
right half-plane `ACDomain = {u : ℂ | 0 < Re u} \\ {2}` and applying an identity theorem.

## Main definition
* `aAnotherRHS`

## Main statement
* `aRadial_eq_another_integral_analytic_continuation_of_gt2`

## Domain for the identity theorem

We work on `ACDomain = {u : ℂ | 0 < Re u} \\ {2}`.
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
  have ha : ACDomain ⊆ rightHalfPlane := by
    intro u hu
    exact hu.1
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := by
    intro u hu h0
    have : u.re = 0 := by simp [h0]
    have : ¬ (0 : ℝ) < u.re := by simp [this]
    exact this (by simpa [rightHalfPlane] using hu.1)
  have hsin_arg : AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain := by
    have hmul : AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u) ACDomain :=
      (analyticOnNhd_const.mul analyticOnNhd_id)
    exact AnalyticOnNhd.div_const hmul
  have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
    -- `sin` is analytic everywhere, so we can compose with the affine map `u ↦ π*u/2`.
    have hsin_univ : AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ) := by
      simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))
    simpa [Function.comp] using hsin_univ.comp hsin_arg (by intro _ _; simp)
  have hsin_sq :
      AnalyticOnNhd ℂ (fun u : ℂ => (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ)) ACDomain :=
    hsin.pow 2
  have hI : AnalyticOnNhd ℂ aAnotherIntegralC ACDomain :=
    (aAnotherIntegralC_analyticOnNhd).mono ha
  have hsub2 : AnalyticOnNhd ℂ (fun u : ℂ => u - 2) ACDomain :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hpow2 : AnalyticOnNhd ℂ (fun u : ℂ => u ^ (2 : ℕ)) ACDomain :=
    analyticOnNhd_id.pow 2
  have hden1 : ∀ u ∈ ACDomain, (π : ℂ) ^ (3 : ℕ) * (u - 2) ≠ 0 := by
    intro u hu
    have hu_ne2 : u ≠ (2 : ℂ) := by simpa using hu.2
    have : u - 2 ≠ 0 := sub_ne_zero.2 hu_ne2
    exact mul_ne_zero (pow_ne_zero _ hπ) this
  have hden2 : ∀ u ∈ ACDomain, (π : ℂ) ^ (3 : ℕ) * (u ^ (2 : ℕ)) ≠ 0 := by
    intro u hu
    have : u ≠ 0 := hu_ne0 u hu
    exact mul_ne_zero (pow_ne_zero _ hπ) (pow_ne_zero _ this)
  have hden3 : ∀ u ∈ ACDomain, (π : ℂ) ^ (3 : ℕ) * u ≠ 0 := by
    intro u hu
    have : u ≠ 0 := hu_ne0 u hu
    exact mul_ne_zero (pow_ne_zero _ hπ) this
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2))) ACDomain := by
    have hden : AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) ^ (3 : ℕ) * (u - 2)) ACDomain :=
      (analyticOnNhd_const.mul hsub2)
    exact analyticOnNhd_const.div hden hden1
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul hpow2) hden2
  have hterm3 :
      AnalyticOnNhd ℂ (fun u : ℂ => (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id) hden3
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)
        ACDomain := by
    simpa [sub_eq_add_neg, add_assoc] using (hterm1.sub hterm2).add (hterm3.add hI)
  -- Multiply together the analytic factors.
  have hconst : AnalyticOnNhd ℂ (fun _u : ℂ => (4 * (Complex.I : ℂ))) ACDomain :=
    analyticOnNhd_const
  simpa [aAnotherRHS] using (hconst.mul hsin_sq).mul hinner

/-!
## Analytic extension of `a'`

The blueprint asserts `a` (hence `a'`) is analytic in a neighborhood of `[0,∞)`.
We will implement this by complexifying the defining contour integrals for the six pieces.
-/

lemma exists_a'_analytic_extension :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      (∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = a' u) := by
  refine ⟨aPrimeC, (aPrimeC_analyticOnNhd).mono (fun u hu => hu.1), ?_⟩
  intro u hu _hu2
  have ha' : MagicFunction.a.RealIntegrals.a' u = a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) (hu := hu.le)).symm
  simpa [ha'] using aPrimeC_ofReal u

/-!
## Final wrapper theorem

This theorem is the desired analytic continuation statement, but in a form that explicitly uses
the complex-analytic RHS `aAnotherRHS` and an abstract analytic extension `f` of `a'`.
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
  -- Reformulate h_gt2 in terms of aAnotherRHS for the generic wrapper.
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
    have hI : aAnotherIntegralC (r : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t := by
      simpa using aAnotherIntegralC_ofReal r
    simp only [aAnotherRHS, hsin, hI, rhsR]
  exact analytic_continuation_of_gt2 exists_a'_analytic_extension aAnotherRHS_analyticOnNhd
    h_rhs_eq h_gt2 hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

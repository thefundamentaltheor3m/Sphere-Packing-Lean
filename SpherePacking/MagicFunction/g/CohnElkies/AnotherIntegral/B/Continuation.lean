module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Parametric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.BPrimeExtension
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
public import SpherePacking.MagicFunction.g.CohnElkies.IntegralReps.ACDomain
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationGeneric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.ContinuationWrapper


/-!
# Analytic continuation for `AnotherIntegral.B`

Assuming the "another integral" formula for `b'` holds for all real `u > 2`, this file extends the
equality to all real `0 < u` with `u ≠ 2` by comparing analytic functions on the punctured
right half-plane `ACDomain = {u : ℂ | 0 < Re u} \\ {2}` and applying an identity theorem.

## Main definition
* `bAnotherRHS`

## Main statement
* `bRadial_eq_another_integral_analytic_continuation_of_gt2`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology

open MeasureTheory Real Complex

open SpherePacking

open MagicFunction.FourierEigenfunctions

noncomputable section

/-!
## Analytic RHS function on `ℂ`
-/

def bAnotherRHS (u : ℂ) : ℂ :=
  (-4 * (Complex.I : ℂ)) *
    (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)

lemma bAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherRHS ACDomain := by
  have hb : ACDomain ⊆ rightHalfPlane := fun u hu => hu.1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := by
    intro u hu h0
    have hre : (0 : ℝ) < u.re := by simpa [rightHalfPlane] using hu.1
    exact (ne_of_gt hre) (by simp [h0])
  have hI : AnalyticOnNhd ℂ bAnotherIntegralC ACDomain :=
    (bAnotherIntegralC_analyticOnNhd).mono hb
  have hsub2 : AnalyticOnNhd ℂ (fun u : ℂ => u - 2) ACDomain :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hden1 : ∀ u ∈ ACDomain, (π : ℂ) * u ≠ 0 := fun u hu =>
    mul_ne_zero hπ (hu_ne0 u hu)
  have hden2 : ∀ u ∈ ACDomain, (π : ℂ) * (u - 2) ≠ 0 := fun u hu =>
    mul_ne_zero hπ (sub_ne_zero.2 (by simpa [Set.mem_singleton_iff] using hu.2))
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (144 : ℂ) / ((π : ℂ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id) hden1
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (1 : ℂ) / ((π : ℂ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul hsub2) hden2
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)
        ACDomain := by
    simpa [add_assoc] using (hterm1.add hterm2).add hI
  unfold bAnotherRHS
  exact analyticOnNhd_sinSq_prefactor_mul (sign := (-4 * (Complex.I : ℂ))) hinner

lemma bAnotherRHS_ofReal (u : ℝ) :
    bAnotherRHS (u : ℂ) =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
            ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) := by
  simp [bAnotherRHS, bAnotherIntegralC_ofReal, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    mul_assoc]

/-!
## Analytic extension of `b'`
-/

lemma exists_b'_analytic_extension :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      (∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = b' u) := by
  refine ⟨bPrimeC, (bPrimeC_analyticOnNhd).mono (fun u hu => hu.1), ?_⟩
  intro u hu _hu2
  have hb' : MagicFunction.b.RealIntegrals.b' u = b' u := by
    simpa using
      (MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) (le_of_lt hu)).symm
  simpa [hb'] using (bPrimeC_ofReal u)

/-!
## Final wrapper theorem
-/

/--
Analytic-continuation step: extend the "another integral" identity for `b'` from `u > 2` to all
real `0 < u` with `u ≠ 2`.
-/
public theorem bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 :
      ∀ r : ℝ, 2 < r →
        b' r =
          (-4 * (Complex.I : ℂ)) *
            (Real.sin (π * r / 2)) ^ (2 : ℕ) *
              ((144 : ℂ) / (π * r) + (1 : ℂ) / (π * (r - 2)) +
                ∫ t in Set.Ioi (0 : ℝ),
                  bAnotherBase t * (Real.exp (-π * r * t) : ℂ)))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
            ∫ t in Set.Ioi (0 : ℝ),
              bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) := by
  let rhsR := fun r : ℝ =>
    (-4 * (Complex.I : ℂ)) *
      (Real.sin (π * r / 2)) ^ (2 : ℕ) *
        ((144 : ℂ) / (π * r) + (1 : ℂ) / (π * (r - 2)) +
          ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * r * t) : ℂ))
  have h_rhs_eq : ∀ u : ℝ, bAnotherRHS (u : ℂ) = rhsR u := bAnotherRHS_ofReal
  exact analytic_continuation_of_gt2 exists_b'_analytic_extension bAnotherRHS_analyticOnNhd
    h_rhs_eq h_gt2 hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
public import SpherePacking.Basic.Domains.RightHalfPlane
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.AnalyticityWrapper
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

## Main definitions
* `bAnotherIntegrandC`, `bAnotherIntegralC`, `bAnotherRHS`

## Main statement
* `bRadial_eq_another_integral_analytic_continuation_of_gt2`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology

open MeasureTheory Real Complex SpherePacking MagicFunction.FourierEigenfunctions

noncomputable section

/-- Complex-parameter integrand for the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  bAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" associated to `b'`. -/
@[expose] public def bAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrandC u t

/-- Restriction of `bAnotherIntegralC` to real parameters. -/
public lemma bAnotherIntegralC_ofReal (u : ℝ) :
    bAnotherIntegralC (u : ℂ) =
      ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * u * t) : ℂ) :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t _ ↦ by simp [bAnotherIntegrandC, mul_assoc])

def bAnotherRHS (u : ℂ) : ℂ :=
  (-4 * (Complex.I : ℂ)) *
    (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / ((π : ℂ) * u) + (1 : ℂ) / ((π : ℂ) * (u - 2)) + bAnotherIntegralC u)

lemma bAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ bAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (144 : ℂ) / ((π : ℂ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id) fun u hu =>
      mul_ne_zero hπ fun h0 =>
        (ne_of_gt (by simpa [rightHalfPlane] using hu.1)) (by simp [h0])
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (1 : ℂ) / ((π : ℂ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero hπ (sub_ne_zero.2 (by simpa [Set.mem_singleton_iff] using hu.2))
  unfold bAnotherRHS
  exact analyticOnNhd_sinSq_prefactor_mul (sign := (-4 * (Complex.I : ℂ))) <| by
    simpa [add_assoc] using
      (hterm1.add hterm2).add ((show AnalyticOnNhd ℂ bAnotherIntegralC rightHalfPlane by
        convert analyticOnNhd_integral_base_exp (base := bAnotherBase) continuousOn_bAnotherBase
          (fun u hu ↦ bAnotherBase_integrable_exp (u := u) hu) using 1).mono fun u hu => hu.1)

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
              bAnotherBase t * (Real.exp (-π * u * t) : ℂ)) :=
  analytic_continuation_of_gt2
    ⟨bPrimeC, bPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.b.RealIntegrals.b' u = b' u by
        simpa using (MagicFunction.g.CohnElkies.b'_eq_realIntegrals_b' (u := u) hu.le).symm]
        using bPrimeC_ofReal u⟩
    bAnotherRHS_analyticOnNhd
    (fun u => by
      simp [bAnotherRHS, bAnotherIntegralC_ofReal, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm, mul_assoc])
    h_gt2 hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

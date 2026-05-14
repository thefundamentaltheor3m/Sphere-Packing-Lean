module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
public import SpherePacking.Basic.Domains.RightHalfPlane
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.Common.AnalyticityWrapper
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.BPrimeExtension
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.ContinuationGeneric
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.LaplaceRepresentation
public import SpherePacking.MagicFunction.b.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# "Another integral" representation for `b'` (`AnotherIntegral.B`)

This file proves the blueprint proposition `prop:b-another-integral`: for real `u` with `0 < u`
and `u ≠ 2`, the function `b' u` is given by an explicit algebraic prefactor times an integral of
`bAnotherIntegrand u`. The proof combines the `u > 2` computation with analytic continuation on
the punctured right half-plane `ACDomain = {u : ℂ | 0 < Re u} \ {2}`.

## Main definitions
* `bAnotherIntegrand`
* `bAnotherIntegrandC`, `bAnotherIntegralC`, `bAnotherRHS`

## Main statement
* `bRadial_eq_another_integral_main`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology
open MeasureTheory Real Complex MagicFunction.FourierEigenfunctions SpherePacking

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

/-- The integrand used in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrand (u t : ℝ) : ℂ :=
  bAnotherBase t * (Real.exp (-π * u * t) : ℂ)

lemma bRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) : b' u =
    (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
        ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hpoint (t : ℝ) : bLaplaceIntegrand u t = bAnotherIntegrand u t +
      ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) := by
    simp [bLaplaceIntegrand, bAnotherIntegrand, bAnotherBase, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_left_comm, mul_comm, mul_add]
  have hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have h2ExpInt : IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hCorrInt : IntegrableOn
      (fun t : ℝ => ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t))
      (Set.Ioi (0 : ℝ)) :=
    ((hExpInt.const_mul (144 : ℂ)).add h2ExpInt).congr <|
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => by
        simp [-Complex.ofReal_exp, add_mul, mul_assoc]
  have hAnotherInt : IntegrableOn (fun t : ℝ => bAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    simpa [show (fun t : ℝ => bAnotherIntegrand u t) =
        fun t : ℝ => bLaplaceIntegrand u t -
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) from
      funext fun t => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (eq_sub_of_add_eq (hpoint t).symm)] using
      (bLaplaceIntegral_convergent (u := u) hu).sub hCorrInt
  have hLapInt_decomp : (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
      (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ),
        ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
          ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t +
            ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi (fun t _ => by simp [hpoint t])]
    exact integral_add hAnotherInt hCorrInt
  have hCorr_eval : (∫ t in Set.Ioi (0 : ℝ),
      ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
      (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) := by
    rw [show (fun t : ℝ => ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
          fun t => (144 : ℂ) * (Real.exp (-π * u * t) : ℂ) +
            (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) from
        funext fun t => by simp [-Complex.ofReal_exp, add_mul, mul_assoc],
      MeasureTheory.integral_add (hExpInt.const_mul (144 : ℂ)) h2ExpInt,
      MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
        (144 : ℂ) (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)),
      integral_exp_neg_pi_mul_Ioi_complex (u := u) hu0,
      integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu]
    push_cast; ring
  rw [show b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) from by
      simpa [bLaplaceIntegrand] using bRadial_eq_laplace_psiI_main (u := u) hu,
    hLapInt_decomp, hCorr_eval]
  ring_nf

/-- Main lemma for blueprint proposition `prop:b-another-integral`. -/
public theorem bRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t)) : ℂ)) *
          Real.exp (-π * u * t)) := by
  simpa [bAnotherIntegrand] using bRadial_eq_another_integral_analytic_continuation_of_gt2
    (h_gt2 := fun r hr => by
      simpa [bAnotherIntegrand] using bRadial_eq_another_integral_of_gt2 (u := r) hr)
    (u := u) hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

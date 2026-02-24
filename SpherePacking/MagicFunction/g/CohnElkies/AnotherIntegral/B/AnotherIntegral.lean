module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Continuation
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
`bAnotherIntegrand u`. The proof combines the `u > 2` computation with analytic continuation.

## Main definitions
* `bAnotherIntegrand`
* `bAnotherIntegral`

## Main statement
* `bRadial_eq_another_integral_main`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators

open MeasureTheory Real Complex

noncomputable section

open MagicFunction.FourierEigenfunctions

/-- The integrand used in the "another integral" representation of `b'`. -/
@[expose] public def bAnotherIntegrand (u t : ℝ) : ℂ :=
  bAnotherBase t * (Real.exp (-π * u * t) : ℂ)

lemma bRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
              ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hLap := bRadial_eq_laplace_psiI_main (u := u) hu
  let μ0 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  have hIntegrable (f : ℝ → ℂ)
      (hf : IntegrableOn (μ := (volume : Measure ℝ)) f (Set.Ioi (0 : ℝ))) :
      Integrable f μ0 := by
    simpa [MeasureTheory.IntegrableOn, μ0] using hf
  -- Normalize the Laplace integral into `bLaplaceIntegrand`.
  have hLap' :
      b' u =
        (-4 * (Complex.I : ℂ)) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) := by
    simpa [bLaplaceIntegrand] using hLap
  -- Pointwise decomposition: subtract off the explicit asymptotic pieces.
  have hpoint (t : ℝ) :
      bLaplaceIntegrand u t =
        bAnotherIntegrand u t +
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) := by
    -- Pure algebra: expand `bAnotherIntegrand` and cancel the added correction terms.
    simp [bLaplaceIntegrand, bAnotherIntegrand, bAnotherBase, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_left_comm, mul_comm, mul_add]
  have hLapInt :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) :=
    bLaplaceIntegral_convergent (u := u) hu
  have hIexp :
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * u) : ℝ) : ℂ) :=
    integral_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have hI2exp :
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ) :=
    integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hExpInt :
      IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have h2ExpInt :
      IntegrableOn
        (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
        (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hCorrInt :
      IntegrableOn
        (fun t : ℝ =>
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t))
        (Set.Ioi (0 : ℝ)) := by
    have hsum :
        IntegrableOn
            (fun t : ℝ =>
              (144 : ℂ) * (Real.exp (-π * u * t) : ℂ) +
                (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
            (Set.Ioi (0 : ℝ)) :=
      (hExpInt.const_mul (144 : ℂ)).add h2ExpInt
    refine hsum.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    simp [-Complex.ofReal_exp, add_mul, mul_assoc]
  have hAnotherInt :
      IntegrableOn (fun t : ℝ => bAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    -- `bAnotherIntegrand = bLaplaceIntegrand - correction`.
    have hEq :
        (fun t : ℝ => bAnotherIntegrand u t) =
          fun t : ℝ =>
            bLaplaceIntegrand u t -
              ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) := by
      funext t
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (eq_sub_of_add_eq (hpoint t).symm)
    simpa [hEq] using hLapInt.sub hCorrInt
  have hLapInt_decomp :
      (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
        (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) +
          (∫ t in Set.Ioi (0 : ℝ),
              ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) := by
    have hcongr :
        (∫ t in Set.Ioi (0 : ℝ), bLaplaceIntegrand u t) =
          ∫ t in Set.Ioi (0 : ℝ),
            bAnotherIntegrand u t +
              ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) := by
      refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ))
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      simp [hpoint t]
    rw [hcongr]
    have hAnother : Integrable (fun t : ℝ => bAnotherIntegrand u t) μ0 :=
      hIntegrable (fun t : ℝ => bAnotherIntegrand u t) hAnotherInt
    have hCorr :
        Integrable
          (fun t : ℝ =>
            ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) μ0 :=
      hIntegrable
        (fun t : ℝ =>
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t))
        hCorrInt
    change
      (∫ t, (bAnotherIntegrand u t +
            ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) ∂μ0) =
        (∫ t, bAnotherIntegrand u t ∂μ0) +
          ∫ t,
            (((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) ∂μ0
    simpa [μ0] using (MeasureTheory.integral_add hAnother hCorr)
  have hCorr_eval :
      (∫ t in Set.Ioi (0 : ℝ),
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
        (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) := by
    let f : ℝ → ℂ := fun t => (144 : ℂ) * (Real.exp (-π * u * t) : ℂ)
    let g : ℝ → ℂ := fun t => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)
    have hf : Integrable f μ0 :=
      hIntegrable f (hExpInt.const_mul (144 : ℂ))
    have hg : Integrable g μ0 :=
      hIntegrable g h2ExpInt
    have hfg :
        (fun t : ℝ =>
            ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t)) =
          fun t => f t + g t := by
      funext t
      simp [-Complex.ofReal_exp, f, g, add_mul, mul_assoc]
    have hIexpμ :
        (∫ t, (Real.exp (-π * u * t) : ℂ) ∂μ0) = ((1 / (π * u) : ℝ) : ℂ) := by
      simpa [μ0] using hIexp
    have hI2expμ :
        (∫ t, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μ0) =
          ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
      simpa [μ0] using hI2exp
    change
      (∫ t,
          ((144 : ℂ) + ((Real.exp (2 * π * t) : ℝ) : ℂ)) * Real.exp (-π * u * t) ∂μ0) = _
    rw [hfg, MeasureTheory.integral_add hf hg]
    have hf_eval :
        (∫ t, f t ∂μ0) = (144 : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
      dsimp [f]
      calc
        (∫ t, (144 : ℂ) * (Real.exp (-π * u * t) : ℂ) ∂μ0) =
            (144 : ℂ) * ∫ t, (Real.exp (-π * u * t) : ℂ) ∂μ0 := by
              simpa [-Complex.ofReal_exp, mul_assoc] using
                (MeasureTheory.integral_const_mul (μ := μ0) (144 : ℂ)
                  (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)))
        _ = (144 : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
              rw [hIexpμ]
    have hg_eval :
        (∫ t, g t ∂μ0) = ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
      simpa [g] using hI2expμ
    rw [hf_eval, hg_eval]
    simp [div_eq_mul_inv]
  -- Put everything together.
  rw [hLap']
  rw [hLapInt_decomp]
  rw [hCorr_eval]
  ring_nf

lemma bRadial_eq_another_integral_analytic_continuation {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
              ∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) := by
  -- Use the identity-theorem argument from `Continuation`, then rewrite the
  -- integral back to `bAnotherIntegrand`.
  have h_gt2 :
      ∀ r : ℝ, 2 < r →
        b' r =
          (-4 * (Complex.I : ℂ)) *
            (Real.sin (π * r / 2)) ^ (2 : ℕ) *
              ((144 : ℂ) / (π * r) + (1 : ℂ) / (π * (r - 2)) +
                ∫ t in Set.Ioi (0 : ℝ), bAnotherBase t * (Real.exp (-π * r * t) : ℂ)) := by
    intro r hr
    simpa [bAnotherIntegrand] using bRadial_eq_another_integral_of_gt2 (u := r) hr
  have hmain :=
    bRadial_eq_another_integral_analytic_continuation_of_gt2 (h_gt2 := h_gt2) (u := u) hu hu2
  simpa [bAnotherIntegrand] using hmain

/-- Main lemma for blueprint proposition `prop:b-another-integral`. -/
public theorem bRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) +
              ∫ t in Set.Ioi (0 : ℝ),
                (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) -
                    ((Real.exp (2 * π * t)) : ℂ)) *
                  Real.exp (-π * u * t)) := by
  -- Final wrapper: unfold `bAnotherIntegrand` and apply analytic-continuation lemma.
  simpa [bAnotherIntegrand] using bRadial_eq_another_integral_analytic_continuation (u := u) hu hu2

end

end MagicFunction.g.CohnElkies.IntegralReps

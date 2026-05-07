module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Core
public import SpherePacking.MagicFunction.a.Schwartz.Basic
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Continuation
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas

/-!
# "Another integral" representation for `a'` (`AnotherIntegral.A`)

Proves blueprint `prop:a-another-integral`: for `0 < u` and `u ≠ 2`, `a' u` equals an explicit
algebraic prefactor times an integral of `aAnotherIntegrand u` (analytic continuation from `u > 2`).
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open MeasureTheory Real Complex
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

lemma corrIntegral_eval {u : ℝ} (hu0 : 0 < u) (hu : 2 < u)
    {c36 c8640 c18144 : ℂ}
    (hc36 : c36 = ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
    (hc8640 : c8640 = ((8640 / π : ℝ) : ℂ))
    (hc18144 : c18144 = ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
    {corr : ℝ → ℂ}
    (hcorr : corr =
      fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t))
    (hIexp :
        (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ))
    (hItexp : (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ))
    (hI2exp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ))
    (hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (hTExpInt : IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (h2ExpInt : IntegrableOn
        (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) := by
  rw [hcorr]
  let f0 : ℝ → ℂ := fun t : ℝ => (Real.exp (-π * u * t) : ℂ)
  let f1 : ℝ → ℂ := fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)
  let f2 : ℝ → ℂ := fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)
  let g0 : ℝ → ℂ := fun t : ℝ => c18144 * f0 t
  let g1 : ℝ → ℂ := fun t : ℝ => (-c8640) * f1 t
  let g2 : ℝ → ℂ := fun t : ℝ => c36 * f2 t
  rw [show (∫ t in Set.Ioi (0 : ℝ),
      (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)) =
      ∫ t in Set.Ioi (0 : ℝ), ((g2 t + g1 t) + g0 t) from
    congrArg (integral (volume.restrict (Set.Ioi 0))) <| by
      funext t; dsimp [f0, f1, f2, g0, g1, g2]; ring]
  change (∫ t, ((g2 t + g1 t) + g0 t) ∂ μIoi0) =
    (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u)
  have hIntegrable (f : ℝ → ℂ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) : Integrable f μIoi0 := by
    simpa [MeasureTheory.IntegrableOn, μIoi0] using hf
  have hG0 : (∫ t, g0 t ∂ μIoi0) = c18144 * ((1 / (π * u) : ℝ) : ℂ) := by
    simpa [g0, f0, μIoi0] using (integral_const_mul (μ := μIoi0) c18144 f0).trans
      (by simpa [f0, μIoi0] using congrArg (c18144 * ·) hIexp)
  have hG1 : (∫ t, g1 t ∂ μIoi0) = (-c8640) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simpa [g1, f1, μIoi0] using (integral_const_mul (μ := μIoi0) (-c8640) f1).trans
      (by simpa [f1, μIoi0] using congrArg ((-c8640) * ·) hItexp)
  have hG2 : (∫ t, g2 t ∂ μIoi0) = c36 * ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
    simpa [g2, f2, μIoi0] using (integral_const_mul (μ := μIoi0) c36 f2).trans
      (by simpa [f2, μIoi0] using congrArg (c36 * ·) hI2exp)
  rw [integral_add_add (μ := μIoi0) ((hIntegrable f2 h2ExpInt).const_mul c36)
      ((hIntegrable f1 hTExpInt).const_mul (-c8640)) ((hIntegrable f0 hExpInt).const_mul c18144),
    hG2, hG1, hG0, hc36, hc8640, hc18144]
  have hu2ne : (u - 2 : ℝ) ≠ 0 := (sub_pos.mpr hu).ne'
  have hune : (u : ℝ) ≠ 0 := hu0.ne'
  push_cast [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp
  ring

lemma aRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              aAnotherIntegral u) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hLap' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    simpa [aLaplaceIntegrand, mul_assoc] using aRadial_eq_laplace_phi0_main hu
  set c36 : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc36
  set c8640 : ℂ := ((8640 / π : ℝ) : ℂ) with hc8640
  set c18144 : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc18144
  let corr : ℝ → ℂ :=
    fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)
  have hIexp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ) :=
    integral_exp_neg_pi_mul_Ioi_complex hu0
  have hItexp : (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := integral_mul_exp_neg_pi_mul_Ioi_complex hu0
  have hI2exp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex hu
  have hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex hu0
  have hTExpInt : IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu0
  have h2ExpInt : IntegrableOn
      (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex hu
  have hCorrInt : IntegrableOn corr (Set.Ioi (0 : ℝ)) := by
    have h36 : IntegrableOn
        (fun t : ℝ => (c36 * Real.exp (2 * π * t)) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2ExpInt.const_mul c36
    have h8640 : IntegrableOn (fun t : ℝ => (c8640 * t) * Real.exp (-π * u * t))
        (Set.Ioi (0 : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hTExpInt.const_mul c8640
    have h18144 : IntegrableOn (fun t : ℝ => c18144 * Real.exp (-π * u * t))
        (Set.Ioi (0 : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hExpInt.const_mul c18144
    refine ((h36.sub h8640).add h18144).congr <|
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_
    dsimp [corr]; ring_nf
  have hLapInt_decomp : (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
      (∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ), corr t) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
        ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t + corr t from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
        simp [-Complex.ofReal_exp, aLaplaceIntegrand, aAnotherIntegrand, c36, c8640, c18144,
          sub_eq_add_neg, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, corr]
        ring]
    exact integral_add (by simpa [MeasureTheory.IntegrableOn] using
      aAnotherIntegrand_integrable_of_pos hu0)
      (by simpa [MeasureTheory.IntegrableOn] using hCorrInt)
  simpa [aAnotherIntegral, hLapInt_decomp, show (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u) from
    corrIntegral_eval hu0 hu hc36 hc8640 hc18144 rfl hIexp hItexp hI2exp hExpInt hTExpInt h2ExpInt,
    add_assoc, add_left_comm, add_comm] using hLap'

/-- Main lemma for blueprint proposition `prop:a-another-integral`. -/
public theorem aRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              ∫ t in Set.Ioi (0 : ℝ),
                ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                        ((8640 / π : ℝ) : ℂ) * t -
                        ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
                    Real.exp (-π * u * t))) := by
  simpa [aAnotherIntegrand] using
    aRadial_eq_another_integral_analytic_continuation_of_gt2 (u := u) (hu := hu) (hu2 := hu2)
      fun r hr => by simpa [aAnotherIntegral] using aRadial_eq_another_integral_of_gt2 (u := r) hr

end MagicFunction.g.CohnElkies.IntegralReps

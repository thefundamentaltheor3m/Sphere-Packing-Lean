module
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Core
public import SpherePacking.MagicFunction.a.Schwartz.Basic
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Continuation
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas


/-!
# "Another integral" representation for `a'` (`AnotherIntegral.A`)

This file proves the blueprint proposition `prop:a-another-integral`: for real `u` with `0 < u`
and `u ≠ 2`, the function `a' u` is given by an explicit algebraic prefactor times an integral of
`aAnotherIntegrand u`. The proof combines the `u > 2` computation with analytic continuation.

## Main statement
* `aRadial_eq_another_integral_main`
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
    (hcorr :
      corr =
        fun t : ℝ =>
          (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t))
    (hIexp :
        (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ))
    (hItexp :
        (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
          ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ))
    (hI2exp :
        (∫ t in Set.Ioi (0 : ℝ),
            (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
          ((1 / (π * (u - 2)) : ℝ) : ℂ))
    (hExpInt :
        IntegrableOn (μ := (volume : Measure ℝ))
          (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (hTExpInt :
        IntegrableOn (μ := (volume : Measure ℝ))
          (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (h2ExpInt :
        IntegrableOn (μ := (volume : Measure ℝ))
          (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) := by
  -- Reduce to a sum of three basic Laplace integrals.
  rw [hcorr]
  let f0 : ℝ → ℂ := fun t : ℝ => (Real.exp (-π * u * t) : ℂ)
  let f1 : ℝ → ℂ := fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)
  let f2 : ℝ → ℂ := fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)
  let g0 : ℝ → ℂ := fun t : ℝ => c18144 * f0 t
  let g1 : ℝ → ℂ := fun t : ℝ => (-c8640) * f1 t
  let g2 : ℝ → ℂ := fun t : ℝ => c36 * f2 t
  have hsplit :
      (fun t : ℝ =>
          (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)) =
        fun t : ℝ => ((g2 t + g1 t) + g0 t) := by
    funext t
    dsimp [f0, f1, f2, g0, g1, g2]
    ring
  -- Rewrite the set integral using the pointwise identity.
  have hcongr :
      (∫ t in Set.Ioi (0 : ℝ),
          (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)) =
        ∫ t in Set.Ioi (0 : ℝ), ((g2 t + g1 t) + g0 t) := by
    refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi ?_
    intro t ht
    exact congrArg (fun f : ℝ → ℂ => f t) hsplit
  rw [hcongr]
  -- Switch to the restricted measure and split the integral.
  let μ0 : Measure ℝ := μIoi0
  change (∫ t, ((g2 t + g1 t) + g0 t) ∂ μ0) =
    (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
        (18144 : ℂ) / (π ^ (3 : ℕ) * u)
  have hIntegrable (f : ℝ → ℂ)
      (hf : IntegrableOn (μ := (volume : Measure ℝ)) f (Set.Ioi (0 : ℝ))) :
      Integrable f μ0 := by
    simpa [MeasureTheory.IntegrableOn, μ0, μIoi0] using hf
  have hf0 : Integrable f0 μ0 := hIntegrable f0 hExpInt
  have hf1 : Integrable f1 μ0 := hIntegrable f1 hTExpInt
  have hf2 : Integrable f2 μ0 := hIntegrable f2 h2ExpInt
  have hg0 : Integrable g0 μ0 := by
    dsimp [g0]
    exact hf0.const_mul c18144
  have hg1 : Integrable g1 μ0 := by
    dsimp [g1]
    exact hf1.const_mul (-c8640)
  have hg2 : Integrable g2 μ0 := by
    dsimp [g2]
    exact hf2.const_mul c36
  have hsplitInt :
      (∫ t, ((g2 t + g1 t) + g0 t) ∂ μ0) =
        (∫ t, g2 t ∂ μ0) + (∫ t, g1 t ∂ μ0) + (∫ t, g0 t ∂ μ0) :=
    integral_add_add (μ := μ0) hg2 hg1 hg0
  have hG0 : (∫ t, g0 t ∂ μ0) = c18144 * ((1 / (π * u) : ℝ) : ℂ) := by
    have h0 : (∫ t, g0 t ∂ μ0) = c18144 * ∫ t, f0 t ∂ μ0 := by
      simpa [g0] using (MeasureTheory.integral_const_mul (μ := μ0) c18144 f0)
    have hI0 : (∫ t, f0 t ∂ μ0) = ((1 / (π * u) : ℝ) : ℂ) := by
      dsimp [f0]
      simpa [μ0, μIoi0] using hIexp
    calc
      (∫ t, g0 t ∂ μ0) = c18144 * ∫ t, f0 t ∂ μ0 := h0
      _ = c18144 * ((1 / (π * u) : ℝ) : ℂ) := by rw [hI0]
  have hG1 :
      (∫ t, g1 t ∂ μ0) = (-c8640) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have h1 : (∫ t, g1 t ∂ μ0) = (-c8640) * ∫ t, f1 t ∂ μ0 := by
      simpa [g1] using (MeasureTheory.integral_const_mul (μ := μ0) (-c8640) f1)
    have hI1 : (∫ t, f1 t ∂ μ0) = ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
      dsimp [f1]
      simpa [μ0, μIoi0] using hItexp
    calc
      (∫ t, g1 t ∂ μ0) = (-c8640) * ∫ t, f1 t ∂ μ0 := h1
      _ = (-c8640) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by rw [hI1]
  have hG2 : (∫ t, g2 t ∂ μ0) = c36 * ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
    have h2 : (∫ t, g2 t ∂ μ0) = c36 * ∫ t, f2 t ∂ μ0 := by
      simpa [g2] using (MeasureTheory.integral_const_mul (μ := μ0) c36 f2)
    have hI2 : (∫ t, f2 t ∂ μ0) = ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
      dsimp [f2]
      simpa [μ0, μIoi0] using hI2exp
    calc
      (∫ t, g2 t ∂ μ0) = c36 * ∫ t, f2 t ∂ μ0 := h2
      _ = c36 * ((1 / (π * (u - 2)) : ℝ) : ℂ) := by rw [hI2]
  rw [hsplitInt, hG2, hG1, hG0]
  have h36term :
      c36 * ((1 / (π * (u - 2)) : ℝ) : ℂ) = (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) := by
    rw [hc36]
    -- Reduce to a real identity via `Complex.ofReal_mul`/`Complex.ofReal_div`.
    have hu2ne : (u - 2 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hu)
    calc
      (((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ((1 / (π * (u - 2)) : ℝ) : ℂ)) =
          (((36 / (π ^ (2 : ℕ)) : ℝ) * (1 / (π * (u - 2)) : ℝ)) : ℂ) := by
            simp [Complex.ofReal_mul]
      _ = ((36 / (π ^ (3 : ℕ) * (u - 2)) : ℝ) : ℂ) := by
            have hR :
                (36 / (π ^ (2 : ℕ)) : ℝ) * (1 / (π * (u - 2))) =
                  36 / (π ^ (3 : ℕ) * (u - 2)) := by
              field_simp [Real.pi_ne_zero, hu2ne]
            simpa [Complex.ofReal_mul] using congrArg (fun r : ℝ => (r : ℂ)) hR
      _ = (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) := by
            -- The denominator is real, so the complex division is the `ofReal` division.
            simp [Complex.ofReal_div]
  have h8640term :
      (-c8640) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) =
        - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) := by
    rw [hc8640]
    have hune : (u : ℝ) ≠ 0 := ne_of_gt hu0
    calc
      (-((8640 / π : ℝ) : ℂ)) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) =
          (-((8640 / π : ℝ) * (1 / (π * u) ^ (2 : ℕ) : ℝ)) : ℂ) := by
            -- Everything is real, so multiplication/negation is preserved by `Complex.ofReal`.
            simp [Complex.ofReal_mul]
      _ = ((-(8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ))) : ℝ) : ℂ) := by
            have hR :
                -(8640 / π : ℝ) * (1 / (π * u) ^ (2 : ℕ) : ℝ) =
                  -(8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) : ℝ) := by
              field_simp [Real.pi_ne_zero, hune]
            simpa [Complex.ofReal_mul, Complex.ofReal_neg] using congrArg (fun r : ℝ => (r : ℂ)) hR
      _ = - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) := by
            have hneg :
                ((-(8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ))) : ℝ) : ℂ) =
                  -((8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) : ℝ) : ℂ) := by
              simp
            have hdiv :
                ((8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) : ℝ) : ℂ) =
                  (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) := by
              simp [Complex.ofReal_div]
            calc
              ((-(8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ))) : ℝ) : ℂ) =
                  -((8640 / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) : ℝ) : ℂ) := hneg
              _ = -((8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ))) := by
                  simp [hdiv]
              _ = - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) := by
                  simp [neg_div]
  have h18144term :
      c18144 * ((1 / (π * u) : ℝ) : ℂ) = (18144 : ℂ) / (π ^ (3 : ℕ) * u) := by
    rw [hc18144]
    have hune : (u : ℝ) ≠ 0 := ne_of_gt hu0
    calc
      (((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ((1 / (π * u) : ℝ) : ℂ)) =
          (((18144 / (π ^ (2 : ℕ)) : ℝ) * (1 / (π * u) : ℝ)) : ℂ) := by
            simp [Complex.ofReal_mul]
      _ = ((18144 / (π ^ (3 : ℕ) * u) : ℝ) : ℂ) := by
            have hR :
                (18144 / (π ^ (2 : ℕ)) : ℝ) * (1 / (π * u)) =
                  18144 / (π ^ (3 : ℕ) * u) := by
              field_simp [Real.pi_ne_zero, hune]
            simpa [Complex.ofReal_mul] using congrArg (fun r : ℝ => (r : ℂ)) hR
      _ = (18144 : ℂ) / (π ^ (3 : ℕ) * u) := by
            simp [Complex.ofReal_div]
  rw [h36term, h8640term, h18144term]
  -- Put the subtraction into `+ (-·)` and normalize the negative quotient.
  rw [sub_eq_add_neg]
  rw [neg_div]
  abel

lemma assemble_another_integral {u : ℝ} {corr : ℝ → ℂ} {E : ℂ}
    (hLap' :
      a' u =
        (4 * (Complex.I : ℂ)) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t))
    (hLapInt_decomp :
      (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
        (∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ), corr t))
    (hCorr_eval : (∫ t in Set.Ioi (0 : ℝ), corr t) = E) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (E + ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  -- Rewrite the Laplace integral and commute the two summands in the bracket.
  simpa [hLapInt_decomp, hCorr_eval, add_assoc, add_left_comm, add_comm] using hLap'

lemma aRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              aAnotherIntegral u) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hu2 : u ≠ 2 := by linarith
  have hLap := aRadial_eq_laplace_phi0_main (u := u) hu
  -- Normalize the Laplace integral into `aLaplaceIntegrand`.
  have hLap' :
      a' u =
        (4 * (Complex.I : ℂ)) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    simpa [aLaplaceIntegrand, mul_assoc] using hLap
  -- Coefficients appearing in the subtracted terms.
  set c36 : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc36
  set c8640 : ℂ := ((8640 / π : ℝ) : ℂ) with hc8640
  set c18144 : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc18144
  let corr : ℝ → ℂ :=
    fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)
  -- Rewrite `aLaplaceIntegrand` as `aAnotherIntegrand` plus the explicit correction terms.
  have hpoint (t : ℝ) :
      aLaplaceIntegrand u t =
        aAnotherIntegrand u t +
          corr t := by
    -- Keep `Real.exp` as a real exponential (avoid rewriting it to `Complex.exp`).
    simp [-Complex.ofReal_exp, aLaplaceIntegrand, aAnotherIntegrand, c36, c8640, c18144,
      sub_eq_add_neg, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, corr]
    ring
  -- Integrability: start from the Laplace integrand, then add/subtract explicit integrable terms.
  have hLapInt :
      IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) :=
    aLaplaceIntegral_convergent (u := u) hu
  -- Complex evaluations and integrability for the explicit correction terms.
  have hIexp :
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ) :=
    integral_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have hItexp :
      (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) :=
    integral_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have hI2exp :
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ) :=
    integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hExpInt :
      IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have hTExpInt :
      IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu0
  have h2ExpInt :
      IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
        (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hCorrInt :
      IntegrableOn corr (Set.Ioi (0 : ℝ)) := by
    -- Expand into a sum of three integrable terms.
    have h36 :
        IntegrableOn (fun t : ℝ => (c36 * Real.exp (2 * π * t)) * Real.exp (-π * u * t))
          (Set.Ioi (0 : ℝ)) := by
      -- Constant multiples preserve integrability.
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2ExpInt.const_mul c36
    have h8640 :
        IntegrableOn (fun t : ℝ => (c8640 * t) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hTExpInt.const_mul c8640
    have h18144 :
        IntegrableOn (fun t : ℝ => c18144 * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hExpInt.const_mul c18144
    -- Combine them with `IntegrableOn.add/sub`, then rewrite back to the factored form.
    have hsum :
        IntegrableOn
            (fun t : ℝ =>
              (c36 * Real.exp (2 * π * t)) * Real.exp (-π * u * t) -
                (c8640 * t) * Real.exp (-π * u * t) +
                  c18144 * Real.exp (-π * u * t))
            (Set.Ioi (0 : ℝ)) :=
      (h36.sub h8640).add h18144
    refine hsum.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    dsimp [corr]
    ring_nf
  have hAnotherInt := aAnotherIntegrand_integrable_of_pos hu0
  -- Split the Laplace integral into the "another integral" plus explicit terms.
  have hLapInt_decomp :
      (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
        (∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) +
          (∫ t in Set.Ioi (0 : ℝ), corr t) := by
    -- Use `hpoint` and then `integral_add`.
    have hcongr :
        (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
          ∫ t in Set.Ioi (0 : ℝ),
            aAnotherIntegrand u t +
              corr t := by
      refine MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi ?_
      intro t ht
      exact hpoint t
    rw [hcongr]
    -- Use additivity of the integral on the restricted measure `volume.restrict (Ioi 0)`.
    have hIntA :
        Integrable (fun t : ℝ => aAnotherIntegrand u t)
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using hAnotherInt
    have hIntC :
        Integrable corr ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using hCorrInt
    -- Avoid `simp`/`simpa` here: rewriting set integrals to restricted-measure integrals can be
    -- expensive, so we `change` the goal to the restricted-measure form and apply `integral_add`.
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    change
        (∫ t, aAnotherIntegrand u t + corr t ∂ μ) =
          (∫ t, aAnotherIntegrand u t ∂ μ) +
            ∫ t, corr t ∂ μ
    exact MeasureTheory.integral_add (μ := μ) hIntA hIntC
  -- Evaluate the correction integral using the Laplace evaluation lemmas.
  have hCorr_eval :
      (∫ t in Set.Ioi (0 : ℝ), corr t) =
        (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) :=
    corrIntegral_eval (u := u) (hu0 := hu0) (hu := hu) (c36 := c36) (c8640 := c8640)
      (c18144 := c18144) (hc36 := hc36) (hc8640 := hc8640) (hc18144 := hc18144) (corr := corr)
      (hcorr := rfl) (hIexp := hIexp) (hItexp := hItexp) (hI2exp := hI2exp)
      (hExpInt := hExpInt) (hTExpInt := hTExpInt) (h2ExpInt := h2ExpInt)
  -- Put everything together (fresh lemma to avoid heartbeat timeouts).
  set E : ℂ :=
    (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
        (18144 : ℂ) / (π ^ (3 : ℕ) * u) with hE
  have hCorr_eval' : (∫ t in Set.Ioi (0 : ℝ), corr t) = E := by
    simpa [hE] using hCorr_eval
  have hgoal :
      a' u =
        (4 * (Complex.I : ℂ)) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (E + ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) :=
    assemble_another_integral (u := u) (corr := corr) (E := E) hLap' hLapInt_decomp hCorr_eval'
  -- Expand `E` and the definition `aAnotherIntegral`.
  simpa [aAnotherIntegral, hE, add_assoc] using hgoal

lemma aRadial_eq_another_integral_analytic_continuation {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  refine aRadial_eq_another_integral_analytic_continuation_of_gt2 (u := u) (hu := hu) (hu2 := hu2)
    (fun r hr => ?_)
  simpa [aAnotherIntegral] using aRadial_eq_another_integral_of_gt2 (u := r) hr

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
  -- Final wrapper: unfold `aAnotherIntegrand` and apply analytic-continuation lemma.
  simpa [aAnotherIntegrand] using aRadial_eq_another_integral_analytic_continuation (u := u) hu hu2

end MagicFunction.g.CohnElkies.IntegralReps

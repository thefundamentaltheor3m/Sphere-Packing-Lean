module
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Calculus lemmas for the `AnotherIntegral` files

This file provides a helper lemma about differentiability of parameter-dependent interval
integrals of the form `∫ t in (0 : ℝ)..1, base t * exp (u * k t)`.

## Main statement
* `differentiableAt_intervalIntegral_mul_exp`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Interval Topology

open MeasureTheory Real Complex Filter Set

open intervalIntegral

/--
Differentiability of a parameter-dependent interval integral with an exponential factor.

This is a convenient wrapper around dominated differentiation for
`u ↦ ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)`.
-/
public lemma differentiableAt_intervalIntegral_mul_exp
    {base k : ℝ → ℂ} (u0 : ℂ) (Cbase K : ℝ)
    (hbase : ContinuousOn base (Ι (0 : ℝ) 1))
    (hk : ContinuousOn k (Ι (0 : ℝ) 1))
    (hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase)
    (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ K) :
    DifferentiableAt ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
  have h1 : (1 : ℝ) ∈ Ι (0 : ℝ) 1 := by simp
  have hCbase : 0 ≤ Cbase := (norm_nonneg (base 1)).trans (hbase_bound 1 h1)
  have hK : 0 ≤ K := (norm_nonneg (k 1)).trans (hk_bound 1 h1)
  let F : ℂ → ℝ → ℂ := fun u t => base t * Complex.exp (u * k t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * (k t) * Complex.exp (u * k t)
  have hexp (u : ℂ) : ContinuousOn (fun t : ℝ => Complex.exp (u * k t)) (Ι (0 : ℝ) 1) := by
    fun_prop
  have hF_meas :
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) (volume.restrict (Ι (0 : ℝ) 1)) := by
    refine Filter.Eventually.of_forall (fun u => ?_)
    exact (hbase.mul (hexp u)).aestronglyMeasurable
      (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF'_meas :
      AEStronglyMeasurable (F' u0) (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hmeas :=
      (hbase.mul (hk.mul (hexp u0))).aestronglyMeasurable
        (μ := (volume : Measure ℝ)) measurableSet_uIoc
    simpa [F', mul_assoc] using hmeas
  have hF_int : IntervalIntegrable (F u0) volume (0 : ℝ) 1 := by
    refine (intervalIntegrable_iff).2 ?_
    have hs : (volume : Measure ℝ) (Ι (0 : ℝ) 1) < ⊤ := by simp
    have hmeas : AEStronglyMeasurable (F u0) (volume.restrict (Ι (0 : ℝ) 1)) :=
      (hF_meas.self_of_nhds)
    let B : ℝ := Cbase * Real.exp (‖u0‖ * K)
    refine MeasureTheory.IntegrableOn.of_bound hs hmeas B ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 <| .of_forall ?_
    intro t ht
    have hb : ‖base t‖ ≤ Cbase := hbase_bound t ht
    have hk' : ‖k t‖ ≤ K := hk_bound t ht
    refine norm_mul_le_of_le (hbase_bound t ht) ?_
    have h1 : ‖u0 * k t‖ ≤ ‖u0‖ * K := by
      calc
        ‖u0 * k t‖ ≤ ‖u0‖ * ‖k t‖ := by
          exact norm_mul_le u0 (k t)
        _ ≤ ‖u0‖ * K := by gcongr
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 h1)
  let E : ℝ := Real.exp ((‖u0‖ + 1) * K)
  let bound : ℝ → ℝ := fun _ => Cbase * (K * E)
  have bound_int : IntervalIntegrable bound volume (0 : ℝ) 1 := by
    simp [bound]
  have h_bound :
      ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
        ∀ u ∈ Metric.ball u0 (1 : ℝ), ‖F' u t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall (fun t ht u hu => ?_)
    have hb : ‖base t‖ ≤ Cbase := hbase_bound t ht
    have hk' : ‖k t‖ ≤ K := hk_bound t ht
    have hu' : ‖u‖ ≤ ‖u0‖ + 1 := by
      have : ‖u - u0‖ < (1 : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hu
      have hle : ‖u - u0‖ ≤ (1 : ℝ) := le_of_lt this
      have : ‖u‖ ≤ ‖u0‖ + ‖u - u0‖ := by
        simpa [sub_eq_add_neg, add_assoc] using (norm_add_le u0 (u - u0))
      exact this.trans (by nlinarith)
    have hexp_le : ‖Complex.exp (u * k t)‖ ≤ E := by
      have h1 : ‖u * k t‖ ≤ (‖u0‖ + 1) * K := norm_mul_le_of_le hu' (hk_bound t ht)
      exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 h1)
    have : ‖F' u t‖ ≤ bound t := by
      have hstep1 :
          ‖F' u t‖ ≤ ‖base t‖ * (‖k t‖ * E) := by
        calc
          ‖F' u t‖ = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by
            simp [F', mul_left_comm, mul_comm]
          _ ≤ ‖base t‖ * (‖k t‖ * E) := by
            have hinner :
                ‖k t‖ * ‖Complex.exp (u * k t)‖ ≤ ‖k t‖ * E :=
              mul_le_mul_of_nonneg_left hexp_le (norm_nonneg (k t))
            exact mul_le_mul_of_nonneg_left hinner (norm_nonneg (base t))
      have hstep2 :
          ‖base t‖ * (‖k t‖ * E) ≤ Cbase * (K * E) := by
        have hk'' : ‖k t‖ * E ≤ K * E :=
          mul_le_mul_of_nonneg_right hk' (Real.exp_nonneg _)
        have hbase' :
            ‖base t‖ * (‖k t‖ * E) ≤ Cbase * (‖k t‖ * E) :=
          mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
        exact (hbase'.trans (mul_le_mul_of_nonneg_left hk'' hCbase))
      simpa [bound, E, mul_assoc] using (hstep1.trans hstep2)
    exact this
  have h_diff :
      ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
        ∀ u ∈ Metric.ball u0 (1 : ℝ), HasDerivAt (fun u : ℂ => F u t) (F' u t) u := by
    refine Filter.Eventually.of_forall (fun t _ u _ => ?_)
    have hmul : HasDerivAt (fun u : ℂ => u * k t) (k t) u :=
      (hasDerivAt_mul_const (k t) (x := u))
    have hexp :
        HasDerivAt (fun u : ℂ => Complex.exp (u * k t)) (Complex.exp (u * k t) * k t) u :=
      HasDerivAt.comp u (Complex.hasDerivAt_exp (u * k t)) hmul
    simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using hexp.const_mul (base t)
  have h :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
      (F := F) (F' := F') (x₀ := u0) (s := Metric.ball u0 (1 : ℝ)) (bound := bound)
      (Metric.ball_mem_nhds u0 (by norm_num)) (hF_meas := hF_meas) (hF_int := hF_int)
      (hF'_meas := hF'_meas)
      (h_bound := h_bound) (bound_integrable := bound_int) (h_diff := h_diff)
  exact h.2.differentiableAt

end MagicFunction.g.CohnElkies.IntegralReps

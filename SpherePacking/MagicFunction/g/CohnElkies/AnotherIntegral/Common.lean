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
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) (volume.restrict (Ι (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall fun u =>
      (hbase.mul (hexp u)).aestronglyMeasurable
        (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF'_meas :
      AEStronglyMeasurable (F' u0) (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa [F', mul_assoc] using (hbase.mul (hk.mul (hexp u0))).aestronglyMeasurable
      (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF_int : IntervalIntegrable (F u0) volume (0 : ℝ) 1 := by
    refine intervalIntegrable_iff.2 ?_
    refine MeasureTheory.IntegrableOn.of_bound (by simp : (volume : Measure ℝ) (Ι (0 : ℝ) 1) < ⊤)
      hF_meas.self_of_nhds (Cbase * Real.exp (‖u0‖ * K)) <|
      (ae_restrict_iff' measurableSet_uIoc).2 <| .of_forall fun t ht => ?_
    refine norm_mul_le_of_le (hbase_bound t ht) ?_
    have h1 : ‖u0 * k t‖ ≤ ‖u0‖ * K :=
      (norm_mul_le u0 (k t)).trans (by gcongr; exact hk_bound t ht)
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
      have hle : ‖u - u0‖ ≤ (1 : ℝ) :=
        (by simpa [Metric.mem_ball, dist_eq_norm] using hu : ‖u - u0‖ < 1).le
      have h2 : ‖u‖ ≤ ‖u0‖ + ‖u - u0‖ := by
        simpa [sub_eq_add_neg, add_assoc] using norm_add_le u0 (u - u0)
      linarith
    have hexp_le : ‖Complex.exp (u * k t)‖ ≤ E :=
      (Complex.norm_exp_le_exp_norm _).trans
        (Real.exp_le_exp.2 (norm_mul_le_of_le hu' (hk_bound t ht)))
    have hstep1 : ‖F' u t‖ ≤ ‖base t‖ * (‖k t‖ * E) := by
      calc
        ‖F' u t‖ = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by
          simp [F', mul_left_comm, mul_comm]
        _ ≤ ‖base t‖ * (‖k t‖ * E) := by
          gcongr
    have hstep2 : ‖base t‖ * (‖k t‖ * E) ≤ Cbase * (K * E) := by gcongr
    simpa [bound, E, mul_assoc] using hstep1.trans hstep2
  have h_diff :
      ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
        ∀ u ∈ Metric.ball u0 (1 : ℝ), HasDerivAt (fun u : ℂ => F u t) (F' u t) u :=
    Filter.Eventually.of_forall fun t _ u _ => by
      simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
        ((Complex.hasDerivAt_exp (u * k t)).comp u
          (hasDerivAt_mul_const (k t) (x := u))).const_mul (base t)
  have h :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
      (F := F) (F' := F') (x₀ := u0) (s := Metric.ball u0 (1 : ℝ)) (bound := bound)
      (Metric.ball_mem_nhds u0 (by norm_num)) (hF_meas := hF_meas) (hF_int := hF_int)
      (hF'_meas := hF'_meas)
      (h_bound := h_bound) (bound_integrable := bound_int) (h_diff := h_diff)
  exact h.2.differentiableAt

end MagicFunction.g.CohnElkies.IntegralReps

module

public import SpherePacking.MagicFunction.PsiTPrimeZ1
public import SpherePacking.Contour.Segments
public import SpherePacking.Integration.Measure
import SpherePacking.Integration.EndpointIntegrability

/-!
# Integrability on `Ioc (0,1)` for the `z₁line` modular bound

This file packages the standard endpoint-integrability argument on `μIoc01` for functions of the
form
`t ↦ ‖ψT' (z₁line t)‖ * (1 / t) ^ (k + 2)`,
using an assumed modular-form bound
`‖ψT' (z₁line t)‖ ≤ Cψ * exp(-π / t) * t ^ k` on `t ∈ Ioc (0,1)`.

## Main statements
* `MagicFunction.integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two`
-/

namespace MagicFunction

open scoped Interval Topology
open MeasureTheory Set Complex Real Filter
open SpherePacking.Integration (μIoc01)

noncomputable section

/-- Integrability on `μIoc01` of `t ↦ ‖ψT' (z₁line t)‖ * (1 / t)^(k+2)`, given the standard modular
bound by `exp(-π/t) * t^k`. -/
public lemma integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
    (ψT' : ℂ → ℂ) (k : ℕ) (Cψ : ℝ)
    (hcont : ContinuousOn (fun t : ℝ => ψT' (SpherePacking.Contour.z₁line t)) (Ioc (0 : ℝ) 1))
    (hbound :
      ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
        ‖ψT' (SpherePacking.Contour.z₁line t)‖ ≤ (Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) :
    Integrable
      (fun t : ℝ => ‖ψT' (SpherePacking.Contour.z₁line t)‖ * (1 / t) ^ (k + 2)) μIoc01 := by
  let g : ℝ → ℝ := fun t => ‖ψT' (SpherePacking.Contour.z₁line t)‖ * (1 / t) ^ (k + 2)
  have hmajor0 :
      IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-Real.pi / t)) (Ioc (0 : ℝ) 1) volume := by
    simpa using
      (SpherePacking.Integration.integrableOn_one_div_sq_mul_exp_neg_div
        (c := Real.pi) (by simpa using Real.pi_pos))
  have hmajor :
      Integrable (fun t : ℝ ↦ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t))) μIoc01 := by
    have h0' :
        Integrable (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-Real.pi / t))
          ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) := by
      simpa [MeasureTheory.IntegrableOn] using hmajor0
    simpa [μIoc01, mul_assoc, mul_left_comm, mul_comm] using h0'.const_mul Cψ
  have hmeas_g : AEStronglyMeasurable g μIoc01 := by
    have hcont_inv :
        ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) (Ioc (0 : ℝ) 1) :=
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono (by
        intro t ht
        simp [ne_of_gt ht.1])
    have hcont_one_div : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioc (0 : ℝ) 1) := by
      simpa [one_div] using hcont_inv
    have hcont_pow : ContinuousOn (fun t : ℝ => (1 / t : ℝ) ^ (k + 2)) (Ioc (0 : ℝ) 1) :=
      hcont_one_div.pow (k + 2)
    have hcont_norm :
        ContinuousOn (fun t : ℝ => ‖ψT' (SpherePacking.Contour.z₁line t)‖) (Ioc (0 : ℝ) 1) :=
      hcont.norm
    have hcont_g : ContinuousOn g (Ioc (0 : ℝ) 1) := by
      simpa [g] using hcont_norm.mul hcont_pow
    simpa [μIoc01] using
      (hcont_g.aestronglyMeasurable
        (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc)
  have hg_bound :
      ∀ᵐ t : ℝ ∂μIoc01, ‖g t‖ ≤ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht0' : 0 ≤ t := ht0.le
    have ht_ne0 : t ≠ 0 := ht0.ne'
    have hdiv0 : 0 ≤ (1 / t : ℝ) := one_div_nonneg.2 ht0'
    have hpow_nonneg : 0 ≤ (1 / t : ℝ) ^ (k + 2) := pow_nonneg hdiv0 (k + 2)
    have hgt0 : 0 ≤ g t := mul_nonneg (norm_nonneg _) hpow_nonneg
    have hnorm_g : ‖g t‖ = g t := by
      simp [Real.norm_eq_abs, abs_of_nonneg hgt0]
    have hpow_simp : (t ^ k) * (1 / t) ^ (k + 2) = 1 / t ^ (2 : ℕ) := by
      calc
        (t ^ k) * (1 / t) ^ (k + 2) =
            (t ^ k) * ((1 / t) ^ k * (1 / t) ^ (2 : ℕ)) := by
              simp [pow_add]
        _ = (t ^ k * (1 / t) ^ k) * (1 / t) ^ (2 : ℕ) := by
              ac_rfl
        _ = ((t * (1 / t)) ^ k) * (1 / t) ^ (2 : ℕ) := by
              simp [mul_pow, mul_assoc]
        _ = (1 / t) ^ (2 : ℕ) := by
              simp [one_div, ht_ne0]
        _ = 1 / t ^ (2 : ℕ) := by
              simp
    have : g t ≤ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
      have hmul := mul_le_mul_of_nonneg_right (hbound t ht) hpow_nonneg
      have hR :
          ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2) =
            (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
        calc
          ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2) =
              (Cψ : ℝ) * (rexp (-Real.pi / t) * (t ^ k * (1 / t) ^ (k + 2))) := by
                ac_rfl
          _ = (Cψ : ℝ) * (rexp (-Real.pi / t) * (1 / t ^ (2 : ℕ))) := by
                simpa [mul_assoc] using
                  congrArg (fun u : ℝ => (Cψ : ℝ) * (rexp (-Real.pi / t) * u)) hpow_simp
          _ = (Cψ : ℝ) * ((1 / t ^ (2 : ℕ)) * rexp (-Real.pi / t)) := by
                ac_rfl
      have hmul' :
          g t ≤ ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2) := by
        simpa [g, mul_assoc, mul_left_comm, mul_comm] using hmul
      exact hmul'.trans (le_of_eq hR)
    simpa [hnorm_g] using this
  exact Integrable.mono' hmajor hmeas_g hg_bound

end

end MagicFunction

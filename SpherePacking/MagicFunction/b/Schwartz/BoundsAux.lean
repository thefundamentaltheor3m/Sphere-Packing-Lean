module

public import SpherePacking.Integration.DifferentiationUnderIntegral

/-!
# Auxiliary inequalities for smooth integrals

This module isolates a recurring bound for the dominated-differentiation integrands
`SpherePacking.Integration.DifferentiationUnderIntegral.gN`.
-/

namespace MagicFunction.b.Schwartz

open scoped Interval

open Complex Real
open SpherePacking.Integration.DifferentiationUnderIntegral

/-- Compute `‖exp (x * coeff t)‖` from the real part of `coeff t`. -/
public lemma norm_cexp_ofReal_mul_coeff_of_coeff_re {coeff : ℝ → ℂ} {x t : ℝ}
    (hcoeff_re : (coeff t).re = -Real.pi * t) :
    ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
  have hre : ((x : ℂ) * coeff t).re = -Real.pi * x * t := by
    calc
      ((x : ℂ) * coeff t).re = x * (coeff t).re := by
        simp [Complex.mul_re]
      _ = x * (-Real.pi * t) := by simp [hcoeff_re]
      _ = (x * (-Real.pi)) * t := by simp [mul_assoc]
      _ = (-Real.pi * x) * t := by simp [mul_left_comm, mul_comm]
      _ = -Real.pi * x * t := by simp [mul_assoc]
  calc
    ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (((x : ℂ) * coeff t).re) := by
      simpa using (Complex.norm_exp ((x : ℂ) * coeff t))
    _ = Real.exp (-Real.pi * x * t) := by simp [hre]

/-- Bound the norm of an integral by bounding the integrand almost everywhere. -/
public lemma norm_integral_le_integral_bound_mul_const {μ : MeasureTheory.Measure ℝ}
    {f : ℝ → ℂ} {bound : ℝ → ℝ} {E : ℝ}
    (hbound_int : MeasureTheory.Integrable bound μ)
    (h_ae : ∀ᵐ t ∂μ, ‖f t‖ ≤ bound t * E) :
    ‖∫ t, f t ∂μ‖ ≤ (∫ t, bound t ∂μ) * E := by
  have hnorm : ‖∫ t, f t ∂μ‖ ≤ ∫ t, ‖f t‖ ∂μ :=
    MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := f)
  have hle :
      (∫ t, ‖f t‖ ∂μ) ≤ ∫ t, bound t * E ∂μ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun t => norm_nonneg (f t)) (hbound_int.mul_const E) h_ae
  have hconst : (∫ t, bound t * E ∂μ) = (∫ t, bound t ∂μ) * E := by
    simpa using (MeasureTheory.integral_mul_const (μ := μ) (r := E) (f := bound))
  exact hnorm.trans (hle.trans_eq hconst)

/-- A pointwise bound for `gN` used in dominated differentiation arguments. -/
public lemma norm_gN_le_bound_mul_exp {coeff : ℝ → ℂ} {ψ : ℂ → ℂ} {z : ℝ → ℂ}
    {n : ℕ} {Cψ x t : ℝ} (hCψ0 : 0 ≤ Cψ)
    (hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n)
    (hψ : ‖ψ (z t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ))
    (hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t)) :
    ‖gN (coeff := coeff) (hf := fun s ↦ (Complex.I : ℂ) * ψ (z s)) n x t‖ ≤
      (((2 * Real.pi) ^ n) * Cψ * t ^ (2 : ℕ)) *
        (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)) := by
  have hexp0 : 0 ≤ Real.exp (-Real.pi * x * t) := by positivity
  have hψ' :
      ‖ψ (z t)‖ * Real.exp (-Real.pi * x * t) ≤
        (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) * Real.exp (-Real.pi * x * t) :=
    mul_le_mul_of_nonneg_right hψ hexp0
  have hfactor0 :
      0 ≤ (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) * Real.exp (-Real.pi * x * t) := by
    have : 0 ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ) := by positivity
    exact mul_nonneg this hexp0
  have hnorm :
      ‖gN (coeff := coeff) (hf := fun s ↦ (Complex.I : ℂ) * ψ (z s)) n x t‖ =
        ‖coeff t‖ ^ n * ‖ψ (z t)‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by
    simp [gN, g, mul_assoc, norm_pow]
  calc
    ‖gN (coeff := coeff) (hf := fun s ↦ (Complex.I : ℂ) * ψ (z s)) n x t‖ =
        ‖coeff t‖ ^ n * ‖ψ (z t)‖ * ‖cexp ((x : ℂ) * coeff t)‖ := hnorm
    _ = ‖coeff t‖ ^ n * (‖ψ (z t)‖ * Real.exp (-Real.pi * x * t)) := by
          simp [hcexp, mul_assoc]
    _ ≤ ‖coeff t‖ ^ n * ((Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) *
          Real.exp (-Real.pi * x * t)) := by
          have := mul_le_mul_of_nonneg_left hψ' (by positivity : 0 ≤ ‖coeff t‖ ^ n)
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ ≤ (2 * Real.pi) ^ n * ((Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) *
          Real.exp (-Real.pi * x * t)) := by
          exact mul_le_mul_of_nonneg_right hcoeff hfactor0
    _ = (((2 * Real.pi) ^ n) * Cψ * t ^ (2 : ℕ)) *
          (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

end MagicFunction.b.Schwartz

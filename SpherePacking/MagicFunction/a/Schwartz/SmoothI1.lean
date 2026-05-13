module
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealIntegrands
public import SpherePacking.MagicFunction.a.Schwartz.SmoothI24Common
public import SpherePacking.Integration.UpperHalfPlaneComp

import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness of `RealIntegrals.I₁'`

Proves `ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₁'` via differentiation under the integral, delegating
to `MagicFunction.a.Schwartz.SmoothI24Common` and supplying the `I₁'`-specific parametrisation.
-/

namespace MagicFunction.a.Schwartz.I1Smooth

noncomputable section

open scoped Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands
open MagicFunction.a.Schwartz.SmoothI24Common
open SpherePacking.Integration SpherePacking.ForMathlib

private lemma arg_z₁'_eq_I_div (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    arg z₁' (1 : ℂ) t = I / t := by
  have htne : (t : ℂ) ≠ 0 := mod_cast ht.1.ne'
  change (-1 : ℂ) / (z₁' t + 1) = I / t
  rw [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)]
  field_simp; ring_nf; simp [Complex.I_sq]

/-- Smoothness of `RealIntegrals.I₁'` as a function `ℝ → ℂ`. -/
public theorem I₁'_contDiff : ContDiff ℝ (⊤ : ℕ∞) I₁' :=
  contDiff_of_eq_integral_g_Ioo (z := z₁') (shift := (1 : ℂ)) (prefactor := I)
    (f := I₁') (fun x => by
      simp [RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁_def,
        DifferentiationUnderIntegral.g, Φ₁', coeff, hf, SmoothI24Common.arg,
        intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
        mul_assoc, mul_left_comm, mul_comm])
    continuous_z₁' norm_z₁'_le_two (by norm_num)
    (fun t ht h0 => by
      have h1 := congrArg Complex.im h0
      simp [z₁'_eq_of_mem (mem_Icc_of_Ioo ht)] at h1; exact ht.1.ne' h1)
    (fun t ht => by simpa [arg_z₁'_eq_I_div (t := t) ht] using one_div_pos.2 ht.1)
    (fun t ht => by linarith [(one_lt_one_div ht.1) ht.2,
      show (arg z₁' (1 : ℂ) t).im = 1 / t from by simp [arg_z₁'_eq_I_div (t := t) ht]])

end

end MagicFunction.a.Schwartz.I1Smooth

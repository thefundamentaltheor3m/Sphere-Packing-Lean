module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.PsiTPrimeZ1
import Mathlib.Topology.Order.ProjIcc
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ6.Bounds
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.MagicFunction.b.Schwartz.BoundsAux


/-!
# Smoothness and decay for `J₁'`

This file proves `ContDiff` and Schwartz-type decay bounds for the primed radial integral `J₁'`
by differentiating under the integral sign on `Ioo (0,1)` and using a modular rewrite to control
`ψT' (z₁' t)` near `t = 0`.

## Main statements
* `ψT'_z₁'_eq`
* `contDiff_J₁'`
* `decay_J₁'`
-/


namespace MagicFunction.b.Schwartz.J1Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm

open Complex Real Set MeasureTheory Filter intervalIntegral UpperHalfPlane

open MagicFunction.Parametrisations
open MagicFunction.b.RealIntegrals
open MagicFunction.b.PsiBounds
open Matrix ModularGroup
open ModularForm

def μ : Measure ℝ := SpherePacking.Integration.μIoo01

attribute [irreducible] μ

instance : IsFiniteMeasure μ := by
  refine ⟨by simp [μ, SpherePacking.Integration.μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩

def coeff (t : ℝ) : ℂ := ((π : ℂ) * (Complex.I : ℂ)) * z₁' t

def hf (t : ℝ) : ℂ := (Complex.I : ℂ) * ψT' (z₁' t)

def g (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.g (coeff := coeff) (hf := hf) x t

def gN (n : ℕ) (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.gN (coeff := coeff) (hf := hf) n x t

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using
    SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₁' t) (hz := norm_z₁'_le_two t)

/-- Modular rewrite for `ψT' (z₁' t)`, used to control the integrand near `t = 0`. -/
public lemma ψT'_z₁'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  have ht0 : 0 < t := ht.1
  have hz_im : 0 < (z₁' t).im := im_z₁'_pos (t := t) ht
  let z : ℍ := ⟨z₁' t, hz_im⟩
  have hψT : ψT z = ψS ((S * T) • z) * (z + 1 : ℂ) ^ (2 : ℕ) := by
    have h1 : (ψS ∣[(-2 : ℤ)] (S * T)) z = ψT z := by
      simpa using congrArg (fun f : ℍ → ℂ => f z) ψS_slash_ST
    simpa using h1.symm.trans (by simpa using (slashST' (z := z) (F := ψS)))
  have hzplus : (z + 1 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, add_left_comm, add_comm] using
      congrArg (fun w : ℂ => w + (1 : ℂ)) (z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht))
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hsmul : (S * T) • z = (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    calc
      (↑((S * T) • z) : ℂ) = (-1 : ℂ) / ((z : ℂ) + 1) := coe_ST_smul (z := z)
      _ = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [hzplus]
      _ = (Complex.I : ℂ) * (1 / t) := by field_simp [htne, Complex.I_ne_zero]; simp
  have hψT' : ψT' (z₁' t) = ψT z := by simp [ψT', hz_im, z]
  have hψS' : ψS ((S * T) • z) = ψS.resToImagAxis (1 / t) := by
    rw [hsmul]; simp [Function.resToImagAxis, ResToImagAxis, ht0]
  -- Avoid `simp` unfolding the `SL(2,ℤ)` action on `ℍ` to a `GL(2,ℝ)` action.
  rw [hψT']
  rw [hψS'] at hψT
  simpa [hzplus] using hψT


lemma J₁'_eq_integral_g_Ioo (x : ℝ) : J₁' x = ∫ t in Ioo (0 : ℝ) 1, g x t := by
  simp [RealIntegrals.J₁', g, hf, coeff, SpherePacking.Integration.DifferentiationUnderIntegral.g,
    mul_assoc, mul_left_comm, mul_comm,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo]

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using continuous_const.mul continuous_z₁'

lemma continuousOn_hf :
    ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  simpa [hf] using
    (continuousOn_const.mul <| by
      simpa using
        MagicFunction.continuousOn_ψT'_z₁'_of (k := 2) (ψS := ψS) (ψT' := ψT')
          (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) continuous_ψS)
          ψT'_z₁'_eq)

lemma exists_bound_norm_hf :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M := by
  rcases MagicFunction.exists_bound_norm_ψT'_z₁'_of (k := 2) (ψS := ψS) (ψT' := ψT')
    exists_bound_norm_ψS_resToImagAxis_Ici_one ψT'_z₁'_eq with ⟨Mψ, hMψ⟩
  exact ⟨Mψ, fun t ht => by simpa [hf] using hMψ t ht⟩

def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μ

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, μ, SpherePacking.Integration.μIoo01, gN] using
    SpherePacking.Integration.DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo
      (coeff := coeff) (hf := hf)
      continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le n x₀

private lemma I_zero_eq_J₁' : (fun x : ℝ => I 0 x) = J₁' := by
  funext x
  simpa [I, μ, SpherePacking.Integration.μIoo01, gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN] using
    (J₁'_eq_integral_g_Ioo x).symm

lemma iteratedDeriv_J₁'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n J₁' = fun x : ℝ ↦ I n x := by
  simpa [I_zero_eq_J₁'] using
    (SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
      (I := I) (hI := fun n x => hasDerivAt_integral_gN (n := n) (x₀ := x)) n)

/-- Smoothness of `J₁'` (the primed radial profile).

The prime in `contDiff_J₁'` refers to the function `J₁'`. -/
public theorem contDiff_J₁' : ContDiff ℝ (⊤ : ℕ∞) J₁' := by
  simpa [I_zero_eq_J₁'] using
    (SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I)
      (fun n x => by simpa using hasDerivAt_integral_gN (n := n) (x₀ := x)))

/-- Schwartz-type decay bounds for `J₁'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₁'` refers to the function `J₁'`. -/
public theorem decay_J₁' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt k (b := 2*π) (by positivity)
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  have hCψ0 : 0 ≤ Cψ :=
    SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity)
      (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ 2
  have hA : 0 ≤ ((2 * Real.pi) ^ n) * Cψ := by positivity [hCψ0]
  have hbound_int : Integrable bound μ := by
    simpa [bound, μ, SpherePacking.Integration.μIoo01, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.Integration.integrable_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 2 hA)
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    simpa [Kn, bound, μ, SpherePacking.Integration.μIoo01, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.Integration.integral_nonneg_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 2 hA)
  refine ⟨Kn * B, fun x hx => ?_⟩
  have hIn : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
        simpa [μ] using SpherePacking.Integration.ae_mem_Ioo01_muIoo01] with t ht
      have hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
      have hψT : ‖ψT' (z₁' t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ 2 := by
        simpa using
          (MagicFunction.norm_modular_rewrite_Ioc_exp_bound
            (k := 2) (Cψ := Cψ) (ψS := ψS) (ψZ := ψT') (z := z₁')
            (hCψ := hCψ) (hEq := ψT'_z₁'_eq) (t := t) ⟨ht.1, le_of_lt ht.2⟩)
      have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        simpa using norm_cexp_ofReal_mul_coeff_of_coeff_re (coeff := coeff) (x := x) (t := t)
          (show (coeff t).re = -Real.pi * t by
            simp [coeff, Complex.mul_re, show (z₁' t).im = t from by
              simp [show z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) from by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht)], mul_assoc])
      exact le_mul_of_le_mul_of_nonneg_left
        (by simpa [gN, hf, bound, mul_assoc, mul_left_comm, mul_comm] using
            MagicFunction.b.Schwartz.norm_gN_le_bound_mul_exp (coeff := coeff) (ψ := ψT')
              (z := z₁') (n := n) (Cψ := Cψ) (x := x) (t := t) hCψ0 hcoeff hψT hcexp :
          ‖gN n x t‖ ≤ bound t * (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)))
        (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx ht.1 :
          Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x))
        (by positivity [hCψ0])
    simpa [I, Kn] using
      (norm_integral_le_integral_bound_mul_const (μ := μ) (f := gN n x) (bound := bound)
        (E := Real.exp (-2 * Real.pi * Real.sqrt x)) (hbound_int := hbound_int) hbound_ae)
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖
        = x ^ k * ‖I n x‖ := by
          simp [Real.norm_eq_abs, abs_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
            congrArg (fun F : ℝ → ℂ => F x) (iteratedDeriv_J₁'_eq_integral_gN (n := n))]
    _ ≤ x ^ k * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x)) := by gcongr
    _ = Kn * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring_nf
    _ ≤ Kn * B := mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hB x hx) hKn_nonneg

end

end MagicFunction.b.Schwartz.J1Smooth

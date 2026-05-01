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
import Mathlib.Analysis.Calculus.Deriv.Mul
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.Integration.Measure
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.MagicFunction.PsiTPrimeZ1
import Mathlib.Topology.Order.ProjIcc
import SpherePacking.MagicFunction.b.Schwartz.BoundsAux

/-!
# Smooth J5

This file defines `coeff`, `g`, `gN`, ... and proves smoothness/decay bounds for
`RealIntegrals.J₅'` by differentiating under the integral sign.

## Main statements
* `ψI'_z₅'_eq`
* `contDiff_J₅'`
* `decay_J₅'`
-/


namespace MagicFunction.b.Schwartz.J5Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm

open Complex Real Set MeasureTheory Filter intervalIntegral UpperHalfPlane SpherePacking.ForMathlib

open MagicFunction.Parametrisations
open MagicFunction.b.RealIntegrals
open MagicFunction.b.PsiBounds
open MagicFunction.b.PsiBounds.PsiExpBounds
open SpherePacking.Integration
open Matrix ModularGroup
open ModularForm

def μ : Measure ℝ := μIoo01

attribute [irreducible] μ

instance : IsFiniteMeasure μ :=
  ⟨by simp [μ, μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩

def coeff (t : ℝ) : ℂ := ((π : ℂ) * (Complex.I : ℂ)) * z₅' t

def hf (t : ℝ) : ℂ := (Complex.I : ℂ) * ψI' (z₅' t)

def gN (n : ℕ) (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.gN (coeff := coeff) (hf := hf) n x t

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using
    norm_mul_pi_I_le_two_pi (z := z₅' t) (hz := (norm_z₅'_le_one t).trans (by norm_num))

lemma continuousOn_ψI'_z₅' : ContinuousOn (fun t : ℝ => ψI' (z₅' t)) (Ioo (0 : ℝ) 1) := by
  refine (continuousOn_iff_continuous_restrict).2 ?_
  have him : ∀ t : Ioo (0 : ℝ) 1, 0 < (z₅' (t : ℝ)).im := fun t =>
    im_z₅'_pos (t := (t : ℝ)) ⟨t.2.1, le_of_lt t.2.2⟩
  simpa [Set.restrict] using
    (continuous_comp_upperHalfPlane_mk
      (ψT := ψI) (ψT' := ψI') (MagicFunction.b.PsiBounds.continuous_ψI)
      (z := fun t : Ioo (0 : ℝ) 1 => z₅' (t : ℝ))
      (continuous_z₅'.comp continuous_subtype_val) him (fun t => by simp [ψI', him t]))

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using continuous_const.mul continuous_z₅'

lemma continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  simpa [hf] using continuousOn_const.mul continuousOn_ψI'_z₅'

/-- Modular rewrite for `ψI' (z₅' t)` in terms of `ψS.resToImagAxis (1 / t)`. -/
public lemma ψI'_z₅'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  have ht0 : 0 < t := ht.1
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      z₅'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht)
  have hz_im : 0 < (z₅' t).im := by simpa [hz5] using ht0
  let z : ℍ := ⟨z₅' t, hz_im⟩
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht0)
  have hsmul : S • z = (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    calc (↑(S • z) : ℂ) = (-1 : ℂ) / (z : ℂ) := by simpa using ModularGroup.coe_S_smul z
      _ = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [z, hz5]
      _ = (Complex.I : ℂ) * (1 / t) := by field_simp [htne, Complex.I_ne_zero]; simp
  have hψS' :
      ψS (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) S) • z) =
        ψS.resToImagAxis (1 / t) := by
    simp [Function.resToImagAxis, ResToImagAxis, ht0,
      show SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) S) • z =
        (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) by simpa using hsmul]
  have hzcoe : (z : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by simp [z, hz5]
  simpa [show ψI' (z₅' t) = ψI z from by simp [ψI', hz_im, z], hψS', hzcoe] using
    ((congrArg (fun f : ℍ → ℂ => f z) ψS_slash_S).symm.trans
      (by simpa using slashS' (z := z) (F := ψS)) :
      ψI z = ψS (S • z) * (z : ℂ) ^ (2 : ℕ))

lemma exists_bound_norm_ψI'_z₅' :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖ψI' (z₅' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_norm_ψS_resToImagAxis_Ici_one
  refine ⟨M, fun t ht => ?_⟩
  have ht0 : 0 < t := ht.1
  have htle : t ≤ 1 := le_of_lt ht.2
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M :=
    hM (1 / t) (by simpa using one_div_le_one_div_of_le ht0 htle)
  calc ‖ψI' (z₅' t)‖ ≤ M * t ^ 2 := by
        have hEq := ψI'_z₅'_eq (t := t) ⟨ht.1, htle⟩; simp_all
    _ ≤ M := by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ ht0.le htle)
        ((norm_nonneg _).trans hψS)

lemma exists_bound_norm_hf :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M :=
  let ⟨M, hM⟩ := exists_bound_norm_ψI'_z₅'
  ⟨M, fun t ht => by simpa [hf] using hM t ht⟩

def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μ

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, μ, μIoo01, gN] using
    DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo (coeff := coeff) (hf := hf)
      continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le n x₀

lemma J₅'_eq_integral_g_Ioo (x : ℝ) :
    J₅' x = (-2 : ℂ) * I 0 x := by
  simp [RealIntegrals.J₅', I, gN, hf, coeff, μ, μIoo01,
    DifferentiationUnderIntegral.gN, DifferentiationUnderIntegral.g,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₅'`.

The prime in `contDiff_J₅'` refers to the function `J₅'`. -/
public theorem contDiff_J₅' : ContDiff ℝ (⊤ : ℕ∞) J₅' := by
  have hmul : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (-2 : ℂ) * I 0 x) :=
    contDiff_const.mul (contDiff_of_hasDerivAt_succ (I := I) (fun n x => by
      simpa using hasDerivAt_integral_gN (n := n) (x₀ := x)))
  -- `simp` normalizes `(-2) * f` to `-(2 * f)`, so match that normal form.
  simpa [show (fun x : ℝ ↦ -(2 * I 0 x)) = J₅' from
    funext fun x => by simpa [mul_assoc] using (J₅'_eq_integral_g_Ioo (x := x)).symm] using hmul

/-- Schwartz-type decay bounds for `J₅'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₅'` refers to the function `J₅'`. -/
public theorem decay_J₅' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    exists_bound_pow_mul_exp_neg_mul_sqrt (k := k) (b := 2 * Real.pi) (by positivity)
  obtain ⟨Cψ, hCψ⟩ := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hCψ0 : 0 ≤ Cψ :=
    SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity)
      (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ 2
  have hbound_int : Integrable bound μ := by
    simpa [bound, μ, SpherePacking.Integration.μIoo01, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.Integration.integrable_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 2 (by positivity [hCψ0]))
  let Kn : ℝ := ∫ t, bound t ∂μ
  refine ⟨2 * Kn * B, fun x hx => ?_⟩
  have hiterJ : iteratedDeriv n J₅' x = (-2 : ℂ) * I n x := by
    calc iteratedDeriv n J₅' x
        = iteratedDeriv n ((-2 : ℂ) • (fun y : ℝ => I 0 y)) x := by
          simp [show J₅' = (-2 : ℂ) • (fun y : ℝ => I 0 y) from funext fun y => by
            simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using J₅'_eq_integral_g_Ioo (x := y)]
      _ = (-2 : ℂ) • iteratedDeriv n (fun y : ℝ => I 0 y) x := by simp
      _ = (-2 : ℂ) * I n x := by
          simp [SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ (I := I)
            (fun m y => by simpa using hasDerivAt_integral_gN (n := m) (x₀ := y)) n, smul_eq_mul]
  have hIn : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
        simpa [μ] using SpherePacking.Integration.ae_mem_Ioo01_muIoo01] with t ht
      have hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
      have hψI : ‖ψI' (z₅' t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ 2 := by
        simpa [one_div] using
          (MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS)
            (ψZ := ψI') (z := z₅') (hCψ := hCψ)
            (hEq := fun s hs => ψI'_z₅'_eq (t := s) hs) (t := t) ⟨ht.1, le_of_lt ht.2⟩)
      have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        simpa using norm_cexp_ofReal_mul_coeff_of_coeff_re (coeff := coeff) (x := x) (t := t)
          (show (coeff t).re = -Real.pi * t by
            simp [coeff, Complex.mul_re, show (z₅' t).im = t from by
              simp [show z₅' t = (Complex.I : ℂ) * (t : ℂ) from by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  z₅'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht)], mul_assoc])
      exact le_mul_of_le_mul_of_nonneg_left
        (by simpa [gN, hf, bound, mul_assoc, mul_left_comm, mul_comm] using
            MagicFunction.b.Schwartz.norm_gN_le_bound_mul_exp (coeff := coeff) (ψ := ψI')
              (z := z₅') (n := n) (Cψ := Cψ) (x := x) (t := t) hCψ0 hcoeff hψI hcexp :
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
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖
        = x ^ k * ‖iteratedDeriv n J₅' x‖ := by
          simp [Real.norm_of_nonneg hx,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := J₅') (x := x)]
    _ ≤ x ^ k * (2 * ‖I n x‖) :=
      mul_le_mul_of_nonneg_left (le_of_eq (by simp [hiterJ])) (pow_nonneg hx k)
    _ ≤ x ^ k * (2 * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x))) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring_nf
    _ ≤ (2 * Kn) * B := by
      simpa using mul_le_mul_of_nonneg_left
        (by simpa [mul_assoc] using hB x hx :
          x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x) ≤ B)
        (by positivity : (0 : ℝ) ≤ 2 * Kn)

end

end MagicFunction.b.Schwartz.J5Smooth

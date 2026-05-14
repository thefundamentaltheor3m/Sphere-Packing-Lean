/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ1
import SpherePacking.Integration.Measure
import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# `b` is a Schwartz function

Builds Schwartz functions from the radial integrals `J₁', ..., J₆'` and assembles the
`(-1)`-Fourier eigenfunction `b`. On `ℝ`, radial profiles are only used at `r = ‖x‖^2 ≥ 0`; a
smooth cutoff yields global Schwartz functions on `ℝ` without changing induced functions on `ℝ⁸`.

Also packages the `SmoothJ24Common` skeleton used by `J₂'` and `J₄'`, and the derived
smoothness/decay statements for those two primed profiles.
-/

noncomputable section

namespace SpherePacking.Integration.SmoothIntegralCommon

open scoped Interval
open Complex Real Set MeasureTheory Filter intervalIntegral
open SpherePacking.Integration.DifferentiationUnderIntegral

variable {coeff hf : ℝ → ℂ}

/-- The basic family of interval integrals, with the `n`-th derivative integrand `gN n`. -/
@[expose] public def I (n : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t

/-- Smoothness of `x ↦ I 0 x` under the hypotheses needed for dominated differentiation. -/
public theorem contDiff_integral
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) := by
  simpa using
    SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I (coeff := coeff) (hf := hf))
      (fun n x => by
        simpa [I] using hasDerivAt_integral_gN_of_continuous (coeff := coeff) (hf := hf)
          continuous_hf continuous_coeff exists_bound_norm_h coeff_norm_le n x)

/-- One-sided decay for `I 0 x` from a uniform bound on `‖cexp ((x : ℂ) * coeff t)‖`. -/
private theorem decay_integral
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (norm_cexp : ∀ x t : ℝ, ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x)) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_h
  have hMh0 : 0 ≤ Mh := (norm_nonneg (hf 1)).trans (hMh 1 (by simp))
  refine ⟨(2 * Real.pi) ^ n * Mh * B, fun x hx => ?_⟩
  have hrepr := congrArg (fun f : ℝ → ℂ => f x) <|
    show iteratedDeriv n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) =
        fun x : ℝ ↦ I (coeff := coeff) (hf := hf) n x by
      simpa using
        SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
          (I := fun (n : ℕ) (x : ℝ) => I (coeff := coeff) (hf := hf) n x)
          (fun n x => by
            simpa [I] using hasDerivAt_integral_gN_of_continuous (coeff := coeff) (hf := hf)
              continuous_hf continuous_coeff ⟨Mh, hMh⟩ coeff_norm_le (n := n) (x₀ := x)) n
  have hnormI :
      ‖I (coeff := coeff) (hf := hf) n x‖ ≤
        (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x) := by
    rw [I]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (C := (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x))
      (f := fun t : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t) (fun t ht => ?_)).trans_eq (by simp)
    have hmul : ‖coeff t‖ ^ n * ‖hf t‖ ≤ (2 * Real.pi) ^ n * Mh :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n) (hMh t ht)
        (norm_nonneg _) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)
    calc ‖gN (coeff := coeff) (hf := hf) n x t‖
        = ‖coeff t‖ ^ n * ‖hf t‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by
          simp [gN, g, norm_pow, mul_left_comm, mul_comm, mul_assoc]
      _ ≤ (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x) := by
          simpa [mul_assoc, norm_cexp] using
            mul_le_mul_of_nonneg_right hmul (norm_nonneg (cexp ((x : ℂ) * coeff t)))
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖
      = x ^ k * ‖I (coeff := coeff) (hf := hf) n x‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hrepr]
    _ ≤ x ^ k * ((2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Real.pi) ^ n * Mh * (x ^ k * Real.exp (-Real.pi * x)) := by ring
    _ ≤ (2 * Real.pi) ^ n * Mh * B :=
        mul_le_mul_of_nonneg_left (hB x hx)
          (mul_nonneg (pow_nonneg (by positivity) n) hMh0)

/-- Specialize `decay_integral` when `Re (coeff t) = -π` for all `t`. -/
public theorem decay_integral_of_coeff_re
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (coeff_re : ∀ t : ℝ, (coeff t).re = (-Real.pi : ℝ)) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖ ≤ C := by
  simpa using
    decay_integral (coeff := coeff) (hf := hf)
      continuous_hf continuous_coeff exists_bound_norm_h coeff_norm_le
      (norm_cexp := fun x t => by
        simp [Complex.norm_exp, Complex.mul_re, coeff_re t, mul_comm])

end SpherePacking.Integration.SmoothIntegralCommon

namespace MagicFunction.b.Schwartz.SmoothJ24Common

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.b.PsiBounds SpherePacking.ForMathlib

/-- The coefficient function `t ↦ (π * I) * z t` used for smooth integral kernels. -/
@[expose] public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t : ℝ ↦ ((π : ℂ) * I) * z t

private lemma continuous_ψT'_comp {z : ℝ → ℂ} (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) :
    Continuous fun t : ℝ => ψT' (z t) := by
  refine SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
    (ψT := ψT) (ψT' := ψT') (MagicFunction.b.PsiBounds.continuous_ψT)
    (z := z) hz him (fun t => by simp [ψT', him t])

private lemma coeff_norm_le {z : ℝ → ℂ} (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (t : ℝ) :
    ‖coeff z t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using norm_mul_pi_I_le_two_pi (z := z t) (hz := hnorm t)
private lemma exists_bound_norm_hf_mul {z : ℝ → ℂ} (c : ℂ) (hz : Continuous z)
    (him : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖c * ψT' (z t)‖ ≤ M := by
  simpa using SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
    (f := fun t : ℝ => c * ψT' (z t)) (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))

/-- `ContDiff` for a function defined as `SmoothIntegralCommon.I` with `coeff t = (π * I) * z t`. -/
public theorem contDiff_of_eq_I0_mul {z : ℝ → ℂ} {c : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ,
        f x =
          SpherePacking.Integration.SmoothIntegralCommon.I
            (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) 0 x)
    (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  simpa [funext hfEq] using
    (SpherePacking.Integration.SmoothIntegralCommon.contDiff_integral
      (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t))
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))
      (by simpa [coeff] using (continuous_const.mul hz))
      (exists_bound_norm_hf_mul (z := z) (c := c) hz him) (coeff_norm_le (z := z) hnorm))

/-- Polynomial decay bounds for iterated derivatives of `f`, assuming `im (z t) = 1`. -/
public theorem decay_of_eq_I0_of_coeff_re_mul {z : ℝ → ℂ} {c : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ,
        f x =
          SpherePacking.Integration.SmoothIntegralCommon.I
            (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) 0 x)
    (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2)
    (him1 : ∀ t : ℝ, (z t).im = 1) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  simpa [funext hfEq] using
    (SpherePacking.Integration.SmoothIntegralCommon.decay_integral_of_coeff_re
      (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t))
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))
      (by simpa [coeff] using (continuous_const.mul hz))
      (exists_bound_norm_hf_mul (z := z) (c := c) hz him) (coeff_norm_le (z := z) hnorm)
      (coeff_re := fun t => by
        simp [coeff, Complex.mul_re, him1 t, mul_assoc]))

end MagicFunction.b.Schwartz.SmoothJ24Common

namespace MagicFunction.b.Schwartz.J2Smooth

open scoped Interval Manifold Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds SpherePacking.ForMathlib

private lemma hfEq_J₂' (x : ℝ) :
    J₂' x = SpherePacking.Integration.SmoothIntegralCommon.I
      (coeff := SmoothJ24Common.coeff z₂')
      (hf := fun t : ℝ ↦ (1 : ℂ) * ψT' (z₂' t)) 0 x := by
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₂'` (the primed radial profile used to define the Schwartz kernel `J₂`). -/
public theorem contDiff_J₂' : ContDiff ℝ (⊤ : ℕ∞) J₂' :=
  SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₂') (c := (1 : ℂ)) hfEq_J₂'
    continuous_z₂' (fun t => by simpa using im_z₂'_pos_all t) norm_z₂'_le_two

/-- Schwartz-type decay bounds for `J₂'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₂' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₂' x‖ ≤ C :=
  SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₂') (c := (1 : ℂ)) hfEq_J₂'
    continuous_z₂' (fun t => by simpa using im_z₂'_pos_all t) norm_z₂'_le_two im_z₂'_eq_one

end MagicFunction.b.Schwartz.J2Smooth

namespace MagicFunction.b.Schwartz.J4Smooth

open scoped Interval Manifold Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds SpherePacking.ForMathlib

private lemma hfEq_J₄' (x : ℝ) :
    J₄' x = SpherePacking.Integration.SmoothIntegralCommon.I
      (coeff := SmoothJ24Common.coeff z₄')
      (hf := fun t : ℝ ↦ (-1 : ℂ) * ψT' (z₄' t)) 0 x := by
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₄'` (the primed radial profile). -/
public theorem contDiff_J₄' : ContDiff ℝ (⊤ : ℕ∞) J₄' :=
  SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₄') (c := (-1 : ℂ)) hfEq_J₄'
    continuous_z₄' (fun t => by simpa using im_z₄'_pos_all t) norm_z₄'_le_two

/-- Schwartz-type decay bounds for `J₄'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₄' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C :=
  SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₄') (c := (-1 : ℂ)) hfEq_J₄'
    continuous_z₄' (fun t => by simpa using im_z₄'_pos_all t) norm_z₄'_le_two im_z₄'_eq_one

end MagicFunction.b.Schwartz.J4Smooth

namespace MagicFunction.b.Schwartz.J3Smooth

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm
open Complex Real Set intervalIntegral
open MagicFunction.Parametrisations MagicFunction.b.RealIntegrals
open Matrix ModularGroup ModularForm

/-- Compatibility of `ψT'` and `ψI'` along the parametrisations `z₃'`/`z₅'`. -/
public lemma ψT'_z₃'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₃' t) = ψI' (z₅' t) := by
  simpa using MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t) ht

lemma J₃'_eq (x : ℝ) :
    J₃' x = (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by
  have hJ3 :
      J₃' x =
        (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) *
          cexp (π * (Complex.I : ℂ) * x) := by
    calc
      J₃' x
          = ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψT' (z₃' t) * cexp (π * (Complex.I : ℂ) * x * (z₃' t)) := by
              simp [RealIntegrals.J₃']
      _ = ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t)) *
                cexp (π * (Complex.I : ℂ) * x) := by
              refine intervalIntegral.integral_congr fun t ht => ?_
              have htIcc : t ∈ Icc (0 : ℝ) 1 := by
                simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
              have hψ := ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
              have hcexp : cexp (π * (Complex.I : ℂ) * x * (z₃' t)) =
                  cexp (π * (Complex.I : ℂ) * x * (z₅' t)) *
                    cexp (π * (Complex.I : ℂ) * x) := by
                have hz : z₃' t = z₅' t + 1 := by
                  simp [z₃'_eq_of_mem htIcc, z₅'_eq_of_mem htIcc, add_comm]
                simp [hz, mul_add, mul_assoc, mul_left_comm, mul_comm, Complex.exp_add]
              grind only
      _ = (∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) *
            cexp (π * (Complex.I : ℂ) * x) := integral_mul_const _ _
  have hK :
      (∫ t in (0 : ℝ)..1,
          (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) =
        (-1 / 2 : ℂ) * J₅' x := by
    set K : ℂ :=
      ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))
    have hJ5 : J₅' x = (-2 : ℂ) * K := by simp [RealIntegrals.J₅', K]
    grind only
  calc
    J₃' x = ((-1 / 2 : ℂ) * J₅' x) * cexp (π * (Complex.I : ℂ) * x) := by simpa [hK] using hJ3
    _ = (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by ring_nf

/-- Smoothness of `J₃'`. -/
public theorem contDiff_J₃' : ContDiff ℝ (⊤ : ℕ∞) J₃' := by
  have hExp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ cexp ((π : ℂ) * Complex.I * (x : ℂ))) :=
    ((contDiff_const.mul contDiff_const).mul ofRealCLM.contDiff).cexp
  have hmul : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x) :=
    (contDiff_const.mul hExp).mul MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅'
  have hEq : (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x) = J₃' :=
    funext fun x => by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (J₃'_eq (x := x)).symm
  simpa [hEq] using hmul

/-- Schwartz-type decay bounds for `J₃'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₃' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₃' x‖ ≤ C := by
  intro k n
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c)
  let f : ℝ → ℂ := fun x ↦ (-1 / 2 : ℂ) • e x
  have hf_cont : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f, e] using ((ofRealCLM.contDiff.mul contDiff_const).cexp.const_smul (-1 / 2 : ℂ))
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left
    (f := f) (g := J₅') (k := k) (n := n) (B := fun m ↦ (1 / 2 : ℝ) * Real.pi ^ m)
    hf_cont MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅'
    (fun m x => SpherePacking.ForMathlib.norm_iteratedFDeriv_smul_cexp_mul_pi_I_le m x)
    (fun m => by simpa using (MagicFunction.b.Schwartz.J5Smooth.decay_J₅' (k := k) (n := m)))
  refine ⟨C, fun x hx => ?_⟩
  have hJ3fun : J₃' = fun y : ℝ ↦ f y * J₅' y :=
    funext fun y => by simp [f, e, c, mul_assoc, mul_left_comm, mul_comm, J₃'_eq (x := y)]
  simpa [hJ3fun] using hC x hx

end MagicFunction.b.Schwartz.J3Smooth

namespace MagicFunction.b.SchwartzIntegrals

open scoped ContDiff Topology
open MagicFunction MagicFunction.b MagicFunction.b.RealIntegrals
open Set Complex Real SchwartzMap RadialSchwartz.Bridge

/-- 1-D Schwartz functions from the primed radial integrals `J₁'`-`J₅'`. -/
public def J₁' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₁')
  MagicFunction.b.Schwartz.J1Smooth.contDiff_J₁' MagicFunction.b.Schwartz.J1Smooth.decay_J₁'
public def J₂' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₂')
  MagicFunction.b.Schwartz.J2Smooth.contDiff_J₂' MagicFunction.b.Schwartz.J2Smooth.decay_J₂'
public def J₃' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₃')
  MagicFunction.b.Schwartz.J3Smooth.contDiff_J₃' MagicFunction.b.Schwartz.J3Smooth.decay_J₃'
public def J₄' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₄')
  MagicFunction.b.Schwartz.J4Smooth.contDiff_J₄' MagicFunction.b.Schwartz.J4Smooth.decay_J₄'
public def J₅' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₅')
  MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅' MagicFunction.b.Schwartz.J5Smooth.decay_J₅'

private theorem J₆'_smooth_aux :
    ContDiff ℝ ∞ (fun r ↦ RadialSchwartz.cutoffC r * RealIntegrals.J₆' r) := by
  simpa using (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1
    (f := RealIntegrals.J₆') MagicFunction.b.Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1)

/-- 1-D Schwartz function from the primed radial integral `J₆'`. -/
public def J₆' : 𝓢(ℝ, ℂ) where
  toFun := RadialSchwartz.Bridge.fCut MagicFunction.b.RealIntegrals.J₆'
  smooth' := by simpa [RadialSchwartz.Bridge.fCut] using J₆'_smooth_aux
  decay' := by
    simpa using (RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
      (f := MagicFunction.b.RealIntegrals.J₆') (hg_smooth := J₆'_smooth_aux)
      MagicFunction.b.Schwartz.J6Smooth.decay_J₆')

/-- Schwartz functions on `ℝ⁸` from the radial profiles `J₁'`-`J₆'`. -/
@[expose] public def J₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₁'
@[expose] public def J₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₂'
@[expose] public def J₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₃'
@[expose] public def J₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₄'
@[expose] public def J₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₅'
@[expose] public def J₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₆'

@[simp] public lemma J₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₁' : ℝ → ℂ) r = RealIntegrals.J₁' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₂' : ℝ → ℂ) r = RealIntegrals.J₂' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₃' : ℝ → ℂ) r = RealIntegrals.J₃' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₄' : ℝ → ℂ) r = RealIntegrals.J₄' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₅' : ℝ → ℂ) r = RealIntegrals.J₅' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₆' : ℝ → ℂ) r = RealIntegrals.J₆' r := fCut_apply_of_nonneg _ hr

end MagicFunction.b.SchwartzIntegrals
namespace MagicFunction.FourierEigenfunctions

open SchwartzMap MagicFunction.b.SchwartzIntegrals

/-- Radial component of the -1-Fourier eigenfunction of Viazovska's magic function. -/
@[expose] public def b' : 𝓢(ℝ, ℂ) :=
  J₁' + J₂' + J₃' + J₄' + J₅' + J₆'

/-- The -1-Fourier eigenfunction of Viazovska's magic function. -/
@[expose] public def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) b'

/-- Expand `b` as a sum of `MagicFunction.b.RadialFunctions.J₁`-`J₆`. -/
public theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁ + MagicFunction.b.RadialFunctions.J₂ +
      MagicFunction.b.RadialFunctions.J₃ + MagicFunction.b.RadialFunctions.J₄ +
      MagicFunction.b.RadialFunctions.J₅ + MagicFunction.b.RadialFunctions.J₆ := by
  ext x
  simp [b, b', MagicFunction.b.RadialFunctions.J₁, MagicFunction.b.RadialFunctions.J₂,
    MagicFunction.b.RadialFunctions.J₃, MagicFunction.b.RadialFunctions.J₄,
    MagicFunction.b.RadialFunctions.J₅, MagicFunction.b.RadialFunctions.J₆,
    sq_nonneg ‖x‖, add_assoc]

end MagicFunction.FourierEigenfunctions

end

/-! ## Special values for `b`, notably `b 0 = 0`. -/

namespace MagicFunction.b.SpecialValuesProof

open scoped UpperHalfPlane Topology
open Set SchwartzMap Real Complex Filter UpperHalfPlane ModularForm
  MagicFunction.FourierEigenfunctions MagicFunction.b.RealIntegrals
  MagicFunction.b.RadialFunctions MagicFunction.Parametrisations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


lemma J₁'_J₃_eq_neg_J₅'_zero : J₁' (0 : ℝ) + J₃' 0 = -J₅' 0 := by
  have hI (z : ℝ → ℂ) (hz : ∀ t ∈ Icc (0 : ℝ) 1, ψT' (z t) = ψI' (z₅' t)) :
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z t)) =
        ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) :=
    intervalIntegral.integral_congr fun t ht => by
      simp [hz t (by simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)]
  have hJ1 : J₁' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₁'] using hI z₁' fun t => MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t)
  have hJ3 : J₃' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₃'] using hI z₃' fun t => MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t)
  simp [hJ1, hJ3, show J₅' (0 : ℝ) = (-2 : ℂ) *
    ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) by simp [J₅']]; ring

private lemma continuous_addIφ :
    Continuous fun t : ℝ => (⟨(t : ℂ) + Complex.I, by simp⟩ : ℍ) :=
  Continuous.upperHalfPlaneMk (by fun_prop) (fun _ => by simp)

lemma ψT'_z₂'_eq_ψI'_add_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := by
  have hz2 : 0 < (z₂' t).im := im_z₂'_pos (t := t) (by simpa using ht)
  simpa [ψT', ψI', hz2, show ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩ : ℍ) = ⟨(t : ℂ) + Complex.I, by simp⟩ by
    ext1; simp [z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]] using
    (show ψT ⟨z₂' t, hz2⟩ = ψI ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩) by simp [ψT, modular_slash_T_apply])

lemma ψS'_add_one (t : ℝ) (ht : 0 < t) :
    ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) := by
  have hz0 : 0 < (t * Complex.I).im := by simpa using ht
  have hz1 : 0 < ((1 : ℂ) + t * Complex.I).im := by simpa using ht
  let z0H : ℍ := ⟨t * Complex.I, hz0⟩
  simpa [ψS', hz0, hz1, ht, z0H, show ((1 : ℝ) +ᵥ z0H : ℍ) = ⟨(1 : ℂ) + t * Complex.I, hz1⟩ by
    ext1; simp [z0H, add_comm]] using show ψS ((1 : ℝ) +ᵥ z0H) = -ψS z0H by
      simpa [modular_slash_T_apply] using congrArg (fun F : ℍ → ℂ => F z0H) ψS_slash_T

lemma integrableOn_ψS'_vertical_left :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  have hC : ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) :=
    fun t ht => (hC0 t ht).trans (by gcongr; exact le_max_left _ _)
  have hEq : ∀ t : ℝ, 0 < t → ψS' (t * Complex.I) = ψS.resToImagAxis t := fun t ht0 => by
    simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
    (by simpa [mul_assoc] using
      ((exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := Real.pi) Real.pi_pos).const_mul C))
    ((((Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
          MagicFunction.b.PsiBounds.continuous_ψS).mono Set.Ioi_subset_Ici_self).congr
        fun t ht => hEq t (lt_trans (by norm_num) ht)).aestronglyMeasurable measurableSet_Ioi) <|
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      simpa [hEq t (lt_trans (by norm_num) ht)] using hC t ht.le

lemma J₂'_J₄_eq_neg_J₆'_zero : J₂' (0 : ℝ) + J₄' 0 = -J₆' 0 := by
  have hJ24 : J₂' (0 : ℝ) + J₄' 0 = ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
    have hJ2 : J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) := by
      simp only [J₂']; exact intervalIntegral.integral_congr fun t ht => by
        simp [ψT'_z₂'_eq_ψI'_add_one (t := t)
          (by simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)]
    have hJ4 : J₄' (0 : ℝ) = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
      rw [show J₄' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) by simp [J₄']]
      have hEq :
          (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t)) =
            ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) :=
        intervalIntegral.integral_congr fun t ht => by
          have htIcc : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
          simp [show z₄' t = (1 - (t : ℂ)) + Complex.I by simpa using z₄'_eq_of_mem htIcc]
      let f : ℝ → ℂ := fun u => ψT' ((u : ℂ) + Complex.I)
      rw [hEq, intervalIntegral.integral_const_mul,
        (intervalIntegral.integral_congr fun t _ => by
          simp [f, show ((1 - t : ℝ) : ℂ) = (1 - t : ℂ) by push_cast; ring] :
            (∫ t in (0 : ℝ)..1, ψT' ((1 - t : ℂ) + Complex.I)) = ∫ t in (0 : ℝ)..1, f (1 - t)),
        (by simp : (∫ t in (0 : ℝ)..1, f (1 - t)) = ∫ t in (0 : ℝ)..1, f t), neg_one_mul]
    have hrel : ∀ t : ℝ, ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) := fun t =>
      sub_eq_of_eq_add' <| by
        have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
        simpa [ψI', ψT', ψS', hz] using
          congrArg (fun F : ℍ → ℂ => F ⟨(t : ℂ) + Complex.I, hz⟩) ψI_eq_add_ψT_ψS
    simpa [hJ2, hJ4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := 0) (b := 1)
        ((by simpa [ψI'] using
            MagicFunction.b.PsiBounds.continuous_ψI.comp continuous_addIφ :
              Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I)).intervalIntegrable _ _)
        ((by simpa [ψT'] using
            MagicFunction.b.PsiBounds.continuous_ψT.comp continuous_addIφ :
              Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I)).intervalIntegrable _ _)).symm.trans
        (intervalIntegral.integral_congr fun t _ => hrel t)
  have hdiffψS :
      DifferentiableOn ℂ (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
    have hH2 := (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
    have hH3 := (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
    have hH4 := (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
    refine (DifferentiableOn.const_mul
        (((hH4.sub hH2).div (hH3.pow 2) (fun _ _ => pow_ne_zero 2 (H₃_ne_zero _))).sub
          ((hH2.add hH3).div (hH4.pow 2) (fun _ _ => pow_ne_zero 2 (H₄_ne_zero _))))
        (128 : ℂ)).congr fun z _ => ?_
    simpa [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
      show (H₄_MF : ℍ → ℂ) = H₄ from rfl] using
      congrArg (fun f : ℍ → ℂ => f (UpperHalfPlane.ofComplex z)) ψS_eq'
  have hcont : ContinuousOn ψS' (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := by
    have hsubset : (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) ⊆ {z : ℂ | 0 < z.im} := fun z hz =>
      lt_of_lt_of_le (by norm_num) (by simpa [mem_Ici] using hz.2 : (1 : ℝ) ≤ z.im)
    refine (hdiffψS.continuousOn.mono hsubset).congr fun z hz => ?_
    have hz' : 0 < z.im := hsubset hz
    simp [ψS', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hdiff : ∀ z ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
      DifferentiableAt ℂ ψS' z := fun z hz => by
    have hzpos : 0 < z.im := lt_trans (by norm_num)
      (by simpa [mem_Ioi] using hz.1.2 : (1 : ℝ) < z.im)
    refine ((hdiffψS z hzpos).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hzpos)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hzpos] with w hw
    simp [ψS', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((0 : ℂ) + t * Complex.I)) = 0 := by
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using
    (Complex.integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := ψS') (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont (s := (∅ : Set ℂ))
        (by simp) hdiff (by simpa using integrableOn_ψS'_vertical_left)
        (by
          simpa [MeasureTheory.IntegrableOn] using (integrableOn_ψS'_vertical_left.neg).congr
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
              simp [ψS'_add_one t (lt_trans (by norm_num) ht)] :
              (fun t : ℝ => -ψS' (t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
                fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I))) (fun ε hε => by
          obtain ⟨M, hM⟩ := Filter.eventually_atImInfty.1 (show ∀ᶠ z in UpperHalfPlane.atImInfty,
            ‖ψS z‖ < ε by simpa [dist_eq_norm] using
              (Metric.tendsto_nhds.1 MagicFunction.b.PsiBounds.tendsto_ψS_atImInfty) ε hε)
          refine ⟨max M 1, fun z hz => ?_⟩
          have hzpos : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
          simpa [ψS', hzpos] using hM ⟨z, hzpos⟩ ((le_max_left _ _).trans hz)))
  have hright : (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
      -∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I) := by
    simpa [MeasureTheory.integral_neg] using MeasureTheory.integral_congr_ae
      (g := fun t : ℝ => -ψS' (t * Complex.I))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        simp [ψS'_add_one t (lt_trans (by norm_num) ht)])
  have hhor : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) -
      (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 := by
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg]
      using show (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
        (Complex.I • (-∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I))) -
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 by
        simpa [hright] using hrect
  have hJ6 : J₆' (0 : ℝ) =
      (-2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
    rw [show J₆' (0 : ℝ) = (-2 : ℂ) *
        ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) by simp [J₆'],
      MeasureTheory.integral_Ici_eq_integral_Ioi,
      MeasureTheory.integral_congr_ae (g := fun t : ℝ => (Complex.I : ℂ) * ψS' (t * Complex.I))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          simp [MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t)
            (le_of_lt (by simpa [Set.mem_Ioi] using ht)), mul_comm])]
    simp [MeasureTheory.integral_const_mul, smul_eq_mul]
  exact hJ24.trans (eq_neg_of_add_eq_zero_left (by
    simp [show (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) =
        (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) by
      simpa [sub_eq_zero] using hhor, hJ6]))

theorem b_zero : MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) = 0 := by
  rw [show MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) =
      J₁' (0 : ℝ) + J₂' 0 + J₃' 0 + J₄' 0 + J₅' 0 + J₆' 0 from by
    open MagicFunction.b.RadialFunctions in
    simpa [J₁, J₂, J₃, J₄, J₅, J₆] using congrArg (fun f : ℝ⁸ → ℂ => f (0 : ℝ⁸))
      MagicFunction.FourierEigenfunctions.b_eq_sum_integrals_RadialFunctions]
  linear_combination J₂'_J₄_eq_neg_J₆'_zero + J₁'_J₃_eq_neg_J₅'_zero

end MagicFunction.b.SpecialValuesProof

namespace MagicFunction.b.SpecialValues

open MagicFunction.FourierEigenfunctions

/-- The magic function `b` vanishes at the origin. -/
public theorem b_zero : b 0 = 0 := by
  simpa using MagicFunction.b.SpecialValuesProof.b_zero

end MagicFunction.b.SpecialValues

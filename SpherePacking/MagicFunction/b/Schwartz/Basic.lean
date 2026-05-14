/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.Integration.DifferentiationUnderIntegral
public import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ1
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ5
import SpherePacking.Integration.UpperHalfPlaneComp

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

/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module
-- import Mathlib

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.a.Basic

import Mathlib.Analysis.Calculus.ContDiff.Bounds

import SpherePacking.ForMathlib.IteratedDeriv

import SpherePacking.MagicFunction.a.Schwartz.SmoothI1
import SpherePacking.MagicFunction.a.Schwartz.SmoothI2
import SpherePacking.MagicFunction.a.Schwartz.SmoothI4
import SpherePacking.MagicFunction.a.Schwartz.SmoothI6
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.MagicFunction.a.IntegralEstimates.I4
import SpherePacking.MagicFunction.a.IntegralEstimates.I6

/-!
# The magic function `a` is Schwartz

This file assembles smoothness and decay estimates for the six auxiliary integrals defining the
radial profile `a'`, and packages them as Schwartz maps on `ℝ` and on
`EuclideanSpace ℝ (Fin 8)`.

## Main definitions
* `MagicFunction.a.SchwartzIntegrals.I₁'` ... `I₆'`
* `MagicFunction.a.SchwartzIntegrals.I₁` ... `I₆`
* `MagicFunction.FourierEigenfunctions.a'`, `MagicFunction.FourierEigenfunctions.a`

## Main statements
* `MagicFunction.FourierEigenfunctions.a_eq_sum_integrals_RadialFunctions`
* `MagicFunction.FourierEigenfunctions.a_eq_sum_integrals_SchwartzIntegrals`
-/

-- NOTE: On `ℝ`, the radial profiles are only used at `r = ‖x‖^2 ≥ 0`. We therefore use a smooth
-- cutoff to build global Schwartz functions on `ℝ` without changing the induced functions on
-- `EuclideanSpace ℝ (Fin 8)`.

noncomputable section

open scoped ContDiff SchwartzMap
open SchwartzMap

namespace MagicFunction.a.SchwartzProperties

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Set Complex Real

section Smooth

/-!
## Smoothness of the auxiliary integrals

We show that each radial integral `I₁'`-`I₆'` is smooth in `r`, either directly by
differentiating under the integral sign or by reducing to previously handled cases.
-/

theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' := by
  simpa using MagicFunction.a.Schwartz.I1Smooth.I₁'_contDiff

theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' := by
  simpa using MagicFunction.a.Schwartz.I2Smooth.I₂'_contDiff

private lemma I₃'_eq_exp_mul_I₁' :
    RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
  ext x
  have hEqOn : EqOn
      (fun t => I * φ₀'' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ 2 * cexp (π * I * x * z₃' t))
      (fun t => cexp (2 * π * I * x) * (I * φ₀'' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 *
                                        cexp (π * I * x * z₁' t)))
      (uIcc 0 1) := fun t ht => by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h1 := z₁'_eq_of_mem ht
    have h3 := z₃'_eq_of_mem ht
    simp_rw [
      show z₃' t - 1 = I * t by simp [h3],
      show z₃' t = z₁' t + 2 by simp [h1, h3]; ring,
      show z₁' t + 1 = I * t by simp [h1],
      mul_add, Complex.exp_add, mul_comm, mul_left_comm, mul_assoc]
  simpa
      [RealIntegrals.I₃', Φ₃, Φ₃', RealIntegrals.I₁', Φ₁, Φ₁', mul_comm, mul_left_comm, mul_assoc]
    using intervalIntegral.integral_congr (a := 0) (b := 1) hEqOn

theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' := by
  simpa [I₃'_eq_exp_mul_I₁'] using (contDiff_const.mul ofRealCLM.contDiff).cexp.mul I₁'_smooth'

theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' := by
  simpa using MagicFunction.a.Schwartz.I4Smooth.I₄'_contDiff

private lemma I₅'_eq_mul_exp_mul_I₁' :
    RealIntegrals.I₅' = fun x : ℝ ↦ (-2 : ℂ) * cexp (π * I * x) * RealIntegrals.I₁' x := by
  ext x
  -- Pull the constant factor `cexp (-π * I * x)` out of `I₁'` and cancel.
  have hI1 :
      RealIntegrals.I₁' x =
        (∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)) *
          cexp (-π * I * x) := by
    calc
      RealIntegrals.I₁' x =
          ∫ t in (0 : ℝ)..1,
            ((-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)) * cexp (-π * I * x) := by
              simp [I₁'_eq, mul_assoc, mul_left_comm, mul_comm]
      _ =
          (∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)) *
            cexp (-π * I * x) := by
              simp
  have hI5 :
      RealIntegrals.I₅' x =
        (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t) := by
    simp [I₅'_eq, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite `I₁'` using `hI1`, cancel exponentials, and match `hI5`.
  symm
  let J : ℂ := ∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)
  have hJ1 : RealIntegrals.I₁' x = J * cexp (-π * I * x) := by
    simpa [J] using hI1
  have hJ5 : RealIntegrals.I₅' x = (-2 : ℂ) * J := by
    simpa [J] using hI5
  calc
    (-2 : ℂ) * cexp (π * I * x) * RealIntegrals.I₁' x
        = (-2 : ℂ) * cexp (π * I * x) * (J * cexp (-π * I * x)) := by
            simp [hJ1]
    _ = (-2 : ℂ) * J * (cexp (π * I * x) * cexp (-π * I * x)) := by
          ac_rfl
    _ = (-2 : ℂ) * J := by
          simp [Complex.exp_neg, mul_assoc]
    _ = RealIntegrals.I₅' x := by
          simpa using hJ5.symm

theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := by
  have hExp : ContDiff ℝ ∞ (fun x : ℝ ↦ cexp (((π : ℂ) * I) * (x : ℂ))) :=
    (contDiff_const.mul ofRealCLM.contDiff).cexp
  have h :
      ContDiff ℝ ∞ (fun x : ℝ ↦ (-2 : ℂ) * cexp (((π : ℂ) * I) * (x : ℂ)) * RealIntegrals.I₁' x) :=
    (contDiff_const.mul hExp).mul I₁'_smooth'
  simpa [I₅'_eq_mul_exp_mul_I₁', mul_assoc, mul_left_comm, mul_comm] using h

theorem I₆'_smooth' : ContDiff ℝ ∞ (fun r : ℝ ↦
  RadialSchwartz.cutoffC r * RealIntegrals.I₆' r) := by
  simpa using MagicFunction.a.Schwartz.I6Smooth.cutoffC_mul_I₆'_contDiff

end Smooth

section Decay

/-! # `a` decays faster than any inverse power of the norm squared.

We follow the proof of Proposition 7.8 in the blueprint.-/

theorem I₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C := by
  simpa using MagicFunction.a.Schwartz.I1Decay.decay'

theorem I₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₂.decay'

theorem I₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := by
  intro k n
  have hI1 : ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m RealIntegrals.I₁' x‖ ≤ C :=
    I₁'_decay' (k := k)
  choose C1 hC1 using hI1
  -- The exponential factor `exp(2π i x)`.
  let c3 : ℂ := (2 * π : ℂ) * I
  let g3 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c3)
  have hg3_smooth : ContDiff ℝ ∞ g3 := by
    have hlin : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ) * c3) := ofRealCLM.contDiff.mul contDiff_const
    simpa [g3] using hlin.cexp
  have hg3_bound : ∀ (m : ℕ) (x : ℝ), ‖iteratedFDeriv ℝ m g3 x‖ ≤ (2 * π) ^ m := by
    intro m x
    have hEq :
        ‖iteratedFDeriv ℝ m g3 x‖ = ‖iteratedDeriv m g3 x‖ := by
      simpa using
        (norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := m) (f := g3) (x := x))
    have hiter : iteratedDeriv m g3 = fun y : ℝ ↦ c3 ^ m * g3 y := by
      simpa [g3] using (SpherePacking.ForMathlib.iteratedDeriv_cexp_mul_const (c := c3) m)
    have hnorm_g3 : ‖g3 x‖ = 1 := by
      simpa [g3, c3, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (2 * π * x))
    have hc3_norm : ‖c3‖ = (2 * π : ℝ) := by
      have hnonneg : 0 ≤ (2 * π : ℝ) := by positivity
      calc
        ‖c3‖ = ‖(2 * π : ℂ)‖ * ‖(I : ℂ)‖ := by simp [c3]
        _ = ‖(2 * π : ℝ)‖ := by simp [Complex.norm_real]
        _ = (2 * π : ℝ) := by simpa using Real.norm_of_nonneg hnonneg
    have hnorm :
        ‖iteratedDeriv m g3 x‖ ≤ (2 * π) ^ m := by
      calc
        ‖iteratedDeriv m g3 x‖ = ‖c3 ^ m * g3 x‖ := by simp [hiter]
        _ = ‖c3‖ ^ m * ‖g3 x‖ := by simp [norm_pow]
        _ ≤ (2 * π) ^ m * 1 := by
              gcongr
              · simp [hc3_norm]
              · simp [hnorm_g3]
        _ = (2 * π) ^ m := by ring
    simpa [hEq] using hnorm
  -- Rewrite `I₃'` as `g3 * I₁'`.
  have hI : RealIntegrals.I₃' = fun x : ℝ ↦ g3 x * RealIntegrals.I₁' x := by
    ext x
    have hEqOn : EqOn
        (fun t => I * φ₀'' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ 2 * cexp (π * I * x * z₃' t))
        (fun t => cexp (2 * π * I * x) * (I * φ₀'' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ 2 *
                                          cexp (π * I * x * z₁' t)))
        (uIcc 0 1) := fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have h1 := z₁'_eq_of_mem ht; have h3 := z₃'_eq_of_mem ht
      simp_rw [
        show z₃' t - 1 = I * t by simp [h3],
        show z₃' t = z₁' t + 2 by simp [h1, h3]; ring,
        show z₁' t + 1 = I * t by simp [h1],
        mul_add, Complex.exp_add, mul_comm, mul_left_comm, mul_assoc]
    -- The rewrite in `hEqOn` produces the factor `exp (I * (x * (π * 2)))`.
    -- Rewrite it as `g3 x = exp ((x : ℂ) * ((2π) * I))`.
    have hfac : cexp (I * ((x : ℂ) * ((π : ℂ) * (2 : ℂ)))) = g3 x := by
      have hexp : (I : ℂ) * ((x : ℂ) * ((π : ℂ) * (2 : ℂ))) = (x : ℂ) * c3 := by
        simp [c3, mul_left_comm, mul_comm]
      simp [g3, hexp]
    simpa [RealIntegrals.I₃', Φ₃, Φ₃', RealIntegrals.I₁', Φ₁, Φ₁', mul_comm, mul_left_comm,
      mul_assoc, g3, hfac] using intervalIntegral.integral_congr (a := 0) (b := 1) hEqOn
  let C3 : ℝ :=
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (2 * π) ^ i * C1 (n - i)
  refine ⟨C3, ?_⟩
  intro x hx
  have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
  have hn : (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  have hmul :
      ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g3 x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ := by
    simpa [hI] using
      (norm_iteratedFDeriv_mul_le (f := g3) (g := RealIntegrals.I₁')
        (hf := hg3_smooth) (hg := I₁'_smooth') x (n := n) hn)
  have hmul' := mul_le_mul_of_nonneg_left hmul hxpow_nonneg
  refine hmul'.trans ?_
  -- distribute `‖x‖^k` across the sum.
  simpa [C3, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_le_sum fun i hi => by
      have hgi : ‖iteratedFDeriv ℝ i g3 x‖ ≤ (2 * π) ^ i := hg3_bound i x
      have hfi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ ≤ C1 (n - i) :=
        hC1 (n - i) x hx
      have hterm :
          ‖x‖ ^ k *
              ((n.choose i : ℝ) *
                (‖iteratedFDeriv ℝ i g3 x‖ *
                  ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖)) ≤
              (n.choose i : ℝ) * (2 * π) ^ i * C1 (n - i) := by
        calc
          ‖x‖ ^ k *
                ((n.choose i : ℝ) *
                  (‖iteratedFDeriv ℝ i g3 x‖ *
                    ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖))
              = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g3 x‖ *
                  (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) := by
                  ring_nf
          _ ≤ (n.choose i : ℝ) * (2 * π) ^ i * C1 (n - i) := by
                gcongr
      simpa [mul_assoc, mul_left_comm, mul_comm] using hterm)

theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₄.decay'

theorem I₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := by
  intro k n
  -- Constants for the decay bounds of `I₁'`.
  have hI1 : ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m RealIntegrals.I₁' x‖ ≤ C :=
    I₁'_decay' (k := k)
  choose C1 hC1 using hI1
  -- The exponential factor `exp(π i x)`.
  let c5 : ℂ := (π : ℂ) * I
  let g5 : ℝ → ℂ := fun x ↦ cexp (c5 * (x : ℂ))
  have hg5_smooth : ContDiff ℝ ∞ g5 := by
    have hlin : ContDiff ℝ ∞ (fun x : ℝ ↦ c5 * (x : ℂ)) :=
      contDiff_const.mul ofRealCLM.contDiff
    simpa [g5] using hlin.cexp
  have hg5_bound : ∀ (m : ℕ) (x : ℝ), ‖iteratedFDeriv ℝ m g5 x‖ ≤ (π) ^ m := by
    intro m x
    have hEq :
        ‖iteratedFDeriv ℝ m g5 x‖ = ‖iteratedDeriv m g5 x‖ := by
      simpa using
        (norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := m) (f := g5) (x := x))
    have hiter : iteratedDeriv m g5 = fun y : ℝ ↦ c5 ^ m * g5 y := by
      simpa [g5, mul_assoc, mul_left_comm, mul_comm] using
        (SpherePacking.ForMathlib.iteratedDeriv_cexp_mul_const (c := c5) m)
    have hnorm_g5 : ‖g5 x‖ = 1 := by
      simpa [g5, c5, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (π * x))
    have hc5_norm : ‖c5‖ = (π : ℝ) := by
      have hnonneg : 0 ≤ (π : ℝ) := Real.pi_pos.le
      calc
        ‖c5‖ = ‖(π : ℂ)‖ * ‖(I : ℂ)‖ := by simp [c5]
        _ = ‖(π : ℝ)‖ := by simp [Complex.norm_real]
        _ = (π : ℝ) := by simpa using Real.norm_of_nonneg hnonneg
    have hnorm :
        ‖iteratedDeriv m g5 x‖ ≤ π ^ m := by
      calc
        ‖iteratedDeriv m g5 x‖ = ‖c5 ^ m * g5 x‖ := by simp [hiter]
        _ = ‖c5‖ ^ m * ‖g5 x‖ := by simp [norm_pow]
        _ ≤ (π : ℝ) ^ m * 1 := by
          gcongr
          · simp [hc5_norm]
          · simp [hnorm_g5]
        _ = π ^ m := by ring
    simpa [hEq] using hnorm
  -- Rewrite `I₅'` as `(-2) * g5 * I₁'`.
  have hI : RealIntegrals.I₅' = fun x : ℝ ↦ (-2 : ℂ) * g5 x * RealIntegrals.I₁' x := by
    ext x
    symm
    -- Match the shared integral and simplify exponentials.
    have hI5 :
        RealIntegrals.I₅' x =
          (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t) := by
      simp [I₅'_eq, mul_assoc, mul_left_comm, mul_comm]
    have hI1 :
        RealIntegrals.I₁' x =
          (∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)) *
            cexp (-π * I * x) := by
      calc
        RealIntegrals.I₁' x =
            ∫ t in (0 : ℝ)..1,
              ((-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)) * cexp (-π * I * x) := by
                simp [I₁'_eq, mul_assoc, mul_left_comm, mul_comm]
        _ =
            (∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)) *
              cexp (-π * I * x) := by
                simp
    let J : ℂ :=
      ∫ t in (0 : ℝ)..1, (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)
    have hJ1 : RealIntegrals.I₁' x = J * cexp (-π * I * x) := by
      simpa [J] using hI1
    have hJ5 : RealIntegrals.I₅' x = (-2 : ℂ) * J := by
      simpa [J] using hI5
    calc
      (-2 : ℂ) * g5 x * RealIntegrals.I₁' x
          = (-2 : ℂ) * g5 x * (J * cexp (-π * I * x)) := by simp [hJ1]
      _ = (-2 : ℂ) * J * (g5 x * cexp (-π * I * x)) := by ac_rfl
      _ = (-2 : ℂ) * J := by
            simp [g5, c5, Complex.exp_neg, mul_left_comm, mul_comm]
      _ = RealIntegrals.I₅' x := by simpa using hJ5.symm
  -- Build the bound for `g5 * I₁'` first, then scale by `‖-2‖ = 2`.
  let Cprod : ℝ :=
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (π) ^ i * (C1 (n - i))
  refine ⟨2 * Cprod, ?_⟩
  intro x hx
  have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
  have hn' : (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  have hmul :
      ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g5 x‖ *
          ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ := by
    simpa using (norm_iteratedFDeriv_mul_le (f := g5) (g := RealIntegrals.I₁')
      (hf := hg5_smooth) (hg := I₁'_smooth') x (n := n) hn')
  have hmul' := mul_le_mul_of_nonneg_left hmul hxpow_nonneg
  have hsmooth_prod : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x := by
    have hsmoothInf : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x := by
      have : ContDiff ℝ ∞ (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) := hg5_smooth.mul I₁'_smooth'
      exact this.contDiffAt
    have hn : (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
    exact hsmoothInf.of_le hn
  have hsmul :
      iteratedFDeriv ℝ n ((-2 : ℂ) • fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x =
        (-2 : ℂ) • iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x := by
    simpa using (iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := n)
      (a := (-2 : ℂ)) (f := fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) hsmooth_prod)
  have htermBound :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x‖ ≤ Cprod := by
    refine hmul'.trans ?_
    simpa [Cprod, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      (Finset.sum_le_sum fun i hi => by
        have hgi : ‖iteratedFDeriv ℝ i g5 x‖ ≤ π ^ i := hg5_bound i x
        have hfi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ ≤ C1 (n - i) :=
          hC1 (n - i) x hx
        have hterm :
            ‖x‖ ^ k *
                ((n.choose i : ℝ) *
                  (‖iteratedFDeriv ℝ i g5 x‖ *
                    ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖)) ≤
                (n.choose i : ℝ) * π ^ i * C1 (n - i) := by
          calc
            ‖x‖ ^ k *
                  ((n.choose i : ℝ) *
                    (‖iteratedFDeriv ℝ i g5 x‖ *
                      ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖))
                = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g5 x‖ *
                    (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) := by
                    ring_nf
            _ ≤ (n.choose i : ℝ) * π ^ i * C1 (n - i) := by
                  gcongr
          -- align with the multiplication association used by `simp` above
        simpa [mul_assoc, mul_left_comm, mul_comm] using hterm)
  have hscale :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₅' x‖ ≤ 2 * Cprod := by
    -- Reduce to the product bound and use `‖-2‖ = 2`.
    have hI' : RealIntegrals.I₅' x = (-2 : ℂ) • (g5 x * RealIntegrals.I₁' x) := by
      simp [hI, mul_assoc]
    -- Use the `smul` behavior of `iteratedFDeriv`.
    have :
        iteratedFDeriv ℝ n RealIntegrals.I₅' x =
          (-2 : ℂ) • iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x := by
      -- rewrite `I₅'` and then use `hsmul`
      simpa [hI, Pi.mul_def, mul_assoc, smul_eq_mul] using hsmul
    -- Take norms and bound.
    have hnorm2 : ‖(-2 : ℂ)‖ = (2 : ℝ) := by simp
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₅' x‖
          = ‖x‖ ^ k * ‖(-2 : ℂ) •
            iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x‖ := by
              simp [this]
      _ = ‖x‖ ^ k * (‖(-2 : ℂ)‖ *
        ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x‖) := by
              simp [norm_smul]
      _ ≤ ‖(-2 : ℂ)‖ * (‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ g5 y * RealIntegrals.I₁' y) x‖) := by
              nlinarith [hxpow_nonneg]
      _ ≤ 2 * Cprod := by
              simpa [hnorm2, mul_assoc, mul_left_comm, mul_comm] using
                (mul_le_mul_of_nonneg_left htermBound (by positivity : (0 : ℝ) ≤ (2 : ℝ)))
  simpa [mul_assoc] using hscale

theorem I₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₆.decay'

end Decay

end MagicFunction.a.SchwartzProperties

namespace MagicFunction.a.SchwartzIntegrals

/--
A Schwartz function on `ℝ` agreeing with `RealIntegrals.I₁'` on `r ≥ 0`.

It is obtained by multiplying `RealIntegrals.I₁'` by the smooth cutoff `RadialSchwartz.cutoffC`.
The prime indicates that this is a radial profile in the variable `r = ‖x‖^2`.
-/
@[expose] public def I₁' : 𝓢(ℝ, ℂ) where
  toFun := fun r ↦ RadialSchwartz.cutoffC r * MagicFunction.a.RealIntegrals.I₁' r
  smooth' := by
    simpa using
      (RadialSchwartz.cutoffC_contDiff.mul MagicFunction.a.SchwartzProperties.I₁'_smooth')
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg
        (f := MagicFunction.a.RealIntegrals.I₁')
        MagicFunction.a.SchwartzProperties.I₁'_smooth'
        MagicFunction.a.SchwartzProperties.I₁'_decay')

/--
A Schwartz function on `ℝ` agreeing with `RealIntegrals.I₂'` on `r ≥ 0`.

It is obtained by multiplying `RealIntegrals.I₂'` by the smooth cutoff `RadialSchwartz.cutoffC`.
The prime indicates that this is a radial profile in the variable `r = ‖x‖^2`.
-/
@[expose] public def I₂' : 𝓢(ℝ, ℂ) where
  toFun := fun r ↦ RadialSchwartz.cutoffC r * MagicFunction.a.RealIntegrals.I₂' r
  smooth' := by
    simpa using
      (RadialSchwartz.cutoffC_contDiff.mul MagicFunction.a.SchwartzProperties.I₂'_smooth')
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg
        (f := MagicFunction.a.RealIntegrals.I₂')
        MagicFunction.a.SchwartzProperties.I₂'_smooth'
        MagicFunction.a.SchwartzProperties.I₂'_decay')

/--
A Schwartz function on `ℝ` agreeing with `RealIntegrals.I₃'` on `r ≥ 0`.

It is obtained by multiplying `RealIntegrals.I₃'` by the smooth cutoff `RadialSchwartz.cutoffC`.
The prime indicates that this is a radial profile in the variable `r = ‖x‖^2`.
-/
@[expose] public def I₃' : 𝓢(ℝ, ℂ) where
  toFun := fun r ↦ RadialSchwartz.cutoffC r * MagicFunction.a.RealIntegrals.I₃' r
  smooth' := by
    simpa using
      (RadialSchwartz.cutoffC_contDiff.mul MagicFunction.a.SchwartzProperties.I₃'_smooth')
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg
        (f := MagicFunction.a.RealIntegrals.I₃')
        MagicFunction.a.SchwartzProperties.I₃'_smooth'
        MagicFunction.a.SchwartzProperties.I₃'_decay')

/--
A Schwartz function on `ℝ` agreeing with `RealIntegrals.I₄'` on `r ≥ 0`.

It is obtained by multiplying `RealIntegrals.I₄'` by the smooth cutoff `RadialSchwartz.cutoffC`.
The prime indicates that this is a radial profile in the variable `r = ‖x‖^2`.
-/
@[expose] public def I₄' : 𝓢(ℝ, ℂ) where
  toFun := fun r ↦ RadialSchwartz.cutoffC r * MagicFunction.a.RealIntegrals.I₄' r
  smooth' := by
    simpa using
      (RadialSchwartz.cutoffC_contDiff.mul MagicFunction.a.SchwartzProperties.I₄'_smooth')
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg
        (f := MagicFunction.a.RealIntegrals.I₄')
        MagicFunction.a.SchwartzProperties.I₄'_smooth'
        MagicFunction.a.SchwartzProperties.I₄'_decay')

/--
A Schwartz function on `ℝ` agreeing with `RealIntegrals.I₅'` on `r ≥ 0`.

It is obtained by multiplying `RealIntegrals.I₅'` by the smooth cutoff `RadialSchwartz.cutoffC`.
The prime indicates that this is a radial profile in the variable `r = ‖x‖^2`.
-/
@[expose] public def I₅' : 𝓢(ℝ, ℂ) where
  toFun := fun r ↦ RadialSchwartz.cutoffC r * MagicFunction.a.RealIntegrals.I₅' r
  smooth' := by
    simpa using
      (RadialSchwartz.cutoffC_contDiff.mul MagicFunction.a.SchwartzProperties.I₅'_smooth')
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg
        (f := MagicFunction.a.RealIntegrals.I₅')
        MagicFunction.a.SchwartzProperties.I₅'_smooth'
        MagicFunction.a.SchwartzProperties.I₅'_decay')

/--
A Schwartz function on `ℝ` agreeing with `RealIntegrals.I₆'` on `r ≥ 0`.

It is obtained by multiplying `RealIntegrals.I₆'` by the smooth cutoff `RadialSchwartz.cutoffC`.
The prime indicates that this is a radial profile in the variable `r = ‖x‖^2`.
-/
@[expose] public def I₆' : 𝓢(ℝ, ℂ) where
  toFun := fun r ↦ RadialSchwartz.cutoffC r * MagicFunction.a.RealIntegrals.I₆' r
  smooth' := by
    simpa using MagicFunction.a.SchwartzProperties.I₆'_smooth'
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
        (f := MagicFunction.a.RealIntegrals.I₆')
        (hg_smooth := MagicFunction.a.SchwartzProperties.I₆'_smooth')
        MagicFunction.a.SchwartzProperties.I₆'_decay')

/-- The Schwartz function on `EuclideanSpace ℝ (Fin 8)` induced from the radial profile `I₁'`. -/
@[expose] public def I₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₁'

/-- The Schwartz function on `EuclideanSpace ℝ (Fin 8)` induced from the radial profile `I₂'`. -/
@[expose] public def I₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₂'

/-- The Schwartz function on `EuclideanSpace ℝ (Fin 8)` induced from the radial profile `I₃'`. -/
@[expose] public def I₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₃'

/-- The Schwartz function on `EuclideanSpace ℝ (Fin 8)` induced from the radial profile `I₄'`. -/
@[expose] public def I₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₄'

/-- The Schwartz function on `EuclideanSpace ℝ (Fin 8)` induced from the radial profile `I₅'`. -/
@[expose] public def I₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₅'

/-- The Schwartz function on `EuclideanSpace ℝ (Fin 8)` induced from the radial profile `I₆'`. -/
@[expose] public def I₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₆'

/-- On `r ≥ 0`, the cutoff is `1`, so `I₁'` agrees with `RealIntegrals.I₁'`. -/
@[simp]
public lemma I₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₁' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₁' r := by
  simp [I₁', SchwartzMap.instFunLike, RadialSchwartz.cutoffC_eq_one_of_nonneg hr]

/-- On `r ≥ 0`, the cutoff is `1`, so `I₂'` agrees with `RealIntegrals.I₂'`. -/
@[simp]
public lemma I₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₂' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₂' r := by
  simp [I₂', SchwartzMap.instFunLike, RadialSchwartz.cutoffC_eq_one_of_nonneg hr]

/-- On `r ≥ 0`, the cutoff is `1`, so `I₃'` agrees with `RealIntegrals.I₃'`. -/
@[simp]
public lemma I₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₃' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₃' r := by
  simp [I₃', SchwartzMap.instFunLike, RadialSchwartz.cutoffC_eq_one_of_nonneg hr]

/-- On `r ≥ 0`, the cutoff is `1`, so `I₄'` agrees with `RealIntegrals.I₄'`. -/
@[simp]
public lemma I₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₄' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₄' r := by
  simp [I₄', SchwartzMap.instFunLike, RadialSchwartz.cutoffC_eq_one_of_nonneg hr]

/-- On `r ≥ 0`, the cutoff is `1`, so `I₅'` agrees with `RealIntegrals.I₅'`. -/
@[simp]
public lemma I₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₅' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₅' r := by
  simp [I₅', SchwartzMap.instFunLike, RadialSchwartz.cutoffC_eq_one_of_nonneg hr]

/-- On `r ≥ 0`, the cutoff is `1`, so `I₆'` agrees with `RealIntegrals.I₆'`. -/
@[simp]
public lemma I₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₆' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₆' r := by
  simp [I₆', SchwartzMap.instFunLike, RadialSchwartz.cutoffC_eq_one_of_nonneg hr]

end MagicFunction.a.SchwartzIntegrals
namespace MagicFunction.FourierEigenfunctions

/--
The radial profile of the `+1` Fourier eigenfunction `a`.

The prime indicates that this is a function of the real parameter `r = ‖x‖^2`.
-/
@[expose] public def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.SchwartzIntegrals.I₁'
  + MagicFunction.a.SchwartzIntegrals.I₂'
  + MagicFunction.a.SchwartzIntegrals.I₃'
  + MagicFunction.a.SchwartzIntegrals.I₄'
  + MagicFunction.a.SchwartzIntegrals.I₅'
  + MagicFunction.a.SchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[expose] public def a : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) a'

/-- Expand `a` as the sum of the six defining integrals from `MagicFunction.a.RadialFunctions`. -/
public theorem a_eq_sum_integrals_RadialFunctions : a =
    MagicFunction.a.RadialFunctions.I₁
  + MagicFunction.a.RadialFunctions.I₂
  + MagicFunction.a.RadialFunctions.I₃
  + MagicFunction.a.RadialFunctions.I₄
  + MagicFunction.a.RadialFunctions.I₅
  + MagicFunction.a.RadialFunctions.I₆ := by
  ext x
  have hr : 0 ≤ (‖x‖ ^ 2) := sq_nonneg ‖x‖
  simp [a, a', MagicFunction.a.RadialFunctions.I₁, MagicFunction.a.RadialFunctions.I₂,
    MagicFunction.a.RadialFunctions.I₃, MagicFunction.a.RadialFunctions.I₄,
    MagicFunction.a.RadialFunctions.I₅, MagicFunction.a.RadialFunctions.I₆,
    schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.add_apply,
    MagicFunction.a.SchwartzIntegrals.I₁'_apply_of_nonneg (r := ‖x‖ ^ 2) hr,
    MagicFunction.a.SchwartzIntegrals.I₂'_apply_of_nonneg (r := ‖x‖ ^ 2) hr,
    MagicFunction.a.SchwartzIntegrals.I₃'_apply_of_nonneg (r := ‖x‖ ^ 2) hr,
    MagicFunction.a.SchwartzIntegrals.I₄'_apply_of_nonneg (r := ‖x‖ ^ 2) hr,
    MagicFunction.a.SchwartzIntegrals.I₅'_apply_of_nonneg (r := ‖x‖ ^ 2) hr,
    MagicFunction.a.SchwartzIntegrals.I₆'_apply_of_nonneg (r := ‖x‖ ^ 2) hr, add_assoc]

/--
Expand `a` as the sum of the six defining integrals from `MagicFunction.a.SchwartzIntegrals`.
-/
public theorem a_eq_sum_integrals_SchwartzIntegrals : a =
    MagicFunction.a.SchwartzIntegrals.I₁
  + MagicFunction.a.SchwartzIntegrals.I₂
  + MagicFunction.a.SchwartzIntegrals.I₃
  + MagicFunction.a.SchwartzIntegrals.I₄
  + MagicFunction.a.SchwartzIntegrals.I₅
  + MagicFunction.a.SchwartzIntegrals.I₆ := by
  ext x
  simp [a, a', MagicFunction.a.SchwartzIntegrals.I₁, MagicFunction.a.SchwartzIntegrals.I₂,
    MagicFunction.a.SchwartzIntegrals.I₃, MagicFunction.a.SchwartzIntegrals.I₄,
    MagicFunction.a.SchwartzIntegrals.I₅, MagicFunction.a.SchwartzIntegrals.I₆,
    schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.add_apply, add_assoc]

end MagicFunction.FourierEigenfunctions

end

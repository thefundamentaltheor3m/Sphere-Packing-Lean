/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.Common.SchwartzAssembly
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.MagicFunction.a.Schwartz.SmoothI1
import SpherePacking.MagicFunction.a.Schwartz.SmoothI2
import SpherePacking.MagicFunction.a.Schwartz.SmoothI4
import SpherePacking.MagicFunction.a.Schwartz.SmoothI6
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.MagicFunction.a.IntegralEstimates.I4
import SpherePacking.MagicFunction.a.IntegralEstimates.I6

/-!
# The magic function `a` is Schwartz

On `ℝ`, the radial profiles are only used at `r = ‖x‖^2 ≥ 0`. We use a smooth cutoff to build
global Schwartz functions on `ℝ` without changing the induced functions on
`EuclideanSpace ℝ (Fin 8)`.
-/

noncomputable section

open scoped ContDiff SchwartzMap
open SchwartzMap

namespace MagicFunction.a.SchwartzProperties

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Set Complex Real MeasureTheory

section Smooth

public theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' :=
  MagicFunction.a.Schwartz.I1Smooth.I₁'_contDiff

public theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' :=
  MagicFunction.a.Schwartz.I2Smooth.I₂'_contDiff

private lemma I₃'_eq_exp_mul_I₁' :
    RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
  ext x
  rw [I₃'_eq, I₁'_eq, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [show cexp (2 * ↑π * I * ↑x) * (-I * φ₀'' (-1 / (I * ↑t)) * ↑t ^ 2 * cexp (-↑π * I * ↑x) *
        cexp (-↑π * ↑x * ↑t)) = -I * φ₀'' (-1 / (I * ↑t)) * ↑t ^ 2 *
        (cexp (2 * ↑π * I * ↑x) * cexp (-↑π * I * ↑x)) * cexp (-↑π * ↑x * ↑t) from by ring,
      ← Complex.exp_add, show 2 * (↑π : ℂ) * I * ↑x + -↑π * I * ↑x = ↑π * I * ↑x from by ring]

public theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' :=
  I₃'_eq_exp_mul_I₁' ▸ (contDiff_const.mul ofRealCLM.contDiff).cexp.mul I₁'_smooth'

public theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' :=
  MagicFunction.a.Schwartz.I4Smooth.I₄'_contDiff

private lemma I₅'_eq_mul_exp_mul_I₁' :
    RealIntegrals.I₅' = fun x : ℝ ↦ (-2 : ℂ) * cexp (π * I * x) * RealIntegrals.I₁' x := by
  ext x
  let f : ℝ → ℂ :=
    fun t => (-I) * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * x * t)
  have hI1 : RealIntegrals.I₁' x = (∫ t in (0 : ℝ)..1, f t) * cexp (-π * I * x) := by
    rw [show RealIntegrals.I₁' x = ∫ t in (0 : ℝ)..1, f t * cexp (-π * I * x) by
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using (I₁'_eq (r := x))]
    simp [intervalIntegral.integral_mul_const]
  rw [show RealIntegrals.I₅' x = (-2 : ℂ) * ∫ t in (0 : ℝ)..1, f t by
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using (I₅'_eq (r := x)), hI1]
  linear_combination (2 * ∫ t in (0 : ℝ)..1, f t) *
    (by simp [← Complex.exp_add] : cexp (π * I * x) * cexp (-π * I * x) = 1)

public theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := I₅'_eq_mul_exp_mul_I₁' ▸
  (contDiff_const.mul (contDiff_const.mul ofRealCLM.contDiff).cexp).mul I₁'_smooth'

public theorem I₆'_smooth' : ContDiff ℝ ∞ (fun r : ℝ ↦
    RadialSchwartz.cutoffC r * RealIntegrals.I₆' r) :=
  MagicFunction.a.Schwartz.I6Smooth.cutoffC_mul_I₆'_contDiff

end Smooth

section Decay

public theorem I₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C :=
  MagicFunction.a.Schwartz.I1Decay.decay'

public theorem I₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₂' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₂.decay'

public theorem I₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := fun k n ↦ by
  let g3 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * ((2 * π : ℂ) * I))
  have hI : RealIntegrals.I₃' = fun x : ℝ ↦ g3 x * RealIntegrals.I₁' x :=
    I₃'_eq_exp_mul_I₁'.trans <| funext fun _ ↦ by simp [g3, mul_comm, mul_left_comm]
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := g3)
    (g := RealIntegrals.I₁') (k := k) (n := n) (B := fun m ↦ (2 * π) ^ m)
    (ofRealCLM.contDiff.mul contDiff_const).cexp I₁'_smooth' (fun m x => by
      simpa [g3, mul_assoc, mul_left_comm, mul_comm, abs_of_nonneg Real.pi_pos.le] using
        SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_ofReal_mul_I_le (a := 2 * π) m x)
    (I₁'_decay' (k := k))
  exact ⟨C, fun x hx => by simpa [hI] using hC x hx⟩

public theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₄.decay'

public theorem I₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := fun k n ↦ by
  let g5 : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * ((π : ℂ) * I))
  let f5 : ℝ → ℂ := fun x ↦ (-2 : ℂ) * g5 x
  have hg5_smooth : ContDiff ℝ ∞ g5 := (ofRealCLM.contDiff.mul contDiff_const).cexp
  have hf5_bound : ∀ (m : ℕ) (x : ℝ), ‖iteratedFDeriv ℝ m f5 x‖ ≤ 2 * π ^ m := fun m x => by
    rw [show iteratedFDeriv ℝ m f5 x = (-2 : ℂ) • iteratedFDeriv ℝ m g5 x by
      simpa [f5, smul_eq_mul] using iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := m)
        (a := (-2 : ℂ)) (f := g5) (hg5_smooth.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, show ‖(-2 : ℂ)‖ = (2 : ℝ) from by simp]
    exact mul_le_mul_of_nonneg_left
      (SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_pi_I_le m x) (by norm_num)
  have hI : RealIntegrals.I₅' = fun x : ℝ ↦ f5 x * RealIntegrals.I₁' x :=
    I₅'_eq_mul_exp_mul_I₁'.trans <| funext fun _ ↦ by simp [f5, g5, mul_comm, mul_left_comm]
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := f5)
    (g := RealIntegrals.I₁') (k := k) (n := n) (B := fun m ↦ 2 * π ^ m)
    (contDiff_const.mul hg5_smooth) I₁'_smooth' hf5_bound (I₁'_decay' (k := k))
  exact ⟨C, fun x hx => by simpa [hI] using hC x hx⟩

public theorem I₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ), 0 ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₆' x‖ ≤ C :=
  MagicFunction.a.IntegralEstimates.I₆.decay'

end Decay

end MagicFunction.a.SchwartzProperties

namespace MagicFunction.a.SchwartzIntegrals

open RadialSchwartz.Bridge

/-- The one-dimensional Schwartz function associated to the primed radial integral `I₁'`. -/
@[expose] public def I₁' : 𝓢(ℝ, ℂ) := fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₁')
  MagicFunction.a.SchwartzProperties.I₁'_smooth' MagicFunction.a.SchwartzProperties.I₁'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `I₂'`. -/
@[expose] public def I₂' : 𝓢(ℝ, ℂ) := fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₂')
  MagicFunction.a.SchwartzProperties.I₂'_smooth' MagicFunction.a.SchwartzProperties.I₂'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `I₃'`. -/
@[expose] public def I₃' : 𝓢(ℝ, ℂ) := fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₃')
  MagicFunction.a.SchwartzProperties.I₃'_smooth' MagicFunction.a.SchwartzProperties.I₃'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `I₄'`. -/
@[expose] public def I₄' : 𝓢(ℝ, ℂ) := fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₄')
  MagicFunction.a.SchwartzProperties.I₄'_smooth' MagicFunction.a.SchwartzProperties.I₄'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `I₅'`. -/
@[expose] public def I₅' : 𝓢(ℝ, ℂ) := fCutSchwartz (f := MagicFunction.a.RealIntegrals.I₅')
  MagicFunction.a.SchwartzProperties.I₅'_smooth' MagicFunction.a.SchwartzProperties.I₅'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `I₆'`.

`I₆'` requires the cutoff variant because its smoothness is only provided on `(-1, ∞)`. -/
@[expose] public def I₆' : 𝓢(ℝ, ℂ) where
  toFun := RadialSchwartz.Bridge.fCut MagicFunction.a.RealIntegrals.I₆'
  smooth' := by
    simpa [RadialSchwartz.Bridge.fCut] using MagicFunction.a.SchwartzProperties.I₆'_smooth'
  decay' := by
    simpa using RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
      (f := MagicFunction.a.RealIntegrals.I₆')
      (hg_smooth := MagicFunction.a.SchwartzProperties.I₆'_smooth')
      MagicFunction.a.SchwartzProperties.I₆'_decay'

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

@[simp] public lemma I₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₁' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₁' r := fCut_apply_of_nonneg _ hr

@[simp] public lemma I₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₂' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₂' r := fCut_apply_of_nonneg _ hr

@[simp] public lemma I₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₃' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₃' r := fCut_apply_of_nonneg _ hr

@[simp] public lemma I₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₄' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₄' r := fCut_apply_of_nonneg _ hr

@[simp] public lemma I₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₅' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₅' r := fCut_apply_of_nonneg _ hr

@[simp] public lemma I₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (I₆' : ℝ → ℂ) r = MagicFunction.a.RealIntegrals.I₆' r := fCut_apply_of_nonneg _ hr

end MagicFunction.a.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

open SchwartzMap MagicFunction.Common

/-- The radial profile of the `+1` Fourier eigenfunction `a`. -/
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
public theorem a_eq_sum_integrals_RadialFunctions :
    a = MagicFunction.a.RadialFunctions.I₁ + MagicFunction.a.RadialFunctions.I₂
      + MagicFunction.a.RadialFunctions.I₃ + MagicFunction.a.RadialFunctions.I₄
      + MagicFunction.a.RadialFunctions.I₅ + MagicFunction.a.RadialFunctions.I₆ := by
  ext x
  simp [a, a', MagicFunction.a.RadialFunctions.I₁, MagicFunction.a.RadialFunctions.I₂,
    MagicFunction.a.RadialFunctions.I₃, MagicFunction.a.RadialFunctions.I₄,
    MagicFunction.a.RadialFunctions.I₅, MagicFunction.a.RadialFunctions.I₆,
    sq_nonneg ‖x‖, add_assoc]

/-- Expand `a` as the sum of the six Schwartz integrals. -/
public theorem a_eq_sum_integrals_SchwartzIntegrals :
    a = MagicFunction.a.SchwartzIntegrals.I₁ + MagicFunction.a.SchwartzIntegrals.I₂
      + MagicFunction.a.SchwartzIntegrals.I₃ + MagicFunction.a.SchwartzIntegrals.I₄
      + MagicFunction.a.SchwartzIntegrals.I₅ + MagicFunction.a.SchwartzIntegrals.I₆ :=
  rfl

end MagicFunction.FourierEigenfunctions

end

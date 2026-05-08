/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module

public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.b.Basic
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ1
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ2
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ3
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ4
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ6.Bounds

/-!
# `b` is a Schwartz function

Builds Schwartz functions from the radial integrals `J₁', ..., J₆'` and assembles the
`(-1)`-Fourier eigenfunction `b`. On `ℝ`, radial profiles are only used at `r = ‖x‖^2 ≥ 0`; a
smooth cutoff yields global Schwartz functions on `ℝ` without changing induced functions on `ℝ⁸`.
-/

noncomputable section

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

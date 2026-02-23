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

This file builds Schwartz functions from the radial integrals `J₁', ..., J₆'` and assembles the
`(-1)`-Fourier eigenfunction `b`.

## Main definitions
* `MagicFunction.b.SchwartzIntegrals.J₁'` (and `J₂'`, ..., `J₆'`)
* `MagicFunction.FourierEigenfunctions.b'`, `MagicFunction.FourierEigenfunctions.b`
-/

-- NOTE: On `ℝ`, the radial profiles are only used at `r = ‖x‖^2 ≥ 0`. We therefore use a smooth
-- cutoff to build global Schwartz functions on `ℝ` without changing the induced functions on
-- `EuclideanSpace ℝ (Fin 8)`.

noncomputable section

namespace MagicFunction.b.SchwartzProperties

open scoped ContDiff Topology

open MagicFunction MagicFunction.b MagicFunction.b.RealIntegrals
open Set Complex Real

section Smooth

open RealIntegrals

/-! ### Smoothness

Smoothness of the radial integrals is proved in the `SmoothJ*` modules by differentiating under the
integral sign. Here we only repackage those results. -/

theorem J₁'_smooth' : ContDiff ℝ ∞ J₁' := Schwartz.J1Smooth.contDiff_J₁'

theorem J₂'_smooth' : ContDiff ℝ ∞ J₂' := Schwartz.J2Smooth.contDiff_J₂'

theorem J₃'_smooth' : ContDiff ℝ ∞ J₃' := Schwartz.J3Smooth.contDiff_J₃'

theorem J₄'_smooth' : ContDiff ℝ ∞ J₄' := Schwartz.J4Smooth.contDiff_J₄'

theorem J₅'_smooth' : ContDiff ℝ ∞ J₅' := Schwartz.J5Smooth.contDiff_J₅'

theorem J₆'_smooth' :
    ContDiff ℝ ∞ (fun r ↦ RadialSchwartz.cutoffC r * RealIntegrals.J₆' r) := by
  simpa using
    (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1
      (f := RealIntegrals.J₆') MagicFunction.b.Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1)

end Smooth

section Decay

/-! ### One-sided decay bounds

The required Schwartz-type bounds on `0 ≤ r` are proved in the `SmoothJ*` modules; we only repackage
them here. -/

theorem J₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ ≤ C := by
  simpa using MagicFunction.b.Schwartz.J1Smooth.decay_J₁'

theorem J₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₂' x‖ ≤ C := by
  simpa using MagicFunction.b.Schwartz.J2Smooth.decay_J₂'

theorem J₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₃' x‖ ≤ C := by
  simpa using MagicFunction.b.Schwartz.J3Smooth.decay_J₃'

theorem J₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₄' x‖ ≤ C := by
  simpa using MagicFunction.b.Schwartz.J4Smooth.decay_J₄'

theorem J₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₅' x‖ ≤ C := by
  simpa using MagicFunction.b.Schwartz.J5Smooth.decay_J₅'

theorem J₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := by
  simpa using MagicFunction.b.Schwartz.J6Smooth.decay_J₆'

end Decay

end MagicFunction.b.SchwartzProperties

namespace MagicFunction.b.SchwartzIntegrals

open SchwartzMap
open RadialSchwartz.Bridge

private lemma fCut_apply_of_nonneg (f : ℝ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    RadialSchwartz.Bridge.fCut f r = f r := by
  simp [fCut, hr]

/-- The one-dimensional Schwartz function associated to the primed radial integral `J₁'`.

The prime indicates this is the radial profile on `ℝ` (used at `r = ‖x‖ ^ 2`). -/
public def J₁' : 𝓢(ℝ, ℂ) :=
  RadialSchwartz.Bridge.fCutSchwartz (f := MagicFunction.b.RealIntegrals.J₁')
    MagicFunction.b.SchwartzProperties.J₁'_smooth'
    MagicFunction.b.SchwartzProperties.J₁'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `J₂'`.

The prime indicates this is the radial profile on `ℝ` (used at `r = ‖x‖ ^ 2`). -/
public def J₂' : 𝓢(ℝ, ℂ) :=
  RadialSchwartz.Bridge.fCutSchwartz (f := MagicFunction.b.RealIntegrals.J₂')
    MagicFunction.b.SchwartzProperties.J₂'_smooth'
    MagicFunction.b.SchwartzProperties.J₂'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `J₃'`.

The prime indicates this is the radial profile on `ℝ` (used at `r = ‖x‖ ^ 2`). -/
public def J₃' : 𝓢(ℝ, ℂ) :=
  RadialSchwartz.Bridge.fCutSchwartz (f := MagicFunction.b.RealIntegrals.J₃')
    MagicFunction.b.SchwartzProperties.J₃'_smooth'
    MagicFunction.b.SchwartzProperties.J₃'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `J₄'`.

The prime indicates this is the radial profile on `ℝ` (used at `r = ‖x‖ ^ 2`). -/
public def J₄' : 𝓢(ℝ, ℂ) :=
  RadialSchwartz.Bridge.fCutSchwartz (f := MagicFunction.b.RealIntegrals.J₄')
    MagicFunction.b.SchwartzProperties.J₄'_smooth'
    MagicFunction.b.SchwartzProperties.J₄'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `J₅'`.

The prime indicates this is the radial profile on `ℝ` (used at `r = ‖x‖ ^ 2`). -/
public def J₅' : 𝓢(ℝ, ℂ) :=
  RadialSchwartz.Bridge.fCutSchwartz (f := MagicFunction.b.RealIntegrals.J₅')
    MagicFunction.b.SchwartzProperties.J₅'_smooth'
    MagicFunction.b.SchwartzProperties.J₅'_decay'

/-- The one-dimensional Schwartz function associated to the primed radial integral `J₆'`.

The prime indicates this is the radial profile on `ℝ` (used at `r = ‖x‖ ^ 2`). -/
public def J₆' : 𝓢(ℝ, ℂ) where
  toFun := RadialSchwartz.Bridge.fCut MagicFunction.b.RealIntegrals.J₆'
  smooth' := by
    simpa [RadialSchwartz.Bridge.fCut] using MagicFunction.b.SchwartzProperties.J₆'_smooth'
  decay' := by
    simpa using
      (RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
        (f := MagicFunction.b.RealIntegrals.J₆')
        (hg_smooth := MagicFunction.b.SchwartzProperties.J₆'_smooth')
        MagicFunction.b.SchwartzProperties.J₆'_decay')

/-- The Schwartz function on `ℝ⁸` obtained from the radial profile `J₁'`. -/
@[expose] public def J₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₁'

/-- The Schwartz function on `ℝ⁸` obtained from the radial profile `J₂'`. -/
@[expose] public def J₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₂'

/-- The Schwartz function on `ℝ⁸` obtained from the radial profile `J₃'`. -/
@[expose] public def J₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₃'

/-- The Schwartz function on `ℝ⁸` obtained from the radial profile `J₄'`. -/
@[expose] public def J₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₄'

/-- The Schwartz function on `ℝ⁸` obtained from the radial profile `J₅'`. -/
@[expose] public def J₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₅'

/-- The Schwartz function on `ℝ⁸` obtained from the radial profile `J₆'`. -/
@[expose] public def J₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₆'

/-- On `0 ≤ r`, the Schwartz function `J₁'` agrees with the integral definition. -/
@[simp]
public lemma J₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₁' : ℝ → ℂ) r = MagicFunction.b.RealIntegrals.J₁' r := by
  simpa [J₁', fCutSchwartz] using fCut_apply_of_nonneg (f := RealIntegrals.J₁') hr

/-- On `0 ≤ r`, the Schwartz function `J₂'` agrees with the integral definition. -/
@[simp]
public lemma J₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₂' : ℝ → ℂ) r = MagicFunction.b.RealIntegrals.J₂' r := by
  simpa [J₂', fCutSchwartz] using fCut_apply_of_nonneg (f := RealIntegrals.J₂') hr

/-- On `0 ≤ r`, the Schwartz function `J₃'` agrees with the integral definition. -/
@[simp]
public lemma J₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₃' : ℝ → ℂ) r = MagicFunction.b.RealIntegrals.J₃' r := by
  simpa [J₃', fCutSchwartz] using fCut_apply_of_nonneg (f := RealIntegrals.J₃') hr

/-- On `0 ≤ r`, the Schwartz function `J₄'` agrees with the integral definition. -/
@[simp]
public lemma J₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₄' : ℝ → ℂ) r = MagicFunction.b.RealIntegrals.J₄' r := by
  simpa [J₄', fCutSchwartz] using fCut_apply_of_nonneg (f := RealIntegrals.J₄') hr

/-- On `0 ≤ r`, the Schwartz function `J₅'` agrees with the integral definition. -/
@[simp]
public lemma J₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₅' : ℝ → ℂ) r = MagicFunction.b.RealIntegrals.J₅' r := by
  simpa [J₅', fCutSchwartz] using fCut_apply_of_nonneg (f := RealIntegrals.J₅') hr

/-- On `0 ≤ r`, the Schwartz function `J₆'` agrees with the integral definition. -/
@[simp]
public lemma J₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₆' : ℝ → ℂ) r = MagicFunction.b.RealIntegrals.J₆' r := by
  simpa [J₆'] using fCut_apply_of_nonneg (f := RealIntegrals.J₆') hr

end MagicFunction.b.SchwartzIntegrals
namespace MagicFunction.FourierEigenfunctions

open SchwartzMap

/-- The radial component of the -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[expose] public def b' : 𝓢(ℝ, ℂ) :=
    MagicFunction.b.SchwartzIntegrals.J₁'
  + MagicFunction.b.SchwartzIntegrals.J₂'
  + MagicFunction.b.SchwartzIntegrals.J₃'
  + MagicFunction.b.SchwartzIntegrals.J₄'
  + MagicFunction.b.SchwartzIntegrals.J₅'
  + MagicFunction.b.SchwartzIntegrals.J₆'

/-- The -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[expose] public def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) b'

/-- Expand `b` as a sum of the radial-kernel integrals `MagicFunction.b.RadialFunctions.J₁`-`J₆`. -/
public theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁
  + MagicFunction.b.RadialFunctions.J₂
  + MagicFunction.b.RadialFunctions.J₃
  + MagicFunction.b.RadialFunctions.J₄
  + MagicFunction.b.RadialFunctions.J₅
  + MagicFunction.b.RadialFunctions.J₆ := by
  ext x
  have hr : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
  simp [b, b', MagicFunction.b.RadialFunctions.J₁, MagicFunction.b.RadialFunctions.J₂,
    MagicFunction.b.RadialFunctions.J₃, MagicFunction.b.RadialFunctions.J₄,
    MagicFunction.b.RadialFunctions.J₅, MagicFunction.b.RadialFunctions.J₆, hr, add_assoc]

/-- Expand `b` as a sum of the Schwartz kernels `MagicFunction.b.SchwartzIntegrals.J₁`-`J₆`. -/
public theorem b_eq_sum_integrals_SchwartzIntegrals : b =
    MagicFunction.b.SchwartzIntegrals.J₁
  + MagicFunction.b.SchwartzIntegrals.J₂
  + MagicFunction.b.SchwartzIntegrals.J₃
  + MagicFunction.b.SchwartzIntegrals.J₄
  + MagicFunction.b.SchwartzIntegrals.J₅
  + MagicFunction.b.SchwartzIntegrals.J₆ := by
  rfl

end MagicFunction.FourierEigenfunctions

end

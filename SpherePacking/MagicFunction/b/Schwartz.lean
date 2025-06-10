/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

-- import Mathlib

-- import SpherePacking.ForMathlib.RadialSchwartz.RadialSchwartz
import SpherePacking.MagicFunction.b.Basic

/-! # `b` is a Schwartz Function

The purpose of this file is to prove that `b` is a Schwartz function. It collects results stated elsewhere and presents them concisely.
-/

-- NOTE: We are not ready for the contents of this file. We first need to fix
-- the dimension bridge for Schwartz functions.

#exit

open MagicFunction MagicFunction.b MagicFunction.b.RadialFunctions MagicFunction.b.RealIntegrals
  MagicFunction.Parametrisations

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.b.SchwartzProperties

section Smooth

/-! # `b` is smooth.

There is no reference for this in the blueprint. The idea is to use integrability to differentiate
inside the integrals. The proof path I have in mind is the following.

We need to use the Leibniz Integral Rule to differentiate under the integral sign. This is stated as
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` in `Mathlib.Analysis.Calculus.ParametricIntegral`
-/

theorem J₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₁' := by
  sorry

theorem J₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₂' := by
  sorry

theorem J₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₃' := by
  sorry

theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' := by
  sorry

theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := by
  sorry

theorem J₆'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₆' := by
  sorry

end Smooth

section Decay

/-! # `b` decays faster than any inverse power of the norm squared.

We follow the proof of Proposition 7.8 in the blueprint.
-/

theorem J₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ ≤ C := by
  sorry

theorem J₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₂' x‖ ≤ C := by
  sorry

theorem J₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₃' x‖ ≤ C := by
  sorry

theorem I₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₄' x‖ ≤ C := by
  sorry

theorem I₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n I₅' x‖ ≤ C := by
  sorry

theorem J₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.b.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.b.SchwartzIntegrals

def J₁' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₁'
  smooth' := MagicFunction.b.SchwartzProperties.J₁'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₁'_decay'

def J₂' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₂'
  smooth' := MagicFunction.b.SchwartzProperties.J₂'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₂'_decay'

def J₃' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₃'
  smooth' := MagicFunction.b.SchwartzProperties.J₃'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₃'_decay'

def I₄' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.I₄'
  smooth' := MagicFunction.b.SchwartzProperties.I₄'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.I₄'_decay'

def I₅' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.I₅'
  smooth' := MagicFunction.b.SchwartzProperties.I₅'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.I₅'_decay'

def J₆' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₆'
  smooth' := MagicFunction.b.SchwartzProperties.J₆'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₆'_decay'

def J₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₁'

def J₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₂'

def J₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₃'

def I₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₄'

def I₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₅'

def J₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₆'

end MagicFunction.b.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.b.SchwartzIntegrals.J₁'
  + MagicFunction.b.SchwartzIntegrals.J₂'
  + MagicFunction.b.SchwartzIntegrals.J₃'
  + MagicFunction.b.SchwartzIntegrals.I₄'
  + MagicFunction.b.SchwartzIntegrals.I₅'
  + MagicFunction.b.SchwartzIntegrals.J₆'

/-- The -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) a'

theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁
  + MagicFunction.b.RadialFunctions.J₂
  + MagicFunction.b.RadialFunctions.J₃
  + MagicFunction.b.RadialFunctions.I₄
  + MagicFunction.b.RadialFunctions.I₅
  + MagicFunction.b.RadialFunctions.J₆ := rfl

theorem b_eq_sum_integrals_SchwartzIntegrals : b =
    MagicFunction.b.SchwartzIntegrals.J₁
  + MagicFunction.b.SchwartzIntegrals.J₂
  + MagicFunction.b.SchwartzIntegrals.J₃
  + MagicFunction.b.SchwartzIntegrals.I₄
  + MagicFunction.b.SchwartzIntegrals.I₅
  + MagicFunction.b.SchwartzIntegrals.J₆ := rfl

theorem b'_eq_sum_RealIntegrals : a' =
    MagicFunction.b.RealIntegrals.J₁'
  + MagicFunction.b.RealIntegrals.J₂'
  + MagicFunction.b.RealIntegrals.J₃'
  + MagicFunction.b.RealIntegrals.I₄'
  + MagicFunction.b.RealIntegrals.I₅'
  + MagicFunction.b.RealIntegrals.J₆' := rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap

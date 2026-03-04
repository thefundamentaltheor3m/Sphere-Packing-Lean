/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


-- import Mathlib

public import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import SpherePacking.MagicFunction.b.Basic

@[expose] public section

/-! # `b` is a Schwartz Function

The purpose of this file is to prove that `b` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.
-/

-- NOTE: We are not ready for the contents of this file. We first need to fix
-- the dimension bridge for Schwartz functions.

-- #exit

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

theorem J₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₄' := by
  sorry

theorem J₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₅' := by
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

theorem J₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C := by
  sorry

theorem J₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖ ≤ C := by
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

def J₄' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₄'
  smooth' := MagicFunction.b.SchwartzProperties.J₄'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₄'_decay'

def J₅' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₅'
  smooth' := MagicFunction.b.SchwartzProperties.J₅'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₅'_decay'

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

def J₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₄'

def J₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₅'

def J₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) J₆'

end MagicFunction.b.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b' : 𝓢(ℝ, ℂ) :=
    MagicFunction.b.SchwartzIntegrals.J₁'
  + MagicFunction.b.SchwartzIntegrals.J₂'
  + MagicFunction.b.SchwartzIntegrals.J₃'
  + MagicFunction.b.SchwartzIntegrals.J₄'
  + MagicFunction.b.SchwartzIntegrals.J₅'
  + MagicFunction.b.SchwartzIntegrals.J₆'

/-- The -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) b'

theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁
  + MagicFunction.b.RadialFunctions.J₂
  + MagicFunction.b.RadialFunctions.J₃
  + MagicFunction.b.RadialFunctions.J₄
  + MagicFunction.b.RadialFunctions.J₅
  + MagicFunction.b.RadialFunctions.J₆ := rfl

theorem b_eq_sum_integrals_SchwartzIntegrals : b =
    MagicFunction.b.SchwartzIntegrals.J₁
  + MagicFunction.b.SchwartzIntegrals.J₂
  + MagicFunction.b.SchwartzIntegrals.J₃
  + MagicFunction.b.SchwartzIntegrals.J₄
  + MagicFunction.b.SchwartzIntegrals.J₅
  + MagicFunction.b.SchwartzIntegrals.J₆ := rfl

theorem b'_eq_sum_RealIntegrals : b' =
    MagicFunction.b.RealIntegrals.J₁'
  + MagicFunction.b.RealIntegrals.J₂'
  + MagicFunction.b.RealIntegrals.J₃'
  + MagicFunction.b.RealIntegrals.J₄'
  + MagicFunction.b.RealIntegrals.J₅'
  + MagicFunction.b.RealIntegrals.J₆' := rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap

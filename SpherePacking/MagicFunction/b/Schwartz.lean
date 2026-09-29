/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


-- import Mathlib

public import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import SpherePacking.MagicFunction.b.Basic

/-!
# `b` is a Schwartz Function

The purpose of this file is to prove that `b` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.
-/

@[expose] public section

-- NOTE: We are not ready for the contents of this file. We first need to fix
-- the dimension bridge for Schwartz functions.

-- #exit

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction MagicFunction.b MagicFunction.b.RadialFunctions MagicFunction.b.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.b.ComplexIntegrands MagicFunction.b.RealIntegrands

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

theorem J₁'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖ ≤ C := by
  sorry

theorem J₂'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₂' x‖ ≤ C := by
  sorry

theorem J₃'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₃' x‖ ≤ C := by
  sorry

theorem J₄'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C := by
  sorry

theorem J₅'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖ ≤ C := by
  sorry

theorem J₆'_decayOn :
    ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.b.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.b.RadialSchwartzIntegrals

def J₁' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.b.SchwartzProperties.J₁'_smooth' <| by
  simp only [sub_self]
  exact MagicFunction.b.SchwartzProperties.J₁'_decayOn

def J₂' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.b.SchwartzProperties.J₂'_smooth' <| by
  simp only [sub_self]
  exact MagicFunction.b.SchwartzProperties.J₂'_decayOn

def J₃' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.b.SchwartzProperties.J₃'_smooth' <| by
  simp only [sub_self]
  exact MagicFunction.b.SchwartzProperties.J₃'_decayOn

def J₄' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.b.SchwartzProperties.J₄'_smooth' <| by
  simp only [sub_self]
  exact MagicFunction.b.SchwartzProperties.J₄'_decayOn

def J₅' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.b.SchwartzProperties.J₅'_smooth' <| by
  simp only [sub_self]
  exact MagicFunction.b.SchwartzProperties.J₅'_decayOn

def J₆' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.b.SchwartzProperties.J₆'_smooth' <| by
  simp only [sub_self]
  exact MagicFunction.b.SchwartzProperties.J₆'_decayOn

def J₁ : RadialSchwartzMap ℂ ℝ⁸ ℂ := J₁'.toRadialSchwartzMap ℝ⁸

def J₂ : RadialSchwartzMap ℂ ℝ⁸ ℂ := J₂'.toRadialSchwartzMap ℝ⁸

def J₃ : RadialSchwartzMap ℂ ℝ⁸ ℂ := J₃'.toRadialSchwartzMap ℝ⁸

def J₄ : RadialSchwartzMap ℂ ℝ⁸ ℂ := J₄'.toRadialSchwartzMap ℝ⁸

def J₅ : RadialSchwartzMap ℂ ℝ⁸ ℂ := J₅'.toRadialSchwartzMap ℝ⁸

def J₆ : RadialSchwartzMap ℂ ℝ⁸ ℂ := J₆'.toRadialSchwartzMap ℝ⁸

end MagicFunction.b.RadialSchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b' : 𝓢(ℝ, ℂ) :=
    MagicFunction.b.RadialSchwartzIntegrals.J₁'
  + MagicFunction.b.RadialSchwartzIntegrals.J₂'
  + MagicFunction.b.RadialSchwartzIntegrals.J₃'
  + MagicFunction.b.RadialSchwartzIntegrals.J₄'
  + MagicFunction.b.RadialSchwartzIntegrals.J₅'
  + MagicFunction.b.RadialSchwartzIntegrals.J₆'

/-- The -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b : RadialSchwartzMap ℂ ℝ⁸ ℂ := b'.toRadialSchwartzMap ℝ⁸

theorem b_eq_sum_RadialSchwartzIntegrals : b =
    MagicFunction.b.RadialSchwartzIntegrals.J₁
  + MagicFunction.b.RadialSchwartzIntegrals.J₂
  + MagicFunction.b.RadialSchwartzIntegrals.J₃
  + MagicFunction.b.RadialSchwartzIntegrals.J₄
  + MagicFunction.b.RadialSchwartzIntegrals.J₅
  + MagicFunction.b.RadialSchwartzIntegrals.J₆ := rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap

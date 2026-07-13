/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import SpherePacking.ForMathlib.RadialSchwartz.SmoothCutoff
public import SpherePacking.MagicFunction.b.Basic

/-! # `b` is a Schwartz Function

The purpose of this file is to prove that `b` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.

As with the `Iⱼ'` (see `SpherePacking.MagicFunction.a.Schwartz`), the one-dimensional integrals
`RealIntegrals.J₁', …, J₆' : ℝ → ℂ` are *not* Schwartz functions: they grow exponentially as
`x → -∞` (and the defining integral of `J₆' x` is only known to converge for `x > -1`, via the
bound `‖ψS z‖ ≤ C e^{-π Im z}` of Lemma `lemma:psi-bound` in the blueprint). Only
their restrictions to `[0, ∞)` matter, since the corresponding functions on `ℝ⁸` are obtained by
composing with `‖·‖ ^ 2 ≥ 0`. We therefore multiply each `Jⱼ'` by a smooth transition function
that vanishes on `(-∞, -1/2]` and is identically `1` on `[0, ∞)` (via
`SchwartzMap.ofNonnegDecay` with `a = -1`): the products are Schwartz functions which agree with
the `Jⱼ'` on `[0, ∞)`, and hence give rise, via composition with `‖·‖ ^ 2`, to Schwartz functions
on `ℝ⁸` that are *equal* to the radial functions `RadialFunctions.J₁, …, J₆`.
-/

@[expose] public section

open MagicFunction MagicFunction.b MagicFunction.b.RadialFunctions MagicFunction.b.RealIntegrals
  MagicFunction.Parametrisations

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.b.SchwartzProperties

section Smooth

/-! # Smoothness of the `Jⱼ'`

There is no reference for this in the blueprint. The idea is to use integrability to differentiate
inside the integrals. The proof path I have in mind is the following.

We need to use the Leibniz Integral Rule to differentiate under the integral sign. This is stated as
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` in `Mathlib.Analysis.Calculus.ParametricIntegral`

The integrals `J₁', …, J₅'` are over the compact interval `[0, 1]`, so they are smooth on all of
`ℝ`. The integral `J₆'` is over `[1, ∞)` and, by the bound `‖ψS z‖ ≤ C e^{-π Im z}` (Lemma
`lemma:psi-bound` in the blueprint), its integrand is of size `e^{-(1 + x) π t}`; convergence —
and hence smoothness of `J₆'` — is therefore only guaranteed on `(-1, ∞)`, which is all that is
needed here.
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

/-- `J₆'` is smooth on `(-1, ∞)`. Unlike `J₁', …, J₅'`, the defining integral of `J₆'` is over
the unbounded interval `[1, ∞)`, and the bound `‖ψS z‖ ≤ C e^{-π Im z}` (Lemma
`lemma:psi-bound` in the blueprint) only controls its integrand, of size `e^{-(1 + x) π t}`, for
`x > -1`. -/
theorem J₆'_smoothOn : ContDiffOn ℝ ∞ RealIntegrals.J₆' (Ioi (-1)) := by
  sorry

end Smooth

section Decay

/-! # The `Jⱼ'` decay rapidly on `[0, ∞)`.

We follow the proof of Proposition 7.8 in the blueprint (`prop:b-schwartz`). Note that the decay
statements are restricted to `[0, ∞)`: they are *false* on all of `ℝ`, since the `Jⱼ'` grow
exponentially as `x → -∞`.
-/

theorem J₁'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x ≥ (0 : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ ≤ C := by
  sorry

theorem J₂'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x ≥ (0 : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₂' x‖ ≤ C := by
  sorry

theorem J₃'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x ≥ (0 : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₃' x‖ ≤ C := by
  sorry

theorem J₄'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x ≥ (0 : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₄' x‖ ≤ C := by
  sorry

theorem J₅'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x ≥ (0 : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₅' x‖ ≤ C := by
  sorry

theorem J₆'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x ≥ (0 : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.b.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.b.SchwartzIntegrals

/-! Each `SchwartzIntegrals.Jⱼ'` is the Schwartz function obtained from `RealIntegrals.Jⱼ'` by
multiplying with the smooth transition function `x ↦ Real.smoothTransition (2 * x + 1)`, which
vanishes on `(-∞, -1/2]` and is identically `1` on `[0, ∞)`. In particular
`SchwartzIntegrals.Jⱼ'` agrees with `RealIntegrals.Jⱼ'` on `[0, ∞)` (see
`Jⱼ'_apply_of_nonneg`). -/

def J₁' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.J₁' (-1) (by norm_num)
  SchwartzProperties.J₁'_smooth'.contDiffOn SchwartzProperties.J₁'_decay_nonneg

def J₂' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.J₂' (-1) (by norm_num)
  SchwartzProperties.J₂'_smooth'.contDiffOn SchwartzProperties.J₂'_decay_nonneg

def J₃' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.J₃' (-1) (by norm_num)
  SchwartzProperties.J₃'_smooth'.contDiffOn SchwartzProperties.J₃'_decay_nonneg

def J₄' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.J₄' (-1) (by norm_num)
  SchwartzProperties.J₄'_smooth'.contDiffOn SchwartzProperties.J₄'_decay_nonneg

def J₅' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.J₅' (-1) (by norm_num)
  SchwartzProperties.J₅'_smooth'.contDiffOn SchwartzProperties.J₅'_decay_nonneg

def J₆' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.J₆' (-1) (by norm_num)
  SchwartzProperties.J₆'_smoothOn SchwartzProperties.J₆'_decay_nonneg

lemma J₁'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : J₁' x = RealIntegrals.J₁' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma J₂'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : J₂' x = RealIntegrals.J₂' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma J₃'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : J₃' x = RealIntegrals.J₃' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma J₄'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : J₄' x = RealIntegrals.J₄' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma J₅'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : J₅' x = RealIntegrals.J₅' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma J₆'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : J₆' x = RealIntegrals.J₆' x :=
  ofNonnegDecay_apply_of_nonneg hx

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

/-! Since `‖x‖ ^ 2 ≥ 0`, the eight-dimensional Schwartz functions `Jⱼ` are *equal* to the radial
functions `RadialFunctions.Jⱼ`: this is the Schwartzness of the eight-dimensional integrals. -/

theorem J₁_coe : ⇑J₁ = RadialFunctions.J₁ := funext fun _ ↦ J₁'_apply_of_nonneg (sq_nonneg _)

theorem J₂_coe : ⇑J₂ = RadialFunctions.J₂ := funext fun _ ↦ J₂'_apply_of_nonneg (sq_nonneg _)

theorem J₃_coe : ⇑J₃ = RadialFunctions.J₃ := funext fun _ ↦ J₃'_apply_of_nonneg (sq_nonneg _)

theorem J₄_coe : ⇑J₄ = RadialFunctions.J₄ := funext fun _ ↦ J₄'_apply_of_nonneg (sq_nonneg _)

theorem J₅_coe : ⇑J₅ = RadialFunctions.J₅ := funext fun _ ↦ J₅'_apply_of_nonneg (sq_nonneg _)

theorem J₆_coe : ⇑J₆ = RadialFunctions.J₆ := funext fun _ ↦ J₆'_apply_of_nonneg (sq_nonneg _)

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

theorem b_eq_sum_integrals_SchwartzIntegrals : b =
    MagicFunction.b.SchwartzIntegrals.J₁
  + MagicFunction.b.SchwartzIntegrals.J₂
  + MagicFunction.b.SchwartzIntegrals.J₃
  + MagicFunction.b.SchwartzIntegrals.J₄
  + MagicFunction.b.SchwartzIntegrals.J₅
  + MagicFunction.b.SchwartzIntegrals.J₆ := rfl

theorem b'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : b' x = RealIntegrals.b' x := by
  simp only [b', SchwartzMap.add_apply, SchwartzIntegrals.J₁'_apply_of_nonneg hx,
    SchwartzIntegrals.J₂'_apply_of_nonneg hx, SchwartzIntegrals.J₃'_apply_of_nonneg hx,
    SchwartzIntegrals.J₄'_apply_of_nonneg hx, SchwartzIntegrals.J₅'_apply_of_nonneg hx,
    SchwartzIntegrals.J₆'_apply_of_nonneg hx]
  rfl

/-- The Schwartz function `b` is equal to the radial function
`MagicFunction.b.RadialFunctions.b`: this is the Schwartzness of `b`. -/
theorem b_coe : ⇑b = MagicFunction.b.RadialFunctions.b :=
  funext fun _ ↦ b'_apply_of_nonneg (sq_nonneg _)

theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁
  + MagicFunction.b.RadialFunctions.J₂
  + MagicFunction.b.RadialFunctions.J₃
  + MagicFunction.b.RadialFunctions.J₄
  + MagicFunction.b.RadialFunctions.J₅
  + MagicFunction.b.RadialFunctions.J₆ := by
  rw [b_coe]; rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap

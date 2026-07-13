/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import SpherePacking.ForMathlib.RadialSchwartz.SmoothCutoff
public import SpherePacking.MagicFunction.a.Basic

/-! # `a` is a Schwartz Function

The purpose of this file is to prove that `a` is a Schwartz function. It collects results stated
elsewhere and presents them concisely.

The one-dimensional integrals `RealIntegrals.I₁', …, I₆' : ℝ → ℂ` are *not* Schwartz functions:
they grow exponentially as `x → -∞` (and the defining integral of `I₆' x` is only known to
converge for `x > -2`). Only their restrictions to `[0, ∞)` matter, since the corresponding
functions on `ℝ⁸` are obtained by composing with `‖·‖ ^ 2 ≥ 0`. We therefore multiply each
`Iⱼ'` by a smooth transition function that vanishes on `(-∞, -1]` and is identically `1` on
`[0, ∞)` (via `SchwartzMap.ofNonnegDecay` with `a = -2`): the products are Schwartz functions
which agree with the `Iⱼ'` on `[0, ∞)`, and hence give rise, via composition with `‖·‖ ^ 2`, to
Schwartz functions on `ℝ⁸` that are *equal* to the radial functions `RadialFunctions.I₁, …, I₆`.
-/

@[expose] public section

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.a.SchwartzProperties

section Smooth

/-! # Smoothness of the `Iⱼ'`

There is no reference for this in the blueprint. The idea is to use integrability to differentiate
inside the integrals. The proof path I have in mind is the following.

We need to use the Leibniz Integral Rule to differentiate under the integral sign. This is stated as
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` in `Mathlib.Analysis.Calculus.ParametricIntegral`

The integrals `I₁', …, I₅'` are over the compact interval `[0, 1]`, so they are smooth on all of
`ℝ`. The integral `I₆'` is over `[1, ∞)` and, by the bound
`MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`, its integrand is of size `e^{-(2 + x) π t}`;
convergence — and hence smoothness of `I₆'` — is therefore only guaranteed on `(-2, ∞)`, which
is all that is needed here.
-/

theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' := by
  sorry

theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' := by
  sorry

theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' := by
  have hI : RealIntegrals.I₃' = fun x : ℝ => cexp (2 * π * I * x) * RealIntegrals.I₁' x := by
    ext x
    have hEqOn : EqOn (Φ₃ x) (fun t => cexp (2 * π * I * x) * Φ₁ x t) (uIcc 0 1) := fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have h1 := z₁'_eq_of_mem ht; have h3 := z₃'_eq_of_mem ht
      simp_rw [
        Φ₃_def, Φ₃'_def, Φ₁_def, Φ₁'_def,
        show z₃' t - 1 = I * t by simp [h3],
        show z₃' t = z₁' t + 2 by simp [h1, h3]; ring,
        show z₁' t + 1 = I * t by simp [h1],
        mul_add, Complex.exp_add, mul_comm, mul_left_comm, mul_assoc]
    simpa [I₃', I₁'] using (intervalIntegral.integral_congr (a := 0) (b := 1) hEqOn).trans
      (intervalIntegral.integral_const_mul (cexp (2 * π * I * x)) (f := Φ₁ x) (a := (0 : ℝ))
        (b := 1))
  simpa [hI] using (contDiff_const.mul ofRealCLM.contDiff).cexp.mul I₁'_smooth'

theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' := by
  sorry

theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := by
  sorry

/-- `I₆'` is smooth on `(-2, ∞)`. Unlike `I₁', …, I₅'`, the defining integral of `I₆'` is over
the unbounded interval `[1, ∞)`, and the bound `MagicFunction.PolyFourierCoeffBound.norm_φ₀_le`
only controls its integrand, of size `e^{-(2 + x) π t}`, for `x > -2`. -/
theorem I₆'_smoothOn : ContDiffOn ℝ ∞ RealIntegrals.I₆' (Ioi (-2)) := by
  sorry

end Smooth

section Decay

/-! # The `Iⱼ'` decay rapidly on `[0, ∞)`.

We follow the proof of Proposition 7.8 in the blueprint. Note that the decay statements are
restricted to `[0, ∞)`: they are *false* on all of `ℝ`, since the `Iⱼ'` grow exponentially as
`x → -∞`. The zeroth-order bounds (the case `k = n = 0`) should follow from the already-proven
`MagicFunction.a.IntegralEstimates.Iⱼ.Iⱼ'_bounding` (after integrating the bounding function),
and the higher-order bounds from the same estimates after differentiating under the integral sign.
-/

theorem I₁'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x, (0 : ℝ) ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C := by
  sorry

theorem I₂'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x, (0 : ℝ) ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₂' x‖ ≤ C := by
  sorry

theorem I₃'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x, (0 : ℝ) ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := by
  sorry

theorem I₄'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x, (0 : ℝ) ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₄' x‖ ≤ C := by
  sorry

theorem I₅'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x, (0 : ℝ) ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₅' x‖ ≤ C := by
  sorry

theorem I₆'_decay_nonneg : ∀ (k n : ℕ), ∃ C, ∀ x, (0 : ℝ) ≤ x →
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₆' x‖ ≤ C := by
  sorry

end Decay

end MagicFunction.a.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.a.SchwartzIntegrals

/-! Each `SchwartzIntegrals.Iⱼ'` is the Schwartz function obtained from `RealIntegrals.Iⱼ'` by
multiplying with the smooth transition function `x ↦ Real.smoothTransition (x + 1)`, which
vanishes on `(-∞, -1]` and is identically `1` on `[0, ∞)`. In particular `SchwartzIntegrals.Iⱼ'`
agrees with `RealIntegrals.Iⱼ'` on `[0, ∞)` (see `Iⱼ'_apply_of_nonneg`). -/

def I₁' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.I₁' (-2) (by norm_num)
  SchwartzProperties.I₁'_smooth'.contDiffOn SchwartzProperties.I₁'_decay_nonneg

def I₂' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.I₂' (-2) (by norm_num)
  SchwartzProperties.I₂'_smooth'.contDiffOn SchwartzProperties.I₂'_decay_nonneg

def I₃' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.I₃' (-2) (by norm_num)
  SchwartzProperties.I₃'_smooth'.contDiffOn SchwartzProperties.I₃'_decay_nonneg

def I₄' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.I₄' (-2) (by norm_num)
  SchwartzProperties.I₄'_smooth'.contDiffOn SchwartzProperties.I₄'_decay_nonneg

def I₅' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.I₅' (-2) (by norm_num)
  SchwartzProperties.I₅'_smooth'.contDiffOn SchwartzProperties.I₅'_decay_nonneg

def I₆' : 𝓢(ℝ, ℂ) := .ofNonnegDecay RealIntegrals.I₆' (-2) (by norm_num)
  SchwartzProperties.I₆'_smoothOn SchwartzProperties.I₆'_decay_nonneg

lemma I₁'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : I₁' x = RealIntegrals.I₁' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma I₂'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : I₂' x = RealIntegrals.I₂' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma I₃'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : I₃' x = RealIntegrals.I₃' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma I₄'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : I₄' x = RealIntegrals.I₄' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma I₅'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : I₅' x = RealIntegrals.I₅' x :=
  ofNonnegDecay_apply_of_nonneg hx

lemma I₆'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : I₆' x = RealIntegrals.I₆' x :=
  ofNonnegDecay_apply_of_nonneg hx

def I₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₁'

def I₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₂'

def I₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₃'

def I₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₄'

def I₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₅'

def I₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) I₆'

/-! Since `‖x‖ ^ 2 ≥ 0`, the eight-dimensional Schwartz functions `Iⱼ` are *equal* to the radial
functions `RadialFunctions.Iⱼ`: this is the Schwartzness of the eight-dimensional integrals. -/

theorem I₁_coe : ⇑I₁ = RadialFunctions.I₁ := funext fun _ ↦ I₁'_apply_of_nonneg (sq_nonneg _)

theorem I₂_coe : ⇑I₂ = RadialFunctions.I₂ := funext fun _ ↦ I₂'_apply_of_nonneg (sq_nonneg _)

theorem I₃_coe : ⇑I₃ = RadialFunctions.I₃ := funext fun _ ↦ I₃'_apply_of_nonneg (sq_nonneg _)

theorem I₄_coe : ⇑I₄ = RadialFunctions.I₄ := funext fun _ ↦ I₄'_apply_of_nonneg (sq_nonneg _)

theorem I₅_coe : ⇑I₅ = RadialFunctions.I₅ := funext fun _ ↦ I₅'_apply_of_nonneg (sq_nonneg _)

theorem I₆_coe : ⇑I₆ = RadialFunctions.I₆ := funext fun _ ↦ I₆'_apply_of_nonneg (sq_nonneg _)

end MagicFunction.a.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.SchwartzIntegrals.I₁'
  + MagicFunction.a.SchwartzIntegrals.I₂'
  + MagicFunction.a.SchwartzIntegrals.I₃'
  + MagicFunction.a.SchwartzIntegrals.I₄'
  + MagicFunction.a.SchwartzIntegrals.I₅'
  + MagicFunction.a.SchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
def a : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) a'

theorem a_eq_sum_integrals_SchwartzIntegrals : a =
    MagicFunction.a.SchwartzIntegrals.I₁
  + MagicFunction.a.SchwartzIntegrals.I₂
  + MagicFunction.a.SchwartzIntegrals.I₃
  + MagicFunction.a.SchwartzIntegrals.I₄
  + MagicFunction.a.SchwartzIntegrals.I₅
  + MagicFunction.a.SchwartzIntegrals.I₆ := rfl

theorem a'_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) : a' x = RealIntegrals.a' x := by
  simp only [a', SchwartzMap.add_apply, SchwartzIntegrals.I₁'_apply_of_nonneg hx,
    SchwartzIntegrals.I₂'_apply_of_nonneg hx, SchwartzIntegrals.I₃'_apply_of_nonneg hx,
    SchwartzIntegrals.I₄'_apply_of_nonneg hx, SchwartzIntegrals.I₅'_apply_of_nonneg hx,
    SchwartzIntegrals.I₆'_apply_of_nonneg hx]
  rfl

/-- The Schwartz function `a` is equal to the radial function
`MagicFunction.a.RadialFunctions.a`: this is the Schwartzness of `a`. -/
theorem a_coe : ⇑a = MagicFunction.a.RadialFunctions.a :=
  funext fun _ ↦ a'_apply_of_nonneg (sq_nonneg _)

theorem a_eq_sum_integrals_RadialFunctions : a =
    MagicFunction.a.RadialFunctions.I₁
  + MagicFunction.a.RadialFunctions.I₂
  + MagicFunction.a.RadialFunctions.I₃
  + MagicFunction.a.RadialFunctions.I₄
  + MagicFunction.a.RadialFunctions.I₅
  + MagicFunction.a.RadialFunctions.I₆ := by
  rw [a_coe]; rfl

end MagicFunction.FourierEigenfunctions

end SchwartzMap

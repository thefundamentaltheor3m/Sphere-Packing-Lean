/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SpherePacking.ForMathlib.RadialSchwartz.Basic
public import SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap

/-!
# Multidimensional Radial Schwartz Functions
-/

@[expose] public noncomputable section

open SchwartzMap Function RCLike ContDiff Set

namespace SchwartzMap

section ofDecay

@[fun_prop]
theorem _root_.Complex.contDiff_ofReal {n} : ContDiff ℝ n Complex.ofReal :=
  ContinuousLinearMap.contDiff Complex.ofRealCLM

-- TODO: it suffices to be contdiff on [a, ∞)

/-- A Schwartz map constructed from a smooth function decaying on a subset by multiplying by a
smooth transition function. -/
@[simps!]
def ofDecayOn {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, ℂ) :=
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition (x - a + 1) * f x
  SchwartzMap.mkOfCocompact F' (by fun_prop) <| by
    intro k n
    obtain ⟨C, hC⟩ := decay k n
    use max C 0
    rw [Filter.Eventually, Filter.mem_cocompact]
    use Set.Icc (a - 1) a, isCompact_Icc
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_setOf_eq]
    obtain hx | hx := hx
    · have hEq : F' =ᶠ[nhds x] fun _ ↦ 0 := by
        filter_upwards [eventually_lt_nhds hx] with y hy
        simp only [F', Real.smoothTransition.zero_of_nonpos (by linarith : y - a + 1 ≤ 0),
          Complex.ofReal_zero, zero_mul]
      rw [(hEq.iteratedFDeriv ℝ n).self_of_nhds, iteratedFDeriv_fun_zero]
      simp
    · have hEq : F' =ᶠ[nhds x] f := by
        filter_upwards [eventually_gt_nhds hx] with y hy
        simp only [F', Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ y - a + 1),
          Complex.ofReal_one, one_mul]
      rw [(hEq.iteratedFDeriv ℝ n).self_of_nhds]
      exact (hC x hx.le).trans (le_max_left _ _)

theorem ofDecayOn_eqOn {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    Set.EqOn f (ofDecayOn smooth decay) (Set.Ici a) := by
  grind [ofDecayOn, mkOfCocompact_toFun, Set.EqOn, Real.smoothTransition.eq_one_iff_one_le,
    Complex.ofReal_one, SchwartzMap.mkOfCocompact, mk_apply]

end ofDecay

section toRadial

-- The `‖·‖²` differentiability helpers formerly here are now mathlib's
-- `hasStrictFDerivAt_norm_sq` / `DifferentiableAt.norm_sq` / `Differentiable.norm_sq`.

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[simps!]
def compNormSq (f : 𝓢(ℝ, ℂ)) : 𝓢(F, ℂ) :=
    f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 ℂ] [SMulCommClass ℝ 𝕜 ℂ]

/-- A radial Schwartz map on `F` obtained by composing a Schwartz map on `ℝ` with `‖·‖ ^ 2`. -/
@[simps!]
def toRadialSchwartzMap (f : 𝓢(ℝ, ℂ)) : RadialSchwartzMap 𝕜 F ℂ :=
  RadialSchwartzMap.mk (compNormSq F f) (Function.isRadial_norm_sq F).comp_right

/-- A radial Schwartz map on `F` built from a smooth function on `ℝ` decaying on `[a, ∞)`. -/
@[simps!]
def _root_.RadialSchwartzMap.ofDecay {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    RadialSchwartzMap 𝕜 F ℂ :=
  (ofDecayOn smooth decay).toRadialSchwartzMap F

end toRadial

end SchwartzMap

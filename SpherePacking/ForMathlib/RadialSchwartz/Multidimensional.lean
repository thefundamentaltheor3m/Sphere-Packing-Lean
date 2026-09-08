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
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a - 1 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, ℂ) :=
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition (x - a + 1) * f x
  SchwartzMap.mkOfCocompact F' (by fun_prop) <| by
    intro k n
    obtain ⟨C, hC⟩ := decay k n
    use C
    rw [Filter.Eventually, Filter.mem_cocompact]
    use Set.Icc (a - 1) a, isCompact_Icc
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_setOf_eq]
    obtain hx | hx := hx
    · have h1 : iteratedFDeriv ℝ n F' x = iteratedFDerivWithin ℝ n F' (Iio (a - 1)) x :=
        (iteratedFDerivWithin_of_isOpen _ isOpen_Iio).symm (by simpa)
      have h2 : iteratedFDerivWithin ℝ n F' (Iio (a - 1)) x =
          iteratedFDerivWithin ℝ n 0 (Iio (a - 1)) x := by
        apply iteratedFDerivWithin_congr _ (by grind)
        intro y hy
        simp only [Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero, F']
        grind [Real.smoothTransition.zero_iff_nonpos]
      rw [h1, h2]
      grw [← hC (a - 1) (by simp)]
      simp only [Real.norm_eq_abs, iteratedFDerivWithin_zero, Pi.zero_apply, norm_zero, mul_zero]
      positivity
    · have : iteratedFDeriv ℝ n F' x = iteratedFDeriv ℝ n f x := by calc
        _ = iteratedFDerivWithin ℝ n F' (Ioi a) x :=
            (iteratedFDerivWithin_of_isOpen _ isOpen_Ioi).symm (by grind)
        _ = iteratedFDerivWithin ℝ n f (Ioi a) x := by
            apply iteratedFDerivWithin_congr _ (by grind)
            grind [Set.EqOn, Real.smoothTransition.eq_one_iff_one_le, Complex.ofReal_one]
        _ = iteratedFDeriv ℝ n f x :=
            iteratedFDerivWithin_of_isOpen _ isOpen_Ioi (by grind)
      grind

theorem ofDecayOn_eqOn {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a - 1 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
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
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a - 1 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    RadialSchwartzMap 𝕜 F ℂ :=
  (ofDecayOn smooth decay).toRadialSchwartzMap F

end toRadial

end SchwartzMap

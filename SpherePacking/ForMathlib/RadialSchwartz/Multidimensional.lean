/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Making a radial Schwartz map
-/
@[expose] public section

open SchwartzMap Function RCLike

section SchwartzMap_multidimensional_of_schwartzMap_real

-- The `‖·‖²` differentiability helpers formerly here are now mathlib's
-- `hasStrictFDerivAt_norm_sq` / `DifferentiableAt.norm_sq` / `Differentiable.norm_sq`.

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

@[simps!]
noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

@[fun_prop]
theorem contDiff_ofReal {n} : ContDiff ℝ n Complex.ofReal :=
  ContinuousLinearMap.contDiff Complex.ofRealCLM

open ContDiff Set
-- TODO: it suffices to be contdiff on [a, ∞)
theorem eq_schwartzMap {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a - 1 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∃ F : 𝓢(ℝ, ℂ), Set.EqOn f F (Set.Ici a) := by
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition (x - a + 1) * f x
  refine ⟨SchwartzMap.mkOfCocompact F' (by fun_prop) ?_, ?_⟩
  · intro k n
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
  · grind [mkOfCocompact_toFun, Set.EqOn, Real.smoothTransition.eq_one_iff_one_le,
      Complex.ofReal_one, SchwartzMap.mkOfCocompact, mk_apply]

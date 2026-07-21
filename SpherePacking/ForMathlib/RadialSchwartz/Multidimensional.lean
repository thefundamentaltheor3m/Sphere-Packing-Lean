/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib -- TODO: less broad import

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

end SchwartzMap_multidimensional_of_schwartzMap_real

-- def SchwartzMap.of_nonneg

open ContDiff

@[simp]
lemma SchwartzMap.mk_apply {f : ℝ → ℂ} {smooth : ContDiff ℝ ∞ f}
    {decay : ∀ (k n : ℕ), ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C} (x : ℝ) :
  (⟨f, smooth, decay⟩ : 𝓢(ℝ, ℂ)) x = f x := rfl

-- TODO: generalize away from ℝ, ℂ
-- TODO: think about if contdiff can be restricted
open Filter Topology
@[simps]
def SchwartzMap.mkOfCocompact (f : ℝ → ℂ) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in cocompact ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := smooth
  decay' k n := by
    specialize decay k n
    obtain ⟨C, hC⟩ := decay
    rw [Filter.Eventually, Filter.mem_cocompact] at hC
    obtain ⟨t, ht, ht'⟩ := hC
    rw [Set.subset_def] at ht'
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at ht'
    let g : ℝ → ℝ := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have : Continuous g := by
      apply Continuous.mul
      · fun_prop
      have := smooth.continuous_iteratedFDeriv (m := n) (WithTop.coe_le_coe.2 (by simp))
      fun_prop
    obtain ⟨C', hC'⟩ := ht.exists_bound_of_continuousOn this.continuousOn
    simp only [norm_mul, norm_pow, norm_norm, g] at hC'
    use max C C'
    grind

open Set
-- TODO: it suffices for decay to hold coboundedly
-- TODO: it suffices to be contdiff on [a, ∞)
theorem eq_schwartzMap {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a - 1 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∃ F : 𝓢(ℝ, ℂ), Set.EqOn f F (Set.Ici a) := by
  -- sorry
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition (x - a + 1) * f x
  refine ⟨SchwartzMap.mkOfCocompact F' ?_ ?_, ?_⟩
  · simp only [F']
    apply ContDiff.mul
    · have := Real.smoothTransition.contDiff (n := ⊤)
      apply ContDiff.fun_comp
      · exact ContinuousLinearMap.contDiff Complex.ofRealCLM
      fun_prop
    · exact smooth
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
        simp only [mem_Iio] at hy
        simp only [Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero,
          Real.smoothTransition.zero_iff_nonpos, F']
        grind
      rw [h1, h2]
      simp only [Real.norm_eq_abs, iteratedFDerivWithin_zero, Pi.zero_apply, norm_zero, mul_zero,
        ge_iff_le]
      have := hC (a - 1) (by simp)
      grw [← this]
      positivity
    · have : iteratedFDeriv ℝ n F' x = iteratedFDeriv ℝ n f x := by calc
        _ = iteratedFDerivWithin ℝ n F' (Ioi a) x :=
          (iteratedFDerivWithin_of_isOpen _ isOpen_Ioi).symm (by grind)
        _ = iteratedFDerivWithin ℝ n f (Ioi a) x := by
          apply iteratedFDerivWithin_congr _ (by grind)
          intro y hy
          simp only [mem_Ioi] at hy
          simp only [F']
          rw [Real.smoothTransition.eq_one_iff_one_le.2]
          · simp
          grind
        _ = iteratedFDeriv ℝ n f x :=
          (iteratedFDerivWithin_of_isOpen _ isOpen_Ioi) (by grind)
      grind
  · intro x hx
    simp only [SchwartzMap.mkOfCocompact, mk_apply, F']
    simp only [Set.mem_Ici] at hx
    rw [Real.smoothTransition.eq_one_iff_one_le.2]
    · simp
    grind

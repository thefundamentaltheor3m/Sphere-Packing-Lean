/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Auxiliary lemmas for `SchwartzMap`

This file collects small lemmas and constructors for `SchwartzMap` that are missing from
Mathlib, in particular a constructor `SchwartzMap.mkOfCocompact` which builds a Schwartz map
from a decay condition that only needs to hold eventually at infinity (cocompactly), rather
than for all `x`.
-/

open ContDiff SchwartzMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp]
public lemma SchwartzMap.mk_apply {f : E → F} {smooth : ContDiff ℝ ∞ f}
    {decay : ∀ (k n : ℕ), ∃ C : ℝ, ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C} (x : E) :
  (⟨f, smooth, decay⟩ : 𝓢(E, F)) x = f x := rfl

@[simp]
public lemma natCast_le_coe_top {n : ℕ} : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) :=
  WithTop.coe_le_coe.2 (by simp)

open Filter Topology

/-- Construct a `SchwartzMap` from a smooth function `f` whose Schwartz decay bounds only need
to hold eventually at infinity (i.e. cocompactly), rather than for every `x`. This relaxes the
hypothesis of the anonymous-constructor form `⟨f, smooth, decay⟩`, since on a bounded region a
continuous function is automatically bounded. -/
@[expose, simps]
public def SchwartzMap.mkOfCocompact (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(E, F) where
  toFun := f
  smooth' := smooth
  decay' k n := by
    obtain ⟨C, hC⟩ := decay k n
    rw [Filter.Eventually, Filter.mem_cocompact] at hC
    obtain ⟨t, ht, ht'⟩ := hC
    simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_setOf_eq] at ht'
    set g : E → ℝ := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have : Continuous g := by
      apply Continuous.mul
      · fun_prop
      have := smooth.continuous_iteratedFDeriv (m := n) (by simp)
      fun_prop
    obtain ⟨C', hC'⟩ := ht.exists_bound_of_continuousOn this.continuousOn
    simp only [norm_mul, norm_pow, norm_norm, g] at hC'
    use max C C'
    grind

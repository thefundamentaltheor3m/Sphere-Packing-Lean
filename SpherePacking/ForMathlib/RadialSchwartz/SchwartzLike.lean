/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! # Schwartz-Like Functions

The purpose of this file is to fix the dimension bridge for Schwartz functions. It is not a priori
clear that this is the right way to go about it (might be easier to relax conditions in
`SchwartzMap.compCLM` and compose a function in r² with the norm instead of composing a function in
r with the norm squared), but based on a few discussions, I feel like this may be useful to do. We
can decide at a later stage if we want to do this here or elsewhere.
-/

open Set SchwartzMap Function RCLike Real

open scoped ContDiff

noncomputable section Preliminaries

-- variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

structure SchwartzLikeMap (S : Set ℝ) where
  toFun : ℝ → ℂ
  uniqueDiffOn : UniqueDiffOn ℝ S := by simp
  smooth' : ContDiffOn ℝ ∞ toFun S
  decay' : ∀ k n : ℕ, ∃ C : ℝ, ∀ x ∈ S, ‖x‖ ^ ((k : ℝ) / 2) *
    ‖iteratedFDerivWithin ℝ n toFun (Ici 0) x‖ ≤ C

def exp_neg_SchwartzLike {K : ℝ} (hk : K > 0) : SchwartzLikeMap (Ici 0) where
  toFun := fun x ↦ exp (-K * x)
  uniqueDiffOn := uniqueDiffOn_Ici 0
  smooth' := by sorry
  decay' := by
    sorry

variable {S : Set ℝ}

instance : CoeFun (SchwartzLikeMap S) fun _ ↦ ℝ → ℂ where
  coe := SchwartzLikeMap.toFun

end Preliminaries

-- noncomputable section SchwartzMap

-- variable (d : ℕ) {S : Set ℝ} (g : SchwartzLikeMap S)

-- def SchwartzLikeMap.comp_norm_sq_SchwartzMap : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) where
--   toFun := fun x ↦ g (‖x‖ ^ 2)
--   smooth' := hsmooth d hContDiffOn
--   decay' := by
--     intro k n
--     obtain ⟨C, hC⟩ := hC d hdecay n k
--     use n.factorial * C * 2 ^ n
--     intro x
--     specialize hC x
--     -- specialize hC (‖x‖ ^ 2)
--     -- simp only [mem_Ici, norm_nonneg, pow_nonneg, norm_pow, norm_norm, forall_const] at hC
--     -- rw [h_pow d x k, Real.rpow_natCast] at hC
--     rw [← iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_univ
--       (ContDiff.contDiffAt <| (contDiff_infty.mp (hsmooth d hContDiffOn)) n) (mem_univ x)]
--     wlog hk_ne_zero : k ≠ 0
--     · simp only [ne_eq, Decidable.not_not] at hk_ne_zero
--       simp only [hk_ne_zero, pow_zero, one_mul] at hC ⊢
--       exact norm_iteratedFDerivWithin_comp_le hContDiffOn (hf d) (hn n) ht (hs d) (hst d) (x := x)
--         (by simp) hC (hD d x n)
--     wlog hx_ne_zero : x ≠ 0
--     · simp only [ne_eq, Decidable.not_not] at hx_ne_zero
--       specialize hC n le_rfl
--       rw [hx_ne_zero, norm_zero, zero_pow hk_ne_zero, zero_mul] at hC ⊢
--       positivity
--     have hx_pos : 0 < ‖x‖ ^ k := by positivity
--     have hC' : ∀ i ≤ n,
--         ‖iteratedFDerivWithin ℝ i g (Ici 0) ((fun x ↦ ‖x‖ ^ 2) x)‖ ≤ C / (‖x‖ ^ k) := by
--       intro i hi
--       specialize hC i hi
--       rw [mul_comm, ← le_div_iff₀ hx_pos (c := ‖x‖ ^ k) (b := C)] at hC
--       exact hC
--     conv_lhs => rw [mul_comm]
--     rw [← le_div_iff₀ hx_pos (c := ‖x‖ ^ k)]
--     have hrearrange : n.factorial * C * 2 ^ n / ‖x‖ ^ k = ↑n.factorial * (C / ‖x‖ ^ k) * 2 ^ n := by
--       field_simp
--     rw [hrearrange]
--     exact norm_iteratedFDerivWithin_comp_le hContDiffOn (hf d) (hn n) ht (hs d) (hst d) (x := x)
--       (by simp) hC' (hD d x n)

-- end SchwartzMap

#min_imports

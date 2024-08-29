/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import Mathlib

/-!
This file proves lemmas involving the summability of functions that decay in a manner comparable to
inverse powers of the norm function on subsets of Euclidean space.
-/

variable {d : ℕ}

open BigOperators Complex Real

section Definitions

-- Consider putting this in `EuclideanSpace` namespace
@[simp]
def Inv_Pow_Norm_Summable_Over_Set_Euclidean (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ (d + 1))

-- TODO: Remove after proving that d + 1 does, indeed, work.
-- Else, use as hack for `Summable_of_Inv_Pow_Summable'`.
def Exists_Inv_Pow_Norm_Summable_Over_Set_Euclidean (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ k > 0, Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖^k)

def IsDecayingMap {X : Set (EuclideanSpace ℝ (Fin d))} (f : X → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ x : X, ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k * ‖f x‖ ≤ C

end Definitions

namespace DecayingMap

section Subtype

variable {X : Set (EuclideanSpace ℝ (Fin d))} {f : X → ℝ} (hf : IsDecayingMap f)

-- I want to say that the composition of a decaying map with `Subtype.val` is a decaying map.
-- The reason I need this is so that I can do summability after excluding zero from the set

-- theorem Decaying_over_compl_finset (s : Finset X) : IsDecayingMap
-- (fun (x : (({x : X // x ∉ s} : Set X) : Set (EuclideanSpace ℝ (Fin d)))) => f x) := by
--   sorry

-- lemma comp_Subtype_val (Y : Subtype X) : IsDecayingMap (fun y : Y.val => f y) := by
--   sorry

end Subtype

section EuclideanSpace

variable {f : EuclideanSpace ℝ (Fin d) → ℝ}
  (hf : IsDecayingMap (fun x : (⊤ : Set (EuclideanSpace ℝ (Fin d))) => f x))

include hf

theorem Summable_of_Inv_Pow_Summable' {X : Set (EuclideanSpace ℝ (Fin d))}
  (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X) (hne_zero : 0 ∉ X) :
  Summable (fun x : X => f x) := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  let k := d + 1
  have hk' : 0 < k := by positivity
  rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean] at hX
  simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs] at hX
  obtain ⟨C, hC⟩ := hf k
  simp only [Set.top_eq_univ, Real.norm_eq_abs, Subtype.forall, Set.mem_univ, true_implies] at hC
  have hC_nonneg : 0 ≤ C := by
    specialize hC (0 : EuclideanSpace ℝ (Fin d))
    rw [norm_zero, zero_pow (Nat.not_eq_zero_of_lt hk'), zero_mul] at hC
    exact hC
  have haux₁ : 0 < C + 1 := by linarith
  specialize hX (ε / (C + 1)) (div_pos hε haux₁)
  obtain ⟨s, hs⟩ := hX
  use s
  intro t ht
  specialize hs t ht
  suffices htriangle : ∑ x ∈ t, |f ↑x| < ε
  · refine lt_of_le_of_lt ?_ htriangle
    rw [Real.norm_eq_abs]
    exact Finset.abs_sum_le_sum_abs (fun i : X ↦ f ↑i) t
  have haux₂ : |∑ x ∈ t, (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹| < ε := by
    rw [← Finset.mul_sum, IsAbsoluteValue.abv_mul (fun (x : ℝ) ↦ |x|) _ _, abs_of_pos haux₁]
    exact (lt_div_iff' haux₁).mp hs
  refine lt_of_le_of_lt ?_ haux₂
  have haux₃ : ∀ x ∈ t, (0 : ℝ) ≤ (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹ := by
    intro x _
    apply mul_nonneg
    · linarith
    · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
  rw [Finset.abs_sum_of_nonneg haux₃]
  cases t.eq_empty_or_nonempty
  · case inl hempty =>
    rw [hempty, Finset.sum_empty, Finset.sum_empty]
  · case inr hnonempty =>
    apply Finset.sum_le_sum
    intro x _
    have haux₄ : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      apply hne_zero
      rw [← h]
      exact Subtype.coe_prop x
    have haux₅ : 0 < (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k) := by
      apply pow_pos
      exact norm_pos_iff'.mpr haux₄
    refine le_of_mul_le_mul_of_pos_right ?_ haux₅
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (ne_of_gt haux₅), mul_one]
    specialize hC x
    refine LE.le.trans hC ?_
    rw [le_add_iff_nonneg_right]
    exact zero_le_one

-- lemma comp_Subtype_val {X : Set (EuclideanSpace ℝ (Fin d))} (s : Subtype X) :

theorem Summable_of_Inv_Pow_Summable
  (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X) :
  Summable (fun x : X => f x) := by
  if hzero : 0 ∈ X then
    let s : Finset (X) := {⟨0, hzero⟩}
    rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean] at hX
    rw [← (Finset.summable_compl_iff s)] at hX ⊢
    let t := {x : X // x ∉ s}
    have htaux₁ : t = {x : X // x ≠ ⟨0, hzero⟩} := by simp only [t, s, Finset.mem_singleton, ne_eq]
    -- have htaux₂ : ⟨0, hzero⟩ ∉ t := by
    --   sorry
    
    -- have htaux₂ : (0 : EuclideanSpace ℝ (Fin d)) ∉ t := sorry
    -- rw [← Inv_Pow_Norm_Summable_Over_Set_Euclidean] at hX
    -- refine Summable_of_Inv_Pow_Summable' (f ∘ Subtype.val) ?_ ?_

    sorry
  else
    exact Summable_of_Inv_Pow_Summable' hf hX hzero

end EuclideanSpace

end DecayingMap

section Schwartz

namespace SchwartzMap

variable (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)

lemma IsDecaying : IsDecayingMap (fun x : (⊤ : Set (EuclideanSpace ℝ (Fin d))) => f x) := by
  intro k
  obtain ⟨C, hC⟩ := f.decay' k 0
  use C
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hC
  simp only [Set.top_eq_univ, Real.norm_eq_abs, Subtype.forall, Set.mem_univ, true_implies]
  exact hC

theorem Summable_of_Inv_Pow_Summable' -- (P : PeriodicSpherePacking d)
  {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X)
  (hne_zero : 0 ∉ X) : Summable (fun x : X => f x) :=
  DecayingMap.Summable_of_Inv_Pow_Summable' (f.IsDecaying) hX hne_zero

end SchwartzMap

end Schwartz

/- *TODO:* Move to `SpherePacking/CohnElkies/Prereqs.lean`
namespace PeriodicSpherePacking

lemma Summable_Inverse_Powers (P : PeriodicSpherePacking d) :
  Inv_Pow_Norm_Summable_Over_Set_Euclidean P.centers := by
  rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean]
  simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs]
  · intro ε hε
    -- Translating and scaling fundamental domains could be a good idea - discussion with Bhavik
    sorry

end PeriodicSpherePacking
-/

/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib

-- TODO: run #min_imports once file completed
import Mathlib.Analysis.Distribution.SchwartzSpace

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' D E F G V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

section TemperateGrowthOn

def Function.HasTemperateGrowthOn (f : E → F) (S : Set E) : Prop :=
  ContDiffOn ℝ ∞ f S ∧
  ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ x ∈ S, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ k

theorem Function.HasTemperateGrowthOn.norm_iteratedFDeriv_le_uniform_aux {f : E → F} {S : Set E}
    (hf_temperate : f.HasTemperateGrowthOn S) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ N ≤ n, ∀ x ∈ S, ‖iteratedFDeriv ℝ N f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  choose k C hf using hf_temperate.2
  use (Finset.range (n + 1)).sup k
  let C' := max (0 : ℝ) ((Finset.range (n + 1)).sup' (by simp) C)
  have hC' : 0 ≤ C' := le_max_left _ _
  use C', hC'
  intro N hN x hx
  rw [← Finset.mem_range_succ_iff] at hN
  grw [hf]
  gcongr
  · simp only [C', Finset.le_sup'_iff, le_max_iff]
    right
    exact ⟨N, hN, le_rfl⟩
  · simp
  · exact Finset.le_sup hN
  · exact hx

end TemperateGrowthOn

section Even

/-! Let's try proving smoothness here. First, a famous result of Whitney: https://projecteuclid.org/journals/duke-mathematical-journal/volume-10/issue-1/Differentiable-even-functions/10.1215/S0012-7094-43-01015-4.full -/

open Function Real
open Filter

variable {f : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ f) (heven : f.Even)

example (x : ℝ) : √(x ^ 2) = |x| := sqrt_sq_eq_abs x

include heven in
lemma Function.Even.comp_abs : f = f ∘ abs := by
  ext x; by_cases hx : x ≥ 0
  · congr; exact (abs_of_nonneg hx).symm
  · rw [ge_iff_le, not_le] at hx
    rw [comp_apply, abs_of_neg hx]
    exact (heven x).symm

include heven in
lemma Function.Even.comp_abs_apply (x : ℝ) : f x = f |x| := by
  conv_lhs => rw [heven.comp_abs]
  rw [comp_apply]

include heven in
lemma Function.Even.HasDeriv_at_zero : deriv f (0 : ℝ) = 0 := by
  wlog hdiff : DifferentiableAt ℝ f 0
  · rw [← differentiableWithinAt_univ] at hdiff
    rw [deriv, fderiv, fderivWithin]
    simp [hdiff]
  -- simp
  suffices deriv f 0 = -deriv f 0 by linarith
  -- apply HasDerivAt.deriv
  -- rw [hasDerivAt_iff_tendsto_slope_zero]
  -- have hHasDerivAt : HasDerivAt f (deriv f 0) 0 := hdiff.hasDerivAt
  have hrw {t : ℝ} : f (-t) - f 0 = f t - f 0 := by rw [heven]
  have hlim₁ : Tendsto (fun t ↦ t⁻¹ • (f (0 + t) - f 0)) (nhdsWithin 0 {0}ᶜ) (nhds (deriv f 0)) :=
    hasDerivAt_iff_tendsto_slope_zero.mp hdiff.hasDerivAt
  simp only [zero_add, smul_eq_mul] at hlim₁
  have hlim₂ : Tendsto (fun t ↦ -((t)⁻¹ * (f t - f 0))) (nhdsWithin 0 {0}ᶜ) (nhds (-deriv f 0)) :=
    hlim₁.neg
  -- do tendsto comp or something - use fact that x ↦ -x tends to 0 as you go to 0 or smth
  sorry

include hsmooth heven in
theorem Function.Even.eq_smooth_comp_sq_of_smooth : ∃ g : ℝ → ℝ, f = g ∘ (fun x => x ^ 2) ∧
    ContDiff ℝ ∞ g := by
  refine ⟨f ∘ sqrt, ?_, ?_⟩
  · ext x
    simp only [heven.comp_abs_apply x, comp_apply, sqrt_sq_eq_abs x]
  · -- Reduce to zero case
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ≠ 0
    · exact ContDiff.comp_contDiffAt x hsmooth <| contDiffAt_sqrt hx
    · rw [ne_eq, Decidable.not_not] at hx
      sorry

end Even

section SmoothCutoff

open Real

lemma exists_smooth_cutoff_orig :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (∀ x : ℝ, x ≤ -1 → f x = 0) ∧ (∀ x : ℝ, x ≥ 0 → f x = 1) := by
      let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
      refine ⟨bump ∘ rexp ∘ (- · ), bump.contDiff.comp (contDiff_exp.comp contDiff_neg), ?_, ?_⟩
      · intro x hx
        apply bump.zero_of_le_dist
        simp only [bump, Function.comp_apply, dist_zero_right, norm_eq_abs, abs_exp]
        rw [← log_le_iff_le_exp (by norm_num)]
        apply le_trans _ (le_neg_of_le_neg hx)
        rw [log_le_iff_le_exp (by norm_num), ← mul_one 2]
        exact two_mul_le_exp
      · exact fun _ _ ↦ bump.one_of_mem_closedBall (by simpa [bump])


end SmoothCutoff

namespace SchwartzMap

variable (𝕜)
variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

example (x : E) : x ∈ (⊤ : Set E) := trivial

def comp (f : 𝓢(E, F)) {g : D → E} {S : Set D} (hS : UniqueDiffOn ℝ S)
  (hf : ∀ x ∈ Sᶜ, ∀ n : ℕ, iteratedFDeriv ℝ n f (g x) = 0) (hg : g.HasTemperateGrowthOn S)
  (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(D, F) where
  toFun := f ∘ g
  smooth' := by
    refine (f.smooth _).comp ?_

    sorry
  decay' := by
    suffices ∀ n : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ x ∈ S,
        ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (f ∘ g) x‖ ≤
        C * s.sup (schwartzSeminormFamily 𝕜 E F) f by
      -- sorry
      intro k n
      rcases this ⟨k, n⟩ with ⟨s, C, _, h⟩
      use C * (s.sup (schwartzSeminormFamily 𝕜 E F)) f
      intro x
      if hx : x ∈ S then
      · exact h x hx
      else
      · specialize hf x hx n
        -- This simplifies greatly when Sᶜ = {0}, but I want to do it in general
        sorry
    -- stop
    rintro ⟨k, n⟩
    rcases hg.norm_iteratedFDeriv_le_uniform_aux n with ⟨l, C, hC, hgrowth⟩
    rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
    have hCg : 1 ≤ 1 + Cg := by
      refine le_add_of_nonneg_right ?_
      specialize hg_upper' 0
      rw [norm_zero] at hg_upper'
      exact nonneg_of_mul_nonneg_left hg_upper' (by positivity)
    let k' := kg * (k + l * n)
    use Finset.Iic (k', n), (1 + Cg) ^ (k + l * n) * ((C + 1) ^ n * n ! * 2 ^ k'), by positivity
    intro x hx
    let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
    have hg_upper'' : (1 + ‖x‖) ^ (k + l * n) ≤ (1 + Cg) ^ (k + l * n) * (1 + ‖g x‖) ^ k' := by
      rw [pow_mul, ← mul_pow]
      gcongr
      rw [add_mul]
      refine add_le_add ?_ (hg_upper' x)
      nth_rw 1 [← one_mul (1 : ℝ)]
      gcongr
      apply one_le_pow₀
      simp only [le_add_iff_nonneg_right, norm_nonneg]
    have hbound (i) (hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i f (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
      have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity
      rw [le_div_iff₀' hpos]
      change i ≤ (k', n).snd at hi
      exact one_add_le_sup_seminorm_apply le_rfl hi _ _
    have hbound' (i) (hi : i ≤ n) :
        ‖iteratedFDerivWithin ℝ i f ⊤ (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
      -- This must be trivial, surely...
      sorry
    have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
        ‖iteratedFDerivWithin ℝ N g S x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
      stop
      refine (hgrowth N hN₂ x).trans ?_
      rw [mul_pow]
      have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
      gcongr
      · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
      · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
        simp only [le_add_iff_nonneg_right, norm_nonneg]
    have hbound_aux_1 : UniqueDiffOn ℝ (⊤ : Set E) := by sorry
    have hbound_aux_2 : Set.MapsTo g S (⊤ : Set E) := fun _ _ ↦ trivial
    -- stop -- Proof I'm trying to generalise
    have := norm_iteratedFDerivWithin_comp_le (f.smooth ⊤).contDiffOn hg.1 (mod_cast le_top)
      hbound_aux_1 hS hbound_aux_2 hx hbound' hgrowth'
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
    stop
    -- I think the cases on whether x ∈ S or not should be done way earlier.
    -- Also maybe S should just be the complement of zero... for convenience, if
    -- nothing else...
    grw [hxk, this]
    have rearrange :
      (1 + ‖x‖) ^ k *
          (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
        (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
          ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
      rw [mul_pow, pow_add, ← pow_mul]
      ring
    rw [rearrange]
    have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [← div_le_iff₀ hgxk'] at hg_upper''
    grw [hg_upper'', ← mul_assoc]
    -- End of proof
    stop
    sorry
    stop
    -- Proof I tried before I realised I had to do suffices hbound
    have := norm_iteratedFDerivWithin_comp_le (f.smooth ⊤).contDiffOn hg.1 (mod_cast le_top) (by sorry) hS (by sorry) trivial hbound hgrowth'
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
    grw [hxk, this]
    have rearrange :
      (1 + ‖x‖) ^ k *
          (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
        (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
          ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
      rw [mul_pow, pow_add, ← pow_mul]
      ring
    rw [rearrange]
    have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [← div_le_iff₀ hgxk'] at hg_upper''
    grw [hg_upper'', ← mul_assoc]

    sorry

def compCLM_original {g : D → E} (hg : g.HasTemperateGrowth)
    (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) →L[𝕜] 𝓢(D, F) := by
  refine mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
    (fun f => (f.smooth ⊤).comp hg.1) ?_
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform_aux n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 ≤ 1 + Cg := by
    refine le_add_of_nonneg_right ?_
    specialize hg_upper' 0
    rw [norm_zero] at hg_upper'
    exact nonneg_of_mul_nonneg_left hg_upper' (by positivity)
  let k' := kg * (k + l * n)
  use Finset.Iic (k', n), (1 + Cg) ^ (k + l * n) * ((C + 1) ^ n * n ! * 2 ^ k'), by positivity
  intro f x
  let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
  have hg_upper'' : (1 + ‖x‖) ^ (k + l * n) ≤ (1 + Cg) ^ (k + l * n) * (1 + ‖g x‖) ^ k' := by
    rw [pow_mul, ← mul_pow]
    gcongr
    rw [add_mul]
    refine add_le_add ?_ (hg_upper' x)
    nth_rw 1 [← one_mul (1 : ℝ)]
    gcongr
    apply one_le_pow₀
    simp only [le_add_iff_nonneg_right, norm_nonneg]
  have hbound (i) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
    have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [le_div_iff₀' hpos]
    change i ≤ (k', n).snd at hi
    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
  have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
      ‖iteratedFDeriv ℝ N g x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
    refine (hgrowth N hN₂ x).trans ?_
    rw [mul_pow]
    have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
    gcongr
    · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
    · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
      simp only [le_add_iff_nonneg_right, norm_nonneg]
  have := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hg.1 (mod_cast le_top) x hbound hgrowth'
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
  grw [hxk, this]
  have rearrange :
    (1 + ‖x‖) ^ k *
        (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
      (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
        ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
    rw [mul_pow, pow_add, ← pow_mul]
    ring
  rw [rearrange]
  have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
  rw [← div_le_iff₀ hgxk'] at hg_upper''
  grw [hg_upper'', ← mul_assoc]

end SchwartzMap

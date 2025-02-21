/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import Mathlib

/-! # Fourier Series
The purpose of this file is to include some results on Fourier series.
-/

open Complex Real

variable {U : Set ℂ} (f : U → ℂ) (c : ℕ → ℂ)

def HasFourierSeries : Prop := ∀ (x : U),
  HasSum (fun n ↦ c n * exp (π * I * n * x)) (f x)

def Has2PiFourierSeries : Prop := ∀ (x : U),
  HasSum (fun n ↦ c n * exp (2 * π * I * n * x)) (f x)

section Odd_Even_Trick

open Function

theorem hasFourierSeries_iff_has2PiFourierSeries :
  HasFourierSeries f c ↔ Has2PiFourierSeries f (extend (fun n ↦ 2 * n) c 0) := by
  simp [HasFourierSeries, Has2PiFourierSeries]
  have hinj : Injective (fun n ↦ 2 * n) := Ring.nsmul_right_injective (by positivity)
  constructor
  · intro H x hx
    specialize H x hx
    
    sorry
  sorry

-- theorem HasFourierSeries.has2PiFourierSeries (H : HasFourierSeries f c) :
--     Has2PiFourierSeries f (fun n ↦ (if Odd n then 0 else c (n / 2))) := by
--   rw [HasFourierSeries] at H
--   rw [Has2PiFourierSeries]
--   intro x
--   obtain ⟨H₁, H₂⟩ := H x
--   simp
--   constructor
--   ·
--     -- stop
--     obtain ⟨L, hL⟩ := H₁
--     use L
--     intro ε hε
--     specialize hL hε
--     simp at hL ⊢
--     obtain ⟨a, ha⟩ := hL
--     use Finset.image (fun n => 2 * n) a
--     intro b hb
--     rw [Finset.sum_ite]
--     sorry
--   · rw [H₂]
--     sorry

end Odd_Even_Trick

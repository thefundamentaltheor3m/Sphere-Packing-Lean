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
  Summable (fun n ↦ c n * exp (π * I * n * x)) ∧ f x = ∑' n, c n * exp (n * I * n * x)

def Has2PiFourierSeries : Prop := ∀ (x : U),
  Summable (fun n ↦ c n * exp (2 * π * I * n * x)) ∧ f x = ∑' n, c n * exp (2 * π * I * n * x)

section Odd_Even_Trick

theorem HasFourierSeries.has2PiFourierSeries (H : HasFourierSeries f c) :
    Has2PiFourierSeries f (fun n ↦ (if Odd n then 0 else c (n / 2))) := by
  rw [HasFourierSeries] at H
  rw [Has2PiFourierSeries]
  intro x
  obtain ⟨H₁, H₂⟩ := H x
  simp
  constructor
  ·
    stop
    obtain ⟨L, hL⟩ := H₁
    use L
    intro ε hε
    specialize hL hε
    simp at hL ⊢
    obtain ⟨a, ha⟩ := hL
    use a
    intro b hb
    specialize ha b hb
    sorry
  · rw [H₂]
    sorry

end Odd_Even_Trick

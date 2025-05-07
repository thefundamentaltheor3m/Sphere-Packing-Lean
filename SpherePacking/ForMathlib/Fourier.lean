/-
Copyright (c) 2025 Sidharth Hariharan, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Binomial

/-! # Fourier Series
The purpose of this file is to include some results on Fourier series.
-/

open Complex Real

variable {U : Set ℂ} (f : U → ℂ) (c : ℕ → ℂ)

/--
Predicate for a function `f : U → ℂ` to have `c : ℕ → ℂ` as its fourier series, ie for all `x ∈ U`,
`∑' n, c n * exp (π * I * n * x) = f x`.
Note we write this using `HasSum` to assert that the sum exists and is equal to `f x`.
-/
def HasFourierSeries : Prop := ∀ (x : U), HasSum (fun n ↦ c n * exp (π * I * n * x)) (f x)

/--
Predicate for a function `f : U → ℂ` to have `c : ℕ → ℂ` as its `2π`-fourier series, ie for all
`x ∈ U`, `∑' n, c n * exp (2 * π * I * n * x) = f x`.
Note we write this using `HasSum` to assert that the sum exists and is equal to `f x`.
-/
def Has2PiFourierSeries : Prop := ∀ (x : U),
  HasSum (fun n ↦ c n * exp (2 * π * I * n * x)) (f x)

section Odd_Even_Trick

open Function

theorem hasFourierSeries_iff_has2PiFourierSeries :
    Has2PiFourierSeries f c ↔ HasFourierSeries f (extend (fun n ↦ 2 * n) c 0) := by
  simp only [HasFourierSeries, Subtype.forall, Has2PiFourierSeries]
  apply forall₂_congr
  intro a ha
  have hinj : Injective (fun n ↦ 2 * n) := mul_right_injective₀ two_ne_zero
  rw [← hasSum_extend_zero hinj]
  congr! 2 with n
  rw [apply_extend (· * cexp (π * I * n * a))]
  simp only [Pi.comp_zero, zero_mul, const_zero]
  by_cases h : ∃ i, 2 * i = n
  · obtain ⟨i, rfl⟩ := h
    rw [Injective.extend_apply hinj, Injective.extend_apply hinj]
    simp only [Nat.cast_mul, Nat.cast_ofNat, comp_apply]
    congr! 2
    ring
  · simp [h]

end Odd_Even_Trick

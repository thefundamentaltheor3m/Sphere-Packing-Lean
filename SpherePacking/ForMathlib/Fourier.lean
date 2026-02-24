/-
Copyright (c) 2025 Sidharth Hariharan, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Fourier series

This file collects a few basic results about Fourier series used in this repository.
-/

namespace SpherePacking.ForMathlib.Fourier

open Complex

variable {U : Set ℂ} (f : U → ℂ) (c : ℕ → ℂ)

/-- `HasFourierSeries f c` means that `c` is a Fourier series for `f`, i.e. for every `x : U` we
have `∑' n, c n * exp (π * I * n * x) = f x`.

We use `HasSum` to assert both existence of the series and its value.
-/
@[expose] public def HasFourierSeries : Prop :=
  ∀ (x : U), HasSum (fun n ↦ c n * exp (Real.pi * I * n * x)) (f x)

/-- `Has2PiFourierSeries f c` means that `c` is a `2π`-Fourier series for `f`, i.e. for every
`x : U` we have `∑' n, c n * exp (2 * π * I * n * x) = f x`.

We use `HasSum` to assert both existence of the series and its value.
-/
@[expose] public def Has2PiFourierSeries : Prop :=
  ∀ (x : U), HasSum (fun n ↦ c n * exp (2 * Real.pi * I * n * x)) (f x)

section Odd_Even_Trick

open Function

/-- Relate `2π`-Fourier series to `π`-Fourier series by extending coefficients to even indices. -/
public theorem hasFourierSeries_iff_has2PiFourierSeries :
    Has2PiFourierSeries f c ↔ HasFourierSeries f (extend (fun n ↦ 2 * n) c 0) := by
  simp only [HasFourierSeries, Subtype.forall, Has2PiFourierSeries]
  apply forall₂_congr
  intro a ha
  have hinj : Injective (fun n ↦ 2 * n) := mul_right_injective₀ two_ne_zero
  rw [← hasSum_extend_zero hinj]
  congr! 2 with n
  rw [apply_extend (· * cexp (Real.pi * I * n * a))]
  simp only [Pi.comp_zero, zero_mul, const_zero]
  by_cases h : ∃ i, 2 * i = n
  · obtain ⟨i, rfl⟩ := h
    rw [Injective.extend_apply hinj, Injective.extend_apply hinj]
    simp only [Nat.cast_mul, Nat.cast_ofNat, comp_apply]
    congr! 2
    ring
  · simp [h]

end SpherePacking.ForMathlib.Fourier.Odd_Even_Trick

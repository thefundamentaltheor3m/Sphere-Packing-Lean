/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Non-vanishing of `θ(τ/2, τ)`

`θ(τ/2, τ) ≠ 0` on the upper half plane, in terms of mathlib's two-variable theta function
`jacobiTheta₂` (cf. Mumford, *Tata Lectures on Theta I*, Ch. I, Lemma 4.1). Since
`Θ₂ τ = e^{πiτ/4} θ(τ/2, τ)` (`Θ₂_as_jacobiTheta₂`), this gives `Θ₂_ne_zero`.
-/

@[expose] public section

open Complex

/-- `θ(τ/2, τ) ≠ 0` for `τ` in the upper half plane: the only zeros of `z ↦ θ(z, τ)` are at
`z = 1/2 + τ/2 + m + nτ`. Alternatively, this follows from `Δ = (H₂ H₃ H₄)² / 256` and the
non-vanishing of `Δ` (Blueprint `lemma:theta-nonvanishing`). -/
theorem jacobiTheta₂_half_mul_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta₂ (τ / 2) τ ≠ 0 := by
  sorry

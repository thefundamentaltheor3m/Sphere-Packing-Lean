/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.FG

/-! # The quotients `φ₀`, `φ₂'`, `φ₄'`

This file defines the quotients `φ₀`, `φ₂'`, `φ₄'` of Eisenstein series by the discriminant `Δ`
used to build the magic function (the blueprint's `φ₀`, `φ₋₂`, `φ₋₄`; negative signs cannot appear
in subscripts of identifiers, hence the primes), together with the extension `φ₀''` of `φ₀` to `ℂ`
by zero outside the upper half plane.
-/

@[expose] public section

open UpperHalfPlane Complex

/-- The quotient `(E₂E₄ - E₆)² / Δ`, the blueprint's `φ₀`. -/
noncomputable def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)

/-- The quotient `E₄(E₂E₄ - E₆) / Δ`, the blueprint's `φ₋₂`. -/
noncomputable def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)

/-- The quotient `E₄² / Δ`, the blueprint's `φ₋₄`. -/
noncomputable def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)

/-- The extension of `φ₀` to `ℂ`, vanishing outside the upper half plane. -/
noncomputable def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0

lemma φ₀''_def {z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by simp [φ₀'', hz]

lemma φ₀''_coe_upperHalfPlane (z : ℍ) : φ₀'' (z : ℂ) = φ₀ z := φ₀''_def z.im_pos

theorem φ₀_eq_F_div_disc : φ₀ = F / Δ := by
  ext z
  simp only [Pi.div_apply, φ₀, F, SlashInvariantForm.toFun_eq_coe,
    ModularForm.toSlashInvariantForm_coe, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]

end

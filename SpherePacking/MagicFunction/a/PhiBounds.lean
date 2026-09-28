/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.MagicFunction.a.FourierExpansions

/-!
# Bounds on φ₀, φ₂', φ₄'

Corollary 7.5-7.7 bounds on the phi functions, stated both with explicit constants
(using `DivDiscBound`) and as Big O asymptotics.

## Main Results

### Explicit constant bounds (for Im(z) > 1/2)

- `φ₀_bound`: ‖φ₀ z‖ ≤ C₀ · exp(-2π · Im z)
- `φ₂'_bound`: ‖φ₂' z‖ ≤ C₂
- `φ₄'_bound`: ‖φ₄' z‖ ≤ C₄ · exp(2π · Im z)

### Big O bounds (as Im(z) → ∞)

- `φ₀_isBigO`: φ₀ = O(exp(-2πt)) along imaginary axis
- `φ₂'_isBigO`: φ₂' = O(1) along imaginary axis
- `φ₄'_isBigO`: φ₄' = O(exp(2πt)) along imaginary axis

## Blueprint references

- **Corollary 7.5**: φ₀ bound with exp(-2πt) decay
- **Corollary 7.6**: φ₂' bounded (constant)
- **Corollary 7.7**: φ₄' bound with exp(2πt) growth
-/

@[expose] public section

open Real UpperHalfPlane Asymptotics
open scoped ArithmeticFunction.sigma
open MagicFunction.PolyFourierCoeffBound
open MagicFunction.a.FourierExpansions

noncomputable section

namespace MagicFunction.a

/-! ## Explicit Constants

Each constant factors as `(factor-norm bound) · DivDiscBound (linear coefficient)`, reflecting the
`‖φ‖ = ‖factor‖ · ‖linear/Δ‖` decomposition. -/

/-- Explicit constant for φ₀ bound (Corollary 7.5). -/
def C_φ₀ : ℝ := B_g * DivDiscBound (evenCoeff bg) 2

/-- Explicit constant for φ₂' bound (Corollary 7.6). -/
def C_φ₂' : ℝ := B_E₄ * DivDiscBound (evenCoeff bg) 2

/-- Explicit constant for φ₄' bound (Corollary 7.7). -/
def C_φ₄' : ℝ := B_E₄ * DivDiscBound (evenCoeff bE₄) 0

/-! ## Positivity of Constants -/

lemma divDiscBound_bg_pos : 0 < DivDiscBound (evenCoeff bg) 2 := by
  refine DivDiscBound_pos (evenCoeff bg) 2 ?_ 5 (evenCoeff_poly bg_poly)
  simp [evenCoeff, bg]

lemma divDiscBound_bE₄_pos : 0 < DivDiscBound (evenCoeff bE₄) 0 := by
  refine DivDiscBound_pos (evenCoeff bE₄) 0 ?_ 4 (evenCoeff_poly bE₄_poly)
  simp [evenCoeff, bE₄]

lemma C_φ₀_pos : 0 < C_φ₀ := mul_pos B_g_pos divDiscBound_bg_pos

lemma C_φ₂'_pos : 0 < C_φ₂' := mul_pos B_E₄_pos divDiscBound_bg_pos

lemma C_φ₄'_pos : 0 < C_φ₄' := mul_pos B_E₄_pos divDiscBound_bE₄_pos

/-! ## Explicit Constant Bounds

Each is `‖φ‖ = ‖factor‖ · ‖linear/Δ‖`, combining a factor-norm bound with a quotient bound. -/

/-- Corollary 7.5: φ₀ decays like exp(-2πt) for Im(z) > 1/2. -/
theorem φ₀_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₀ z‖ ≤ C_φ₀ * Real.exp (-2 * π * z.im) := by
  have hfact : φ₀ z = (E₂ z * E₄ z - E₆ z) * ((E₂ z * E₄ z - E₆ z) / Δ z) := by
    simp only [φ₀]; ring
  rw [hfact, C_φ₀, show (-2 * π * z.im : ℝ) = -(2 * π) * z.im by ring]
  exact (norm_mul_le_of_le (norm_g_le z hz.le) (g_div_Δ_bound z hz)).trans_eq (by ring)

/-- Corollary 7.6: φ₂' is bounded for Im(z) > 1/2. -/
theorem φ₂'_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₂' z‖ ≤ C_φ₂' := by
  have hfact : φ₂' z = E₄ z * ((E₂ z * E₄ z - E₆ z) / Δ z) := by simp only [φ₂']; ring
  rw [hfact, C_φ₂']
  exact norm_mul_le_of_le (norm_E₄_le z hz.le) (g_div_Δ_bound z hz)

/-- Corollary 7.7: φ₄' grows at most like exp(2πt) for Im(z) > 1/2. -/
theorem φ₄'_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₄' z‖ ≤ C_φ₄' * Real.exp (2 * π * z.im) := by
  have hfact : φ₄' z = E₄ z * (E₄ z / Δ z) := by simp only [φ₄']; ring
  rw [hfact, C_φ₄']
  exact (norm_mul_le_of_le (norm_E₄_le z hz.le) (E₄_div_Δ_bound z hz)).trans_eq (by ring)

/-! ## Big O Bounds

These express the same bounds as asymptotic estimates along the imaginary axis
(`z = it` as `t → ∞`), using the existing `ResToImagAxis` restriction. -/

/-- Corollary 7.5 (Big O form): `φ₀ = O(exp(-2πt))` as `t → ∞`. -/
theorem φ₀_isBigO : φ₀.resToImagAxis =O[Filter.atTop] (fun t ↦ Real.exp (-2 * π * t)) := by
  rw [Asymptotics.isBigO_iff]; use C_φ₀
  filter_upwards [Filter.eventually_gt_atTop (1 / 2 : ℝ)] with t ht
  have ht' : 0 < t := by linarith
  simpa [ResToImagAxis, ht', UpperHalfPlane.im, Real.norm_eq_abs] using
    φ₀_bound ⟨Complex.I * t, by simp [ht']⟩ (by simpa [UpperHalfPlane.im] using ht)

/-- Corollary 7.6 (Big O form): `φ₂' = O(1)` as `t → ∞`. -/
theorem φ₂'_isBigO : φ₂'.resToImagAxis =O[Filter.atTop] (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]; use C_φ₂'
  filter_upwards [Filter.eventually_gt_atTop (1 / 2 : ℝ)] with t ht
  have ht' : 0 < t := by linarith
  simpa [ResToImagAxis, ht'] using
    φ₂'_bound ⟨Complex.I * t, by simp [ht']⟩ (by simpa [UpperHalfPlane.im] using ht)

/-- Corollary 7.7 (Big O form): `φ₄' = O(exp(2πt))` as `t → ∞`. -/
theorem φ₄'_isBigO : φ₄'.resToImagAxis =O[Filter.atTop] (fun t ↦ Real.exp (2 * π * t)) := by
  rw [Asymptotics.isBigO_iff]; use C_φ₄'
  filter_upwards [Filter.eventually_gt_atTop (1 / 2 : ℝ)] with t ht
  have ht' : 0 < t := by linarith
  simpa [ResToImagAxis, ht', UpperHalfPlane.im, Real.norm_eq_abs] using
    φ₄'_bound ⟨Complex.I * t, by simp [ht']⟩ (by simpa [UpperHalfPlane.im] using ht)

end MagicFunction.a

end

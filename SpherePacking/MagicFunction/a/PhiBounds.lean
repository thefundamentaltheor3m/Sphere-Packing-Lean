/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.MagicFunction.a.FourierExpansions

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

open Real UpperHalfPlane Asymptotics
open MagicFunction.PolyFourierCoeffBound
open MagicFunction.a.FourierExpansions

noncomputable section

namespace MagicFunction.a

/-! ## Explicit Constants

The constants are defined using `DivDiscBound` from the Fourier coefficient machinery. -/

/-- Explicit constant for φ₀ bound (Corollary 7.5). -/
def C_φ₀ : ℝ := DivDiscBound c_E₂E₄E₆ 4

/-- Explicit constant for φ₂' bound (Corollary 7.6).
    Note: Uses c_E₄_E₂E₄E₆ (product coefficient), not c_E₂E₄E₆ (square coefficient). -/
def C_φ₂' : ℝ := DivDiscBound c_E₄_E₂E₄E₆ 2

/-- Explicit constant for φ₄' bound (Corollary 7.7). -/
def C_φ₄' : ℝ := DivDiscBound c_E₄_sq 0

/-! ## Positivity of Constants -/

lemma C_φ₀_pos : 0 < C_φ₀ := by
  refine DivDiscBound_pos c_E₂E₄E₆ 4 ?_ 11 c_E₂E₄E₆_poly
  simp only [c_E₂E₄E₆, toIntCoeff, evenExt, cauchyCoeff, a_E₂E₄E₆]
  -- c_E₂E₄E₆(4) is the Cauchy coefficient at index 2 (since evenExt doubles)
  -- which is a_E₂E₄E₆(1) * a_E₂E₄E₆(1) = (720 * 1 * σ₃(1))² ≠ 0
  sorry

lemma C_φ₂'_pos : 0 < C_φ₂' := by
  refine DivDiscBound_pos c_E₄_E₂E₄E₆ 2 ?_ 10 c_E₄_E₂E₄E₆_poly
  simp only [c_E₄_E₂E₄E₆, toIntCoeff, evenExt, cauchyCoeff, b_E₄, a_E₂E₄E₆]
  sorry

lemma C_φ₄'_pos : 0 < C_φ₄' := by
  refine DivDiscBound_pos c_E₄_sq 0 ?_ 9 c_E₄_sq_poly
  simp only [c_E₄_sq, toIntCoeff, evenExt, cauchyCoeff, b_E₄]
  -- c_E₄_sq(0) is the Cauchy coefficient at index 0
  -- which is b_E₄(0) * b_E₄(0) = 1 * 1 = 1 ≠ 0
  sorry

/-! ## Explicit Constant Bounds

These are the direct bounds from Corollaries 7.5-7.7. -/

/-- Corollary 7.5: φ₀ decays like exp(-2πt) for Im(z) > 1/2. -/
theorem φ₀_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₀ z‖ ≤ C_φ₀ * Real.exp (-2 * π * z.im) := by
  have h := DivDiscBoundOfPolyFourierCoeff z hz c_E₂E₄E₆ 4 (summable_E₂E₄E₆_sq z)
      11 c_E₂E₄E₆_poly (fun z ↦ ((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) E₂E₄E₆_sq_fourier
  simp only [φ₀, C_φ₀]; convert h using 2; ring_nf

/-- Corollary 7.6: φ₂' is bounded for Im(z) > 1/2. -/
theorem φ₂'_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₂' z‖ ≤ C_φ₂' := by
  -- Note: Uses c_E₄_E₂E₄E₆ (product coefficient), not c_E₂E₄E₆ (square coefficient)
  have h := DivDiscBoundOfPolyFourierCoeff z hz c_E₄_E₂E₄E₆ 2 (summable_E₄_E₂E₄E₆ z)
      10 c_E₄_E₂E₄E₆_poly (fun z ↦ E₄ z * (E₂ z * E₄ z - E₆ z)) E₄_E₂E₄E₆_fourier
  simp only [φ₂', C_φ₂']
  calc ‖(E₄ z * (E₂ z * E₄ z - E₆ z)) / Δ z‖
      ≤ DivDiscBound c_E₄_E₂E₄E₆ 2 * Real.exp (-π * (2 - 2) * z.im) := h
    _ = DivDiscBound c_E₄_E₂E₄E₆ 2 * Real.exp 0 := by ring_nf
    _ = DivDiscBound c_E₄_E₂E₄E₆ 2 := by simp

/-- Corollary 7.7: φ₄' grows at most like exp(2πt) for Im(z) > 1/2. -/
theorem φ₄'_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₄' z‖ ≤ C_φ₄' * Real.exp (2 * π * z.im) := by
  have h := DivDiscBoundOfPolyFourierCoeff z hz c_E₄_sq 0 (summable_E₄_sq z)
      9 c_E₄_sq_poly (fun z ↦ E₄ z ^ 2) E₄_sq_fourier
  simp only [φ₄', C_φ₄']; convert h using 2; ring_nf

/-! ## Big O Bounds

These express the same bounds as asymptotic estimates along the imaginary axis
(z = it as t → ∞). We parametrize by t > 0 and construct the corresponding point in ℍ. -/

/-- Helper to construct a point on the imaginary axis. -/
def iAxis (t : ℝ) (ht : 0 < t) : ℍ := ⟨Complex.I * t, by simp [ht]⟩

@[simp] lemma iAxis_im (t : ℝ) (ht : 0 < t) : (iAxis t ht).im = t := by
  simp [iAxis, UpperHalfPlane.im]

/-- φ₀ restricted to imaginary axis as a function of t. -/
def φ₀_iAxis (t : ℝ) : ℂ := if ht : 0 < t then φ₀ (iAxis t ht) else 0

/-- φ₂' restricted to imaginary axis as a function of t. -/
def φ₂'_iAxis (t : ℝ) : ℂ := if ht : 0 < t then φ₂' (iAxis t ht) else 0

/-- φ₄' restricted to imaginary axis as a function of t. -/
def φ₄'_iAxis (t : ℝ) : ℂ := if ht : 0 < t then φ₄' (iAxis t ht) else 0

/-- Corollary 7.5 (Big O form): φ₀ = O(exp(-2πt)) as t → ∞. -/
theorem φ₀_isBigO : φ₀_iAxis =O[Filter.atTop] (fun t ↦ Real.exp (-2 * π * t)) := by
  rw [Asymptotics.isBigO_iff]; use C_φ₀
  filter_upwards [Filter.eventually_gt_atTop (1 / 2 : ℝ)] with t ht
  have ht' : 0 < t := by linarith
  simpa [φ₀_iAxis, ht', Real.norm_eq_abs] using
    φ₀_bound (iAxis t ht') (by simp [iAxis_im]; linarith)

/-- Corollary 7.6 (Big O form): φ₂' = O(1) as t → ∞. -/
theorem φ₂'_isBigO : φ₂'_iAxis =O[Filter.atTop] (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]; use C_φ₂'
  filter_upwards [Filter.eventually_gt_atTop (1 / 2 : ℝ)] with t ht
  have ht' : 0 < t := by linarith
  simpa [φ₂'_iAxis, ht'] using φ₂'_bound (iAxis t ht') (by simp [iAxis_im]; linarith)

/-- Corollary 7.7 (Big O form): φ₄' = O(exp(2πt)) as t → ∞. -/
theorem φ₄'_isBigO : φ₄'_iAxis =O[Filter.atTop] (fun t ↦ Real.exp (2 * π * t)) := by
  rw [Asymptotics.isBigO_iff]; use C_φ₄'
  filter_upwards [Filter.eventually_gt_atTop (1 / 2 : ℝ)] with t ht
  have ht' : 0 < t := by linarith
  simpa [φ₄'_iAxis, ht', Real.norm_eq_abs] using
    φ₄'_bound (iAxis t ht') (by simp [iAxis_im]; linarith)

end MagicFunction.a

end

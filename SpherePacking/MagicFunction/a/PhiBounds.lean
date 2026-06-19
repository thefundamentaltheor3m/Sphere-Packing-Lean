/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
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
  refine DivDiscBound_pos (evenCoeff bg) 2 ?_ 5 (evenCoeff_isBigO bg_isBigO)
  simp [evenCoeff, bg]

lemma divDiscBound_bE₄_pos : 0 < DivDiscBound (evenCoeff bE₄) 0 := by
  refine DivDiscBound_pos (evenCoeff bE₄) 0 ?_ 5 (evenCoeff_isBigO bE₄_isBigO)
  simp [evenCoeff, bE₄]

lemma C_φ₀_pos : 0 < C_φ₀ := mul_pos B_g_pos divDiscBound_bg_pos

lemma C_φ₂'_pos : 0 < C_φ₂' := mul_pos B_E₄_pos divDiscBound_bg_pos

lemma C_φ₄'_pos : 0 < C_φ₄' := mul_pos B_E₄_pos divDiscBound_bE₄_pos

/-! ## Explicit Constant Bounds

Each is `‖φ‖ = ‖factor‖ · ‖linear/Δ‖`, combining a factor-norm bound with a quotient bound. -/

/-- Combine a factor-norm bound with a quotient bound: if `‖a‖ ≤ x` and `‖b‖ ≤ y` (with `0 ≤ x`)
then `‖a · b‖ ≤ x · y`. Each φ-bound below is an instance with `a = factor`, `b = linear/Δ`. -/
lemma norm_mul_le_mul {a b : ℂ} {x y : ℝ} (ha : ‖a‖ ≤ x) (hb : ‖b‖ ≤ y) (hx : 0 ≤ x) :
    ‖a * b‖ ≤ x * y := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) hx

/-- Corollary 7.5: φ₀ decays like exp(-2πt) for Im(z) > 1/2. -/
theorem φ₀_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₀ z‖ ≤ C_φ₀ * Real.exp (-2 * π * z.im) := by
  have hfact : φ₀ z = (E₂ z * E₄ z - E₆ z) * ((E₂ z * E₄ z - E₆ z) / Δ z) := by
    simp only [φ₀]; ring
  rw [hfact, C_φ₀, show (-2 * π * z.im : ℝ) = -(2 * π) * z.im by ring]
  calc ‖(E₂ z * E₄ z - E₆ z) * ((E₂ z * E₄ z - E₆ z) / Δ z)‖
      ≤ B_g * rexp (-(2 * π) * z.im) * DivDiscBound (evenCoeff bg) 2 :=
        norm_mul_le_mul (norm_g_le z hz.le) (g_div_Δ_bound z hz)
          (mul_nonneg B_g_pos.le (Real.exp_pos _).le)
    _ = B_g * DivDiscBound (evenCoeff bg) 2 * rexp (-(2 * π) * z.im) := by ring

/-- Corollary 7.6: φ₂' is bounded for Im(z) > 1/2. -/
theorem φ₂'_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₂' z‖ ≤ C_φ₂' := by
  have hfact : φ₂' z = E₄ z * ((E₂ z * E₄ z - E₆ z) / Δ z) := by simp only [φ₂']; ring
  rw [hfact, C_φ₂']
  exact norm_mul_le_mul (norm_E₄_le z hz.le) (g_div_Δ_bound z hz) B_E₄_pos.le

/-- Corollary 7.7: φ₄' grows at most like exp(2πt) for Im(z) > 1/2. -/
theorem φ₄'_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖φ₄' z‖ ≤ C_φ₄' * Real.exp (2 * π * z.im) := by
  have hfact : φ₄' z = E₄ z * (E₄ z / Δ z) := by simp only [φ₄']; ring
  rw [hfact, C_φ₄']
  calc ‖E₄ z * (E₄ z / Δ z)‖
      ≤ B_E₄ * (DivDiscBound (evenCoeff bE₄) 0 * Real.exp (2 * π * z.im)) :=
        norm_mul_le_mul (norm_E₄_le z hz.le) (E₄_div_Δ_bound z hz) B_E₄_pos.le
    _ = B_E₄ * DivDiscBound (evenCoeff bE₄) 0 * Real.exp (2 * π * z.im) := by ring

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

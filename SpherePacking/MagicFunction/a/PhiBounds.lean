/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.MagicFunction.PolyFourierCoeffBound

/-!
# PhiBounds Structure

Bundles Corollary 7.5-7.7 bounds on φ₀, φ₂', φ₄' as hypotheses.

## Blueprint references

- **Corollary 7.5**: φ₀ bound with exp(-2πt) decay
- **Corollary 7.6**: φ₂' bounded (constant)
- **Corollary 7.7**: φ₄' bound with exp(2πt) growth
-/

open Real UpperHalfPlane

noncomputable section

namespace MagicFunction.a

/-- Bundle of Corollary 7.5-7.7 bounds as hypotheses.
    Blueprint states these for Im(z) > 1/2, which is the condition we use. -/
structure PhiBounds where
  C₀ : ℝ
  C₂ : ℝ
  C₄ : ℝ
  hC₀_pos : 0 < C₀
  hC₂_pos : 0 < C₂
  hC₄_pos : 0 < C₄
  hφ₀ : ∀ z : ℍ, 1/2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)
  hφ₂ : ∀ z : ℍ, 1/2 < z.im → ‖φ₂' z‖ ≤ C₂
  hφ₄ : ∀ z : ℍ, 1/2 < z.im → ‖φ₄' z‖ ≤ C₄ * Real.exp (2 * π * z.im)

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

open MagicFunction.PolyFourierCoeffBound in
/-- Coefficient function for φ₀ = ((E₂E₄ - E₆)²) / Δ and φ₂' = E₄(E₂E₄ - E₆) / Δ -/
private def c_φ₀₂ : ℤ → ℂ := fun n ↦ n * (σ 3 n.toNat)

/-- The coefficient function c_φ₀₂ has polynomial growth O(n^5). -/
private lemma c_φ₀₂_poly : c_φ₀₂ =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- Define the ℕ version
  let d : ℕ → ℂ := fun n ↦ n * (σ 3 n)
  have hcd (n : ℕ) : c_φ₀₂ n = d n := by simp [c_φ₀₂, d]
  have hdpoly : d =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℂ)) := by
    have h₁ (n : ℕ) : n ^ 5 = n * n ^ 4 := Nat.pow_succ'
    norm_cast
    simp only [h₁]
    push_cast
    refine Asymptotics.IsBigO.mul (Asymptotics.isBigO_refl _ Filter.atTop) ?_
    have h := MagicFunction.PolyFourierCoeffBound.ArithmeticFunction.sigma_asymptotic' 3
    simp only [Nat.reduceAdd] at h
    norm_cast at h ⊢
  -- Convert to ℤ → ℝ version
  simp only [Asymptotics.isBigO_iff, norm_pow, Complex.norm_natCast, Filter.eventually_atTop,
    ge_iff_le] at hdpoly ⊢
  obtain ⟨R, m, hR⟩ := hdpoly
  use R, m
  intro n hn
  have hnnonneg : 0 ≤ n := calc 0 ≤ (m : ℤ) := by positivity
    _ ≤ ↑n := hn
  have hnnat : n.toNat = n := by simp only [Int.ofNat_toNat, sup_eq_left, hnnonneg]
  have hmnnat : m ≤ n.toNat := by zify; rw [hnnat]; exact hn
  specialize hR n.toNat hmnnat
  rw [← hcd, hnnat] at hR
  calc norm (c_φ₀₂ n)
  _ ≤ R * n.toNat ^ 5 := hR
  _ = R * |↑n| ^ 5 := by
    simp only [mul_eq_mul_left_iff]; norm_cast; left
    rw [Nat.cast_pow, hnnat]; simp [hnnonneg, abs_of_nonneg]

open MagicFunction.PolyFourierCoeffBound in
/-- Coefficient function for φ₄' = E₄² / Δ -/
private def c_φ₄ : ℤ → ℂ := fun n ↦ if n ≤ 0 then 1 else n * (σ 3 n.toNat)

/-- The coefficient function c_φ₄ has polynomial growth O(n^5).
    For n > 0, c_φ₄ n = n * σ₃(n), which matches c_φ₀₂. -/
private lemma c_φ₄_poly : c_φ₄ =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- For n > 0, c_φ₄ n = c_φ₀₂ n, so we use c_φ₀₂_poly
  have heq : c_φ₄ =ᶠ[Filter.atTop] c_φ₀₂ := by
    simp only [Filter.EventuallyEq, Filter.eventually_atTop, ge_iff_le]
    use 1
    intro n hn
    simp only [c_φ₄, c_φ₀₂]
    have h : ¬n ≤ 0 := by omega
    simp only [h, ↓reduceIte]
  exact c_φ₀₂_poly.congr' heq.symm Filter.EventuallyEq.rfl

open MagicFunction.PolyFourierCoeffBound ArithmeticFunction

/-- PhiBounds instance from modular forms theory using explicit DivDiscBound constants.
    This avoids the axiom of choice by using computable bounds directly.
    The bounds follow from Corollaries 7.5-7.7 which use Ramanujan identities.
    See PolyFourierCoeffBound.lean for the underlying lemmas (norm_φ₀_le, etc.). -/
def phiBounds : PhiBounds where
  C₀ := DivDiscBound c_φ₀₂ 4
  C₂ := DivDiscBound c_φ₀₂ 2
  C₄ := DivDiscBound c_φ₄ 0
  hC₀_pos := by
    refine DivDiscBound_pos c_φ₀₂ 4 ?_ 5 c_φ₀₂_poly
    -- c_φ₀₂ 4 = 4 * σ₃(4) = 4 * 73 ≠ 0
    simp only [c_φ₀₂, ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, Int.cast_eq_zero, false_or]
    norm_cast  -- σ₃(4) = 73 ≠ 0
  hC₂_pos := by
    refine DivDiscBound_pos c_φ₀₂ 2 ?_ 5 c_φ₀₂_poly
    -- c_φ₀₂ 2 = 2 * σ₃(2) = 2 * 9 ≠ 0
    simp only [c_φ₀₂, ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, Int.cast_eq_zero, false_or]
    norm_cast  -- σ₃(2) = 9 ≠ 0
  hC₄_pos := by
    refine DivDiscBound_pos c_φ₄ 0 ?_ 5 c_φ₄_poly
    -- c_φ₄ 0 = 1 ≠ 0
    simp only [c_φ₄, le_refl, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
  hφ₀ := fun z hz => by
    -- φ₀ = ((E₂E₄ - E₆)²) / Δ, n₀=4 gives exp(-π*(4-2)*z.im) = exp(-2π*z.im)
    have hcsum : Summable fun (i : ℕ) => fouterm c_φ₀₂ z (i + 4) := by
      -- Summability from polynomial growth + exponential decay (Ramanujan)
      sorry
    have hf : ∀ x : ℍ, ((E₂ x) * (E₄ x) - (E₆ x)) ^ 2 = ∑' (n : ℕ), fouterm c_φ₀₂ x (n + 4) := by
      -- Fourier expansion identity (Ramanujan)
      sorry
    have h := DivDiscBoundOfPolyFourierCoeff z hz c_φ₀₂ 4 hcsum 5 c_φ₀₂_poly
        (fun z ↦ ((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) hf
    simp only [φ₀]
    convert h using 2
    ring_nf
  hφ₂ := fun z hz => by
    -- φ₂' = E₄(E₂E₄ - E₆) / Δ, n₀=2 gives exp(-π*(2-2)*z.im) = 1 (constant bound)
    have hcsum : Summable fun (i : ℕ) => fouterm c_φ₀₂ z (i + 2) := by
      sorry
    have hf : ∀ x : ℍ, E₄ x * (E₂ x * E₄ x - E₆ x) = ∑' (n : ℕ), fouterm c_φ₀₂ x (n + 2) := by
      sorry
    have h := DivDiscBoundOfPolyFourierCoeff z hz c_φ₀₂ 2 hcsum 5 c_φ₀₂_poly
        (fun z ↦ E₄ z * (E₂ z * E₄ z - E₆ z)) hf
    simp only [φ₂']
    calc ‖(E₄ z * (E₂ z * E₄ z - E₆ z)) / Δ z‖
        ≤ DivDiscBound c_φ₀₂ 2 * Real.exp (-π * (2 - 2) * z.im) := h
      _ = DivDiscBound c_φ₀₂ 2 * Real.exp 0 := by ring_nf
      _ = DivDiscBound c_φ₀₂ 2 := by simp
  hφ₄ := fun z hz => by
    -- φ₄' = E₄² / Δ, n₀=0 gives exp(-π*(0-2)*z.im) = exp(2π*z.im)
    have hcsum : Summable fun (i : ℕ) => fouterm c_φ₄ z (i + 0) := by
      sorry
    have hf : ∀ x : ℍ, E₄ x ^ 2 = ∑' (n : ℕ), fouterm c_φ₄ x (n + 0) := by
      sorry
    have h := DivDiscBoundOfPolyFourierCoeff z hz c_φ₄ 0 hcsum 5 c_φ₄_poly
        (fun z ↦ E₄ z ^ 2) hf
    simp only [φ₄']
    convert h using 2
    ring_nf

end MagicFunction.a

end

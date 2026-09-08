/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Polynomial Bounds on Cauchy-Product Coefficients

Exact coefficient functions for the `q`-expansions entering `φ₀ = (E₂E₄ - E₆)² / Δ`, and
polynomial growth bounds for their Cauchy products. The definitions here (`bE₄`, `bg`,
`evenCoeff`) are the same functions used by the Fourier-expansion identities, so this file is
the canonical home for both.

The single-series coefficients (`bg` for `E₂E₄ - E₆`, `bE₄` for `E₄`) have polynomial growth by
the divisor bound `ArithmeticFunction.sigma_le_pow_succ`. The square `(E₂E₄ - E₆)²` and the
products with `E₄` have coefficients given by Cauchy products, and `cauchyCoeff_poly` shows a
Cauchy product of two polynomially bounded sequences is again polynomially bounded (with the
degree increasing by one). `evenCoeff` re-indexes a `q`-series (`q = e^{2πiz}`) as a
`ℤ`-indexed `r`-series (`r = e^{πiz}`, so `q = r²`) supported on even indices, as consumed by
`DivDiscBoundOfPolyFourierCoeff`.

## Main results

* `cauchyCoeff_poly`: `a = O(n^k)` and `b = O(n^ℓ)` give `cauchyCoeff a b = O(n^(k+ℓ+1))`,
* `c_E₂E₄E₆_poly`, `c_E₄_E₂E₄E₆_poly`, `c_E₄_sq_poly`: the concrete `O(n^11)`, `O(n^10)`,
  `O(n^9)` bounds for the three coefficient families.
-/

@[expose] public section

open Real Complex
open scoped ArithmeticFunction.sigma

noncomputable section

namespace MagicFunction.a.FourierExpansions

/-! ## Coefficient Functions

The coefficient functions are defined to give exact Fourier expansions.
The key is converting from q-expansions (exp(2πinz)) to r-expansions (exp(πinz)).

Since q = exp(2πiz) = r² where r = exp(πiz), a q-series ∑ aₙ qⁿ becomes
an r-series with only even indices: ∑ a_{m/2} rᵐ for even m.

We use `evenCoeff` for this even-indexed re-indexing. -/

/-- The `q`-expansion coefficients of `E₄`. -/
def bE₄ : ℕ → ℂ := fun m => if m = 0 then 1 else 240 * (σ 3 m : ℂ)

/-- The `q`-expansion coefficients of `E₂E₄ − E₆` (vanishing at `0`). -/
def bg : ℕ → ℂ := fun m => 720 * (m : ℂ) * (σ 3 m : ℂ)

/-- Cauchy product (convolution) of two sequences at index n. -/
def cauchyCoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

/-- Re-index an ℕ-indexed `q`-series (`q = e^{2πiz}`) as a ℤ-indexed `r`-series
(`r = e^{πiz}`, `q = r²`): even indices `2m` (`m ≥ 0`) carry `b m`, odd indices carry `0`.
Beware that a negative even index `k` also carries `b 0` (via `Int.toNat`); the
`evenCoeff_cauchyCoeff_zero_*` lemmas give vanishing there from `b 0 = 0`. -/
def evenCoeff (b : ℕ → ℂ) : ℤ → ℂ := fun k => if Even k then b (k / 2).toNat else 0

/-- Coefficient function for (E₂E₄ - E₆)²: Cauchy product of bg with itself,
    re-indexed for the q→r conversion. -/
def c_E₂E₄E₆ : ℤ → ℂ := evenCoeff (cauchyCoeff bg bg)

/-- Coefficient function for E₄ * (E₂E₄ - E₆): Cauchy product of bE₄ and bg,
    re-indexed for the q→r conversion. -/
def c_E₄_E₂E₄E₆ : ℤ → ℂ := evenCoeff (cauchyCoeff bE₄ bg)

/-- Coefficient function for E₄²: Cauchy product of bE₄ with itself,
    re-indexed for the q→r conversion. -/
def c_E₄_sq : ℤ → ℂ := evenCoeff (cauchyCoeff bE₄ bE₄)

/-! ## Polynomial Growth Infrastructure -/

/-- A big-O bound `a =O[atTop] (n ^ k)` upgrades to a single global constant: there is `M > 0`
with `‖a i‖ ≤ M * n ^ k` for every `n ≥ 1` and every `i ≤ n`. The big-O bound covers the large
indices, while the finitely many initial terms are absorbed into `M`. -/
lemma exists_global_poly_bound {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    ∃ M > 0, ∀ n i : ℕ, 1 ≤ n → i ≤ n → ‖a i‖ ≤ M * (n : ℝ) ^ k := by
  obtain ⟨C, hC0, hC⟩ := Asymptotics.bound_of_isBigO_nat_atTop ha
  refine ⟨max C (‖a 0‖ + 1), lt_max_of_lt_left hC0, fun n i hn hi ↦ ?_⟩
  have hM0 : (0 : ℝ) ≤ max C (‖a 0‖ + 1) := le_max_of_le_left hC0.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hn)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · calc ‖a 0‖ ≤ max C (‖a 0‖ + 1) * 1 := by
          rw [mul_one]; exact le_max_of_le_right (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hn1 hM0
  · have hi' : ((i : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hi0.ne'
    have h := hC (pow_ne_zero k hi')
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h.trans (mul_le_mul (le_max_left _ _)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hi) k) (by positivity) hM0)

/-- Cauchy product of two polynomial-growth sequences has polynomial growth.
    If a = O(n^k) and b = O(n^ℓ), then cauchyCoeff a b = O(n^(k + ℓ + 1)).
    This follows from |∑_{i+j=n} a(i)·b(j)| ≤ (n+1) · sup|a(i)| · sup|b(j)|. -/
lemma cauchyCoeff_poly {a b : ℕ → ℂ} {k ℓ : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (hb : b =O[Filter.atTop] (fun n ↦ (n ^ ℓ : ℝ))) :
    cauchyCoeff a b =O[Filter.atTop] (fun n ↦ (n ^ (k + ℓ + 1) : ℝ)) := by
  -- Each of the `n + 1` terms of the Cauchy product is bounded by `A * n ^ k * (B * n ^ ℓ)`,
  -- and the factor `n + 1 ≤ 2 * n` is absorbed by the extra power of `n`.
  obtain ⟨A, hA, ha_bound⟩ := exists_global_poly_bound ha
  obtain ⟨B, hB, hb_bound⟩ := exists_global_poly_bound hb
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * A * B, Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  calc ‖cauchyCoeff a b n‖
      = ‖∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2‖ := rfl
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖a kl.1‖ * ‖b kl.2‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ ≤ ∑ _kl ∈ Finset.antidiagonal n, A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ) := by
        refine Finset.sum_le_sum fun ⟨i, j⟩ hij ↦ ?_
        simp only [Finset.mem_antidiagonal] at hij
        exact mul_le_mul (ha_bound n i hn (by omega)) (hb_bound n j hn (by omega))
          (norm_nonneg _) (by positivity)
    _ = ((n : ℝ) + 1) * (A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]; push_cast; ring
    _ ≤ 2 * (n : ℝ) * (A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ)) := by
        have : (0 : ℝ) ≤ A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ) := by positivity
        nlinarith
    _ = 2 * A * B * (n : ℝ) ^ (k + ℓ + 1) := by ring
    _ = 2 * A * B * ‖(n : ℝ) ^ (k + ℓ + 1)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- bg has polynomial growth O(n^5). -/
lemma bg_poly : bg =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- bg(n) = 720 * n * σ₃(n). Since σ₃(n) ≤ n^4, the product is O(n^5).
  rw [Asymptotics.isBigO_iff]
  use 720
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [bg]
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n ^ 5)]
  have hσ : (σ 3 n : ℝ) ≤ n ^ 4 := by exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 3 n
  have h720 : ‖(720 : ℂ)‖ = 720 := by norm_num
  calc ‖(720 : ℂ)‖ * n * ((σ 3) n : ℝ)
      ≤ 720 * n * n ^ 4 := by rw [h720]; nlinarith
    _ = 720 * n ^ 5 := by ring

/-- bE₄ has polynomial growth O(n^4). -/
lemma bE₄_poly : bE₄ =O[Filter.atTop] (fun n ↦ (n ^ 4 : ℝ)) := by
  -- bE₄(n) = 240 * σ₃(n) for n ≥ 1. Since σ₃(n) ≤ n^4, the product is O(n^4).
  rw [Asymptotics.isBigO_iff]
  use 240
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [bE₄, Nat.ne_of_gt hn, ↓reduceIte]
  rw [Complex.norm_mul, Complex.norm_natCast]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n ^ 4)]
  have hσ : (σ 3 n : ℝ) ≤ n ^ 4 := by exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 3 n
  have h240 : ‖(240 : ℂ)‖ = 240 := by norm_num
  calc ‖(240 : ℂ)‖ * ((σ 3) n : ℝ) ≤ 240 * n ^ 4 := by rw [h240]; nlinarith

/-! ## Even Re-indexing Lemmas

Properties of the `evenCoeff` re-indexing map used for q→r series conversion. -/

/-- evenCoeff at an even index equals the original coefficient. -/
lemma evenCoeff_even (b : ℕ → ℂ) (n : ℕ) : evenCoeff b (2 * n) = b n := by
  have he : Even (2 * (n : ℤ)) := even_two_mul _
  have h2 : ((2 * (n : ℤ)) / 2).toNat = n := by omega
  simp only [evenCoeff, if_pos he, h2]

/-- evenCoeff at a non-even index is zero. -/
lemma evenCoeff_odd (b : ℕ → ℂ) {k : ℤ} (hk : ¬ Even k) : evenCoeff b k = 0 := if_neg hk

/-- Cauchy product at 0 is zero if right factor vanishes at 0. -/
lemma cauchyCoeff_zero_of_right_zero {a b : ℕ → ℂ} (hb0 : b 0 = 0) :
    cauchyCoeff a b 0 = 0 := by
  simp only [cauchyCoeff, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hb0, mul_zero]

/-- Cauchy product at 1 is zero if both factors vanish at 0. -/
lemma cauchyCoeff_one_zero_of_both_zero {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    cauchyCoeff a b 1 = 0 := by
  simp only [cauchyCoeff]
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  rcases Nat.eq_zero_or_pos i with hi | hi
  · simp only [hi, ha0, zero_mul]
  · simp only [Nat.lt_one_iff.mp (by omega : j < 1), hb0, mul_zero]

/-- `evenCoeff` of a Cauchy product vanishes for `k < 2` (negative `k` included) when the right
factor vanishes at 0. -/
lemma evenCoeff_cauchyCoeff_zero_of_lt_two {a b : ℕ → ℂ} (hb0 : b 0 = 0) (k : ℤ) (hk : k < 2) :
    evenCoeff (cauchyCoeff a b) k = 0 := by
  by_cases he : Even k
  · have h0 : (k / 2).toNat = 0 := by omega
    rw [evenCoeff, if_pos he, h0]
    exact cauchyCoeff_zero_of_right_zero hb0
  · exact evenCoeff_odd _ he

/-- `evenCoeff` of a Cauchy self-product vanishes for `k < 4` (negative `k` included) when the
factor vanishes at 0. -/
lemma evenCoeff_cauchyCoeff_zero_of_lt_four {a : ℕ → ℂ} (ha0 : a 0 = 0) (k : ℤ) (hk : k < 4) :
    evenCoeff (cauchyCoeff a a) k = 0 := by
  by_cases he : Even k
  · have h01 : (k / 2).toNat = 0 ∨ (k / 2).toNat = 1 := by omega
    rw [evenCoeff, if_pos he]
    rcases h01 with h | h <;> rw [h]
    · exact cauchyCoeff_zero_of_right_zero ha0
    · exact cauchyCoeff_one_zero_of_both_zero ha0 ha0
  · exact evenCoeff_odd _ he

/-- Even re-indexing preserves polynomial growth: if a = O(n^k) on ℕ, then
evenCoeff a = O(n^k) on ℤ. -/
lemma evenCoeff_poly {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    evenCoeff a =O[Filter.atTop] (fun n : ℤ ↦ (n ^ k : ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := exists_global_poly_bound ha
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℤ)] with m hm
  by_cases he : Even m
  · have h := hbound m.toNat (m / 2).toNat (by omega) (by omega)
    have hmcast : (m.toNat : ℝ) = m := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ m)
    simpa [evenCoeff, he, hmcast, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ m)] using h
  · simp only [evenCoeff_odd _ he, norm_zero]
    positivity

/-- c_E₂E₄E₆ has polynomial growth O(n^11).
    Cauchy product of two O(n^5) sequences, then even re-indexing. -/
lemma c_E₂E₄E₆_poly : c_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 11 : ℝ)) :=
  -- cauchyCoeff bg bg: O(n^5) × O(n^5) → O(n^{5+5+1}) = O(n^11)
  evenCoeff_poly (cauchyCoeff_poly bg_poly bg_poly)

/-- c_E₄_E₂E₄E₆ has polynomial growth O(n^10).
    Cauchy product of O(n^4) and O(n^5) sequences, then even re-indexing. -/
lemma c_E₄_E₂E₄E₆_poly : c_E₄_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 10 : ℝ)) :=
  -- cauchyCoeff bE₄ bg: O(n^4) × O(n^5) → O(n^{4+5+1}) = O(n^10)
  evenCoeff_poly (cauchyCoeff_poly bE₄_poly bg_poly)

/-- c_E₄_sq has polynomial growth O(n^9).
    Cauchy product of two O(n^4) sequences, then even re-indexing. -/
lemma c_E₄_sq_poly : c_E₄_sq =O[Filter.atTop] (fun n ↦ (n ^ 9 : ℝ)) :=
  -- cauchyCoeff bE₄ bE₄: O(n^4) × O(n^4) → O(n^{4+4+1}) = O(n^9)
  evenCoeff_poly (cauchyCoeff_poly bE₄_poly bE₄_poly)

end MagicFunction.a.FourierExpansions

end

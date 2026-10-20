/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.MagicFunction.a.FourierExpansions
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Fourier expansions of the quadratic products entering φ₀, φ₂', and φ₄'

Exact `fouterm` expansions of the three quadratic products appearing in the formulas for
`φ₀`, `φ₂'`, and `φ₄'`:

- `(E₂E₄ − E₆)²`, with coefficients `c_E₂E₄E₆ = evenCoeff (cauchyCoeff bg bg)`;
- `E₄ · (E₂E₄ − E₆)`, with coefficients `c_E₄_E₂E₄E₆ = evenCoeff (cauchyCoeff bE₄ bg)`;
- `E₄²`, with coefficients `c_E₄_sq = evenCoeff (cauchyCoeff bE₄ bE₄)`.

## Route

Each product identity follows the same path:

1. Rewrite each linear factor as an ℕ-indexed `q`-series (`E₄_qexp_nat`, `g_qexp_nat`).
2. Multiply via the Cauchy product formula
   `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`; the norm-summability inputs come
   from the generic `summable_norm_q_series_of_poly` plus the `*_poly` growth bounds.
3. Factor each antidiagonal block into `cauchyCoeff · qⁿ` (`antidiagonal_qexp_factor`).
4. Reindex the `q`-series (`q = e^{2πiz}`) to a `fouterm` sum (`r = e^{πiz}`) with
   `qexp_eq_fouterm`, and shift the starting index with `tsum_fouterm_shift` using the
   `evenCoeff_cauchyCoeff_zero_*` vanishing lemmas (shift `4` for the `bg` square,
   `2` for the mixed product, none for the `bE₄` square).
-/

@[expose] public section

open Real Complex UpperHalfPlane
open MagicFunction.PolyFourierCoeffBound

noncomputable section

namespace MagicFunction.a.FourierExpansions

/-! ## Generic q-series summability

Polynomial-growth coefficients against the geometrically decaying `q = e^{2πiz}` (for `z : ℍ`)
give absolutely summable `q`-series. This single lemma serves all products below: the required
coefficient bounds are `bg_poly`, `bE₄_poly` and their Cauchy products via `cauchyCoeff_poly`. -/

/-- Norm-summability of a `q`-series whose coefficients grow polynomially: for `z : ℍ`,
`∑ ‖c m · e^{2πimz}‖` converges since `‖e^{2πiz}‖ < 1` and `c = O(mᵏ)`. -/
lemma summable_norm_q_series_of_poly {c : ℕ → ℂ} {k : ℕ}
    (hc : c =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) (z : ℍ) :
    Summable fun m : ℕ ↦ ‖c m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)‖ := by
  have hr := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hu : c =O[Filter.atTop] (fun n : ℕ ↦ (↑(n ^ k) : ℝ)) := by
    simpa [Nat.cast_pow] using hc
  refine (summable_real_norm_mul_geometric_of_norm_lt_one hr hu).congr fun m ↦ ?_
  rw [← Complex.exp_nat_mul]
  congr 3
  ring

/-- Summability of a `q`-series whose coefficients grow polynomially (see
`summable_norm_q_series_of_poly` for the absolute version). -/
lemma summable_q_series_of_poly {c : ℕ → ℂ} {k : ℕ}
    (hc : c =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) (z : ℍ) :
    Summable fun m : ℕ ↦ c m * cexp (2 * ↑π * Complex.I * ↑m * ↑z) :=
  (summable_norm_q_series_of_poly hc z).of_norm

/-! ## Cauchy product blocks -/

/-- Each antidiagonal block of the product of two `q`-series factors as the Cauchy coefficient
times a single `q`-power: `∑_{k+l=n} (a k · qᵏ)(b l · qˡ) = cauchyCoeff a b n · qⁿ`. -/
lemma antidiagonal_qexp_factor (a b : ℕ → ℂ) (z : ℍ) (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n,
      (a kl.1 * cexp (2 * ↑π * Complex.I * ↑kl.1 * ↑z)) *
      (b kl.2 * cexp (2 * ↑π * Complex.I * ↑kl.2 * ↑z)) =
    cauchyCoeff a b n * cexp (2 * ↑π * Complex.I * ↑n * ↑z) := by
  simp only [cauchyCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ⟨k, l⟩ hkl ↦ ?_
  simp only [Finset.mem_antidiagonal] at hkl
  have hexp : 2 * ↑π * Complex.I * ↑k * ↑z + 2 * ↑π * Complex.I * ↑l * ↑z =
      2 * ↑π * Complex.I * ↑n * ↑z := by rw [← hkl]; push_cast; ring
  calc a k * cexp (2 * ↑π * Complex.I * ↑k * ↑z) * (b l * cexp (2 * ↑π * Complex.I * ↑l * ↑z))
      = a k * b l * (cexp (2 * ↑π * Complex.I * ↑k * ↑z) *
          cexp (2 * ↑π * Complex.I * ↑l * ↑z)) := by ring
    _ = a k * b l * cexp (2 * ↑π * Complex.I * ↑k * ↑z +
          2 * ↑π * Complex.I * ↑l * ↑z) := by rw [← Complex.exp_add]
    _ = a k * b l * cexp (2 * ↑π * Complex.I * ↑n * ↑z) := by rw [hexp]

/-! ## The three product expansions -/

/-- Fourier expansion of `(E₂E₄ − E₆)²`. In the `q`-convention the factor is
`720·∑_{m≥1} m·σ₃(m)·qᵐ`, so the square starts at `q²`, i.e. `r⁴` in the `fouterm`
(`r = e^{πiz}`) convention. -/
lemma E₂E₄E₆_sq_fourier (x : ℍ) :
    (E₂ x * E₄ x - E₆ x) ^ 2 = ∑' n : ℕ, fouterm c_E₂E₄E₆ x (↑n + 4) := by
  have hnorm := summable_norm_q_series_of_poly bg_poly x
  rw [pow_two, g_qexp_nat x,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm]
  simp only [antidiagonal_qexp_factor]
  rw [qexp_eq_fouterm (cauchyCoeff bg bg) x, tsum_fouterm_shift x 4
    (fun k hk ↦ evenCoeff_cauchyCoeff_zero_of_lt_four (by simp [bg]) k (by omega))]
  simp only [c_E₂E₄E₆, Nat.cast_ofNat]

/-- Fourier expansion of `E₄·(E₂E₄ − E₆)`. The product starts at `q¹`, i.e. `r²` in the
`fouterm` convention. -/
lemma E₄_E₂E₄E₆_fourier (x : ℍ) :
    E₄ x * (E₂ x * E₄ x - E₆ x) = ∑' n : ℕ, fouterm c_E₄_E₂E₄E₆ x (↑n + 2) := by
  have hnormb := summable_norm_q_series_of_poly bE₄_poly x
  have hnormg := summable_norm_q_series_of_poly bg_poly x
  rw [g_qexp_nat x, E₄_qexp_nat x,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormb hnormg]
  simp only [antidiagonal_qexp_factor]
  rw [qexp_eq_fouterm (cauchyCoeff bE₄ bg) x, tsum_fouterm_shift x 2
    (fun k hk ↦ evenCoeff_cauchyCoeff_zero_of_lt_two (by simp [bg]) k (by omega))]
  simp only [c_E₄_E₂E₄E₆, Nat.cast_ofNat]

/-- Fourier expansion of `E₄²`. Since `E₄ = 1 + 240·∑_{m≥1} σ₃(m)·qᵐ`, the square starts at
the constant term, so no index shift is needed. -/
lemma E₄_sq_fourier (x : ℍ) :
    E₄ x ^ 2 = ∑' n : ℕ, fouterm c_E₄_sq x (↑n + 0) := by
  have hnorm := summable_norm_q_series_of_poly bE₄_poly x
  rw [pow_two, E₄_qexp_nat x,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm]
  simp only [antidiagonal_qexp_factor]
  rw [qexp_eq_fouterm (cauchyCoeff bE₄ bE₄) x]
  simp only [c_E₄_sq]

end MagicFunction.a.FourierExpansions

end

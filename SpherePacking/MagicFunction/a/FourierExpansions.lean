/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.ForMathlib.SpecificLimits
import SpherePacking.ModularForms.FG

/-!
# Fourier Expansion Identities for Phi Bounds

States the Fourier expansion identities needed to connect the phi functions
(φ₀, φ₂', φ₄') to the DivDiscBound machinery in PolyFourierCoeffBound.

## Convention

The standard q-expansion uses q = exp(2πiz), while `fouterm` uses exp(πinz).
Since q = exp(2πiz) and setting r = exp(πiz), we have q = r².

This means:
- A q-expansion ∑ aₙ qⁿ becomes ∑ aₙ r^{2n} in the fouterm convention
- The starting index n₀ in fouterm corresponds to n₀/2 in q-space

## Main Results

- `summable_fouterm_of_poly`: Summability from polynomial growth + exponential decay
- `E₂E₄E₆_sq_fourier`: (E₂E₄ - E₆)² in fouterm form (n₀ = 4)
- `E₄_E₂E₄E₆_fourier`: E₄(E₂E₄ - E₆) in fouterm form (n₀ = 2)
- `E₄_sq_fourier`: E₄² in fouterm form (n₀ = 0)

## References

- Blueprint Corollaries 7.5-7.7
- `SpherePacking.ModularForms.FG`: q-expansion identities (`E₂_mul_E₄_sub_E₆`, `E₄_sigma_qexp`)
-/

open Real Complex UpperHalfPlane
open scoped ArithmeticFunction.sigma
open MagicFunction.PolyFourierCoeffBound

noncomputable section

namespace MagicFunction.a.FourierExpansions

/-! ## Coefficient Functions

The coefficient functions are defined to give exact Fourier expansions.
The key is converting from q-expansions (exp(2πinz)) to r-expansions (exp(πinz)).

Since q = exp(2πiz) = r² where r = exp(πiz), a q-series ∑ aₙ qⁿ becomes
an r-series with only even indices: ∑ a_{m/2} rᵐ for even m.

We use `Function.extend (fun n ↦ 2 * n)` for this even-indexing. -/

/-- Q-expansion coefficient for E₂E₄ - E₆: coefficient at qⁿ is 720·n·σ₃(n) for n ≥ 1. -/
def a_E₂E₄E₆ : ℕ → ℂ := fun n ↦ if n = 0 then 0 else 720 * n * (σ 3 n)

/-- Q-expansion coefficient for E₄: coefficient at qⁿ is 240·σ₃(n) for n ≥ 1, and 1 for n = 0. -/
def b_E₄ : ℕ → ℂ := fun n ↦ if n = 0 then 1 else 240 * (σ 3 n)

/-- Cauchy product (convolution) of two sequences at index n. -/
def cauchyCoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

/-- Even extension: extend a sequence to all naturals, zero on odd indices.
    evenExt a m = a(m/2) if m is even, 0 if m is odd. -/
def evenExt (a : ℕ → ℂ) : ℕ → ℂ := Function.extend (fun n ↦ 2 * n) a 0

/-- Convert ℕ coefficient to ℤ coefficient (zero for negative indices). -/
def toIntCoeff (a : ℕ → ℂ) : ℤ → ℂ := fun k ↦ if k < 0 then 0 else a k.toNat

/-- Coefficient function for (E₂E₄ - E₆)²: uses Cauchy product of a_E₂E₄E₆ with itself,
    then even extension for q→r conversion. -/
def c_E₂E₄E₆ : ℤ → ℂ := toIntCoeff (evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆))

/-- Coefficient function for E₄ * (E₂E₄ - E₆): uses Cauchy product of b_E₄ and a_E₂E₄E₆,
    then even extension. -/
def c_E₄_E₂E₄E₆ : ℤ → ℂ := toIntCoeff (evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆))

/-- Coefficient function for E₄²: uses Cauchy product of b_E₄ with itself,
    then even extension. -/
def c_E₄_sq : ℤ → ℂ := toIntCoeff (evenExt (cauchyCoeff b_E₄ b_E₄))

/-! ## Polynomial Growth Infrastructure -/

/-- Cauchy product of two polynomial-growth sequences has polynomial growth.
    If a = O(n^k) and b = O(n^ℓ), then cauchyCoeff a b = O(n^(k + ℓ + 1)).
    This follows from |∑_{i+j=n} a(i)·b(j)| ≤ (n+1) · sup|a(i)| · sup|b(j)|. -/
lemma cauchyCoeff_poly {a b : ℕ → ℂ} {k ℓ : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (hb : b =O[Filter.atTop] (fun n ↦ (n ^ ℓ : ℝ))) :
    cauchyCoeff a b =O[Filter.atTop] (fun n ↦ (n ^ (k + ℓ + 1) : ℝ)) := by
  -- Strategy: We split the bound into large indices (where Big-O bounds apply) and
  -- small indices (bounded by a constant). The sum has (n+1) terms, absorbed by n^{k+ℓ+1}.
  simp only [Asymptotics.isBigO_iff] at ha hb ⊢
  obtain ⟨Ca, hCa⟩ := ha
  obtain ⟨Cb, hCb⟩ := hb
  simp only [Filter.eventually_atTop] at hCa hCb ⊢
  obtain ⟨Na, hNa⟩ := hCa
  obtain ⟨Nb, hNb⟩ := hCb
  -- For small indices, compute explicit bound on |a| and |b|
  let Ma : ℝ := if h : Na = 0 then 1 else
    (Finset.sup' (Finset.range Na) (Finset.nonempty_range_iff.mpr h)
      (fun i ↦ ‖a i‖)) + 1
  let Mb : ℝ := if h : Nb = 0 then 1 else
    (Finset.sup' (Finset.range Nb) (Finset.nonempty_range_iff.mpr h)
      (fun j ↦ ‖b j‖)) + 1
  have hMa_pos : 0 < Ma := by
    simp only [Ma]; split_ifs with h
    · norm_num
    · have hn : (Finset.range Na).Nonempty := Finset.nonempty_range_iff.mpr h
      have hnn : 0 ≤ Finset.sup' (Finset.range Na) hn (fun i ↦ ‖a i‖) :=
        Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.pos_of_ne_zero h)) (norm_nonneg _)
      linarith
  have hMb_pos : 0 < Mb := by
    simp only [Mb]; split_ifs with h
    · norm_num
    · have hn : (Finset.range Nb).Nonempty := Finset.nonempty_range_iff.mpr h
      have hnn : 0 ≤ Finset.sup' (Finset.range Nb) hn (fun j ↦ ‖b j‖) :=
        Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.pos_of_ne_zero h)) (norm_nonneg _)
      linarith
  -- The key constant
  let C := 2 * (max |Ca| Ma) * (max |Cb| Mb)
  use C
  refine ⟨max Na Nb + 1, fun n hn ↦ ?_⟩
  have hNa' : n ≥ Na := le_of_max_le_left (Nat.le_of_succ_le hn)
  have hNb' : n ≥ Nb := le_of_max_le_right (Nat.le_of_succ_le hn)
  have hn_ge1 : 1 ≤ n := Nat.one_le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn)
  have hn_pos : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn_ge1
  have hn_pos' : (0 : ℝ) < n := by linarith
  -- Key: for ANY i ≤ n, we have ‖a i‖ ≤ max(|Ca|, Ma) * n^k
  have ha_bound : ∀ i ≤ n, ‖a i‖ ≤ (max |Ca| Ma) * (n : ℝ) ^ k := fun i hi ↦ by
    by_cases hi' : i < Na
    · have hMa_bound : ‖a i‖ < Ma := by
        simp only [Ma]
        split_ifs with h
        · omega
        · calc ‖a i‖ ≤ Finset.sup' (Finset.range Na) _ (fun i ↦ ‖a i‖) :=
              Finset.le_sup' (fun i ↦ ‖a i‖) (Finset.mem_range.mpr hi')
            _ < _ + 1 := by linarith
      calc ‖a i‖ ≤ Ma := le_of_lt hMa_bound
        _ ≤ max |Ca| Ma := le_max_right _ _
        _ = (max |Ca| Ma) * 1 := (mul_one _).symm
        _ ≤ (max |Ca| Ma) * (n : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_left _ (le_max_of_le_right (le_of_lt hMa_pos))
            calc (1 : ℝ) = 1 ^ k := (one_pow k).symm
              _ ≤ (n : ℝ) ^ k := by apply pow_le_pow_left₀ (by norm_num) hn_pos
    · push_neg at hi'
      have h_ik_nonneg : (0 : ℝ) ≤ (i : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
      have := hNa i hi'
      rw [Real.norm_eq_abs, abs_of_nonneg h_ik_nonneg] at this
      calc ‖a i‖ ≤ Ca * (i : ℝ) ^ k := this
        _ ≤ |Ca| * (i : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_right (le_abs_self Ca)
            exact pow_nonneg (Nat.cast_nonneg _) k
        _ ≤ |Ca| * (n : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg Ca)
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hi) k
        _ ≤ (max |Ca| Ma) * (n : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_right (le_max_left _ _)
            exact pow_nonneg (Nat.cast_nonneg _) k
  have hb_bound : ∀ j ≤ n, ‖b j‖ ≤ (max |Cb| Mb) * (n : ℝ) ^ ℓ := fun j hj ↦ by
    by_cases hj' : j < Nb
    · have hMb_bound : ‖b j‖ < Mb := by
        simp only [Mb]
        split_ifs with h
        · omega
        · calc ‖b j‖ ≤ Finset.sup' (Finset.range Nb) _ (fun j ↦ ‖b j‖) :=
              Finset.le_sup' (fun j ↦ ‖b j‖) (Finset.mem_range.mpr hj')
            _ < _ + 1 := by linarith
      calc ‖b j‖ ≤ Mb := le_of_lt hMb_bound
        _ ≤ max |Cb| Mb := le_max_right _ _
        _ = (max |Cb| Mb) * 1 := (mul_one _).symm
        _ ≤ (max |Cb| Mb) * (n : ℝ) ^ ℓ := by
            apply mul_le_mul_of_nonneg_left _ (le_max_of_le_right (le_of_lt hMb_pos))
            calc (1 : ℝ) = 1 ^ ℓ := (one_pow ℓ).symm
              _ ≤ (n : ℝ) ^ ℓ := by apply pow_le_pow_left₀ (by norm_num) hn_pos
    · push_neg at hj'
      have h_jl_nonneg : (0 : ℝ) ≤ (j : ℝ) ^ ℓ := pow_nonneg (Nat.cast_nonneg _) ℓ
      have := hNb j hj'
      rw [Real.norm_eq_abs, abs_of_nonneg h_jl_nonneg] at this
      calc ‖b j‖ ≤ Cb * (j : ℝ) ^ ℓ := this
        _ ≤ |Cb| * (j : ℝ) ^ ℓ := by
            apply mul_le_mul_of_nonneg_right (le_abs_self Cb)
            exact pow_nonneg (Nat.cast_nonneg _) ℓ
        _ ≤ |Cb| * (n : ℝ) ^ ℓ := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg Cb)
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hj) ℓ
        _ ≤ (max |Cb| Mb) * (n : ℝ) ^ ℓ := by
            apply mul_le_mul_of_nonneg_right (le_max_left _ _)
            exact pow_nonneg (Nat.cast_nonneg _) ℓ
  -- Now compute the bound
  have h_const_pos : 0 < max |Ca| Ma * max |Cb| Mb := by
    apply mul_pos
    · exact lt_max_of_lt_right hMa_pos
    · exact lt_max_of_lt_right hMb_pos
  calc ‖cauchyCoeff a b n‖
      = ‖∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2‖ := rfl
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖a kl.1 * b kl.2‖ := norm_sum_le _ _
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖a kl.1‖ * ‖b kl.2‖ := by
        apply Finset.sum_le_sum; intro x _; exact norm_mul_le _ _
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ((max |Ca| Ma) * (n : ℝ) ^ k) * ((max |Cb| Mb) * (n : ℝ) ^ ℓ) := by
        apply Finset.sum_le_sum
        intro ⟨i, j⟩ hij
        simp only [Finset.mem_antidiagonal] at hij
        have hi : i ≤ n := by omega
        have hj : j ≤ n := by omega
        apply mul_le_mul (ha_bound i hi) (hb_bound j hj) (norm_nonneg _)
        apply mul_nonneg (le_max_of_le_right (le_of_lt hMa_pos))
        exact pow_nonneg (Nat.cast_nonneg _) k
    _ = ((Finset.antidiagonal n).card : ℝ) * (((max |Ca| Ma) * (n : ℝ) ^ k) * ((max |Cb| Mb) * (n : ℝ) ^ ℓ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((n + 1) : ℝ) * (((max |Ca| Ma) * (n : ℝ) ^ k) * ((max |Cb| Mb) * (n : ℝ) ^ ℓ)) := by
        rw [Finset.Nat.card_antidiagonal]; simp
    _ = (max |Ca| Ma) * (max |Cb| Mb) * ((n : ℝ) + 1) * (n : ℝ) ^ (k + ℓ) := by ring
    _ ≤ (max |Ca| Ma) * (max |Cb| Mb) * (2 * (n : ℝ)) * (n : ℝ) ^ (k + ℓ) := by
        have h1 : (n : ℝ) + 1 ≤ 2 * n := by linarith
        have h2 : (max |Ca| Ma) * (max |Cb| Mb) * (n : ℝ) ^ (k + ℓ) ≥ 0 := by
          apply mul_nonneg (le_of_lt h_const_pos)
          exact pow_nonneg (Nat.cast_nonneg _) (k + ℓ)
        nlinarith
    _ = C * (n : ℝ) ^ (k + ℓ + 1) := by
        simp only [C]
        have h_pow : (n : ℝ) ^ (k + ℓ + 1) = n * (n : ℝ) ^ (k + ℓ) := by ring
        rw [h_pow]; ring
    _ = C * ‖(n : ℝ) ^ (k + ℓ + 1)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]

/-- a_E₂E₄E₆ has polynomial growth O(n^5). -/
lemma a_E₂E₄E₆_poly : a_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- a_E₂E₄E₆(n) = 720 * n * σ₃(n) for n ≥ 1. Since σ₃(n) ≤ n^4, the product is O(n^5).
  rw [Asymptotics.isBigO_iff]
  use 720
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [a_E₂E₄E₆, Nat.ne_of_gt hn, ↓reduceIte]
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n ^ 5)]
  have hσ : (σ 3 n : ℝ) ≤ n ^ 4 := by exact_mod_cast sigma_bound 3 n
  have h720 : ‖(720 : ℂ)‖ = 720 := by norm_num
  calc ‖(720 : ℂ)‖ * n * ((σ 3) n : ℝ)
      ≤ 720 * n * n ^ 4 := by rw [h720]; nlinarith
    _ = 720 * n ^ 5 := by ring

/-- b_E₄ has polynomial growth O(n^4). -/
lemma b_E₄_poly : b_E₄ =O[Filter.atTop] (fun n ↦ (n ^ 4 : ℝ)) := by
  -- b_E₄(n) = 240 * σ₃(n) for n ≥ 1. Since σ₃(n) ≤ n^4, the product is O(n^4).
  rw [Asymptotics.isBigO_iff]
  use 240
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [b_E₄, Nat.ne_of_gt hn, ↓reduceIte]
  rw [Complex.norm_mul, Complex.norm_natCast]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n ^ 4)]
  have hσ : (σ 3 n : ℝ) ≤ n ^ 4 := by exact_mod_cast sigma_bound 3 n
  have h240 : ‖(240 : ℂ)‖ = 240 := by norm_num
  calc ‖(240 : ℂ)‖ * ((σ 3) n : ℝ) ≤ 240 * n ^ 4 := by rw [h240]; nlinarith

/-! ## Even Extension Lemmas

Properties of the even extension map used for q→r series conversion. -/

/-- evenExt at even index equals original coefficient. -/
lemma evenExt_even (a : ℕ → ℂ) (n : ℕ) : evenExt a (2 * n) = a n := by
  simp only [evenExt]
  rw [Function.Injective.extend_apply]
  exact fun m₁ m₂ h ↦ by omega

/-- evenExt at odd index is zero. -/
lemma evenExt_odd (a : ℕ → ℂ) (n : ℕ) : evenExt a (2 * n + 1) = 0 := by
  simp only [evenExt]
  rw [Function.extend_apply']
  · rfl
  · intro ⟨m, hm⟩
    omega

/-- Even extension preserves polynomial growth. If a = O(n^k), then evenExt a = O(n^k). -/
lemma evenExt_poly {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    evenExt a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)) := by
  rw [Asymptotics.isBigO_iff] at ha ⊢
  obtain ⟨C, hC⟩ := ha
  -- Use |C| to ensure we have a nonnegative constant
  use |C|
  rw [Filter.eventually_atTop] at hC ⊢
  obtain ⟨N, hN⟩ := hC
  refine ⟨2 * N, fun m hm ↦ ?_⟩
  simp only [Real.norm_eq_abs]
  by_cases heven : Even m
  · -- m = 2*n for some n, and evenExt a (2*n) = a n
    obtain ⟨n, hn⟩ := heven
    have hn_2n : m = 2 * n := by omega
    have hn_ge : n ≥ N := by omega
    rw [hn_2n, evenExt_even]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
    have hm_nonneg : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
    have hbound := hN n hn_ge
    simp only [Real.norm_eq_abs, abs_of_nonneg hn_nonneg] at hbound
    rw [abs_of_nonneg hm_nonneg]
    have hC_abs : C ≤ |C| := le_abs_self C
    have hn_le_2n : (n : ℝ) ≤ (2 * n : ℕ) := by simp only [Nat.cast_mul, Nat.cast_ofNat]; linarith
    have hpow_le : (n : ℝ) ^ k ≤ ((2 * n : ℕ) : ℝ) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le_2n k
    calc ‖a n‖ ≤ C * (n : ℝ) ^ k := hbound
      _ ≤ |C| * (n : ℝ) ^ k := mul_le_mul_of_nonneg_right hC_abs hn_nonneg
      _ ≤ |C| * ((2 * n : ℕ) : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow_le (abs_nonneg C)
  · -- m is odd, so evenExt a m = 0
    have heq : evenExt a m = 0 := by
      simp only [evenExt]
      rw [Function.extend_apply']
      · rfl
      · intro ⟨n, hn⟩; exact heven ⟨n, by omega⟩
    rw [heq, norm_zero]
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
    rw [abs_of_nonneg hm_nonneg]
    exact mul_nonneg (abs_nonneg C) hm_nonneg

/-- toIntCoeff preserves polynomial growth (for atTop on ℤ). -/
lemma toIntCoeff_poly {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    toIntCoeff a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)) := by
  rw [Asymptotics.isBigO_iff] at ha ⊢
  obtain ⟨C, hC⟩ := ha
  use C
  rw [Filter.eventually_atTop] at hC ⊢
  obtain ⟨N, hN⟩ := hC
  refine ⟨(N : ℤ), fun m hm ↦ ?_⟩
  simp only [toIntCoeff]
  have hm_nonneg : 0 ≤ m := le_trans (Int.natCast_nonneg N) hm
  simp only [not_lt.mpr hm_nonneg, ↓reduceIte]
  have htoNat : m.toNat ≥ N := by omega
  have hm_eq : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_nonneg
  have hm_real_eq : (m.toNat : ℝ) = (m : ℝ) := by
    have h : (m.toNat : ℤ) = m := hm_eq
    exact congrArg (↑· : ℤ → ℝ) h
  have := hN m.toNat htoNat
  have hnat_nonneg : (0 : ℝ) ≤ (m.toNat : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
  have hint_nonneg : (0 : ℝ) ≤ (m : ℝ) ^ k := by rw [← hm_real_eq]; exact hnat_nonneg
  simp only [Real.norm_eq_abs, abs_of_nonneg hnat_nonneg] at this
  simp only [Real.norm_eq_abs, abs_of_nonneg hint_nonneg]
  calc ‖a m.toNat‖ ≤ C * (m.toNat : ℝ) ^ k := this
    _ = C * (m : ℝ) ^ k := by rw [hm_real_eq]

/-- c_E₂E₄E₆ has polynomial growth O(n^11).
    Cauchy product of two O(n^5) sequences, then even extension. -/
lemma c_E₂E₄E₆_poly : c_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  unfold c_E₂E₄E₆
  apply toIntCoeff_poly
  apply evenExt_poly
  -- cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆: O(n^5) × O(n^5) → O(n^{5+5+1}) = O(n^11)
  exact cauchyCoeff_poly a_E₂E₄E₆_poly a_E₂E₄E₆_poly

/-- c_E₄_E₂E₄E₆ has polynomial growth O(n^10).
    Cauchy product of O(n^4) and O(n^5) sequences, then even extension. -/
lemma c_E₄_E₂E₄E₆_poly : c_E₄_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 10 : ℝ)) := by
  unfold c_E₄_E₂E₄E₆
  apply toIntCoeff_poly
  apply evenExt_poly
  -- cauchyCoeff b_E₄ a_E₂E₄E₆: O(n^4) × O(n^5) → O(n^{4+5+1}) = O(n^10)
  exact cauchyCoeff_poly b_E₄_poly a_E₂E₄E₆_poly

/-- c_E₄_sq has polynomial growth O(n^9).
    Cauchy product of two O(n^4) sequences, then even extension. -/
lemma c_E₄_sq_poly : c_E₄_sq =O[Filter.atTop] (fun n ↦ (n ^ 9 : ℝ)) := by
  unfold c_E₄_sq
  apply toIntCoeff_poly
  apply evenExt_poly
  -- cauchyCoeff b_E₄ b_E₄: O(n^4) × O(n^4) → O(n^{4+4+1}) = O(n^9)
  exact cauchyCoeff_poly b_E₄_poly b_E₄_poly

/-! ## Q-Series Summability -/

/-- Summability of b_E₄ q-series. -/
lemma b_E₄_q_series_summable (z : ℍ) :
    Summable (fun n ↦ b_E₄ n * cexp (2 * π * Complex.I * n * z)) := by
  -- b_E₄(0) = 1, b_E₄(n) = 240 * σ₃(n) for n ≥ 1
  -- Use: (tail n ≥ 1) is 240 * sigma3_qexp which is summable
  have hsigma := sigma3_qexp_summable z
  -- Define the ℕ-indexed function f such that f(n+1) = original(n) for n : ℕ+
  let f : ℕ → ℂ := fun n ↦ (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z)
  -- f(n+1) is summable via summable_pnat_iff_summable_succ
  have hf_tail : Summable (fun n : ℕ ↦ f (n + 1)) := by
    rw [← summable_pnat_iff_summable_succ]
    convert hsigma using 1
  -- Our tail b_E₄(n+1) = 240 * f(n+1)
  have htail : Summable (fun n : ℕ ↦
      b_E₄ (n + 1) * cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) := by
    have hconv : (fun n : ℕ ↦ b_E₄ (n + 1) * cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) =
        (fun n : ℕ ↦ (240 : ℂ) * f (n + 1)) := by
      ext n
      simp only [b_E₄, Nat.add_one_ne_zero, ↓reduceIte, f]
      push_cast
      ring
    rw [hconv]
    exact Summable.mul_left 240 hf_tail
  -- Add back the n=0 term using summable_nat_add_iff
  rw [← summable_nat_add_iff 1]
  convert htail using 2 with n
  congr 2
  push_cast
  ring

/-- Summability of a_E₂E₄E₆ q-series. -/
lemma a_E₂E₄E₆_q_series_summable (z : ℍ) :
    Summable (fun n ↦ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) := by
  -- a_E₂E₄E₆(0) = 0, a_E₂E₄E₆(n) = 720 * n * σ₃(n) for n ≥ 1
  -- Use sigma_qexp_summable_generic 1 3 for n * σ₃(n)
  have hsigma := sigma_qexp_summable_generic 1 3 z
  simp only [pow_one] at hsigma
  -- Define the ℕ-indexed function
  let f : ℕ → ℂ := fun n ↦ (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z)
  -- f(n+1) is summable
  have hf_tail : Summable (fun n : ℕ ↦ f (n + 1)) := by
    rw [← summable_pnat_iff_summable_succ]
    convert hsigma using 1
  -- Our tail a_E₂E₄E₆(n+1) = 720 * f(n+1)
  have htail : Summable (fun n : ℕ ↦
      a_E₂E₄E₆ (n + 1) * cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) := by
    have hconv : (fun n : ℕ ↦ a_E₂E₄E₆ (n + 1) * cexp (2 * π * Complex.I * ((n : ℂ) + 1) * z)) =
        (fun n : ℕ ↦ (720 : ℂ) * f (n + 1)) := by
      ext n
      simp only [a_E₂E₄E₆, Nat.add_one_ne_zero, ↓reduceIte, f]
      push_cast
      ring
    rw [hconv]
    exact Summable.mul_left 720 hf_tail
  -- Add back the n=0 term
  rw [← summable_nat_add_iff 1]
  convert htail using 2 with n
  congr 2
  push_cast
  ring

/-- Norm summability of b_E₄ q-series. -/
lemma b_E₄_q_series_norm_summable (z : ℍ) :
    Summable (fun n ↦ ‖b_E₄ n * cexp (2 * π * Complex.I * n * z)‖) :=
  (b_E₄_q_series_summable z).norm

/-- Norm summability of a_E₂E₄E₆ q-series. -/
lemma a_E₂E₄E₆_q_series_norm_summable (z : ℍ) :
    Summable (fun n ↦ ‖a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)‖) :=
  (a_E₂E₄E₆_q_series_summable z).norm

/-- The antidiagonal sum of q-series factors as cauchyCoeff times q^n. -/
lemma antidiagonal_qexp_factor (a b : ℕ → ℂ) (z : ℍ) (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n,
      (a kl.1 * cexp (2 * π * Complex.I * kl.1 * z)) *
      (b kl.2 * cexp (2 * π * Complex.I * kl.2 * z)) =
    cauchyCoeff a b n * cexp (2 * π * Complex.I * n * z) := by
  simp only [cauchyCoeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_antidiagonal] at hkl
  have hexp : 2 * ↑π * Complex.I * ↑k * ↑z + 2 * ↑π * Complex.I * ↑l * ↑z =
      2 * ↑π * Complex.I * ↑n * ↑z := by rw [← hkl]; push_cast; ring
  calc a k * cexp (2 * ↑π * Complex.I * ↑k * ↑z) * (b l * cexp (2 * ↑π * Complex.I * ↑l * ↑z))
      = a k * b l * (cexp (2 * ↑π * Complex.I * ↑k * ↑z) *
          cexp (2 * ↑π * Complex.I * ↑l * ↑z)) := by ring
    _ = a k * b l * cexp (2 * ↑π * Complex.I * ↑k * ↑z +
          2 * ↑π * Complex.I * ↑l * ↑z) := by rw [← Complex.exp_add]
    _ = a k * b l * cexp (2 * ↑π * Complex.I * ↑n * ↑z) := by rw [hexp]

/-- The norm of exp(πiz) for z : ℍ is less than 1.
    Proof: |exp(πiz)| = exp(Re(πiz)) = exp(-π·z.im) < 1 since z.im > 0. -/
lemma norm_exp_pi_I_z_lt_one (z : ℍ) : ‖Complex.exp (π * Complex.I * z)‖ < 1 := by
  rw [Complex.norm_exp]
  have him : (π * Complex.I * (z : ℂ)).re = -π * z.im := by
    have h1 : (π * Complex.I : ℂ).re = 0 := by simp [Complex.I_re]
    have h2 : (π * Complex.I : ℂ).im = π := by simp [Complex.I_im]
    simp only [mul_re, h1, zero_mul, h2]
    simp only [UpperHalfPlane.coe_im]
    ring
  rw [him]
  have hneg : -π * z.im < 0 := by nlinarith [Real.pi_pos, z.im_pos]
  exact Real.exp_lt_one_iff.mpr hneg

/-- The norm of exp(2πiz) for z : ℍ is less than 1. -/
lemma norm_exp_2pi_I_z_lt_one (z : ℍ) : ‖cexp (2 * π * Complex.I * z)‖ < 1 := by
  have h1 := norm_exp_pi_I_z_lt_one z
  rw [show (2 : ℂ) * π * Complex.I * z = (π * Complex.I * z) + (π * Complex.I * z) by ring]
  rw [Complex.exp_add, Complex.norm_mul]
  have hnorm_nonneg : 0 ≤ ‖cexp (π * Complex.I * z)‖ := norm_nonneg _
  calc ‖cexp (π * Complex.I * z)‖ * ‖cexp (π * Complex.I * z)‖
      = ‖cexp (π * Complex.I * z)‖ ^ 2 := sq _ |>.symm
    _ < 1 := sq_lt_one_iff₀ hnorm_nonneg |>.mpr h1

/-- Generic summability of Cauchy product q-series with polynomial growth coefficients. -/
lemma summable_cauchy_q_series_of_poly {a b : ℕ → ℂ} {k ℓ : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (hb : b =O[Filter.atTop] (fun n ↦ (n ^ ℓ : ℝ))) (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff a b n * cexp (2 * π * Complex.I * n * z)) := by
  let r := cexp (2 * π * Complex.I * z)
  have hr : ‖r‖ < 1 := norm_exp_2pi_I_z_lt_one z
  have hpoly : cauchyCoeff a b =O[Filter.atTop] (fun n ↦ (↑(n ^ (k + ℓ + 1)) : ℝ)) := by
    have := cauchyCoeff_poly ha hb; convert this using 2; simp
  have h_eq : ∀ n : ℕ, cauchyCoeff a b n * cexp (2 * π * Complex.I * n * z) =
      cauchyCoeff a b n * r ^ n := fun n => by
    simp only [r, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [h_eq]
  exact Summable.of_norm (summable_real_norm_mul_geometric_of_norm_lt_one hr hpoly)

/-- Summability of Cauchy product of b_E₄ q-series. -/
lemma cauchy_b_E₄_q_series_summable (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff b_E₄ b_E₄ n * cexp (2 * π * Complex.I * n * z)) :=
  summable_cauchy_q_series_of_poly b_E₄_poly b_E₄_poly z

/-- Summability of Cauchy product of a_E₂E₄E₆ q-series. -/
lemma cauchy_a_E₂E₄E₆_q_series_summable (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) :=
  summable_cauchy_q_series_of_poly a_E₂E₄E₆_poly a_E₂E₄E₆_poly z

/-- Summability of Cauchy product of b_E₄ and a_E₂E₄E₆ q-series. -/
lemma cauchy_b_E₄_a_E₂E₄E₆_q_series_summable (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff b_E₄ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) :=
  summable_cauchy_q_series_of_poly b_E₄_poly a_E₂E₄E₆_poly z

/-! ## Q-Series Representations

Expressing Eisenstein series as ℕ-indexed q-series. -/

/-- E₄ as ℕ-indexed q-series with b_E₄ coefficients. -/
lemma E₄_as_q_series (z : ℍ) :
    E₄ z = ∑' (n : ℕ), b_E₄ n * cexp (2 * π * Complex.I * n * z) := by
  rw [E₄_sigma_qexp z]
  -- E₄ z = 1 + 240 * ∑' (n : ℕ+), σ₃(n) * exp(2πinz)
  -- Goal: 1 + 240 * ∑' (n : ℕ+), σ₃(n) * ... = ∑' (n : ℕ), b_E₄ n * ...
  -- b_E₄(0) = 1, b_E₄(n+1) = 240 * σ₃(n+1)
  have hsum : Summable (fun n : ℕ ↦ b_E₄ n * cexp (2 * π * Complex.I * n * z)) :=
    b_E₄_q_series_summable z
  rw [← tsum_pnat_eq_tsum_succ4 (fun n ↦ b_E₄ n * cexp (2 * π * Complex.I * n * z)) hsum]
  -- Goal: 1 + 240 * ... = b_E₄(0) * exp(0) + ∑' (n : ℕ+) b_E₄(n) * ...
  simp only [b_E₄, ↓reduceIte, Nat.cast_zero, mul_zero, PNat.ne_zero]
  -- Goal: 1 + 240 * ∑' ... = 1 * cexp(0 * z) + ∑' (240 * σ₃) * ...
  rw [← tsum_mul_left]
  congr 1
  · simp
  · congr 1; ext n; ring

/-- E₂E₄ - E₆ as ℕ-indexed q-series with a_E₂E₄E₆ coefficients. -/
lemma E₂E₄_sub_E₆_as_q_series (z : ℍ) :
    E₂ z * E₄ z - E₆ z = ∑' (n : ℕ), a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z) := by
  rw [E₂_mul_E₄_sub_E₆ z]
  -- E₂E₄ - E₆ = 720 * ∑' (n : ℕ+), n * σ₃(n) * exp(2πinz)
  -- a_E₂E₄E₆(0) = 0, a_E₂E₄E₆(n+1) = 720 * (n+1) * σ₃(n+1)
  have hsum : Summable (fun n : ℕ ↦ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) :=
    a_E₂E₄E₆_q_series_summable z
  rw [← tsum_pnat_eq_tsum_succ4 (fun n ↦ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) hsum]
  simp only [a_E₂E₄E₆, Nat.cast_zero, mul_zero, ↓reduceIte, zero_mul, zero_add, PNat.ne_zero]
  -- Goal: 720 * ∑' n * σ₃(n) * ... = ∑' (720 * n * σ₃(n)) * ...
  rw [← tsum_mul_left]
  congr 1
  ext n
  ring

/-! ## Q-Series to R-Series Conversion -/

/-- Converting a q-series (exp(2πinz)) to r-series (exp(πinz)) using even extension. -/
lemma q_series_eq_r_series (a : ℕ → ℂ) (z : ℍ)
    (hsum : Summable (fun n ↦ a n * cexp (2 * π * Complex.I * n * z))) :
    ∑' (n : ℕ), a n * cexp (2 * π * Complex.I * n * z) =
    ∑' (m : ℕ), evenExt a m * cexp (π * Complex.I * m * z) := by
  let f := fun m ↦ evenExt a m * cexp (π * Complex.I * m * z)
  have heven_sum : Summable (fun k ↦ f (2 * k)) := by
    convert hsum using 1
    ext k
    simp only [f, evenExt_even]
    congr 2
    push_cast
    ring
  have hodd_sum : Summable (fun k ↦ f (2 * k + 1)) := by
    simp only [f, evenExt_odd, zero_mul]; exact summable_zero
  rw [← tsum_even_add_odd heven_sum hodd_sum]
  simp only [f, evenExt_odd, zero_mul, tsum_zero, add_zero]
  congr 1
  ext k
  simp only [evenExt_even]
  congr 2
  push_cast
  ring

/-- Summability of r-series (exp(πinz)) with polynomial-growth evenExt coefficients. -/
lemma summable_evenExt_r_series {a b : ℕ → ℂ} {k ℓ : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (hb : b =O[Filter.atTop] (fun n ↦ (n ^ ℓ : ℝ))) (z : ℍ) :
    Summable (fun m ↦ evenExt (cauchyCoeff a b) m * cexp (π * Complex.I * m * z)) := by
  have hr : ‖cexp (π * Complex.I * z)‖ < 1 := norm_exp_pi_I_z_lt_one z
  have hpoly : evenExt (cauchyCoeff a b) =O[Filter.atTop]
      (fun n ↦ (↑(n ^ (k + ℓ + 1)) : ℝ)) := by
    have := evenExt_poly (cauchyCoeff_poly ha hb)
    convert this using 2; simp
  have h_eq : ∀ n : ℕ, evenExt (cauchyCoeff a b) n * cexp (π * Complex.I * n * z) =
      evenExt (cauchyCoeff a b) n * (cexp (π * Complex.I * z)) ^ n := fun n => by
    rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [h_eq]
  exact Summable.of_norm (summable_real_norm_mul_geometric_of_norm_lt_one hr hpoly)

/-! ## Summability Lemmas

The Fourier series terms are summable because:
1. Coefficients have polynomial growth O(n^k)
2. Exponential factor exp(-π·n·z.im) decays geometrically for z.im > 0
3. Polynomial times geometric is summable -/

/-- Summability of fouterm series with polynomial-growth coefficients.
    For z : ℍ, the exponential term exp(πinz) has norm exp(-πn·z.im) < 1,
    so polynomial-growth coefficients give a summable series.

    Proof sketch:
    1. Rewrite fouterm c z (i + n₀) = u(i) * r^i where r = exp(πiz), u(i) = c(i+n₀) * const
    2. ‖r‖ = exp(-π·z.im) < 1 (by norm_exp_pi_I_z_lt_one)
    3. u has O(n^k) growth (isBigO_shift + multiplication by constant)
    4. Apply summable_real_norm_mul_geometric_of_norm_lt_one -/
lemma summable_fouterm_of_poly {c : ℤ → ℂ} {k : ℕ}
    (hpoly : c =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (z : ℍ) (n₀ : ℤ) : Summable fun (i : ℕ) ↦ fouterm c z (i + n₀) := by
  -- Key fact: ‖exp(πiz)‖ < 1 for z : ℍ
  have hr : ‖Complex.exp (π * Complex.I * z)‖ < 1 := norm_exp_pi_I_z_lt_one z
  -- Shifted coefficients have polynomial growth (reusing hpoly' from PolyFourierCoeffBound)
  have hshift := hpoly' c n₀ k hpoly
  -- Factor fouterm c z (i + n₀) = u(i) * r^i
  -- where r = cexp(π * I * z) and u(i) = c(i + n₀) * cexp(π * I * n₀ * z)
  let r := cexp (π * Complex.I * z)
  let const := cexp (π * Complex.I * n₀ * z)
  let u : ℕ → ℂ := fun i => c (i + n₀) * const
  have h_factor : ∀ i : ℕ, fouterm c z (i + n₀) = u i * r ^ i := fun i => by
    simp only [fouterm, u, r, const, ← Complex.exp_nat_mul, Int.cast_add, Int.cast_natCast]
    rw [show (↑π * Complex.I * (↑i + ↑n₀) * ↑z : ℂ) =
        ↑π * Complex.I * ↑n₀ * ↑z + ↑π * Complex.I * ↑i * ↑z by ring, Complex.exp_add]
    ring
  -- u has polynomial growth: ‖u n‖ = ‖c(n+n₀)‖ * ‖const‖ is O(n^k)
  have hu : u =O[Filter.atTop] (fun n ↦ (↑(n ^ k) : ℝ)) := by
    simp only [u, show ∀ i, c (↑i + n₀) * const = const * c (↑i + n₀) from fun _ => mul_comm _ _]
    convert hshift.const_mul_left const using 2 with n
    simp only [Nat.cast_pow]
  -- Apply summability theorem
  simp_rw [h_factor]
  exact Summable.of_norm (summable_real_norm_mul_geometric_of_norm_lt_one hr hu)

/-- Summability for (E₂E₄ - E₆)² expansion (n₀ = 4). -/
lemma summable_E₂E₄E₆_sq (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₂E₄E₆ z (i + 4) :=
  summable_fouterm_of_poly c_E₂E₄E₆_poly z 4

/-- Summability for E₄(E₂E₄ - E₆) expansion (n₀ = 2). -/
lemma summable_E₄_E₂E₄E₆ (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₄_E₂E₄E₆ z (i + 2) :=
  summable_fouterm_of_poly c_E₄_E₂E₄E₆_poly z 2

/-- Summability for E₄² expansion (n₀ = 0). -/
lemma summable_E₄_sq (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₄_sq z (i + 0) :=
  summable_fouterm_of_poly c_E₄_sq_poly z 0

/-! ## Fourier Expansion Identities

These connect the Eisenstein series products to fouterm sums.
The proofs use `E₂_mul_E₄_sub_E₆` and `E₄_sigma_qexp` from `FG.lean`. -/

/-- Fourier expansion of (E₂E₄ - E₆)².
    In q = exp(2πiz) convention: (E₂E₄ - E₆) = 720·∑_{n≥1} n·σ₃(n)·qⁿ
    The square starts at q², which is r⁴ in r = exp(πiz) convention. -/
lemma E₂E₄E₆_sq_fourier (x : ℍ) :
    ((E₂ x) * (E₄ x) - (E₆ x)) ^ 2 = ∑' (n : ℕ), fouterm c_E₂E₄E₆ x (n + 4) := by
  -- Step 1: (E₂E₄ - E₆) as q-series
  have hE₂E₄E₆ := E₂E₄_sub_E₆_as_q_series x
  -- Step 2: Square
  simp only [sq, hE₂E₄E₆]
  -- Step 3: Apply Cauchy product formula
  have hnorm := a_E₂E₄E₆_q_series_norm_summable x
  have hsum := a_E₂E₄E₆_q_series_summable x
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hnorm hsum hnorm hsum]
  -- Step 4: Factor out exponential
  simp only [antidiagonal_qexp_factor]
  -- Step 5: Convert q-series to r-series
  have hcauchy_sum := cauchy_a_E₂E₄E₆_q_series_summable x
  rw [q_series_eq_r_series (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) x hcauchy_sum]
  -- Step 6: Show the first 4 terms are zero, then reindex
  -- Since a_E₂E₄E₆(0) = 0:
  -- - cauchyCoeff(a,a)(0) = a(0)*a(0) = 0
  -- - cauchyCoeff(a,a)(1) = a(0)*a(1) + a(1)*a(0) = 0
  -- In r-space: evenExt puts 0 for odd, so m=0,1,2,3 all give 0
  have ha0 : a_E₂E₄E₆ 0 = 0 := by simp only [a_E₂E₄E₆, ↓reduceIte]
  have hcauchy0 : cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆ 0 = 0 := by
    simp only [cauchyCoeff]
    -- antidiagonal 0 = {(0,0)}, so this is a(0)*a(0) = 0*0 = 0
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, ha0, zero_mul]
  have hcauchy1 : cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆ 1 = 0 := by
    simp only [cauchyCoeff]
    apply Finset.sum_eq_zero
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_antidiagonal] at hij
    rcases Nat.eq_zero_or_pos i with hi | hi
    · simp only [hi, ha0, zero_mul]
    · have hj : j = 0 := by omega
      simp only [hj, ha0, mul_zero]
  have heven0 : evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) 0 = 0 := by
    have h : (0 : ℕ) = 2 * 0 := by omega
    rw [h, evenExt_even, hcauchy0]
  have heven1 : evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) 1 = 0 := by
    have h : (1 : ℕ) = 2 * 0 + 1 := by omega
    rw [h, evenExt_odd]
  have heven2 : evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) 2 = 0 := by
    have h : (2 : ℕ) = 2 * 1 := by omega
    rw [h, evenExt_even, hcauchy1]
  have heven3 : evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) 3 = 0 := by
    have h : (3 : ℕ) = 2 * 1 + 1 := by omega
    rw [h, evenExt_odd]
  have hzero_small : ∀ m < 4, evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) m *
      cexp (π * Complex.I * m * x) = 0 := by
    intro m hm
    interval_cases m <;> simp only [heven0, heven1, heven2, heven3, zero_mul]
  -- Summability of r-series
  have hsum_r : Summable (fun m ↦ evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) m *
      cexp (π * Complex.I * m * x)) := summable_evenExt_r_series a_E₂E₄E₆_poly a_E₂E₄E₆_poly x
  -- The full sum equals sum from m=4 onwards
  have hsplit : ∑' m, evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) m * cexp (π * Complex.I * m * x) =
      ∑' (n : ℕ), evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) (n + 4) *
        cexp (π * Complex.I * (n + 4) * x) := by
    rw [← hsum_r.sum_add_tsum_nat_add 4]
    -- First 4 terms are zero
    have h04 : ∑ m ∈ Finset.range 4, evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆) m *
        cexp (π * Complex.I * m * x) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_range] at hm
      exact hzero_small m hm
    rw [h04, zero_add]
    -- Match the index expressions
    congr 1
    ext n
    congr 2
    push_cast; ring
  rw [hsplit]
  -- Now match with fouterm
  congr 1
  ext n
  simp only [fouterm, c_E₂E₄E₆, toIntCoeff]
  have hpos : ¬((n : ℤ) + 4 < 0) := by omega
  simp only [hpos, ↓reduceIte]
  have htoNat : ((n : ℤ) + 4).toNat = n + 4 := by omega
  rw [htoNat]
  congr 2
  push_cast
  ring

/-- Fourier expansion of E₄(E₂E₄ - E₆).
    Product starts at q¹, which is r² in fouterm convention. -/
lemma E₄_E₂E₄E₆_fourier (x : ℍ) :
    E₄ x * (E₂ x * E₄ x - E₆ x) = ∑' (n : ℕ), fouterm c_E₄_E₂E₄E₆ x (n + 2) := by
  -- Step 1: E₄ and (E₂E₄ - E₆) as q-series
  have hE₄ := E₄_as_q_series x
  have hE₂E₄E₆ := E₂E₄_sub_E₆_as_q_series x
  rw [hE₂E₄E₆, hE₄]
  -- Step 2: Apply Cauchy product formula
  have hnorm_b := b_E₄_q_series_norm_summable x
  have hsum_b := b_E₄_q_series_summable x
  have hnorm_a := a_E₂E₄E₆_q_series_norm_summable x
  have hsum_a := a_E₂E₄E₆_q_series_summable x
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hnorm_b hsum_b hnorm_a hsum_a]
  -- Step 3: Factor out exponential
  simp only [antidiagonal_qexp_factor]
  -- Step 4: Convert q-series to r-series
  have hcauchy_sum := cauchy_b_E₄_a_E₂E₄E₆_q_series_summable x
  rw [q_series_eq_r_series (cauchyCoeff b_E₄ a_E₂E₄E₆) x hcauchy_sum]
  -- Step 5: Show the first 2 terms are zero, then reindex
  -- Since a_E₂E₄E₆(0) = 0:
  -- cauchyCoeff(b,a)(0) = b(0)*a(0) = 1*0 = 0
  -- In r-space: evenExt(cauchyCoeff) 0 = 0, evenExt(cauchyCoeff) 1 = 0 (odd)
  have ha0 : a_E₂E₄E₆ 0 = 0 := by simp only [a_E₂E₄E₆, ↓reduceIte]
  have hcauchy0 : cauchyCoeff b_E₄ a_E₂E₄E₆ 0 = 0 := by
    simp only [cauchyCoeff]
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, ha0, mul_zero]
  have heven0 : evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) 0 = 0 := by
    have h : (0 : ℕ) = 2 * 0 := by omega
    rw [h, evenExt_even, hcauchy0]
  have heven1 : evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) 1 = 0 := by
    have h : (1 : ℕ) = 2 * 0 + 1 := by omega
    rw [h, evenExt_odd]
  have hzero_small : ∀ m < 2, evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) m *
      cexp (π * Complex.I * m * x) = 0 := by
    intro m hm
    interval_cases m <;> simp only [heven0, heven1, zero_mul]
  -- Summability of r-series
  have hsum_r : Summable (fun m ↦ evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) m *
      cexp (π * Complex.I * m * x)) := summable_evenExt_r_series b_E₄_poly a_E₂E₄E₆_poly x
  -- The full sum equals sum from m=2 onwards
  have hsplit : ∑' m, evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) m * cexp (π * Complex.I * m * x) =
      ∑' (n : ℕ), evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) (n + 2) *
        cexp (π * Complex.I * (n + 2) * x) := by
    rw [← hsum_r.sum_add_tsum_nat_add 2]
    have h02 : ∑ m ∈ Finset.range 2, evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆) m *
        cexp (π * Complex.I * m * x) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_range] at hm
      exact hzero_small m hm
    rw [h02, zero_add]
    congr 1
    ext n
    congr 2
    push_cast; ring
  rw [hsplit]
  -- Now match with fouterm
  congr 1
  ext n
  simp only [fouterm, c_E₄_E₂E₄E₆, toIntCoeff]
  have hpos : ¬((n : ℤ) + 2 < 0) := by omega
  simp only [hpos, ↓reduceIte]
  have htoNat : ((n : ℤ) + 2).toNat = n + 2 := by omega
  rw [htoNat]
  congr 2
  push_cast
  ring

/-- Fourier expansion of E₄².
    E₄ = 1 + 240·∑_{n≥1} σ₃(n)·qⁿ, so E₄² starts at constant term 1. -/
lemma E₄_sq_fourier (x : ℍ) :
    E₄ x ^ 2 = ∑' (n : ℕ), fouterm c_E₄_sq x (n + 0) := by
  -- Step 1: E₄ as q-series
  have hE₄ := E₄_as_q_series x
  -- Step 2: E₄² = (∑ b_E₄(n) q^n)²
  simp only [sq, hE₄]
  -- Step 3: Apply Cauchy product formula
  have hnorm_f := b_E₄_q_series_norm_summable x
  have hsum_f := b_E₄_q_series_summable x
  -- The product of two summable series equals tsum of Cauchy product
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hnorm_f hsum_f hnorm_f hsum_f]
  -- Step 4: Factor out exponential using antidiagonal_qexp_factor
  simp only [antidiagonal_qexp_factor]
  -- Step 5: Convert q-series to r-series
  rw [q_series_eq_r_series (cauchyCoeff b_E₄ b_E₄) x (cauchy_b_E₄_q_series_summable x)]
  -- Step 6: Match with fouterm c_E₄_sq
  -- c_E₄_sq n = toIntCoeff (evenExt (cauchyCoeff b_E₄ b_E₄)) n
  -- For n : ℕ, toIntCoeff a n = a n, and fouterm uses exp(πinz)
  -- Both sides are definitionally equal after unfolding
  congr 1

end MagicFunction.a.FourierExpansions

end

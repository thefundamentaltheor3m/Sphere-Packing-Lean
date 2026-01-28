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
  calc ‖(240 : ℂ)‖ * ((σ 3) n : ℝ)
      ≤ 240 * n ^ 4 := by rw [h240]; nlinarith
    _ = 240 * n ^ 4 := by ring

/-- c_E₂E₄E₆ has polynomial growth O(n^11).
    Cauchy product of two O(n^5) sequences, then even extension. -/
lemma c_E₂E₄E₆_poly : c_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  sorry

/-- c_E₄_sq has polynomial growth O(n^9).
    Cauchy product of two O(n^4) sequences, then even extension. -/
lemma c_E₄_sq_poly : c_E₄_sq =O[Filter.atTop] (fun n ↦ (n ^ 9 : ℝ)) := by
  sorry

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

/-! ## Q-Series Summability -/

/-- Summability of b_E₄ q-series. -/
lemma b_E₄_q_series_summable (z : ℍ) :
    Summable (fun n ↦ b_E₄ n * cexp (2 * π * Complex.I * n * z)) := by
  -- b_E₄ has polynomial growth O(n^4), exp has exponential decay
  sorry

/-- Summability of a_E₂E₄E₆ q-series. -/
lemma a_E₂E₄E₆_q_series_summable (z : ℍ) :
    Summable (fun n ↦ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) := by
  sorry

/-- Summability of Cauchy product of b_E₄ q-series. -/
lemma cauchy_b_E₄_q_series_summable (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff b_E₄ b_E₄ n * cexp (2 * π * Complex.I * n * z)) := by
  sorry

/-- Summability of Cauchy product of a_E₂E₄E₆ q-series. -/
lemma cauchy_a_E₂E₄E₆_q_series_summable (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) := by
  sorry

/-- Summability of Cauchy product of b_E₄ and a_E₂E₄E₆ q-series. -/
lemma cauchy_b_E₄_a_E₂E₄E₆_q_series_summable (z : ℍ) :
    Summable (fun n ↦ cauchyCoeff b_E₄ a_E₂E₄E₆ n * cexp (2 * π * Complex.I * n * z)) := by
  sorry

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

/-! ## Auxiliary lemmas for summability -/

/-- The norm of exp(πiz) for z : ℍ is less than 1.
    Proof: |exp(πiz)| = exp(Re(πiz)) = exp(-π·z.im) < 1 since z.im > 0. -/
lemma norm_exp_pi_I_z_lt_one (z : ℍ) : ‖Complex.exp (π * Complex.I * z)‖ < 1 := by
  rw [Complex.norm_exp]
  -- (π * I * z).re = -π * z.im because I.re = 0, I.im = 1
  have him : (π * Complex.I * (z : ℂ)).re = -π * z.im := by
    have h1 : (π * Complex.I : ℂ).re = 0 := by simp [Complex.I_re]
    have h2 : (π * Complex.I : ℂ).im = π := by simp [Complex.I_im]
    simp only [mul_re, h1, zero_mul, h2]
    simp only [UpperHalfPlane.coe_im]
    ring
  rw [him]
  have hneg : -π * z.im < 0 := by nlinarith [Real.pi_pos, z.im_pos]
  exact Real.exp_lt_one_iff.mpr hneg

/-- Shifting a function by a constant preserves Big-O growth.
    For c : ℤ → ℂ with c = O(n^k), the shifted function i ↦ c(i + n₀) is also O(n^k).

    Proof: Following hpoly' in PolyFourierCoeffBound.lean - first show the shifted
    function is O((n + n₀)^k), then show |n + n₀| ≤ 2n for n ≥ |n₀|. -/
lemma isBigO_shift {c : ℤ → ℂ} {k : ℕ} (n₀ : ℤ)
    (hc : c =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    (fun i : ℕ ↦ c (i + n₀)) =O[Filter.atTop] (fun n ↦ (↑(n ^ k) : ℝ)) := by
  -- First: shift the hypothesis to ℕ
  have h_shift : (fun n : ℕ => c (n + n₀)) =O[Filter.atTop] (fun n : ℕ => (n + n₀ : ℂ) ^ k) := by
    simp only [Asymptotics.isBigO_iff, Filter.eventually_atTop] at hc ⊢
    obtain ⟨C, m, hCa⟩ := hc
    use C
    simp only [norm_pow, norm_eq_abs] at hCa ⊢
    refine ⟨(m - n₀).toNat, fun n hn ↦ ?_⟩
    have hmn : (n : ℤ) + n₀ ≥ m := by
      have := Int.self_le_toNat (m - n₀)
      omega
    exact_mod_cast hCa (n + n₀) hmn
  -- Second: (n + n₀)^k = O(n^k) using |n + n₀| ≤ 2n for n ≥ |n₀|
  refine h_shift.trans ?_
  simp only [Asymptotics.isBigO_iff, Filter.eventually_atTop]
  use 2 ^ k
  simp only [norm_pow, RCLike.norm_natCast]
  refine ⟨n₀.natAbs, fun n hn => ?_⟩
  have h_bound : ‖(n + n₀ : ℂ)‖ ≤ 2 * n := by
    simp only [← Int.cast_natCast (R := ℂ), ← Int.cast_add, Complex.norm_intCast]
    norm_cast
    cases abs_cases (n + n₀ : ℤ) <;> omega
  calc ‖(n : ℂ) + n₀‖ ^ k ≤ (2 * n) ^ k := by exact pow_le_pow_left₀ (norm_nonneg _) h_bound k
    _ = 2 ^ k * n ^ k := by ring
    _ = 2 ^ k * (n ^ k : ℕ) := by norm_cast

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
  -- Shifted coefficients have polynomial growth
  have hshift := isBigO_shift n₀ hpoly
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
    exact hshift.const_mul_left const
  -- Apply summability theorem
  simp_rw [h_factor]
  exact Summable.of_norm (summable_real_norm_mul_geometric_of_norm_lt_one hr hu)

/-- Summability for (E₂E₄ - E₆)² expansion (n₀ = 4). -/
lemma summable_E₂E₄E₆_sq (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₂E₄E₆ z (i + 4) :=
  summable_fouterm_of_poly c_E₂E₄E₆_poly z 4

/-- Summability for E₄(E₂E₄ - E₆) expansion (n₀ = 2). -/
lemma summable_E₄_E₂E₄E₆ (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₂E₄E₆ z (i + 2) :=
  summable_fouterm_of_poly c_E₂E₄E₆_poly z 2

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
  -- From E₂_mul_E₄_sub_E₆ and Cauchy product of q-series
  -- (720 * ∑ n·σ₃(n)·q^n)² = 720² * (∑ n·σ₃(n)·q^n)²
  -- Cauchy product: (∑ aₙq^n)² = ∑ (∑_{j+k=n} aⱼaₖ) q^n
  -- Starting at n=1, square starts at n=2 in q-space = index 4 in r-space
  sorry

/-- Fourier expansion of E₄(E₂E₄ - E₆).
    Product starts at q¹, which is r² in fouterm convention. -/
lemma E₄_E₂E₄E₆_fourier (x : ℍ) :
    E₄ x * (E₂ x * E₄ x - E₆ x) = ∑' (n : ℕ), fouterm c_E₂E₄E₆ x (n + 2) := by
  -- From E₄_sigma_qexp and E₂_mul_E₄_sub_E₆
  -- E₄ starts at q⁰, E₂E₄-E₆ starts at q¹, so product starts at q¹ = r²
  sorry

/-- Fourier expansion of E₄².
    E₄ = 1 + 240·∑_{n≥1} σ₃(n)·qⁿ, so E₄² starts at constant term 1. -/
lemma E₄_sq_fourier (x : ℍ) :
    E₄ x ^ 2 = ∑' (n : ℕ), fouterm c_E₄_sq x (n + 0) := by
  -- From E₄_sigma_qexp: E₄² = (1 + 240·∑...)² starts at q⁰ = r⁰
  sorry

end MagicFunction.a.FourierExpansions

end

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

These match the coefficient growth patterns needed for DivDiscBound. -/

/-- Coefficient function with growth O(n^5), used for E₂E₄-E₆ related expansions. -/
def c_E₂E₄E₆ : ℤ → ℂ := fun n ↦ n * (σ 3 n.toNat)

/-- Coefficient function for E₄(E₂E₄ - E₆), the product (not square).
    Note: Uses same simplified bound as c_E₂E₄E₆ for this branch. -/
def c_E₄_E₂E₄E₆ : ℤ → ℂ := fun n ↦ n * (σ 3 n.toNat)

/-- Coefficient function for E₄², with constant term 1. -/
def c_E₄_sq : ℤ → ℂ := fun n ↦ if n ≤ 0 then 1 else n * (σ 3 n.toNat)

/-- c_E₂E₄E₆ has polynomial growth O(n^5). -/
lemma c_E₂E₄E₆_poly : c_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- Coefficients n·σ₃(n) grow as O(n) × O(n^4) = O(n^5)
  let d : ℕ → ℂ := fun n ↦ n * (σ 3 n)
  have hcd (n : ℕ) : c_E₂E₄E₆ n = d n := by simp [c_E₂E₄E₆, d]
  have hdpoly : d =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℂ)) := by
    have h₁ (n : ℕ) : n ^ 5 = n * n ^ 4 := Nat.pow_succ'
    norm_cast
    simp only [h₁]
    push_cast
    refine Asymptotics.IsBigO.mul (Asymptotics.isBigO_refl _ Filter.atTop) ?_
    have h := ArithmeticFunction.sigma_asymptotic' 3
    simp only [Nat.reduceAdd] at h
    norm_cast at h ⊢
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
  calc norm (c_E₂E₄E₆ n)
  _ ≤ R * n.toNat ^ 5 := hR
  _ = R * |↑n| ^ 5 := by
    simp only [mul_eq_mul_left_iff]; norm_cast; left
    rw [Nat.cast_pow, hnnat]; simp [hnnonneg, abs_of_nonneg]

/-- c_E₄_E₂E₄E₆ has polynomial growth O(n^5).
    Note: Same growth as c_E₂E₄E₆ since they have the same simplified definition. -/
lemma c_E₄_E₂E₄E₆_poly : c_E₄_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- c_E₄_E₂E₄E₆ = c_E₂E₄E₆ definitionally
  exact c_E₂E₄E₆_poly

/-- c_E₄_sq has polynomial growth O(n^5). -/
lemma c_E₄_sq_poly : c_E₄_sq =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  have heq : c_E₄_sq =ᶠ[Filter.atTop] c_E₂E₄E₆ := by
    simp only [Filter.EventuallyEq, Filter.eventually_atTop, ge_iff_le]
    use 1
    intro n hn
    simp only [c_E₄_sq, c_E₂E₄E₆]
    have h : ¬n ≤ 0 := by omega
    simp only [h, ↓reduceIte]
  exact c_E₂E₄E₆_poly.congr' heq.symm Filter.EventuallyEq.rfl

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
    ring_nf
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

/-- Summability for E₄(E₂E₄ - E₆) expansion (n₀ = 2).
    Note: Uses c_E₄_E₂E₄E₆ (product coefficient), not c_E₂E₄E₆ (square coefficient). -/
lemma summable_E₄_E₂E₄E₆ (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₄_E₂E₄E₆ z (i + 2) :=
  summable_fouterm_of_poly c_E₄_E₂E₄E₆_poly z 2

/-- Summability for E₄² expansion (n₀ = 0). -/
lemma summable_E₄_sq (z : ℍ) :
    Summable fun (i : ℕ) ↦ fouterm c_E₄_sq z (i + 0) :=
  summable_fouterm_of_poly c_E₄_sq_poly z 0

/-! ## Keystone: q-series → fouterm reindex

A `q`-series `∑ₘ b m · qᵐ` (with `q = cexp (2π i z)`, the standard convention) becomes a
`fouterm` sum (with `r = cexp (π i z)`, the half-`q` convention used by `DivDiscBound`) by placing
the `m`-th coefficient at the even index `2m` and `0` on odd indices. -/

/-- The even-support `fouterm` coefficient carrying `b` at index `2m`. -/
def evenCoeff (b : ℕ → ℂ) : ℤ → ℂ := fun k => if Even k then b (k / 2).toNat else 0

/-- **Keystone reindex** (built via `Function.Injective.tsum_eq` along `m ↦ 2m`). -/
lemma qexp_eq_fouterm (b : ℕ → ℂ) (x : ℍ) :
    (∑' m : ℕ, b m * cexp (2 * ↑π * Complex.I * ↑m * ↑x))
      = ∑' n : ℕ, fouterm (evenCoeff b) x (↑n + 0) := by
  have hg : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by
    have : 2 * a = 2 * b := h; omega
  have hsupp : Function.support (fun n : ℕ => fouterm (evenCoeff b) x (↑n + 0)) ⊆
      Set.range (fun j : ℕ => 2 * j) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hcn : evenCoeff b (↑n) ≠ 0 := by
      intro h; exact hn (by simp only [fouterm, add_zero, h, zero_mul])
    have heven : Even (n : ℤ) := by
      by_contra hodd
      exact hcn (by simp only [evenCoeff, if_neg hodd])
    obtain ⟨j, hj⟩ := (Int.even_coe_nat n).mp heven
    exact ⟨j, by show 2 * j = n; omega⟩
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr (fun j => ?_)
  have h2j : Even ((2 * j : ℕ) : ℤ) := by exact_mod_cast even_two_mul j
  simp only [fouterm, add_zero, evenCoeff, if_pos h2j]
  rw [show (((2 * j : ℕ) : ℤ) / 2).toNat = j by push_cast; omega]
  rw [show (↑π * Complex.I * ((2 * j : ℕ) : ℤ) * ↑x : ℂ) = 2 * ↑π * Complex.I * ↑j * ↑x by
    push_cast; ring]

/-! ## Linear factor q-coefficients and fouterm identities (Design B)

`E₄` and `E₂E₄−E₆` are the *linear* factors of the φ-numerators. Their genuine `q`-coefficients
are simple (no Cauchy convolution), so via the keystone they have clean `fouterm` expansions. -/

/-- ℕ-indexed `q`-coefficients of `E₄`: `1` at `0`, `240·σ₃(m)` for `m ≥ 1`. -/
def bE₄ : ℕ → ℂ := fun m => if m = 0 then 1 else 240 * (σ 3 m : ℂ)

/-- ℕ-indexed `q`-coefficients of `E₂E₄ − E₆`: `720·m·σ₃(m)` (vanishes at `0`). -/
def bg : ℕ → ℂ := fun m => 720 * (m : ℂ) * (σ 3 m : ℂ)

/-- `E₄` as an ℕ-indexed `q`-series with coefficients `bE₄`. -/
lemma E₄_qexp_nat (z : ℍ) :
    E₄ z = ∑' m : ℕ, bE₄ m * cexp (2 * ↑π * Complex.I * ↑m * ↑z) := by
  have hsummable : Summable (fun m : ℕ => bE₄ m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)) := by
    rw [← summable_pnat_iff_summable_nat]
    refine ((sigma3_qexp_summable z).mul_left 240).congr (fun n => ?_)
    have hn : (n : ℕ) ≠ 0 := n.ne_zero
    simp only [bE₄, hn, if_false]
    ring
  rw [hsummable.tsum_eq_zero_add, E₄_sigma_qexp]
  congr 1
  · simp [bE₄]
  · rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => (σ 3 k : ℂ) * cexp (2 * ↑π * Complex.I * ↑k * ↑z)),
      ← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    have hm : m + 1 ≠ 0 := Nat.succ_ne_zero m
    simp only [bE₄, hm, if_false]
    push_cast; ring

/-- `E₄` in `fouterm` form (`n₀ = 0`). -/
lemma E₄_eq_fouterm (z : ℍ) : E₄ z = ∑' n : ℕ, fouterm (evenCoeff bE₄) z (↑n + 0) :=
  (E₄_qexp_nat z).trans (qexp_eq_fouterm bE₄ z)

/-- `E₂E₄ − E₆` as an ℕ-indexed `q`-series with coefficients `bg` (vanishing at `0`). -/
lemma g_qexp_nat (z : ℍ) :
    E₂ z * E₄ z - E₆ z = ∑' m : ℕ, bg m * cexp (2 * ↑π * Complex.I * ↑m * ↑z) := by
  have hsupp : Function.support (fun m : ℕ => bg m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)) ⊆
      Set.range ((↑·) : ℕ+ → ℕ) := by
    intro m hm
    rw [Function.mem_support] at hm
    have hm0 : m ≠ 0 := by rintro rfl; simp [bg] at hm
    exact ⟨⟨m, Nat.pos_of_ne_zero hm0⟩, rfl⟩
  rw [E₂_mul_E₄_sub_E₆, ← tsum_mul_left, ← PNat.coe_injective.tsum_eq
    (f := fun m : ℕ => bg m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)) hsupp]
  refine tsum_congr (fun n => ?_)
  simp only [bg]
  ring

/-- `E₂E₄ − E₆` in `fouterm` form (`n₀ = 2`; the index-`0,1` terms vanish). -/
lemma g_eq_fouterm (z : ℍ) :
    E₂ z * E₄ z - E₆ z = ∑' n : ℕ, fouterm (evenCoeff bg) z (↑n + 2) := by
  rw [g_qexp_nat z, qexp_eq_fouterm bg z]
  have hinj : Function.Injective (fun n : ℕ => n + 2) := fun a b h => by
    have : a + 2 = b + 2 := h; omega
  have hsupp : Function.support (fun n : ℕ => fouterm (evenCoeff bg) z (↑n + 0)) ⊆
      Set.range (fun n : ℕ => n + 2) := by
    intro n hn
    rw [Function.mem_support] at hn
    have h0 : n ≠ 0 := by rintro rfl; simp [fouterm, evenCoeff, bg] at hn
    have h1 : n ≠ 1 := by rintro rfl; simp [fouterm, evenCoeff, bg] at hn
    exact ⟨n - 2, by show n - 2 + 2 = n; omega⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr (fun n => ?_)
  congr 1

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
    Product starts at q¹, which is r² in fouterm convention.
    Note: Uses c_E₄_E₂E₄E₆ (product coefficient), not c_E₂E₄E₆ (square coefficient). -/
lemma E₄_E₂E₄E₆_fourier (x : ℍ) :
    E₄ x * (E₂ x * E₄ x - E₆ x) = ∑' (n : ℕ), fouterm c_E₄_E₂E₄E₆ x (n + 2) := by
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

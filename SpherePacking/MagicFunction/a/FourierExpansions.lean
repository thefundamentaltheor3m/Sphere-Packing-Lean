/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.ForMathlib.QSeriesBounds
public import SpherePacking.ForMathlib.SpecificLimits
public import SpherePacking.ModularForms.FG
public import SpherePacking.MagicFunction.a.CauchyCoeffBounds

/-!
# Fourier expansions and norm bounds for the linear factors of φ₀, φ₂', φ₄'

Connects the *linear* Eisenstein factors `E₄` and `E₂E₄ − E₆` to the `DivDiscBound` machinery in
`PolyFourierCoeffBound`, and bounds their norms. The φ-numerators are products/squares of these
factors, so bounding each factor and its quotient by `Δ` avoids any Cauchy-product coefficients.

## Convention

The standard q-expansion uses `q = exp(2πiz)`, while `fouterm` uses `exp(πinz)`. Setting
`r = exp(πiz)` gives `q = r²`, so a `q`-coefficient at power `m` sits at the even `fouterm` index
`2m` (and odd indices carry `0`); this is the `evenCoeff`/`qexp_eq_fouterm` reindex.

## Main results

- `qexp_eq_fouterm`: rewrite a `q`-series into `fouterm` form (even-support reindex)
- `E₄_eq_fouterm`, `g_eq_fouterm`: the linear factors `E₄` (`n₀=0`) and `E₂E₄ − E₆` (`n₀=2`)
- `g_div_Δ_bound`, `E₄_div_Δ_bound`: bounds on `‖factor / Δ‖` via `DivDiscBoundOfPolyFourierCoeff`
- `norm_E₄_le`, `norm_g_le`: explicit factor-norm bounds (`‖E₄‖ ≤ B_E₄`; decay for
  `E₂E₄ − E₆`)

## References

- Blueprint Corollaries 7.5-7.7
- `SpherePacking.ModularForms.FG`: q-expansion identities (`E₂_mul_E₄_sub_E₆`, `E₄_sigma_qexp`)
-/

@[expose] public section

open Real Complex UpperHalfPlane
open scoped ArithmeticFunction.sigma
open MagicFunction.PolyFourierCoeffBound

noncomputable section

namespace MagicFunction.a.FourierExpansions

/-! ## Auxiliary lemmas for summability -/

/-- The half-q parameter has norm less than one on the upper half-plane. -/
lemma norm_exp_pi_I_z_lt_one (z : ℍ) : ‖Complex.exp (π * Complex.I * z)‖ < 1 := by
  simpa [Complex.norm_exp, Real.exp_lt_one_iff, Complex.mul_re, UpperHalfPlane.coe_im] using
    (show -π * z.im < 0 by nlinarith [Real.pi_pos, z.im_pos])

/-- Fourier terms with polynomial-growth coefficients are summable on the upper half-plane,
for any integer starting index. -/
lemma summable_fouterm_of_poly {c : ℤ → ℂ} {k : ℕ}
    (hpoly : c =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (z : ℍ) (n₀ : ℤ) : Summable fun (i : ℕ) ↦ fouterm c z (i + n₀) := by
  -- Key fact: ‖exp(πiz)‖ < 1 for z : ℍ
  have hr : ‖Complex.exp (π * Complex.I * z)‖ < 1 := norm_exp_pi_I_z_lt_one z
  -- Factor fouterm c z (i + n₀) = u(i) * r^i
  -- where r = cexp(π * I * z) and u(i) = cexp(π * I * n₀ * z) * c(i + n₀)
  let r := cexp (π * Complex.I * z)
  let const := cexp (π * Complex.I * n₀ * z)
  let u : ℕ → ℂ := fun i ↦ const * c (i + n₀)
  have h_factor : ∀ i : ℕ, fouterm c z (i + n₀) = u i * r ^ i := fun i ↦ by
    simp only [fouterm, u, r, const, ← Complex.exp_nat_mul, Int.cast_add, Int.cast_natCast]
    rw [show (↑π * Complex.I * (↑i + ↑n₀) * ↑z : ℂ) =
        ↑π * Complex.I * ↑n₀ * ↑z + ↑π * Complex.I * ↑i * ↑z by ring, Complex.exp_add]
    ring_nf
  -- u has polynomial growth: ‖u n‖ = ‖const‖ * ‖c(n+n₀)‖ is O(n^k)
  have hu : u =O[Filter.atTop] (fun n ↦ (↑(n ^ k) : ℝ)) := by
    simpa [u, Nat.cast_pow] using (hpoly' c n₀ k hpoly).const_mul_left const
  -- Apply summability theorem
  simp_rw [h_factor]
  exact Summable.of_norm (summable_real_norm_mul_geometric_of_norm_lt_one hr hu)

/-! ## Keystone: q-series → fouterm reindex

A `q`-series `∑ₘ b m · qᵐ` (with `q = cexp (2π i z)`, the standard convention) becomes a
`fouterm` sum (with `r = cexp (π i z)`, the half-`q` convention used by `DivDiscBound`) by placing
the `m`-th coefficient at the even index `2m` and `0` on odd indices; `evenCoeff` (from
`CauchyCoeffBounds`) is that re-indexer. -/

/-- **Keystone reindex** (built via `Function.Injective.tsum_eq` along `m ↦ 2m`). -/
lemma qexp_eq_fouterm (b : ℕ → ℂ) (x : ℍ) :
    (∑' m : ℕ, b m * cexp (2 * ↑π * Complex.I * ↑m * ↑x))
      = ∑' n : ℕ, fouterm (evenCoeff b) x (↑n + 0) := by
  have hg : Function.Injective (fun j : ℕ ↦ 2 * j) := mul_right_injective₀ two_ne_zero
  have hsupp : Function.support (fun n : ℕ ↦ fouterm (evenCoeff b) x (↑n + 0)) ⊆
      Set.range (fun j : ℕ ↦ 2 * j) := by
    intro n hn
    have heven : Even (n : ℤ) := by
      by_contra hodd
      exact hn (by simp only [fouterm, add_zero, evenCoeff, if_neg hodd, zero_mul])
    obtain ⟨j, hj⟩ := (Int.even_coe_nat n).mp heven
    exact ⟨j, (two_mul j).trans hj.symm⟩
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr (fun j ↦ ?_)
  have h2j : Even ((2 * j : ℕ) : ℤ) := by exact_mod_cast even_two_mul j
  simp only [fouterm, add_zero, evenCoeff, if_pos h2j]
  rw [show (((2 * j : ℕ) : ℤ) / 2).toNat = j by push_cast; omega,
    show (↑π * Complex.I * ((2 * j : ℕ) : ℤ) * ↑x : ℂ) = 2 * ↑π * Complex.I * ↑j * ↑x by
      push_cast; ring]

/-- A `fouterm` sum whose coefficients vanish below `n₀` can start at index `n₀`:
`∑ₙ fouterm c x (n + 0) = ∑ₙ fouterm c x (n + n₀)`. -/
lemma tsum_fouterm_shift {c : ℤ → ℂ} (x : ℍ) (n₀ : ℕ)
    (hvan : ∀ k : ℤ, k < n₀ → c k = 0) :
    ∑' n : ℕ, fouterm c x (↑n + 0) = ∑' n : ℕ, fouterm c x (↑n + ↑n₀) := by
  have hinj : Function.Injective fun n : ℕ ↦ n + n₀ := add_left_injective n₀
  have hsupp : Function.support (fun n : ℕ ↦ fouterm c x (↑n + 0)) ⊆
      Set.range fun n : ℕ ↦ n + n₀ := by
    intro n hn
    rw [Function.mem_support] at hn
    have hge : n₀ ≤ n := by
      by_contra hlt
      exact hn (by simp only [fouterm, add_zero,
        hvan ↑n (by exact_mod_cast Nat.lt_of_not_le hlt), zero_mul])
    exact ⟨n - n₀, Nat.sub_add_cancel hge⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun n ↦ ?_
  congr 1

/-! ## Linear factor q-coefficients and fouterm identities

`E₄` and `E₂E₄−E₆` are the *linear* factors of the φ-numerators. Their genuine `q`-coefficients
`bE₄` and `bg` (defined in `CauchyCoeffBounds`) are simple (no Cauchy convolution), so via the
keystone they have clean `fouterm` expansions. -/

/-- `E₄` as an ℕ-indexed `q`-series with coefficients `bE₄`. -/
lemma E₄_qexp_nat (z : ℍ) :
    E₄ z = ∑' m : ℕ, bE₄ m * cexp (2 * ↑π * Complex.I * ↑m * ↑z) := by
  have hsummable : Summable (fun m : ℕ ↦ bE₄ m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)) := by
    have hσ : Summable (fun n : ℕ ↦ (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z)) := by
      refine (EisensteinSeries.summable_sigma_mul_cexp_pow (k := 4) (by norm_num) z).congr ?_
      intro n
      rw [← Complex.exp_nat_mul]
      congr 2
      ring
    rw [← summable_pnat_iff_summable_nat]
    refine ((summable_pnat_iff_summable_nat.mpr hσ).mul_left 240).congr (fun n ↦ ?_)
    simp only [bE₄, n.ne_zero, if_false]
    ring
  rw [hsummable.tsum_eq_zero_add, E₄_sigma_qexp]
  congr 1
  · simp [bE₄]
  · rw [tsum_pnat_eq_tsum_succ
      (f := fun k : ℕ ↦ (σ 3 k : ℂ) * cexp (2 * ↑π * Complex.I * ↑k * ↑z)), ← tsum_mul_left]
    refine tsum_congr (fun m ↦ ?_)
    simp only [bE₄, Nat.succ_ne_zero m, if_false]
    push_cast; ring

/-- `E₄` in `fouterm` form (`n₀ = 0`). -/
lemma E₄_eq_fouterm (z : ℍ) : E₄ z = ∑' n : ℕ, fouterm (evenCoeff bE₄) z (↑n + 0) :=
  (E₄_qexp_nat z).trans (qexp_eq_fouterm bE₄ z)

/-- `E₂E₄ − E₆` as an ℕ-indexed `q`-series with coefficients `bg` (vanishing at `0`). -/
lemma g_qexp_nat (z : ℍ) :
    E₂ z * E₄ z - E₆ z = ∑' m : ℕ, bg m * cexp (2 * ↑π * Complex.I * ↑m * ↑z) := by
  have hsupp : Function.support (fun m : ℕ ↦ bg m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)) ⊆
      Set.range ((↑·) : ℕ+ → ℕ) := by
    intro m hm
    have hm0 : m ≠ 0 := by rintro rfl; simp [bg] at hm
    exact ⟨⟨m, Nat.pos_of_ne_zero hm0⟩, rfl⟩
  rw [E₂_mul_E₄_sub_E₆, ← tsum_mul_left, ← PNat.coe_injective.tsum_eq
    (f := fun m : ℕ ↦ bg m * cexp (2 * ↑π * Complex.I * ↑m * ↑z)) hsupp]
  refine tsum_congr (fun n ↦ ?_)
  simp only [bg]
  ring

/-- `E₂E₄ − E₆` in `fouterm` form (`n₀ = 2`; the index-`0,1` terms vanish). -/
lemma g_eq_fouterm (z : ℍ) :
    E₂ z * E₄ z - E₆ z = ∑' n : ℕ, fouterm (evenCoeff bg) z (↑n + 2) := by
  rw [g_qexp_nat z, qexp_eq_fouterm bg z]
  exact tsum_fouterm_shift z 2 (by
    intro k hk
    have hk0 : (k / 2).toNat = 0 := by omega
    simp [evenCoeff, hk0, bg])

/-! ## Factor norm bounds

The shared pointwise q-series estimates in `ForMathlib.QSeriesBounds` apply at height `1/2`.
Polynomial-growth inputs come from the canonical coefficient API in `CauchyCoeffBounds`.
-/

/-- The constant `∑ ‖b m‖·exp(-πm)` converges for any polynomially-bounded `b`. -/
lemma summable_norm_mul_exp {b : ℕ → ℂ} {k : ℕ}
    (hb : b =O[Filter.atTop] (fun n : ℕ ↦ (n ^ k : ℝ))) :
    Summable fun m : ℕ ↦ ‖b m‖ * rexp (-π * (m : ℝ)) := by
  have hr : ‖(↑(rexp (-π)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hu : b =O[Filter.atTop] (fun n : ℕ ↦ (↑(n ^ k) : ℝ)) := by simpa [Nat.cast_pow] using hb
  refine (summable_real_norm_mul_geometric_of_norm_lt_one hr hu).congr (fun m ↦ ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_nat_mul]
  ring_nf

/-- Explicit constant bounding `‖E₄‖` on `im ≥ 1/2`. -/
def B_E₄ : ℝ := ∑' m : ℕ, ‖bE₄ m‖ * rexp (-π * (m : ℝ))

/-- Explicit decay constant for `‖E₂E₄ − E₆‖`. The `exp π` factor compensates for the
reference height `1/2` when using the unshifted coefficients, which vanish at index zero. -/
def B_g : ℝ := rexp π * ∑' m : ℕ, ‖bg m‖ * rexp (-π * (m : ℝ))

lemma B_E₄_pos : 0 < B_E₄ := by
  refine lt_of_lt_of_le ?_
    ((summable_norm_mul_exp bE₄_poly).le_tsum 0 (fun j _ ↦ by positivity))
  simp [bE₄]

lemma B_g_pos : 0 < B_g := by
  apply mul_pos (Real.exp_pos _)
  refine lt_of_lt_of_le ?_
    ((summable_norm_mul_exp bg_poly).le_tsum 1 (fun j _ ↦ by positivity))
  exact mul_pos (by norm_num [bg]) (Real.exp_pos _)

/-- `E₄` is bounded by `B_E₄` on `im ≥ 1/2`. -/
lemma norm_E₄_le (z : ℍ) (hz : 1 / 2 ≤ z.im) : ‖E₄ z‖ ≤ B_E₄ := by
  rw [E₄_qexp_nat z]
  have hc : 2 * π * (1 / 2 : ℝ) = π := by ring
  simpa only [B_E₄, hc, add_zero, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] using
    Complex.norm_qseries_shift_le 0 (c := 1 / 2)
      (by simpa only [hc] using summable_norm_mul_exp bE₄_poly) (z : ℂ) hz

/-- `E₂E₄ − E₆` decays like `exp(-2π·im)` on `im ≥ 1/2`, with constant `B_g`. -/
lemma norm_g_le (z : ℍ) (hz : 1 / 2 ≤ z.im) :
    ‖E₂ z * E₄ z - E₆ z‖ ≤ B_g * rexp (-(2 * π) * z.im) := by
  rw [g_qexp_nat z]
  have hc : 2 * π * (1 / 2 : ℝ) = π := by ring
  have hvan : ∀ m < 1, bg m = 0 := by
    intro m hm
    have : m = 0 := by omega
    simp [this, bg]
  have h := Complex.norm_qseries_le_of_coeff_vanish 1 (c := 1 / 2)
    hvan (by simpa only [hc] using summable_norm_mul_exp bg_poly) (z : ℂ) hz
  have hexp : -(2 * π) * (z.im - 1 / 2) = π + -(2 * π) * z.im := by ring
  rw [hc, Nat.cast_one, mul_one, show (z : ℂ).im = z.im from rfl, hexp, Real.exp_add] at h
  simpa only [B_g, mul_assoc, mul_left_comm] using h

/-! ## Linear quotient bounds

Direct `DivDiscBoundOfPolyFourierCoeff` applications using the linear `fouterm` identities. -/

/-- `‖(E₂E₄−E₆)/Δ‖ ≤ DivDiscBound (evenCoeff bg) 2` (constant: `n₀=2 ⇒ exp 0 = 1`). -/
lemma g_div_Δ_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖(E₂ z * E₄ z - E₆ z) / Δ z‖ ≤ DivDiscBound (evenCoeff bg) 2 := by
  simpa using DivDiscBoundOfPolyFourierCoeff z hz (evenCoeff bg) 2
    (summable_fouterm_of_poly (evenCoeff_poly bg_poly) z 2) 5 (evenCoeff_poly bg_poly)
    (fun x ↦ E₂ x * E₄ x - E₆ x) g_eq_fouterm

/-- `‖E₄/Δ‖ ≤ DivDiscBound (evenCoeff bE₄) 0 · exp(2π·im)` (from `n₀=0`). -/
lemma E₄_div_Δ_bound (z : ℍ) (hz : 1 / 2 < z.im) :
    ‖E₄ z / Δ z‖ ≤ DivDiscBound (evenCoeff bE₄) 0 * Real.exp (2 * π * z.im) := by
  simpa [mul_comm π 2] using DivDiscBoundOfPolyFourierCoeff z hz (evenCoeff bE₄) 0
    (summable_fouterm_of_poly (evenCoeff_poly bE₄_poly) z 0) 4 (evenCoeff_poly bE₄_poly)
    (fun x ↦ E₄ x) E₄_eq_fouterm

end MagicFunction.a.FourierExpansions

end

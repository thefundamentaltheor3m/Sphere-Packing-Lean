/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.tsumderivWithin
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.Tactic.NormNum.Parity

/-! # The Eisenstein series `E₄` and `E₆`

This file defines the normalised level-one Eisenstein series `E k` (as `ModularForm Γ(1) k`,
with constant term `1`; mathlib's `ModularForm.E` is typed over `𝒮ℒ`, the two coincide as
functions on `ℍ`), its specialisations `E₄` and `E₆`, together with the quotients `φ₀`, `φ₂'`,
`φ₄'` of Eisenstein series by the discriminant `Δ` used to build the magic function, and collects
the properties of `E₂`, `E₄` and `E₆` needed by the project:

* `E₄_periodic`, `E₆_periodic`, `E₄_S_transform`, `E₆_S_transform`: pointwise transformation laws
  under the generators of `SL(2, ℤ)`.
* `E4_q_exp`, `E4_q_exp_zero`, `E6_q_exp_zero`: explicit `q`-expansion coefficients
  (`240 · σ₃` for `E₄`).
* `Ek_ne_zero`, `E4_ne_zero`, `E6_ne_zero`: non-vanishing, via mathlib's
  `EisensteinSeries.E_ne_zero`.
* `E₂_sigma_qexp`, `E₄_sigma_qexp`: the `q`-expansions `E₂ = 1 - 24 ∑ σ₁(n) qⁿ` and
  `E₄ = 1 + 240 ∑ σ₃(n) qⁿ` written with `cexp (2πinz)`, together with the summability and
  derivative bounds `sigma_qexp_summable_generic`, `sigma_qexp_deriv_bound_generic` for the
  `σ`-twisted `q`-series that appear when differentiating them termwise.
* `E_even_imag_axis_real`, `E₂_imag_axis_real`, `E₄_imag_axis_real`, `E₆_imag_axis_real`:
  realness on the positive imaginary axis; `sigma_qexp_tsum_re_pos`: positivity of the
  differentiated `σ_k` `q`-series there.

Boundedness of `E₂` at `i∞` is now mathlib's `EisensteinSeries.isBoundedAtImInfty_E2`.
-/

@[expose] public section

open ModularForm hiding E₄ E₆
open UpperHalfPlane Complex

open scoped Real Nat ArithmeticFunction.sigma

noncomputable section

/-! ## Definitions and transformation laws -/

/-- The normalised Eisenstein series of weight `k` and level one, with constant term `1`.
The scaling by `1/2` matches the normalisation, since the sum is taken over coprime pairs. -/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma 1) k :=
  (1 / 2 : ℂ) • eisensteinSeriesMF hk 0

/-- The normalised Eisenstein series of weight `4` and level one, with constant term `1`. -/
def E₄ := E 4 (by norm_num)

/-- The normalised Eisenstein series of weight `6` and level one, with constant term `1`. -/
def E₆ := E 6 (by norm_num)

/-- E₄ is 1-periodic: E₄(z + 1) = E₄(z), as a modular form for Γ(1). -/
lemma E₄_periodic (z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 4 1 E₄.toSlashInvariantForm z

/-- E₆ is 1-periodic: E₆(z + 1) = E₆(z), as a modular form for Γ(1). -/
lemma E₆_periodic (z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 6 1 E₆.toSlashInvariantForm z

/-- E₄ transforms under S as: E₄(-1/z) = z⁴ · E₄(z) -/
lemma E₄_S_transform (z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := by
  have h : (E₄.toFun ∣[(4 : ℤ)] ModularGroup.S) z = E₄.toFun z :=
    congrFun (E₄.slash_action_eq' _
      (Subgroup.mem_map.mpr ⟨_, CongruenceSubgroup.mem_Gamma_one _, rfl⟩)) z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg, ModularForm.toFun_eq_coe] at h
  field_simp [ne_zero z] at h
  exact h

/-- E₆ transforms under S as: E₆(-1/z) = z⁶ · E₆(z) -/
lemma E₆_S_transform (z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := by
  have h : (E₆.toFun ∣[(6 : ℤ)] ModularGroup.S) z = E₆.toFun z :=
    congrFun (E₆.slash_action_eq' _
      (Subgroup.mem_map.mpr ⟨_, CongruenceSubgroup.mem_Gamma_one _, rfl⟩)) z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg, ModularForm.toFun_eq_coe] at h
  field_simp [ne_zero z] at h
  exact h

/-! ## The quotients `φ₀`, `φ₂'`, `φ₄'`

The blueprint's `φ₀`, `φ₋₂`, `φ₋₄`; negative signs cannot appear in subscripts of
identifiers, hence the primes. -/

/-- The quotient `(E₂E₄ - E₆)² / Δ`, the blueprint's `φ₀`. -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)

/-- The quotient `E₄(E₂E₄ - E₆) / Δ`, the blueprint's `φ₋₂`. -/
def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)

/-- The quotient `E₄² / Δ`, the blueprint's `φ₋₄`. -/
def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)

/-- The extension of `φ₀` to `ℂ`, vanishing outside the upper half plane. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0

lemma φ₀''_def {z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by simp [φ₀'', hz]

lemma φ₀''_coe_upperHalfPlane (z : ℍ) : φ₀'' (z : ℂ) = φ₀ z := φ₀''_def z.im_pos

/-! ## `q`-expansion coefficients and non-vanishing -/

private lemma E4_eq' :
    (E₄ : ℍ → ℂ) = (ModularForm.E (k := 4) (by norm_num) : ℍ → ℂ) := rfl

private lemma E6_eq' :
    (E₆ : ℍ → ℂ) = (ModularForm.E (k := 6) (by norm_num) : ℍ → ℂ) := rfl

lemma E4_q_exp : (fun m => (qExpansion 1 E₄).coeff m) =
    fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  ext m
  rw [E4_eq', EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) m]
  split
  · rfl
  · simp [bernoulli, bernoulli'_four]; ring

lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1 :=
  E4_eq' ▸ EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)

lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1 :=
  E6_eq' ▸ EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)

lemma Ek_ne_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : E k hk ≠ 0 := by
  have h := EisensteinSeries.E_ne_zero (k := k) (by exact_mod_cast hk) hk2
  rwa [DFunLike.ne_iff] at h ⊢

lemma E4_ne_zero : E₄ ≠ 0 := Ek_ne_zero 4 (by norm_num) (by decide)

lemma E6_ne_zero : E₆ ≠ 0 := Ek_ne_zero 6 (by norm_num) (by decide)

/-! ## `q`-expansions in terms of `cexp (2πinz)`

Mathlib states the `q`-expansions of `E₂` and `E₄` in terms of `𝕢 z ^ n`; the lemmas below restate
them with `cexp (2 π i n z)` and `ℕ+`-indexing, the form used when differentiating termwise
(`D_qexp_tsum_pnat`), together with the summability and derivative bounds this requires. -/

/-- The `q`-series `∑' n : ℕ+, n ^ a * σ b n * exp (2 π i n z)` is summable for `z : ℍ`.

The case `a = 0` is mathlib's `EisensteinSeries.summable_sigma_mul_cexp_pow`, up to
`𝕢 z ^ n` versus `cexp (2πinz)` and `ℕ` versus `ℕ+` indexing; the cases `a ≥ 1` are the ones
needed for the termwise-differentiated series. -/
lemma sigma_qexp_summable_generic (a b : ℕ) (z : ℍ) :
    Summable (fun n : ℕ+ ↦ (n : ℂ) ^ a * (σ b n : ℂ) * cexp (2 * π * Complex.I * n * z)) := by
  refine ((summable_norm_pow_mul_geometric_of_norm_lt_one (a + b + 1)
    (norm_exp_two_pi_I_lt_one z)).comp_injective PNat.coe_injective).of_norm_bounded fun n ↦ ?_
  rw [show (2 * π * Complex.I * n * z : ℂ) = n * (2 * π * Complex.I * z) by ring,
    Complex.exp_nat_mul]
  simp only [Function.comp_apply, norm_mul, norm_pow, Complex.norm_natCast]
  rw [add_assoc, pow_add]
  gcongr
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ b n

/-- Summable bound on compact sets for the terms of the differentiated `σ_k` `q`-series, the
`hsum_deriv` hypothesis of `D_qexp_tsum_pnat`. -/
lemma sigma_qexp_deriv_bound_generic (k : ℕ) :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (z : K),
        ‖(σ k n : ℂ) * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * z.1)‖ ≤ u n := by
  intro K hK hKc
  obtain ⟨u₀, hu₀_sum, hu₀_bound⟩ := iter_deriv_comp_bound3 K hK hKc (k + 2)
  refine ⟨fun n ↦ u₀ n, hu₀_sum.subtype _, fun n z ↦ le_trans ?_ (hu₀_bound n z)⟩
  have hσ : (σ k n : ℝ) ≤ (2 * π * n) ^ (k + 1) :=
    le_trans (by exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n) <| pow_le_pow_left₀
      (by positivity) (le_mul_of_one_le_left (by positivity) (by linarith [Real.two_le_pi])) _
  simpa [abs_of_pos Real.pi_pos, Real.pi_pos, pow_succ] using hσ

/-- The `q`-expansion `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`. This restates Mathlib's
`EisensteinSeries.E2_eq_tsum_cexp` with `cexp (2πi n z)` in place of `𝕢 z ^ n`. -/
lemma E₂_sigma_qexp (z : ℍ) :
    E₂ z = 1 - 24 * ∑' (n : ℕ+), (σ 1 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
  simp [E₂, EisensteinSeries.E2_eq_tsum_cexp, ← Complex.exp_nat_mul, mul_comm, mul_left_comm,
    mul_assoc]

/-- `E₄ = 1 + 240 ∑' n : ℕ+, σ₃ n qⁿ`. -/
lemma E₄_sigma_qexp (z : ℍ) :
    E₄ z = 1 + 240 * ∑' (n : ℕ+), (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
  refine (EisensteinSeries.q_expansion_bernoulli (by norm_num : 3 ≤ 4) (by decide) z).trans ?_
  norm_num [bernoulli, bernoulli'_four, ← Complex.exp_nat_mul, mul_comm, mul_assoc, mul_left_comm]

/-! ## Realness on the imaginary axis -/

/-- On imaginary axis z = I*t, the q-expansion exponent 2πi·n·z reduces to -(2πnt).
This is useful for reusing the same algebraic simplification across `E₂`, `E₄`, `E₆`. -/
lemma exp_imag_axis_arg (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * n =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  simp [Complex.ext_iff, mul_right_comm]

/-- Each term `n σ_k n exp (-2πnt)` of a differentiated `σ_k` `q`-series is positive at `z = it`. -/
lemma sigma_qexp_term_re_pos (k : ℕ) (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    0 < (n * σ k n *
      cexp (2 * π * Complex.I * n * (⟨Complex.I * t, by simp [ht]⟩ : ℍ))).re := by
  rw [mul_right_comm (2 * π * Complex.I), exp_imag_axis_arg t ht n]
  simp only [Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im, mul_zero, sub_zero,
    Complex.natCast_re, Complex.natCast_im]
  refine mul_pos (mul_pos ?_ ?_) (Real.exp_pos _)
  · exact_mod_cast n.pos
  · exact_mod_cast ArithmeticFunction.sigma_pos k n n.ne_zero

/-- A differentiated `σ_k` `q`-series has positive real part at `z = it` for `t > 0`. -/
lemma sigma_qexp_tsum_re_pos (k : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < (∑' n : ℕ+, n * σ k n *
      cexp (2 * π * Complex.I * n * (⟨Complex.I * t, by simp [ht]⟩ : ℍ))).re := by
  have hsum : Summable fun n : ℕ+ ↦ n * σ k n *
      cexp (2 * π * Complex.I * n * (⟨Complex.I * t, by simp [ht]⟩ : ℍ)) := by
    simpa [pow_one] using sigma_qexp_summable_generic 1 k ⟨Complex.I * t, by simp [ht]⟩
  rw [Complex.re_tsum hsum]
  exact Summable.tsum_pos ⟨_, Complex.hasSum_re hsum.hasSum⟩
    (fun n ↦ (sigma_qexp_term_re_pos k t ht n).le) 1 (sigma_qexp_term_re_pos k t ht 1)

/-- `E_k(it)` is real for all `t > 0` when `k` is even and `k ≥ 4`.
This is the generalized theorem from which `E₄_imag_axis_real` and `E₆_imag_axis_real` follow. -/
theorem E_even_imag_axis_real (k : ℕ) (hk : (3 : ℤ) ≤ k) (hk2 : Even k) :
    ResToImagAxis.Real (E k hk).toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hk' : 3 ≤ k := by exact_mod_cast hk
  change (E k hk z).im = 0
  rw [show (E k hk) z = ModularForm.E hk' z from rfl,
    EisensteinSeries.q_expansion_riemannZeta hk' hk2 z]
  simp only [zpow_natCast]
  -- Step 1: On the imaginary axis the nome is real: `q = exp (-2πt)`
  have hq_real : cexp (2 * ↑Real.pi * Complex.I * z) =
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
    rw [show 2 * ↑Real.pi * Complex.I * (z : ℂ) = ((-(2 * Real.pi * t) : ℝ) : ℂ) by
        simpa [z] using exp_imag_axis_arg t ht 1,
      ← Complex.ofReal_exp]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ =>
      (σ (k - 1) n : ℂ) * cexp (2 * ↑Real.pi * Complex.I * z) ^ (n : ℕ) := by
    have h := (EisensteinSeries.summable_sigma_mul_cexp_pow (k := k) (by omega) z).comp_injective
      PNat.coe_injective
    exact h.congr fun n => rfl
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' n : ℕ+,
      (σ (k - 1) n : ℂ) * cexp (2 * ↑Real.pi * Complex.I * z) ^ (n : ℕ)).im = 0 := by
    rw [im_tsum hsum]
    simp only [hq_real, ← Complex.ofReal_pow, Complex.mul_im, Complex.natCast_im,
      Complex.natCast_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, tsum_zero]
  -- Step 4: The coefficient is real, so the product with the sum is real
  have hpow_im : ((-(2 * Real.pi * Complex.I)) ^ k : ℂ).im = 0 := by
    rw [show (-(2 * Real.pi * Complex.I) : ℂ) ^ k = (-(2 * Real.pi) : ℂ) ^ k * Complex.I ^ k by
      ring]
    have h1 : ((-(2 * Real.pi)) ^ k : ℂ).im = 0 := by norm_cast
    have h2 : (Complex.I ^ k : ℂ).im = 0 := by
      obtain ⟨m, hm⟩ := hk2
      rw [hm, ← two_mul, pow_mul, I_sq]
      rcases m.even_or_odd with hm' | hm' <;> simp [hm'.neg_one_pow]
    simp [Complex.mul_im, h1, h2]
  -- For ζ(k) when k ≥ 4, it's real (mathlib: riemannZeta_im_eq_zero_of_one_lt)
  have hzeta_im : (riemannZeta k).im = 0 := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from by push_cast; ring]
    exact riemannZeta_im_eq_zero_of_one_lt (by exact_mod_cast show 1 < (k : ℤ) by omega)
  have hcoeff_im : ((riemannZeta k)⁻¹ * (-2 * ↑Real.pi * Complex.I) ^ k / (k - 1)! : ℂ).im = 0 := by
    simp [Complex.div_im, Complex.mul_im, Complex.inv_im, hzeta_im, neg_mul, hpow_im]
  rw [Complex.add_im, Complex.one_im, Complex.mul_im, hcoeff_im, hsum_im]
  ring

/-- `E₄(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun :=
  E_even_imag_axis_real 4 (by norm_num) (by norm_num)

/-- `E₆(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun :=
  E_even_imag_axis_real 6 (by norm_num) (by norm_num)

/-- `E₂(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₂_imag_axis_real : ResToImagAxis.Real E₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₂ z).im = 0
  rw [E₂_eq]
  simp only [sub_im, one_im, zero_sub]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      have h1 : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
        simpa [z] using exp_imag_axis_arg (t := t) ht n
      simpa [mul_assoc, mul_left_comm, mul_comm] using h1
    have hone_sub_real : (1 - cexp (2 * ↑Real.pi * Complex.I * ↑↑n * ↑z)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, hexp_arg, exp_ofReal_im, sub_zero]
    have hnum_real : (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z)).im = 0 := by
      simp only [mul_im, natCast_im, hexp_arg, exp_ofReal_im, mul_zero, zero_mul, add_zero]
    simp [Complex.div_im, hnum_real, hone_sub_real]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    set r : ℂ := cexp (2 * ↑Real.pi * Complex.I * z) with hr
    have hr_norm : ‖r‖ < 1 := by
      simpa [hr] using exp_upperHalfPlane_lt_one z
    have hs : Summable fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n) := by
      simpa [pow_one] using
        (summable_norm_pow_mul_geometric_div_one_sub (k := 1) (r := r) hr_norm)
    refine (hs.comp_injective PNat.coe_injective).congr ?_
    intro n
    have hpow : r ^ (n : ℕ) = cexp (2 * ↑Real.pi * Complex.I * (↑n : ℂ) * z) := by
      rw [hr]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * ↑Real.pi * Complex.I * z) (n : ℕ)).symm
    simp [hpow]
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp [hterm_im]
  -- Step 4: 24 * sum is real, so -(24 * sum).im = 0
  simp [Complex.mul_im, hsum_im]

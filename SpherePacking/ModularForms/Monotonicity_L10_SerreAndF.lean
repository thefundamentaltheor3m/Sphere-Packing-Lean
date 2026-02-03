/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.FG
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.summable_lems

/-!
# L₁₀ Definition and Serre Derivative Positivity

This file contains the definition of `L₁₀`, Serre derivative algebra, and the F-side analysis
including vanishing order and log-derivative limits. The main result is `serre_D_L₁₀_pos_imag_axis`.

## Main definitions and results

* `L₁₀` : The key function `L₁,₀ = (∂₁₀F)G - F(∂₁₀G)` for monotonicity analysis.
* `serre_D_L₁₀` : Formula for `∂₂₂ L₁,₀`.
* `serre_D_L₁₀_pos_imag_axis` : `∂₂₂ L₁,₀(it) > 0` for all `t > 0`.
* `F_vanishing_order` : `F / q² → 720²` as `im(z) → ∞`.
* `D_F_div_F_tendsto` : `(D F)/F → 2` as `im(z) → ∞`.
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

namespace MonotoneFG

/-! ## Helper lemmas -/

/-- If f/g → c ≠ 0, then eventually f ≠ 0. -/
lemma eventually_ne_zero_of_tendsto_div {f g : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : Filter.Tendsto (fun z => f z / g z) atImInfty (nhds c)) :
    ∀ᶠ z : ℍ in atImInfty, f z ≠ 0 := by
  have h_quot_ne := h.eventually_ne hc
  filter_upwards [h_quot_ne] with z hz hf
  exact hz (by simp [hf])

/-!
## Section 1: Definition and Properties of L₁,₀

The key object in proving monotonicity is:
  `L₁,₀ = (∂₁₀F)G - F(∂₁₀G)`

By the quotient rule for derivatives:
  `d/dt (F(it)/G(it)) = (-2π) * L₁,₀(it) / G(it)²`

So proving L₁,₀(it) > 0 implies Q is decreasing.
-/

/--
The function `L₁,₀ = (∂₁₀F)G - F(∂₁₀G)`.
Blueprint: Proposition 8.12.
-/
noncomputable def L₁₀ (z : ℍ) : ℂ :=
  serre_D 10 F z * G z - F z * serre_D 10 G z

/--
Alternative form: `L₁,₀ = F'G - FG'` where `'` denotes the normalized derivative.
This follows from the fact that ∂₀ = D (the E₂ term cancels in the difference).
-/
theorem L₁₀_eq_FD_G_sub_F_DG (z : ℍ) :
    L₁₀ z = D F z * G z - F z * D G z := by
  simp only [L₁₀, serre_D]
  ring

/-!
## Section 2: Serre Derivative of L₁,₀

We need to compute `∂₂₂ L₁,₀` and show it's positive on the imaginary axis.
-/

/--
The Serre derivative `∂₂₂ L₁,₀`.
Blueprint: Using the product rule (Theorem 6.53) twice.
The cross terms `(∂₁₀F)(∂₁₀G)` cancel in the subtraction.
-/
theorem serre_D_L₁₀ (z : ℍ) :
    serre_D 22 L₁₀ z = serre_D 12 (serre_D 10 F) z * G z
      - F z * serre_D 12 (serre_D 10 G) z := by
  have hF := F_holo; have hG := G_holo
  have hDF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) := serre_D_differentiable hF
  have hDG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 G) := serre_D_differentiable hG
  rw [show L₁₀ = serre_D 10 F * G - F * serre_D 10 G from rfl]
  have hsub := serre_D_sub (22 : ℤ) _ _ (hDF.mul hG) (hF.mul hDG)
  simp only [Int.cast_ofNat] at hsub
  rw [hsub, Pi.sub_apply]
  have h1 : serre_D 22 (serre_D 10 F * G) z =
      serre_D 12 (serre_D 10 F) z * G z + serre_D 10 F z * serre_D 10 G z := by
    conv_lhs => rw [show (22 : ℂ) = 12 + 10 by norm_num]
    simpa [Pi.mul_apply, Pi.add_apply] using congrFun (serre_D_mul 12 10 _ G hDF hG) z
  have h2 : serre_D 22 (F * serre_D 10 G) z =
      serre_D 10 F z * serre_D 10 G z + F z * serre_D 12 (serre_D 10 G) z := by
    conv_lhs => rw [show (22 : ℂ) = 10 + 12 by norm_num]
    simpa [Pi.mul_apply, Pi.add_apply] using congrFun (serre_D_mul 10 12 F _ hF hDG) z
  rw [h1, h2]; ring

/--
`∂₂₂ L₁,₀ = Δ(7200(-E₂')G + 640H₂F)` on the upper half-plane.
Blueprint: Follows from differential equations (65) and (66).
-/
theorem serre_D_L₁₀_eq (z : ℍ) :
    serre_D 22 L₁₀ z = Δ z * (7200 * (-(D E₂ z)) * G z + 640 * H₂ z * F z) := by
  -- From serre_D_L₁₀: ∂₂₂L₁₀ = (∂₁₂∂₁₀F)G - F(∂₁₂∂₁₀G)
  rw [serre_D_L₁₀]
  -- From MLDE_F: ∂₁₂∂₁₀F = (5/6)F + 7200Δ(-E₂')
  -- From MLDE_G: ∂₁₂∂₁₀G = (5/6)G - 640ΔH₂
  have hF_eq := MLDE_F
  have hG_eq := MLDE_G
  -- Apply at point z
  have hF_z := congrFun hF_eq z
  have hG_z := congrFun hG_eq z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply] at hF_z hG_z
  rw [hF_z, hG_z]
  -- Expand negDE₂ and simplify constant functions
  simp only [negDE₂, Pi.neg_apply]
  -- Use Δ_fun_eq_Δ to replace Δ_fun z with Δ z
  simp only [Δ_fun_eq_Δ]
  -- Handle constant functions
  have h5 : (5 : ℍ → ℂ) z = (5 : ℂ) := rfl
  have h6 : (6⁻¹ : ℍ → ℂ) z = (6 : ℂ)⁻¹ := rfl
  have h7200 : (7200 : ℍ → ℂ) z = (7200 : ℂ) := rfl
  have h640 : (640 : ℍ → ℂ) z = (640 : ℂ) := rfl
  rw [h5, h6, h7200, h640]
  -- Substituting: (5/6)E₄FG + 7200Δ·(-D E₂)·G - F·((5/6)E₄G - 640·Δ·H₂)
  --             = (5/6)E₄FG + 7200Δ·(-D E₂)·G - (5/6)E₄FG + 640·Δ·H₂·F
  --             = Δ·(7200·(-D E₂)·G + 640·H₂·F)
  ring

/-!
### negDE₂ imaginary axis properties

We prove that `negDE₂ = -(D E₂)` is real and positive on the imaginary axis.
From `ramanujan_E₂`: `D E₂ = 12⁻¹ * (E₂² - E₄)`, so `negDE₂ = 12⁻¹ * (E₄ - E₂²)`.
The positivity `E₄(it) > E₂(it)²` follows from the q-expansion coefficients being positive.
-/

/-- Extract the imaginary part condition at a point from `ResToImagAxis.Real`. -/
private lemma im_eq_zero_of_real {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (t : ℝ) (ht : 0 < t) :
    (F ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  have := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
  exact this

/-- Extract the positivity condition at a point from `ResToImagAxis.Pos`. -/
private lemma re_pos_of_pos {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) (t : ℝ) (ht : 0 < t) :
    0 < (F ⟨Complex.I * t, by simp [ht]⟩).re := by
  have := hF.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this
  exact this


/--
`∂₂₂ L₁,₀(it) > 0` for all `t > 0`.
Blueprint: Corollary 8.9 - both terms in the expression are positive.
- `-D E₂(it) > 0` (negDE₂_imag_axis_pos)
- `Δ(it) > 0` (Delta_imag_axis_pos)
- `G(it) > 0` and `H₂(it) > 0` and `F(it) > 0`
-/
theorem serre_D_L₁₀_pos_imag_axis : ResToImagAxis.Pos (serre_D 22 L₁₀) := by
  refine ⟨?_, fun t ht => ?_⟩
  -- Part 1: Real on imaginary axis
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    rw [serre_D_L₁₀_eq z]
    change (Δ z * (7200 * negDE₂ z * G z + 640 * H₂ z * F z)).im = 0
    have hΔ_real : (Δ z).im = 0 := by
      have := Delta_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hG_real : (G z).im = 0 := by
      have := G_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hH₂_real : (H₂ z).im = 0 := by
      have := H₂_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hF_real : (F z).im = 0 := by
      have := F_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hnegDE₂_real : (negDE₂ z).im = 0 := by
      have := negDE₂_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have h1 : (7200 * negDE₂ z * G z).im = 0 := by
      rw [Complex.mul_im, Complex.mul_im]
      simp only [(by norm_num : (7200 : ℂ).im = 0), hnegDE₂_real, hG_real]; ring
    have h2 : (640 * H₂ z * F z).im = 0 := by
      rw [Complex.mul_im, Complex.mul_im]
      simp only [(by norm_num : (640 : ℂ).im = 0), hH₂_real, hF_real]; ring
    have hsum_real : (7200 * negDE₂ z * G z + 640 * H₂ z * F z).im = 0 := by
      rw [Complex.add_im, h1, h2]; ring
    rw [Complex.mul_im, hΔ_real, hsum_real]; ring
  -- Part 2: Positive on imaginary axis
  · simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
    set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    rw [serre_D_L₁₀_eq z]
    change 0 < (Δ z * (7200 * negDE₂ z * G z + 640 * H₂ z * F z)).re
    have hΔ_pos : (Δ z).re > 0 := by
      have := Delta_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hΔ_real : (Δ z).im = 0 := by
      have := Delta_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hnegDE₂_pos : (negDE₂ z).re > 0 := by
      have := negDE₂_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hnegDE₂_real : (negDE₂ z).im = 0 := by
      have := negDE₂_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hG_pos : (G z).re > 0 := by
      have := G_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hG_real : (G z).im = 0 := by
      have := G_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hH₂_pos : (H₂ z).re > 0 := by
      have := H₂_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hH₂_real : (H₂ z).im = 0 := by
      have := H₂_imag_axis_pos.1 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hF_pos : (F z).re > 0 := by
      have := F_imag_axis_pos.2 t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hF_real : (F z).im = 0 := by
      have := F_imag_axis_real t ht
      simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
    have hsum_pos : (7200 * negDE₂ z * G z + 640 * H₂ z * F z).re > 0 := by
      have h1_re : (7200 * negDE₂ z * G z).re = 7200 * (negDE₂ z).re * (G z).re := by
        rw [Complex.mul_re, Complex.mul_re]
        simp only [(by norm_num : (7200 : ℂ).re = 7200), (by norm_num : (7200 : ℂ).im = 0),
          hnegDE₂_real, hG_real]; ring
      have h2_re : (640 * H₂ z * F z).re = 640 * (H₂ z).re * (F z).re := by
        rw [Complex.mul_re, Complex.mul_re]
        simp only [(by norm_num : (640 : ℂ).re = 640), (by norm_num : (640 : ℂ).im = 0),
          hH₂_real, hF_real]; ring
      rw [Complex.add_re, h1_re, h2_re]
      apply add_pos
      · exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 7200) hnegDE₂_pos) hG_pos
      · exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 640) hH₂_pos) hF_pos
    have hsum_real : (7200 * negDE₂ z * G z + 640 * H₂ z * F z).im = 0 := by
      have h1 : (7200 * negDE₂ z * G z).im = 0 := by
        rw [Complex.mul_im, Complex.mul_im]
        simp only [(by norm_num : (7200 : ℂ).im = 0), hnegDE₂_real, hG_real]; ring
      have h2 : (640 * H₂ z * F z).im = 0 := by
        rw [Complex.mul_im, Complex.mul_im]
        simp only [(by norm_num : (640 : ℂ).im = 0), hH₂_real, hF_real]; ring
      rw [Complex.add_im, h1, h2]; ring
    rw [Complex.mul_re, hΔ_real, hsum_real, mul_zero, sub_zero]
    exact mul_pos hΔ_pos hsum_pos

/-!
## Section 3: Large-t Positivity of L₁,₀

Using Lemma 8.11 (vanishing orders), we show L₁,₀(it) > 0 for large t.
-/

/-- Summability of (m+1)^5 * exp(-2πm) via comparison with shifted sum. -/
lemma summable_pow5_shift : Summable fun m : ℕ => (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 5 (by positivity : 0 < 2 * π)
  have h_eq : ∀ m : ℕ, (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) =
      rexp (2 * π) * ((m + 1) ^ 5 * rexp (-2 * π * (m + 1))) := by
    intro m
    have h1 : rexp (-2 * π * m) = rexp (2 * π) * rexp (-2 * π * (m + 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]; ring
  simp_rw [h_eq]
  apply Summable.mul_left
  convert h.comp_injective Nat.succ_injective using 1
  ext m; simp only [Function.comp_apply, Nat.succ_eq_add_one]; push_cast; ring_nf

/-- Summability of (m+1)^6 * exp(-2πm) via comparison with shifted sum. -/
lemma summable_pow6_shift : Summable fun m : ℕ => (m + 1 : ℝ) ^ 6 * rexp (-2 * π * m) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 6 (by positivity : 0 < 2 * π)
  have h_eq : ∀ m : ℕ, (m + 1 : ℝ) ^ 6 * rexp (-2 * π * m) =
      rexp (2 * π) * ((m + 1) ^ 6 * rexp (-2 * π * (m + 1))) := by
    intro m
    have h1 : rexp (-2 * π * m) = rexp (2 * π) * rexp (-2 * π * (m + 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]; ring
  simp_rw [h_eq]
  apply Summable.mul_left
  convert h.comp_injective Nat.succ_injective using 1
  ext m; simp only [Function.comp_apply, Nat.succ_eq_add_one]; push_cast; ring_nf

/--
Helper lemma: `Θ₂(z) / exp(πiz/4) → 2` as `im(z) → ∞`.
This follows from `Θ₂ = exp(πiz/4) * jacobiTheta₂(z/2, z)` and `jacobiTheta₂(z/2, z) → 2`.
-/
theorem Θ₂_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ => Θ₂ z / cexp (π * Complex.I * z / 4))
      atImInfty (nhds (2 : ℂ)) := by
  have h := jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  convert h using 1
  ext z
  rw [Θ₂_as_jacobiTheta₂]
  field_simp [Complex.exp_ne_zero]

/--
Helper lemma: `H₂(z) / exp(πiz) → 16` as `im(z) → ∞`.
Since `H₂ = Θ₂⁴` and `Θ₂ / exp(πiz/4) → 2`, we get `H₂ / exp(πiz) → 2⁴ = 16`.
-/
theorem H₂_div_exp_tendsto :
    Filter.Tendsto (fun z : ℍ => H₂ z / cexp (π * Complex.I * z))
      atImInfty (nhds (16 : ℂ)) := by
  have h_eq : ∀ z : ℍ, H₂ z / cexp (π * I * z) = (Θ₂ z / cexp (π * I * z / 4)) ^ 4 := fun z => by
    simp only [H₂, div_pow, ← Complex.exp_nat_mul]; congr 2; ring
  simp_rw [h_eq]; convert Θ₂_div_exp_tendsto.pow 4; norm_num

/--
The vanishing order of F at infinity is 2.
Blueprint: From q-expansion F = 720² * q² * (1 + O(q)), so F / q² → 720² as im(z) → ∞.
Here q = exp(2πiz), so q² = exp(4πiz) = exp(2πi * 2 * z).
-/
theorem F_vanishing_order :
    Filter.Tendsto (fun z : ℍ => F z / cexp (2 * π * Complex.I * 2 * z))
      atImInfty (nhds (720 ^ 2 : ℂ)) := by
  -- F = (E₂E₄ - E₆)² and we want to show F / q² → 720² where q = exp(2πiz)
  -- Strategy: Show (E₂E₄ - E₆) / q → 720, then square
  -- From E₂_mul_E₄_sub_E₆: E₂E₄ - E₆ = 720 * ∑' n : ℕ+, n * σ₃(n) * q^n
  -- Dividing by q and using QExp.tendsto_nat: limit is 720 * σ₃(1) = 720
  have h_diff_tendsto : Filter.Tendsto (fun z : ℍ => (E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z))
      atImInfty (nhds (720 : ℂ)) := by
    -- Use E₂_mul_E₄_sub_E₆ and reindex from ℕ+ to ℕ, then apply QExp.tendsto_nat
    have h_rw : ∀ z : ℍ, E₂ z * E₄ z - E₆ z =
        720 * ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * n * z) := E₂_mul_E₄_sub_E₆
    have h_eq : ∀ z : ℍ,
        (E₂ z * E₄ z - E₆ z) / cexp (2 * π * Complex.I * z) =
        720 * (∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z)) := by
      intro z
      rw [h_rw z, mul_div_assoc, ← tsum_div_const]
      congr 1; apply tsum_congr; intro n
      rw [mul_div_assoc, ← Complex.exp_sub]; congr 2; ring
    simp_rw [h_eq]
    -- Reindex ℕ+ to ℕ via `tsum_pnat_eq_tsum_succ3`: n ↦ m+1
    have h_reindex : ∀ z : ℍ,
        ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z) =
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) := by
      intro z
      simpa [tsum_pnat_eq_tsum_succ3] using
        (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
          (n : ℂ) * (↑(ArithmeticFunction.sigma 3 n) : ℂ) *
            cexp (2 * π * Complex.I * ((n : ℂ) - 1) * z)))
    simp_rw [h_reindex]
    -- Apply QExp.tendsto_nat with coefficient function a(m) = (m+1) * σ₃(m+1)
    set a : ℕ → ℂ := fun m => ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) with ha
    have ha0 : a 0 = 1 := by simp [ha, ArithmeticFunction.sigma_one]
    have h_tendsto : Filter.Tendsto
        (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m))
        atImInfty (nhds (a 0)) := by
      apply QExp.tendsto_nat a
      -- Summability: ‖a m‖ ≤ (m+1)^5, and (m+1)^5 * exp(-2πm) is summable
      have hbound : ∀ m : ℕ, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 5 := by
        intro m
        simp only [ha, norm_mul, Complex.norm_natCast]
        have h1 : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
          exact_mod_cast (sigma_bound 3 (m + 1))
        calc (↑(m + 1) : ℝ) * (ArithmeticFunction.sigma 3 (m + 1) : ℝ)
            ≤ (↑(m + 1) : ℝ) * (↑(m + 1) : ℝ) ^ 4 :=
              mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
          _ = (↑(m + 1) : ℝ) ^ 5 := by ring
      apply Summable.of_nonneg_of_le
      · intro m; positivity
      · intro m
        calc ‖a m‖ * rexp (-2 * π * m)
            ≤ ((m + 1 : ℕ) : ℝ) ^ 5 * rexp (-2 * π * m) :=
              mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _)
          _ = (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) := by simp
      · exact summable_pow5_shift
    have h_eq2 : ∀ z : ℍ,
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) =
        ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m) := by
      intro z; apply tsum_congr; intro m; simp only [ha]; ring_nf
    simp_rw [h_eq2, ha0] at h_tendsto ⊢
    convert h_tendsto.const_mul (720 : ℂ) using 2; ring
  -- F / q² = ((E₂E₄ - E₆) / q)² → 720²
  have h_exp_eq : ∀ z : ℍ, cexp (2 * π * I * 2 * z) = cexp (2 * π * I * z) ^ 2 := by
    intro z; rw [← Complex.exp_nat_mul]; congr 1; ring
  have h_F_eq : ∀ z : ℍ, F z / cexp (2 * π * I * 2 * z) =
      ((E₂ z * E₄ z - E₆ z) / cexp (2 * π * I * z)) ^ 2 := by
    intro z
    simp only [F, h_exp_eq, sq, div_mul_div_comm, Pi.mul_apply, Pi.sub_apply,
      ModularForm.toFun_eq_coe]
  simp_rw [h_F_eq]
  exact h_diff_tendsto.pow 2

/-- D(E₂E₄ - E₆) equals 720 times the q-expansion with n²·σ₃(n) coefficients.

This is key for the log-derivative limit: `(D F)/F → 2` as `z → i∞`,
since F has vanishing order 2 (F ~ c·q²).

TODO: The proof requires:
1. From E₂_mul_E₄_sub_E₆: E₂E₄ - E₆ = 720 * ∑' n·σ₃(n)·qⁿ
2. Apply D linearity: D(720 * ∑') = 720 * D(∑')
3. Apply D_qexp_tsum_pnat with a(n) = n·σ₃(n):
   - D(∑' a(n)·qⁿ) = ∑' n·a(n)·qⁿ = ∑' n²·σ₃(n)·qⁿ

Technical requirements for D_qexp_tsum_pnat:
- Summability: n·σ₃(n) ≤ n⁵ (since σ₃(n) ≤ n⁴ by sigma_bound)
  so ‖n·σ₃(n)·qⁿ‖ ≤ n⁵ * exp(-2πn·y) is summable via a33 with k=5
- Derivative bound: ‖n·σ₃(n)·n·qⁿ‖ ≤ n⁶ * exp(-2πn·y_min) on compact K ⊂ ℍ
  is summable via Real.summable_pow_mul_exp_neg_nat_mul

Note: This depends on E₂_mul_E₄_sub_E₆ from Derivative.lean (which uses D_E₄_eq_tsum).
-/
theorem D_diff_qexp (z : ℍ) :
    D (fun w => E₂ w * E₄ w - E₆ w) z =
      720 * ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
  -- Step 1: Rewrite using E₂_mul_E₄_sub_E₆
  have h_eq : ∀ w : ℍ, E₂ w * E₄ w - E₆ w =
      720 * ∑' (n : ℕ+), ↑n * ↑(σ 3 n) * cexp (2 * π * I * ↑n * w) := E₂_mul_E₄_sub_E₆
  -- Step 2: Define coefficient function a(n) = n * σ₃(n)
  let a : ℕ+ → ℂ := fun n => ↑n * ↑(σ 3 n)
  -- Helper: ‖a n‖ ≤ n⁵ (used in both hsum and hsum_deriv)
  have norm_a_le : ∀ n : ℕ+, ‖a n‖ ≤ (n : ℝ)^5 := fun n => by
    simp only [a, Complex.norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ↑(σ 3 ↑n) ≤ (n : ℝ) * (n : ℝ)^4 := by
           gcongr; exact_mod_cast sigma_bound 3 n
       _ = (n : ℝ)^5 := by ring
  -- Step 3: Summability of a(n) * q^n (using |a(n)| ≤ n⁵)
  have hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * ↑n * ↑z)) := by
    have hpos : 0 < 2 * π * z.im := by nlinarith [pi_pos, z.im_pos]
    apply Summable.of_norm_bounded (g := fun n : ℕ+ => ((n : ℕ) : ℝ)^5 * rexp (-(2 * π * z.im) * n))
        ((Real.summable_pow_mul_exp_neg_nat_mul 5 hpos).subtype _)
    intro n
    calc ‖a n * cexp (2 * π * I * ↑n * ↑z)‖
        = ‖a n‖ * ‖cexp (2 * π * I * ↑n * ↑z)‖ := norm_mul _ _
      _ ≤ (n : ℝ)^5 * ‖cexp (2 * π * I * ↑n * ↑z)‖ := by gcongr; exact norm_a_le n
      _ = (n : ℝ)^5 * rexp (-(2 * π * z.im) * ↑n) := by
          congr 1; rw [Complex.norm_exp]; congr 1
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im,
            UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, mul_zero, mul_one,
            zero_add, add_zero, sub_zero]; ring
  -- Step 4: Derivative bounds for a(n) * q^n (using |a(n)| ≤ n⁵, so derivative ≤ n⁶)
  have hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K), ‖a n * (2 * π * I * ↑n) *
        cexp (2 * π * I * ↑n * k.1)‖ ≤ u n := by
    intro K hK_sub hK_compact
    by_cases hK_nonempty : K.Nonempty
    · obtain ⟨k_min, hk_min_mem, hk_min_le⟩ := hK_compact.exists_isMinOn hK_nonempty
        Complex.continuous_im.continuousOn
      have hy_min_pos : 0 < k_min.im := hK_sub hk_min_mem
      have hpos : 0 < 2 * π * k_min.im := by nlinarith [pi_pos]
      have h := Real.summable_pow_mul_exp_neg_nat_mul 6 hpos
      have hconv : Summable (fun n : ℕ+ =>
          2 * π * ((n : ℕ) : ℝ)^6 * rexp (-(2 * π * k_min.im) * (n : ℕ))) := by
        have : Summable (fun n : ℕ+ => ((n : ℕ) : ℝ)^6 * rexp (-(2 * π * k_min.im) * (n : ℕ))) :=
          h.subtype _
        convert this.mul_left (2 * π) using 1
        ext n; ring
      use fun n => 2 * π * (n : ℝ)^6 * rexp (-2 * π * ↑n * k_min.im)
      constructor
      · apply hconv.of_nonneg_of_le
        · intro n; positivity
        · intro n
          have h1 : -2 * π * ↑↑n * k_min.im = -(2 * π * k_min.im) * ↑↑n := by ring
          simp only [h1]; exact le_refl _
      · intro n ⟨k, hk_mem⟩
        have hk_im : k_min.im ≤ k.im := hk_min_le hk_mem
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast n.pos
        have h_norm_2pin : ‖(2 : ℂ) * π * I * ↑↑n‖ = 2 * π * n := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
              Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg pi_pos.le]
        calc ‖a n * (2 * π * I * ↑↑n) * cexp (2 * π * I * ↑↑n * k)‖
            = ‖a n‖ * ‖(2 * π * I * ↑↑n)‖ * ‖cexp (2 * π * I * ↑↑n * k)‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ (n : ℝ)^5 * (2 * π * n) * rexp (-2 * π * n * k.im) := by
              rw [h_norm_2pin]
              have hexp : ‖cexp (2 * π * I * ↑↑n * k)‖ ≤ rexp (-2 * π * n * k.im) := by
                rw [Complex.norm_exp]
                have : (2 * π * I * ↑↑n * k).re = -2 * π * n * k.im := by
                  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                    Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im,
                    mul_zero, mul_one, zero_add, add_zero, sub_zero]; ring
                rw [this]
              gcongr; exact norm_a_le n
          _ ≤ (n : ℝ)^5 * (2 * π * n) * rexp (-2 * π * n * k_min.im) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp_of_le
              apply mul_le_mul_of_nonpos_left hk_im
              nlinarith [pi_pos, hn_pos]
          _ = 2 * π * (n : ℝ)^6 * rexp (-2 * π * n * k_min.im) := by ring
    · use fun _ => 0
      constructor
      · exact summable_zero
      · intro n ⟨k, hk_mem⟩
        exfalso; exact hK_nonempty ⟨k, hk_mem⟩
  -- Step 5: Apply D_qexp_tsum_pnat with b(n) = 720 * a(n) = 720 * n * σ₃(n)
  -- This avoids needing D_const_mul and MDifferentiable for the tsum
  let b : ℕ+ → ℂ := fun n => 720 * (↑n * ↑(σ 3 n))
  have h_eq' : ∀ w : ℍ, E₂ w * E₄ w - E₆ w = ∑' (n : ℕ+), b n * cexp (2 * π * I * ↑n * w) :=
    fun w => by rw [h_eq]; simp only [b, ← tsum_mul_left]; congr 1; funext n; ring
  have hsum' : Summable (fun n : ℕ+ => b n * cexp (2 * π * I * ↑n * ↑z)) := by
    convert hsum.mul_left 720 using 1; funext n; simp only [b]; ring
  have hsum_deriv' : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K), ‖b n * (2 * π * I * ↑n) *
        cexp (2 * π * I * ↑n * k.1)‖ ≤ u n := by
    intro K hK_sub hK_compact
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK_sub hK_compact
    refine ⟨fun n => 720 * u n, hu_sum.mul_left 720, fun n k => ?_⟩
    calc ‖b n * (2 * π * I * ↑n) * cexp (2 * π * I * ↑n * k.1)‖
        = 720 * ‖a n * (2 * π * I * ↑n) * cexp (2 * π * I * ↑n * k.1)‖ := by
          simp only [b, a, norm_mul, Complex.norm_ofNat]; ring
      _ ≤ 720 * u n := mul_le_mul_of_nonneg_left (hu_bound n k) (by norm_num)
  have hD := D_qexp_tsum_pnat b z hsum' hsum_deriv'
  calc D (fun w => E₂ w * E₄ w - E₆ w) z
      = D (fun w => ∑' (n : ℕ+), b n * cexp (2 * π * I * ↑n * w)) z := by
        congr 1; ext w; exact h_eq' w
    _ = ∑' (n : ℕ+), (n : ℂ) * b n * cexp (2 * π * I * ↑n * z) := hD
    _ = 720 * ∑' (n : ℕ+), (n : ℂ) ^ 2 * ↑(σ 3 n) * cexp (2 * π * I * ↑n * z) := by
        simp only [b, ← tsum_mul_left, sq]; congr 1; funext n; ring

-- Helper: D(E₂E₄ - E₆) / q → 720 (same pattern as f/q → 720)
-- This follows from D acting as q·d/dq on q-expansions, so D(n·σ₃(n)·qⁿ) = n²·σ₃(n)·qⁿ
-- and the leading coefficient 1²·σ₃(1) = 1 gives the limit 720·1 = 720
theorem D_diff_div_q_tendsto :
    Filter.Tendsto (fun z : ℍ => D (fun w => E₂ w * E₄ w - E₆ w) z /
      cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := by
  -- Use D_diff_qexp and the QExp.tendsto_nat pattern
  -- D(f) = 720 * ∑ n² * σ₃(n) * q^n
  -- D(f)/q = 720 * ∑ n² * σ₃(n) * q^(n-1)
  -- Leading term (n=1): 1² * σ₃(1) = 1, so limit is 720 * 1 = 720
  have h_rw : ∀ z : ℍ, D (fun w => E₂ w * E₄ w - E₆ w) z =
      720 * ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := D_diff_qexp
  simp_rw [h_rw]
  -- Divide by q and reindex
  have h_eq : ∀ z : ℍ,
      (720 * ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z)) / cexp (2 * π * I * z) =
      720 * (∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * π * I * (↑n - 1) * z)) := by
    intro z
    rw [mul_div_assoc, ← tsum_div_const]
    congr 1; apply tsum_congr; intro n
    rw [mul_div_assoc, ← Complex.exp_sub]
    congr 2; ring
  simp_rw [h_eq]
  -- Reindex ℕ+ to ℕ via n ↦ m+1
  have h_reindex : ∀ z : ℍ,
      ∑' n : ℕ+, (↑↑n : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) ↑n) *
        cexp (2 * π * I * (↑n - 1) * z) =
      ∑' m : ℕ, (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) *
        cexp (2 * π * I * m * z) := by
    intro z
    rw [← Equiv.tsum_eq (Equiv.pnatEquivNat)]
    apply tsum_congr; intro m
    simp only [Equiv.pnatEquivNat_apply, PNat.natPred_add_one]
    congr 2
    -- Need: ↑↑m - 1 = ↑m.natPred in ℂ
    -- From PNat.natPred_add_one: m.natPred + 1 = ↑m
    have h := PNat.natPred_add_one m
    simp only [← h, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  simp_rw [h_reindex]
  -- Apply QExp.tendsto_nat pattern
  -- a(m) = (m+1)² * σ₃(m+1), a(0) = 1² * σ₃(1) = 1 * 1 = 1
  have ha : ∀ m : ℕ, (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) =
      if m = 0 then 1 else (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) := by
    intro m
    split_ifs with h
    · simp [h, ArithmeticFunction.sigma_one]
    · rfl
  -- Apply QExp.tendsto_nat with coefficient function a(m) = (m+1)² * σ₃(m+1)
  set a : ℕ → ℂ := fun m => (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) with ha_def
  have ha0 : a 0 = 1 := by simp [ha_def, ArithmeticFunction.sigma_one]
  have h_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * I * z * m))
      atImInfty (nhds (a 0)) := by
    apply QExp.tendsto_nat a
    -- Summability: ‖a m‖ ≤ (m+1)^6, and (m+1)^6 * exp(-2πm) is summable
    have hbound : ∀ m : ℕ, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 6 := by
      intro m
      simp only [ha_def, norm_mul, Complex.norm_natCast, Complex.norm_pow]
      have h1 : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
        exact_mod_cast (sigma_bound 3 (m + 1))
      calc (↑(m + 1) : ℝ) ^ 2 * (ArithmeticFunction.sigma 3 (m + 1) : ℝ)
          ≤ (↑(m + 1) : ℝ) ^ 2 * (↑(m + 1) : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (Nat.cast_nonneg _) _)
        _ = (↑(m + 1) : ℝ) ^ 6 := by ring
    apply Summable.of_nonneg_of_le
    · intro m; positivity
    · intro m
      calc ‖a m‖ * rexp (-2 * π * m)
          ≤ ((m + 1 : ℕ) : ℝ) ^ 6 * rexp (-2 * π * m) :=
            mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _)
        _ = (m + 1 : ℝ) ^ 6 * rexp (-2 * π * m) := by simp
    · exact summable_pow6_shift
  have h_eq2 : ∀ z : ℍ,
      ∑' m : ℕ, (↑(m + 1) : ℂ) ^ 2 * ↑((ArithmeticFunction.sigma 3) (m + 1)) *
        cexp (2 * π * I * m * z) =
      ∑' m : ℕ, a m * cexp (2 * π * I * z * m) := by
    intro z; apply tsum_congr; intro m; simp only [ha_def]; ring_nf
  simp_rw [h_eq2, ha0] at h_tendsto ⊢
  convert h_tendsto.const_mul (720 : ℂ) using 2; ring

theorem D_F_div_F_tendsto :
    Filter.Tendsto (fun z : ℍ => D F z / F z) atImInfty (nhds (2 : ℂ)) := by
  -- F = (E₂E₄ - E₆)² = f² where f = E₂E₄ - E₆
  -- D(f²) = 2f·Df (chain rule), so DF/F = 2·Df/f
  -- f/q → 720 (from F_vanishing_order proof), and f has vanishing order 1
  -- Df/f → 1 (the vanishing order), so DF/F → 2

  -- Step 1: Define f and show F = f²
  set f : ℍ → ℂ := fun z => E₂ z * E₄.toFun z - E₆.toFun z with hf_def
  have hF_eq : ∀ z, F z = (f z) ^ 2 := fun z => by
    simp only [F, hf_def, sq, Pi.mul_apply, Pi.sub_apply, ModularForm.toFun_eq_coe]
  -- Step 2: f is holomorphic
  have hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    apply MDifferentiable.sub
    · exact MDifferentiable.mul E₂_holo' E₄.holo'
    · exact E₆.holo'
  -- Step 3: D(F) = 2·f·D(f) by chain rule
  have hDF_eq : ∀ z, D F z = 2 * f z * D f z := by
    intro z
    have h := D_sq f hf_holo
    have hF_eq' : F = f ^ 2 := by
      ext z
      simp only [F, hf_def, sq, Pi.mul_apply, Pi.sub_apply, ModularForm.toFun_eq_coe,
        Pi.pow_apply]
    rw [hF_eq']
    exact congr_fun h z
  -- Step 4: Therefore D(F)/F = 2·D(f)/f
  have hDF_div_eq : ∀ z, F z ≠ 0 → D F z / F z = 2 * (D f z / f z) := by
    intro z hFz
    have hfz : f z ≠ 0 := by
      intro hf_zero
      apply hFz
      rw [hF_eq z, hf_zero, sq, zero_mul]
    rw [hDF_eq z, hF_eq z, sq]
    field_simp [hfz]
  -- Step 5: f/q → 720 (from F_vanishing_order proof)
  have hf_div_q : Filter.Tendsto (fun z : ℍ => f z / cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := by
    -- This is exactly h_diff_tendsto from F_vanishing_order proof
    -- Note: E₄ z = E₄.toFun z by ModularForm.toFun_eq_coe
    have h_f_eq : ∀ z : ℍ, f z = E₂ z * E₄ z - E₆ z := fun z => by
      simp only [hf_def, ModularForm.toFun_eq_coe]
    have h_rw : ∀ z : ℍ, E₂ z * E₄ z - E₆ z =
        720 * ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * n * z) := E₂_mul_E₄_sub_E₆
    have h_eq : ∀ z : ℍ,
        f z / cexp (2 * π * Complex.I * z) =
        720 * (∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z)) := by
      intro z
      rw [h_f_eq z, h_rw z, mul_div_assoc, ← tsum_div_const]
      congr 1; apply tsum_congr; intro n
      rw [mul_div_assoc, ← Complex.exp_sub]; congr 2; ring
    simp_rw [h_eq]
    have h_reindex : ∀ z : ℍ,
        ∑' n : ℕ+, ↑n * ↑(ArithmeticFunction.sigma 3 n) *
          cexp (2 * π * Complex.I * (n - 1) * z) =
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) := by
      intro z
      simpa [tsum_pnat_eq_tsum_succ3] using
        (tsum_pnat_eq_tsum_succ3 (f := fun n : ℕ =>
          (n : ℂ) * (↑(ArithmeticFunction.sigma 3 n) : ℂ) *
            cexp (2 * π * Complex.I * ((n : ℂ) - 1) * z)))
    simp_rw [h_reindex]
    set a : ℕ → ℂ := fun m => ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) with ha
    have ha0 : a 0 = 1 := by simp [ha, ArithmeticFunction.sigma_one]
    have h_tendsto : Filter.Tendsto
        (fun z : ℍ => ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m))
        atImInfty (nhds (a 0)) := by
      apply QExp.tendsto_nat a
      have hbound : ∀ m : ℕ, ‖a m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ 5 := by
        intro m
        simp only [ha, norm_mul, Complex.norm_natCast]
        have h1 : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 4 := by
          exact_mod_cast (sigma_bound 3 (m + 1))
        calc (↑(m + 1) : ℝ) * (ArithmeticFunction.sigma 3 (m + 1) : ℝ)
            ≤ (↑(m + 1) : ℝ) * (↑(m + 1) : ℝ) ^ 4 :=
              mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
          _ = (↑(m + 1) : ℝ) ^ 5 := by ring
      apply Summable.of_nonneg_of_le
      · intro m; positivity
      · intro m
        calc ‖a m‖ * rexp (-2 * π * m)
            ≤ ((m + 1 : ℕ) : ℝ) ^ 5 * rexp (-2 * π * m) :=
              mul_le_mul_of_nonneg_right (hbound m) (Real.exp_nonneg _)
          _ = (m + 1 : ℝ) ^ 5 * rexp (-2 * π * m) := by simp
      · exact summable_pow5_shift
    have h_eq2 : ∀ z : ℍ,
        ∑' m : ℕ, ↑(m + 1) * ↑(ArithmeticFunction.sigma 3 (m + 1)) *
          cexp (2 * π * Complex.I * m * z) =
        ∑' m : ℕ, a m * cexp (2 * π * Complex.I * z * m) := by
      intro z; apply tsum_congr; intro m; simp only [ha]; ring_nf
    simp_rw [h_eq2, ha0] at h_tendsto ⊢
    convert h_tendsto.const_mul (720 : ℂ) using 2; ring
  -- Step 6: D(f)/q → 720 (by D_diff_div_q_tendsto)
  have hDf_div_q : Filter.Tendsto (fun z : ℍ => D f z / cexp (2 * π * Complex.I * z))
      atImInfty (nhds (720 : ℂ)) := D_diff_div_q_tendsto
  -- Step 7: D(f)/f → 1 by dividing limits (720/720 = 1)
  have h_720_ne : (720 : ℂ) ≠ 0 := by norm_num
  have hDf_div_f : Filter.Tendsto (fun z : ℍ => D f z / f z) atImInfty (nhds 1) := by
    have h_eq : ∀ z : ℍ, cexp (2 * π * Complex.I * z) ≠ 0 →
        D f z / f z = (D f z / cexp (2 * π * Complex.I * z)) /
          (f z / cexp (2 * π * Complex.I * z)) := by
      intro z hexp
      field_simp [hexp]
    have h_exp_ne : ∀ᶠ z : ℍ in atImInfty, cexp (2 * π * Complex.I * z) ≠ 0 :=
      Filter.Eventually.of_forall (fun _ => Complex.exp_ne_zero _)
    have h_f_ne : ∀ᶠ z : ℍ in atImInfty, f z / cexp (2 * π * Complex.I * z) ≠ 0 :=
      hf_div_q.eventually_ne h_720_ne
    have h_limit : Filter.Tendsto
        (fun z => (D f z / cexp (2 * π * Complex.I * z)) /
          (f z / cexp (2 * π * Complex.I * z)))
        atImInfty (nhds (720 / 720 : ℂ)) := by
      apply Filter.Tendsto.div hDf_div_q hf_div_q h_720_ne
    simp only [div_self h_720_ne] at h_limit
    apply h_limit.congr'
    filter_upwards [h_exp_ne, h_f_ne] with z hexp hf_ne
    exact (h_eq z hexp).symm
  -- Step 8: D(F)/F → 2·1 = 2
  have h_F_ne := eventually_ne_zero_of_tendsto_div (by norm_num : (720^2 : ℂ) ≠ 0) F_vanishing_order
  have h_2_eq : (2 : ℂ) = 2 * 1 := by ring
  rw [h_2_eq]
  apply (hDf_div_f.const_mul (2 : ℂ)).congr'
  filter_upwards [h_F_ne] with z hFz
  exact (hDF_div_eq z hFz).symm

end MonotoneFG

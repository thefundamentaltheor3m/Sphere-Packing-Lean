/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.Monotonicity_ImagAxis
import SpherePacking.ModularForms.summable_lems

/-!
Auxiliary lemmas for `SpherePacking.ModularForms.Monotonicity`.

This file contains Sections 1–3: the definition of `L₁₀`, Serre-derivative computations, and
large-t positivity / limit statements used to prove `L₁₀(it) > 0`.
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

namespace MonotoneFG

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
  -- MDifferentiable hypotheses
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := F_holo
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := G_holo
  have hDF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) := serre_D_differentiable hF
  have hDG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 G) := serre_D_differentiable hG
  -- Expand L₁₀ and apply serre_D_sub
  -- Note: L₁₀ z = (serre_D 10 F * G - F * serre_D 10 G) z
  have hL₁₀_eq : L₁₀ = serre_D 10 F * G - F * serre_D 10 G := rfl
  rw [hL₁₀_eq]
  -- Use serre_D_sub: need to align coercions (22 : ℤ) vs (22 : ℂ)
  have hsub := serre_D_sub (22 : ℤ) _ _ (hDF.mul hG) (hF.mul hDG)
  simp only [Int.cast_ofNat] at hsub
  rw [hsub, Pi.sub_apply]
  -- Apply serre_D_mul to first term: serre_D 22 ((serre_D 10 F) * G)
  -- 22 = 12 + 10, so serre_D_mul gives: ∂₁₂(∂₁₀F) * G + (∂₁₀F) * ∂₁₀G
  have h1 : serre_D 22 (serre_D 10 F * G) z =
      serre_D 12 (serre_D 10 F) z * G z + serre_D 10 F z * serre_D 10 G z := by
    conv_lhs => rw [show (22 : ℂ) = 12 + 10 by norm_num]
    have := congrFun (serre_D_mul 12 10 (serre_D 10 F) G hDF hG) z
    simp only [Pi.mul_apply, Pi.add_apply] at this ⊢
    exact this
  -- Apply serre_D_mul to second term: serre_D 22 (F * (serre_D 10 G))
  -- 22 = 10 + 12, so serre_D_mul gives: ∂₁₀F * (∂₁₀G) + F * ∂₁₂(∂₁₀G)
  have h2 : serre_D 22 (F * serre_D 10 G) z =
      serre_D 10 F z * serre_D 10 G z + F z * serre_D 12 (serre_D 10 G) z := by
    conv_lhs => rw [show (22 : ℂ) = 10 + 12 by norm_num]
    have := congrFun (serre_D_mul 10 12 F (serre_D 10 G) hF hDG) z
    simp only [Pi.mul_apply, Pi.add_apply] at this ⊢
    exact this
  -- Combine: cross terms (∂₁₀F)(∂₁₀G) cancel
  rw [h1, h2]
  ring

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

/-- `negDE₂(it) = -(D E₂)(it)` is real for all `t > 0`. -/
theorem negDE₂_imag_axis_real : ResToImagAxis.Real negDE₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hE₂_real : (E₂ z).im = 0 := by
    have := E₂_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
  have hE₄_real : (E₄.toFun z).im = 0 := by
    have := E₄_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
  have h12_real : ((12 : ℂ)⁻¹).im = 0 := by norm_num
  have hE₂_sq_real : (E₂ z * E₂ z).im = 0 := by rw [Complex.mul_im, hE₂_real]; ring
  have hdiff_real : (E₂ z * E₂ z - E₄ z).im = 0 := by
    rw [Complex.sub_im, hE₂_sq_real]
    simp only [ModularForm.toFun_eq_coe, zero_sub, neg_eq_zero] at hE₄_real ⊢; exact hE₄_real
  have hprod_real : ((12 : ℂ)⁻¹ * (E₂ z * E₂ z - E₄ z)).im = 0 := by
    rw [Complex.mul_im, h12_real, hdiff_real]; ring
  simp only [negDE₂, Pi.neg_apply, ramanujan_E₂, Pi.mul_apply, Pi.sub_apply, neg_im]
  exact neg_eq_zero.mpr hprod_real

/-- E₂ equals 1 minus 24 times the σ₁ q-expansion.

This combines E₂_eq (which gives n/(1-q^n) form) with tsum_eq_tsum_sigma
(which converts n/(1-q^n) to σ₁ form).

The proof uses:
1. tsum_pnat_eq_tsum_succ3 to convert ℕ+ sums to ℕ sums (with n+1 indexing)
2. tsum_eq_tsum_sigma to show the two ℕ-indexed forms are equal

See E2.lean:857-864 for the pattern used in E₂_eq.
-/
lemma E₂_eq_sigma (z : ℍ) :
    E₂ z = 1 - 24 * ∑' (n : ℕ+), ↑(σ 1 n) * cexp (2 * π * I * ↑n * z) := by
  rw [E₂_eq z]
  -- Goal: 1 - 24 * ∑' n/(1-q^n) = 1 - 24 * ∑' σ₁(n) * q^n
  -- Suffices to show: ∑' n/(1-q^n) = ∑' σ₁(n) * q^n
  congr 2
  -- Use tsum_pnat_eq_tsum_succ3 to convert both sums from ℕ+ to ℕ indexing
  -- hr rewrites LHS: ∑' ℕ+, n/(1-q) → ∑' ℕ, (n+1)/(1-q)
  -- hl rewrites RHS: ∑' ℕ+, σ₁(n)*q → ∑' ℕ, σ₁(n+1)*q
  have hl := tsum_pnat_eq_tsum_succ3 (fun n => ArithmeticFunction.sigma 1 n *
      cexp (2 * π * Complex.I * n * z))
  have hr := tsum_pnat_eq_tsum_succ3 (fun n => n * cexp (2 * π * Complex.I * n * z) /
      (1 - cexp (2 * π * Complex.I * n * z)))
  rw [hr, hl]
  -- Apply tsum_eq_tsum_sigma to show the ℕ-indexed sums are equal
  have ht := tsum_eq_tsum_sigma z
  simp at *
  rw [ht]

/-- The σ₁ q-series is summable for any z in the upper half-plane. -/
private lemma sigma1_qexp_summable (z : ℍ) :
    Summable (fun n : ℕ+ => ↑((σ 1) ↑n) * cexp (2 * π * I * ↑n * ↑z)) := by
  have hz := z.im_pos
  have hpos : 0 < 2 * π * z.im := by nlinarith [pi_pos]
  have h := Real.summable_pow_mul_exp_neg_nat_mul 2 hpos
  have hconv : Summable (fun n : ℕ+ => ((n : ℕ) : ℝ)^2 * rexp (-(2 * π * z.im) * (n : ℕ))) :=
    h.subtype _
  apply Summable.of_norm_bounded
    (g := fun n : ℕ+ => ((n : ℕ) : ℝ)^2 * rexp (-(2 * π * z.im) * (n : ℕ))) hconv
  intro n
  have hsig : ‖(↑((σ 1) ↑n) : ℂ)‖ ≤ (n : ℝ)^2 := by
    have hsig' := sigma_bound 1 n
    simp only [Complex.norm_natCast]
    exact_mod_cast hsig'
  calc ‖↑((σ 1) ↑n) * cexp (2 * π * I * ↑n * ↑z)‖
      = ‖(↑((σ 1) ↑n) : ℂ)‖ * ‖cexp (2 * π * I * ↑n * ↑z)‖ := norm_mul _ _
    _ ≤ (n : ℝ)^2 * ‖cexp (2 * π * I * ↑n * ↑z)‖ := by
        apply mul_le_mul_of_nonneg_right hsig; positivity
    _ = (n : ℝ)^2 * rexp (-(2 * π * z.im) * ↑n) := by
        congr 1; rw [Complex.norm_exp]
        congr 1
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
          Complex.natCast_re, Complex.natCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring

/-- Derivative bound for σ₁ q-series on compact subsets of ℍ. -/
private lemma sigma1_qexp_deriv_bound :
    ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (k : K), ‖↑((σ 1) ↑n) * (2 * π * I * ↑n) *
        cexp (2 * π * I * ↑n * k.1)‖ ≤ u n := by
  intro K hK_sub hK_compact
  by_cases hK_nonempty : K.Nonempty
  · obtain ⟨k_min, hk_min_mem, hk_min_le⟩ := hK_compact.exists_isMinOn hK_nonempty
      Complex.continuous_im.continuousOn
    have hy_min_pos : 0 < k_min.im := hK_sub hk_min_mem
    have hpos : 0 < 2 * π * k_min.im := by nlinarith [pi_pos]
    have h := Real.summable_pow_mul_exp_neg_nat_mul 3 hpos
    have hconv : Summable (fun n : ℕ+ =>
        2 * π * ((n : ℕ) : ℝ)^3 * rexp (-(2 * π * k_min.im) * (n : ℕ))) := by
      have h' : Summable (fun n : ℕ+ => (2 * π) * (((n : ℕ) : ℝ)^3 *
          rexp (-(2 * π * k_min.im) * (n : ℕ)))) := (h.subtype _).mul_left (2 * π)
      convert h' using 1
      ext n
      ring
    use fun n => 2 * π * (n : ℝ)^3 * rexp (-2 * π * ↑n * k_min.im)
    constructor
    · apply hconv.of_nonneg_of_le
      · intro n; positivity
      · intro n
        have h1 : -2 * π * ↑↑n * k_min.im = -(2 * π * k_min.im) * ↑↑n := by ring
        simp only [h1]
        rfl
    · intro n ⟨k, hk_mem⟩
      have hk_im : k_min.im ≤ k.im := hk_min_le hk_mem
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast n.pos
      have hsig : ‖(↑((σ 1) ↑n) : ℂ)‖ ≤ (n : ℝ)^2 := by
        have hsig' := sigma_bound 1 n
        simp only [Complex.norm_natCast]
        exact_mod_cast hsig'
      have h_norm_2pin : ‖(2 : ℂ) * π * I * ↑↑n‖ = 2 * π * n := by
        rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul]
        simp only [Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos pi_pos, Complex.norm_I, Complex.norm_natCast]
        ring
      have h_norm_exp : ‖cexp (2 * π * I * ↑↑n * k)‖ = rexp (-2 * π * ↑↑n * k.im) := by
        rw [Complex.norm_exp]; congr 1
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
          Complex.natCast_re, Complex.natCast_im]
        ring
      calc ‖↑((σ 1) ↑n) * (2 * π * I * ↑n) * cexp (2 * π * I * ↑n * k)‖
          = ‖(↑((σ 1) ↑n) : ℂ)‖ * ‖(2 : ℂ) * π * I * ↑↑n‖ * ‖cexp (2 * π * I * ↑↑n * k)‖ := by
            rw [norm_mul, norm_mul]
        _ = ‖(↑((σ 1) ↑n) : ℂ)‖ * (2 * π * n) * rexp (-2 * π * ↑↑n * k.im) := by
            rw [h_norm_2pin, h_norm_exp]
        _ ≤ (n : ℝ)^2 * (2 * π * n) * rexp (-2 * π * ↑↑n * k.im) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right hsig
              nlinarith [pi_pos, hn_pos]
            · positivity
        _ = 2 * π * (n : ℝ)^3 * rexp (-2 * π * ↑↑n * k.im) := by ring
        _ ≤ 2 * π * (n : ℝ)^3 * rexp (-2 * π * ↑↑n * k_min.im) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp_of_le
            have h_neg : -2 * π * ↑↑n ≤ 0 := by nlinarith [pi_pos, hn_pos]
            have h_ineq := mul_le_mul_of_nonpos_left hk_im h_neg
            linarith
  · use fun _ => 0
    constructor
    · exact summable_zero
    · intro n ⟨k, hk_mem⟩; exact (hK_nonempty ⟨k, hk_mem⟩).elim

theorem D_E₂_qexp (z : ℍ) :
    D E₂ z = -24 * ∑' n : ℕ+, (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
  -- Define coefficient function
  let a : ℕ+ → ℂ := fun n => ↑((ArithmeticFunction.sigma 1) ↑n)
  let qseries : ℍ → ℂ := fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * ↑n * w)
  -- Use E₂_eq_sigma and D_qexp_tsum_pnat
  have hE₂_eq : ∀ w : ℍ, E₂ w = 1 - 24 * qseries w := E₂_eq_sigma
  have hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * ↑n * ↑z)) := sigma1_qexp_summable z
  have hsum_deriv := sigma1_qexp_deriv_bound
  have hD_qseries : D qseries z = ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * ↑n * z) :=
    D_qexp_tsum_pnat a z hsum hsum_deriv
  -- D(E₂) = D(1 - 24 * qseries) = D(1) - 24 * D(qseries) = -24 * D(qseries)
  -- We compute this using the definition of D
  simp only [D]
  have h_E₂_agree : (E₂ ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w => 1 - 24 * ∑' n : ℕ+, a n * cexp (2 * π * I * ↑n * w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, hE₂_eq, qseries, coe_mk_subtype]
  rw [h_E₂_agree.deriv_eq]
  -- Step 1: The qseries ∘ ofComplex agrees with the ℂ → ℂ tsum near z
  have h_qseries_agree : (qseries ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * ↑n * w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, qseries, coe_mk_subtype]
  -- Step 2: From hD_qseries, get deriv (qseries ∘ ofComplex) z = (2πi) * ∑' n * a n * qⁿ
  have h_deriv_qseries : deriv (qseries ∘ ofComplex) z =
      2 * π * I * ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * ↑n * z) := by
    have hD := hD_qseries; simp only [D] at hD
    -- hD : (2πi)⁻¹ * deriv (...) = tsum, multiply both sides by 2πi
    have := congrArg (fun x => 2 * π * I * x) hD
    simp only [mul_inv_cancel_left₀ two_pi_I_ne_zero] at this
    exact this
  -- Step 3: deriv of tsum = deriv of qseries ∘ ofComplex (they agree near z)
  have h_deriv_tsum : deriv (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * ↑n * w)) z =
      2 * π * I * ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * ↑n * z) := by
    rw [← h_qseries_agree.deriv_eq, h_deriv_qseries]
  -- Step 4: tsum is differentiable at z (from D_qexp_tsum_pnat infrastructure)
  have h_diff_tsum : DifferentiableAt ℂ
      (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * ↑n * w)) z := by
    -- Since E₂ = 1 - 24 * qseries, we have qseries = (1 - E₂) / 24
    -- E₂ is holomorphic (MDifferentiable), so qseries is differentiable
    have hE₂_diff : DifferentiableAt ℂ (E₂ ∘ ofComplex) z :=
      MDifferentiableAt_DifferentiableAt (E₂_holo' z)
    have h_diff_expr : DifferentiableAt ℂ (fun w => (1 - E₂ (ofComplex w)) / 24) z :=
      ((differentiableAt_const 1).sub hE₂_diff).div_const 24
    -- qseries ∘ ofComplex = (1 - E₂ ∘ ofComplex) / 24 near z
    have h_eq : (qseries ∘ ofComplex) =ᶠ[nhds (z : ℂ)] (fun w => (1 - E₂ (ofComplex w)) / 24) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, qseries]
      have := hE₂_eq ⟨w, hw⟩
      -- this : E₂ ⟨w,hw⟩ = 1 - 24 * qseries ⟨w,hw⟩, so qseries = (1 - E₂) / 24
      rw [this]; ring
    have h_diff_qseries : DifferentiableAt ℂ (qseries ∘ ofComplex) z :=
      h_eq.differentiableAt_iff.mpr h_diff_expr
    exact h_qseries_agree.symm.differentiableAt_iff.mpr h_diff_qseries
  -- Step 5: Compute deriv (1 - 24 * tsum) = -deriv(24 * tsum) = -24 * deriv(tsum)
  rw [deriv_const_sub, deriv_const_mul _ h_diff_tsum, h_deriv_tsum]
  -- Step 6: Simplify (2πi)⁻¹ * (-24 * (2πi * ∑')) = -24 * ∑'
  -- The key cancellation: (2πi)⁻¹ * 2πi = 1
  -- Goal: (2πI)⁻¹ * -(24 * (2πI * ∑')) = -24 * ∑'
  have h_cancel : (2 * ↑π * I)⁻¹ * (2 * ↑π * I) = 1 := inv_mul_cancel₀ two_pi_I_ne_zero
  set S := ∑' n : ℕ+, ↑↑n * a n * cexp (2 * ↑π * I * ↑↑n * ↑z) with hS
  calc (2 * ↑π * I)⁻¹ * -(24 * (2 * ↑π * I * S))
      = -((2 * ↑π * I)⁻¹ * (24 * (2 * ↑π * I * S))) := by ring
    _ = -(24 * ((2 * ↑π * I)⁻¹ * (2 * ↑π * I) * S)) := by ring
    _ = -(24 * (1 * ∑' n : ℕ+, ↑↑n * a n * cexp (2 * ↑π * I * ↑↑n * ↑z))) := by rw [h_cancel]
    _ = -24 * ∑' n : ℕ+, ↑↑n * a n * cexp (2 * ↑π * I * ↑↑n * ↑z) := by ring
    _ = -24 * ∑' n : ℕ+, ↑↑n * ↑((σ 1) ↑n) * cexp (2 * ↑π * I * ↑↑n * ↑z) := rfl

theorem E₄_sub_E₂_sq_qexp (z : ℍ) :
    E₄.toFun z - E₂ z * E₂ z =
      288 * ∑' n : ℕ+, (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
        cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
  -- From ramanujan_E₂: D E₂ = 12⁻¹ * (E₂² - E₄)
  -- Rearranging: E₄ - E₂² = -12 * D E₂
  have h_ram : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := ramanujan_E₂
  have h_ram_z : D E₂ z = 12⁻¹ * (E₂ z * E₂ z - E₄.toFun z) := congrFun h_ram z
  -- Rearrange: E₄ - E₂² = -12 * D E₂
  have h_rearr : E₄.toFun z - E₂ z * E₂ z = -12 * D E₂ z := by
    have h12_ne : (12 : ℂ)⁻¹ ≠ 0 := by norm_num
    calc E₄.toFun z - E₂ z * E₂ z
        = -(E₂ z * E₂ z - E₄.toFun z) := by ring
      _ = -(12 * (12⁻¹ * (E₂ z * E₂ z - E₄.toFun z))) := by field_simp
      _ = -12 * (12⁻¹ * (E₂ z * E₂ z - E₄.toFun z)) := by ring
      _ = -12 * D E₂ z := by rw [← h_ram_z]
  rw [h_rearr, D_E₂_qexp z]
  -- -12 * (-24 * ∑...) = 288 * ∑...
  have h288 : (-12 : ℂ) * -24 = 288 := by norm_num
  rw [← mul_assoc, h288]

/--
On the imaginary axis, `E₄(it).re > E₂(it).re²` for all `t > 0`.
This follows from the q-expansion: `E₄ - E₂² = 288 * ∑ n * σ₁(n) * qⁿ` has positive terms,
and on z = it, q = exp(-2πt) ∈ (0,1) is positive, so each term is positive.
-/
theorem hE₄_gt_E₂sq (t : ℝ) (ht : 0 < t) :
    (E₄.toFun ⟨Complex.I * t, by simp [ht]⟩).re > (E₂ ⟨Complex.I * t, by simp [ht]⟩).re ^ 2 := by
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩ with hz_def
  have hz_eq : (z : ℂ) = Complex.I * t := rfl
  have hqexp := E₄_sub_E₂_sq_qexp z
  have hE₂_real := im_eq_zero_of_real E₂_imag_axis_real t ht
  have hE₂_sq_re : (E₂ z * E₂ z).re = (E₂ z).re ^ 2 := by
    rw [Complex.mul_re, hE₂_real, mul_zero, sub_zero, sq]
  -- Difference real part
  have hdiff_re : (E₄.toFun z - E₂ z * E₂ z).re = (E₄.toFun z).re - (E₂ z).re ^ 2 := by
    rw [Complex.sub_re, hE₂_sq_re]
  -- Need to show the difference is positive via q-expansion
  rw [gt_iff_lt, ← sub_pos, ← hdiff_re, hqexp]
  -- Now: (288 * ∑ n * σ₁(n) * qⁿ).re > 0
  -- 288 is real, so (288 * x).re = 288 * x.re
  have h288_real : (288 : ℂ).im = 0 := by norm_num
  rw [mul_re, h288_real, zero_mul, sub_zero]
  apply mul_pos (by norm_num : (0 : ℝ) < 288)
  -- Show the sum has positive real part using the pattern from E₂_mul_E₄_sub_E₆
  -- Step 1: Summability of the series
  have hsum : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
    · intro n; exact norm_nonneg _
    · intro n
      calc ‖(↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
              cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑↑n : ℂ)‖ * ‖(↑((ArithmeticFunction.sigma 1) ↑n) : ℂ)‖ *
              ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (↑n : ℝ) * (↑n : ℝ)^2 * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            gcongr
            · rw [Complex.norm_natCast]
            · rw [Complex.norm_natCast]
              have hbound := sigma_bound 1 n
              exact_mod_cast hbound
        _ = ‖(↑n : ℂ) ^ 3 * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
            rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
            ring
    · have := a33 3 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- Adjust the exponent form to match the goal
  have hsum' : Summable fun n : ℕ+ => (↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z) := by
    simp_rw [show ∀ n : ℕ+, (2 : ℂ) * ↑Real.pi * Complex.I * ↑n * z =
        2 * ↑Real.pi * Complex.I * z * n by intro n; ring]
    exact hsum
  -- Key simplification: on z = I*t, the exponential becomes real
  have hexp_simpl : ∀ n : ℕ+, cexp (2 * ↑Real.pi * Complex.I * ↑n * z) =
      Real.exp (-(2 * π * n * t)) := by
    intro n
    rw [hz_eq]
    have harg : (2 : ℂ) * ↑Real.pi * Complex.I * ↑n * (Complex.I * ↑t) =
        ↑(-(2 * π * (n : ℕ) * t)) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [harg, Complex.ofReal_exp]
  -- Step 2: Each term is real on imaginary axis: n * σ(1,n) * exp(-2πnt)
  have hterm_real : ∀ n : ℕ+, ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).im = 0 := by
    intro n
    rw [hexp_simpl]
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  -- Step 3: Each term is positive
  have hterm_pos : ∀ n : ℕ+, 0 < ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    intro n
    rw [hexp_simpl]
    simp only [mul_re, natCast_re, natCast_im, sub_zero,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    -- Term is n * σ(1,n) * exp(-2πnt), all factors positive
    apply mul_pos
    · apply mul_pos
      · exact_mod_cast n.pos
      · exact_mod_cast ArithmeticFunction.sigma_pos 1 n n.ne_zero
    · exact Real.exp_pos _
  -- Step 4: Sum of positive terms is positive
  have hsum_re : Summable fun n : ℕ+ => ((↑↑n : ℂ) * ↑((ArithmeticFunction.sigma 1) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * ↑n * z)).re := by
    obtain ⟨x, hx⟩ := hsum'
    exact ⟨x.re, Complex.hasSum_re hx⟩
  rw [Complex.re_tsum hsum']
  exact Summable.tsum_pos hsum_re (fun n => le_of_lt (hterm_pos n)) 1 (hterm_pos 1)

/--
`negDE₂(it) = -(D E₂)(it) > 0` for all `t > 0`.
Blueprint: Corollary 8.9 - this follows from the Ramanujan formula `D E₂ = (E₂² - E₄)/12`,
which gives `negDE₂ = (E₄ - E₂²)/12`. The inequality `E₄(it) > E₂(it)²` holds because
the q-expansion `E₄ - E₂² = 288q + 1728q² + ...` has positive coefficients, and on the
imaginary axis `q = exp(-2πt) > 0`.
-/
theorem negDE₂_imag_axis_pos : ResToImagAxis.Pos negDE₂ := by
  refine ⟨negDE₂_imag_axis_real, fun t ht => ?_⟩
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hE₂_real : (E₂ z).im = 0 := by
    have := E₂_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
  have hE₄_real : (E₄.toFun z).im = 0 := by
    have := E₄_imag_axis_real t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at this; exact this
  have h12_real : ((12 : ℂ)⁻¹).im = 0 := by norm_num
  have hE₂_sq_real : (E₂ z * E₂ z).im = 0 := by rw [Complex.mul_im, hE₂_real]; ring
  have hdiff_real : (E₂ z * E₂ z - E₄ z).im = 0 := by
    simp only [ModularForm.toFun_eq_coe] at hE₄_real
    rw [Complex.sub_im, hE₂_sq_real, hE₄_real]; ring
  simp only [negDE₂, Pi.neg_apply, ramanujan_E₂, Pi.mul_apply, Pi.sub_apply, neg_re,
    ModularForm.toFun_eq_coe]
  -- Goal has 12⁻¹ as a constant function; h12_real applies to (12 : ℂ)⁻¹
  have h12_at_z : (12⁻¹ : ℍ → ℂ) z = (12 : ℂ)⁻¹ := rfl
  rw [h12_at_z, Complex.mul_re, h12_real, hdiff_real, mul_zero, sub_zero, neg_pos]
  -- Goal: 12⁻¹.re * (E₂ z² - E₄ z).re < 0, i.e., E₄.re > E₂.re²
  have hE₂_sq_re : (E₂ z * E₂ z).re = (E₂ z).re ^ 2 := by
    rw [Complex.mul_re, hE₂_real, mul_zero, sub_zero, sq]
  rw [Complex.sub_re, hE₂_sq_re]
  have h12_pos : (0 : ℝ) < ((12 : ℂ)⁻¹).re := by norm_num
  -- hE₄_gt_E₂sq gives (E₄.toFun z).re > (E₂ z).re^2, need to convert to E₄ z
  have h_ineq := hE₄_gt_E₂sq t ht
  simp only [ModularForm.toFun_eq_coe] at h_ineq
  nlinarith [h_ineq, h12_pos]

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

/--
The vanishing order of G at infinity is 5/2.
Blueprint: H₂ = Θ₂⁴ ~ 16q^(1/2), H₄ → 1 as im(z) → ∞.
So G = H₂³(2H₂² + 5H₂H₄ + 5H₄²) ~ H₂³ * 5 = 5 * 16³ * q^(3/2) = 20480 * q^(3/2).
Here q^(3/2) = exp(3πiz) = exp(2πi * (3/2) * z).
-/
theorem G_vanishing_order :
    Filter.Tendsto (fun z : ℍ => G z / cexp (2 * π * Complex.I * (3/2) * z))
      atImInfty (nhds (20480 : ℂ)) := by
  -- G = H₂³ * (2H₂² + 5H₂H₄ + 5H₄²)
  -- As z → ∞: H₂ / exp(πiz) → 16, H₂ → 0, H₄ → 1
  -- So G / exp(3πiz) → 16³ * 5 = 20480
  have hH₂_asymp := H₂_div_exp_tendsto
  have hH₂_zero := H₂_tendsto_atImInfty
  have hH₄_one := H₄_tendsto_atImInfty
  -- Simplify the exponent: 2π * I * (3/2) * z = 3 * π * I * z
  have h_exp_eq : ∀ z : ℍ, cexp (2 * π * I * (3 / 2) * z) = cexp (3 * π * I * z) := by
    intro z; congr 1; ring
  simp_rw [h_exp_eq]
  -- G / exp(3πiz) = (H₂ / exp(πiz))³ * (2H₂² + 5H₂H₄ + 5H₄²)
  have h_eq : ∀ z : ℍ, G z / cexp (3 * π * I * z) =
      (H₂ z / cexp (π * I * z)) ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := by
    intro z
    have hne : cexp (π * I * z) ≠ 0 := Complex.exp_ne_zero _
    have hne3 : cexp (3 * π * I * z) ≠ 0 := Complex.exp_ne_zero _
    have h_exp_pow : cexp (π * I * z) ^ 3 = cexp (3 * π * I * z) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    unfold G
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.ofNat_apply, div_pow, h_exp_pow]
    field_simp [hne, hne3]
  simp_rw [h_eq]
  -- The polynomial part: 2H₂² + 5H₂H₄ + 5H₄² → 0 + 0 + 5 = 5
  have h_poly : Filter.Tendsto (fun z : ℍ => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2)
      atImInfty (nhds 5) := by
    have h1 : Filter.Tendsto (fun z : ℍ => 2 * H₂ z ^ 2) atImInfty (nhds 0) := by
      simpa using (hH₂_zero.pow 2).const_mul 2
    have h2 : Filter.Tendsto (fun z : ℍ => 5 * H₂ z * H₄ z) atImInfty (nhds 0) := by
      simpa [mul_assoc] using (hH₂_zero.mul hH₄_one).const_mul 5
    have h3 : Filter.Tendsto (fun z : ℍ => 5 * H₄ z ^ 2) atImInfty (nhds 5) := by
      simpa using (hH₄_one.pow 2).const_mul 5
    simpa [add_assoc] using h1.add (h2.add h3)
  -- (H₂/exp(πiz))³ → 16³, polynomial → 5, product: 16³ * 5 = 20480
  convert (hH₂_asymp.pow 3).mul h_poly; norm_num

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
  -- Step 3: Summability of a(n) * q^n (using |a(n)| ≤ n⁵)
  have hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * ↑n * ↑z)) := by
    have hz := z.im_pos
    have hpos : 0 < 2 * π * z.im := by nlinarith [pi_pos]
    have h := Real.summable_pow_mul_exp_neg_nat_mul 5 hpos
    have hconv : Summable (fun n : ℕ+ => ((n : ℕ) : ℝ)^5 * rexp (-(2 * π * z.im) * (n : ℕ))) :=
      h.subtype _
    apply Summable.of_norm_bounded (g := fun n : ℕ+ =>
        ((n : ℕ) : ℝ)^5 * rexp (-(2 * π * z.im) * (n : ℕ))) hconv
    intro n
    have hsig : ‖(↑n * ↑(σ 3 n) : ℂ)‖ ≤ (n : ℝ)^5 := by
      have hsig' := sigma_bound 3 n
      simp only [Complex.norm_mul, Complex.norm_natCast]
      calc (n : ℝ) * ↑(σ 3 ↑n)
          ≤ (n : ℝ) * (n : ℝ)^4 := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast hsig'
            · positivity
        _ = (n : ℝ)^5 := by ring
    calc ‖a n * cexp (2 * π * I * ↑n * ↑z)‖
        = ‖(↑n * ↑(σ 3 n) : ℂ)‖ * ‖cexp (2 * π * I * ↑n * ↑z)‖ := norm_mul _ _
      _ ≤ (n : ℝ)^5 * ‖cexp (2 * π * I * ↑n * ↑z)‖ := by
          apply mul_le_mul_of_nonneg_right hsig; positivity
      _ = (n : ℝ)^5 * rexp (-(2 * π * z.im) * ↑n) := by
          congr 1; rw [Complex.norm_exp]
          congr 1
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im,
            UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, mul_zero, mul_one,
            zero_add, add_zero, sub_zero]
          ring
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
        have ha_bound : ‖a n‖ ≤ (n : ℝ)^5 := by
          have hsig' := sigma_bound 3 n
          simp only [a, Complex.norm_mul, Complex.norm_natCast]
          calc (n : ℝ) * ↑(σ 3 ↑n)
              ≤ (n : ℝ) * (n : ℝ)^4 := by
                apply mul_le_mul_of_nonneg_left
                · exact_mod_cast hsig'
                · positivity
            _ = (n : ℝ)^5 := by ring
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
              gcongr
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
  -- Step 5: Apply D_qexp_tsum_pnat
  have hD : D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * ↑n * w)) z =
      ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * ↑n * z) :=
    D_qexp_tsum_pnat a z hsum hsum_deriv
  -- Step 6: Compute D(E₂E₄ - E₆) = 720 * D(∑ a(n) * q^n) = 720 * ∑ n² * σ₃(n) * qⁿ
  -- Use hD and the definition of a to get the result
  calc D (fun w => E₂ w * E₄ w - E₆ w) z
      = D (fun w => 720 * ∑' (n : ℕ+), a n * cexp (2 * π * I * ↑n * w)) z := by
        congr 1; ext w; exact h_eq w
    _ = 720 * D (fun w => ∑' (n : ℕ+), a n * cexp (2 * π * I * ↑n * w)) z := by
        rw [D_const_mul]; sorry -- MDifferentiable for tsum
    _ = 720 * ∑' (n : ℕ+), (n : ℂ) * a n * cexp (2 * π * I * ↑n * z) := by rw [hD]
    _ = 720 * ∑' (n : ℕ+), (n : ℂ) ^ 2 * ↑(σ 3 n) * cexp (2 * π * I * ↑n * z) := by
        congr 1; apply tsum_congr; intro n; simp only [a, sq]; ring

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

/--
Log-derivative limit for G: `(D G)/G → 3/2` as `z → i∞`.
This follows from G having vanishing order 3/2: G ~ c·q^(3/2) where q = exp(2πiz).
Taking logarithmic derivative: D(log G) = (D G)/G → 3/2.
-/
-- Helper: D(exp(πiz))/exp(πiz) = 1/2
-- This follows from D = (2πi)⁻¹·d/dz and d/dz(exp(πiz)) = πi·exp(πiz)
-- So D(exp(πiz)) = (2πi)⁻¹·πi·exp(πiz) = (1/2)·exp(πiz)
theorem D_exp_pi_div_exp_pi (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w)) z / cexp (π * Complex.I * z) = 1 / 2 := by
  -- D = (2πi)⁻¹·d/dz, and d/dz(exp(πiz)) = πi·exp(πiz)
  -- So D(exp(πiz)) = (2πi)⁻¹·πi·exp(πiz) = (1/2)·exp(πiz)
  -- Therefore D(exp(πiz))/exp(πiz) = 1/2
  simp only [D]
  -- Compute deriv ((fun w : ℍ => cexp(π*I*w)) ∘ ofComplex) at (z : ℂ)
  -- Uses: d/dz(exp(πiz)) = πi·exp(πiz), and ofComplex is identity on upper half plane
  have h_deriv : deriv ((fun w : ℍ => cexp (π * Complex.I * w)) ∘ ⇑ofComplex) (z : ℂ) =
      π * Complex.I * cexp (π * Complex.I * z) := by
    -- Step 1: Compute derivative of (fun w => cexp(πIw)) using chain rule
    have h_exp_deriv : HasDerivAt (fun w : ℂ => cexp (π * Complex.I * w))
        (π * Complex.I * cexp (π * Complex.I * z)) (z : ℂ) := by
      have h_at_piIz : HasDerivAt cexp (cexp (π * Complex.I * z)) (π * Complex.I * z) :=
        Complex.hasDerivAt_exp (π * Complex.I * z)
      have h_linear : HasDerivAt (fun w : ℂ => π * Complex.I * w) (π * Complex.I) (z : ℂ) := by
        have h := (hasDerivAt_id (z : ℂ)).const_mul (π * Complex.I)
        simp only [mul_one, id] at h
        exact h
      exact h_at_piIz.scomp (z : ℂ) h_linear
    -- Step 2: Show the composed function equals the simple function in a neighborhood
    have h_agree : ((fun w : ℍ => cexp (π * Complex.I * w)) ∘ ⇑ofComplex) =ᶠ[nhds (z : ℂ)]
        (fun w : ℂ => cexp (π * Complex.I * w)) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  have h_exp_ne : cexp (π * Complex.I * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp [h_exp_ne]

-- Helper: D(jacobiTheta₂(z/2, z)) → 0 as im(z) → ∞
-- jacobiTheta₂(z/2, z) = Σ_{n∈ℤ} exp(π·I·n·(n+1)·z)
-- D(exp(2πi·k·z)) = k·exp(2πi·k·z), so
-- D(exp(π·I·n·(n+1)·z)) = (n(n+1)/2)·exp(π·I·n·(n+1)·z)
-- For n ∈ {-1, 0}: n(n+1) = 0, so coefficient = 0, contributing 0 to D(h)
-- For n ∉ {-1, 0}: term decays exponentially, and polynomial prefactor doesn't affect limit
theorem D_jacobiTheta₂_half_mul_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z)
      atImInfty (nhds 0) := by
  -- Express D as (2πi)⁻¹ * (tsum of term_fderiv applied to (1/2, 1))
  -- Key: chain rule for τ ↦ (τ/2, τ) gives direction (1/2, 1)
  have h_D_eq_tsum : ∀ z : ℍ, D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z = (2 * π * I)⁻¹ *
      ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (z / 2) z) ((1 : ℂ) / 2, 1) := by
    intro z
    simp only [D, Function.comp_def]
    congr 1
    -- Key: coe ∘ ofComplex =ᶠ id near z (since im(z) > 0)
    have h_eq : (fun x => jacobiTheta₂ (↑(ofComplex x) / 2) (↑(ofComplex x) : ℂ)) =ᶠ[nhds (z : ℂ)]
        (fun x => jacobiTheta₂ (x / 2) x) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    rw [h_eq.deriv_eq]
    -- deriv jacobiTheta₂(t/2, t) at t = z
    -- By chain rule: ∂/∂z + (1/2)·∂/∂w applied to jacobiTheta₂(w, z)
    -- = jacobiTheta₂_fderiv(z/2, z)(1/2, 1) = Σ term_fderiv(n, z/2, z)(1/2, 1)
    have h_deriv_eq : deriv (fun t => jacobiTheta₂ (t / 2) t) (z : ℂ) =
        (jacobiTheta₂_fderiv ((z : ℂ) / 2) z) ((1 : ℂ) / 2, 1) := by
      -- Chain rule: deriv(g ∘ f) = (fderiv g) (fderiv f 1)
      -- f(t) = (t/2, t), g(p) = jacobiTheta₂ p.1 p.2
      set f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
      set g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
      -- Fréchet derivative of f
      let f' : ℂ →L[ℂ] ℂ × ℂ := {
        toFun := fun h => (h / 2, h)
        map_add' := by intro x y; simp only [add_div, Prod.mk_add_mk]
        map_smul' := by
          intro c x
          simp only [RingHom.id_apply, Prod.smul_mk, smul_eq_mul, mul_div_assoc]
        cont := by continuity }
      have hf_1 : f' 1 = ((1 : ℂ) / 2, 1) := by simp only [f', ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk, AddHom.coe_mk, one_div]
      have hf : HasFDerivAt f f' (z : ℂ) := by
        have h1 : HasDerivAt (fun t : ℂ => t / 2) (1 / 2 : ℂ) (z : ℂ) :=
          (hasDerivAt_id _).div_const 2
        have h2 : HasDerivAt (fun t : ℂ => t) 1 (z : ℂ) := hasDerivAt_id _
        have hprod := h1.prodMk h2
        convert hprod.hasFDerivAt using 1
        ext : 1
        simp only [f', ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
          Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq]
        exact ⟨(one_mul _).symm, trivial⟩
      -- Fréchet derivative of g at f(z)
      have hf_val : f (z : ℂ) = ((z : ℂ) / 2, (z : ℂ)) := by simp [f]
      have hg : HasFDerivAt g (jacobiTheta₂_fderiv ((z : ℂ) / 2) z) (f (z : ℂ)) := by
        rw [hf_val]; exact hasFDerivAt_jacobiTheta₂ ((z : ℂ) / 2) z.2
      -- Compose and extract deriv
      have h_comp := hg.comp (z : ℂ) hf
      simp only [Function.comp_def, g, f] at h_comp
      rw [h_comp.hasDerivAt.deriv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hf_1]
    rw [h_deriv_eq]
    exact ((hasSum_jacobiTheta₂_term_fderiv ((z : ℂ) / 2) z.2).mapL
      (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ) / 2, 1))).tsum_eq.symm
  simp_rw [h_D_eq_tsum]
  -- Tsum → 0 via dominated convergence
  -- Key: im(z/2) = im(z)/2 > 0, and both im(z/2) and im(z) grow as im(z) → ∞
  have h_tsum_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (z / 2) z) ((1 : ℂ) / 2, 1))
      atImInfty (nhds 0) := by
    -- Apply dominated convergence with:
    -- f(z, n) = (term_fderiv n (z/2) z)((1/2, 1))
    -- g(n) = 0 (each term → 0)
    -- bound(n) = 3π|n|² exp(-π(1·n² - 1·|n|)) for im(z) ≥ 1
    -- Strategy: For im(z) ≥ 1, use norm_jacobiTheta₂_term_fderiv_le and norm_jacobiTheta₂_term_le
    -- with T = im(z), S = im(z)/2, giving bound decaying as exp(-π·im(z)·(n² - |n|))
    rw [show (0 : ℂ) = ∑' (k : ℤ), (0 : ℂ) from tsum_zero.symm]
    apply tendsto_tsum_of_dominated_convergence (α := ℍ) (𝓕 := atImInfty)
      (f := fun z n => (jacobiTheta₂_term_fderiv n ((z : ℂ) / 2) z) ((1 : ℂ) / 2, 1))
      (g := fun _ => 0)
      (bound := fun n => 3 * π * |n| ^ 2 * Real.exp (-π * (1 * n ^ 2 - 1 * |n|)))
    -- 1. Summability of bound
    · simpa [mul_assoc] using
        (summable_pow_mul_jacobiTheta₂_term_bound (1/2) one_pos 2).mul_left (3 * π)
    -- 2. Pointwise convergence: each term → 0 as im(z) → ∞
    -- Key: For n = 0 or n = -1, coefficient πin(1+n) = 0. For other n, exponential decay.
    · intro n
      -- The term is: cexp(πin(1+n)τ) * πin(1+n) applied to direction (1/2, 1)
      -- For n = 0 or n = -1: πin(1+n) = 0, so term = 0
      -- For other n: exponential decay cexp(-π·n(1+n)·im(τ)) → 0
      by_cases hn0 : n = 0
      · -- n = 0: the linear map (2πi·0)•fst + (πi·0²)•snd = 0
        -- zero_mul is needed but linter reports it unused (false positive: removing it breaks proof)
        set_option linter.unusedSimpArgs false in
        simp only [hn0, jacobiTheta₂_term_fderiv, Int.cast_zero, mul_zero, sq,
          zero_mul, zero_smul, add_zero, Complex.exp_zero, one_smul]
        -- Goal: (0 • fst + 0 • snd) (1/2, 1) = 0 for all z
        -- Goal: (0 • fst + 0 • snd) (1/2, 1) = 0 for all z
        have h_eq : (fun _ : ℍ => ((0 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ +
            (0 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) ((1 : ℂ) / 2, 1)) = fun _ => 0 := by
          ext x
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
            smul_eq_mul, mul_one]
          ring
        rw [h_eq]
        exact tendsto_const_nhds
      by_cases hn1 : n = -1
      · -- n = -1: applied to (1/2, 1), (-2πi)·(1/2) + (πi)·1 = -πi + πi = 0
        simp only [hn1, jacobiTheta₂_term_fderiv]
        -- Simplify: (2πi(-1))•fst + (πi·1)•snd, applied to (1/2, 1)
        simp only [Int.cast_neg, Int.cast_one, sq, neg_mul, neg_neg,
          mul_neg, mul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
        -- Goal: exp(...) * (-(2πi) * (1/2) + πi)
        -- = exp(...) * (-πi + πi) = exp(...) * 0 = 0
        have h_sum : -(2 * ↑π * I * ((1 : ℂ) / 2)) + ↑π * I = 0 := by ring
        simp only [h_sum, mul_zero]
        exact tendsto_const_nhds
      · -- n ≠ 0 and n ≠ -1: exponential decay
        -- n(1+n) > 0 for n ≥ 1 or n ≤ -2, giving exponential decay
        have hnn : n * (1 + n) > 0 := by
          rcases Int.lt_or_gt_of_ne hn0 with hn_neg | hn_pos
          · have h1n : 1 + n < 0 := by omega
            exact Int.mul_pos_of_neg_of_neg hn_neg h1n
          · have h1n : 1 + n > 0 := by omega
            exact Int.mul_pos hn_pos h1n
        simp only [jacobiTheta₂_term_fderiv, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', smul_eq_mul]
        have h_exp_eq : ∀ x : ℍ, 2 * ↑π * I * ↑n * (↑x / 2) + ↑π * I * ↑n ^ 2 * ↑x =
            ↑π * I * ↑n * (1 + n) * ↑x := by intro x; ring
        have h_coeff_eq : 2 * ↑π * I * ↑n * (1 / 2) + ↑π * I * ↑n ^ 2 * 1 =
            ↑π * I * ↑n * (1 + n) := by ring
        simp_rw [h_exp_eq, h_coeff_eq]
        have h_exp_tendsto : Filter.Tendsto (fun x : ℍ => cexp (↑π * I * ↑n * (1 + ↑n) * ↑x))
            atImInfty (nhds 0) := by
          rw [Complex.tendsto_exp_nhds_zero_iff]
          have h_re_eq : ∀ x : ℍ, (↑π * I * ↑n * (1 + ↑n) * ↑x).re =
              -π * (↑n * (1 + ↑n)) * x.im := by
            intro x
            simp only [mul_re, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im,
              intCast_re, intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
              add_re, add_im, one_re, one_im, mul_im]
            ring
          simp_rw [h_re_eq]
          have h_const_neg : -π * (↑n * (1 + ↑n)) < (0 : ℝ) := by
            have hnn' : (0 : ℝ) < ↑n * (1 + ↑n) := by exact_mod_cast hnn
            nlinarith [Real.pi_pos]
          rw [Filter.tendsto_const_mul_atBot_of_neg h_const_neg]
          exact Filter.tendsto_im_atImInfty
        convert h_exp_tendsto.mul tendsto_const_nhds using 1
        simp
    -- 3. Bound condition: ‖f(z,n)‖ ≤ bound(n) eventually (for im(z) ≥ 1)
    · apply Filter.eventually_atImInfty.mpr
      use 1
      intro z hz k
      have h_opnorm := ContinuousLinearMap.le_opNorm
        (jacobiTheta₂_term_fderiv k (↑z / 2) ↑z) ((1 : ℂ) / 2, 1)
      have h_v_norm : ‖((1 : ℂ) / 2, (1 : ℂ))‖ = 1 := by
        simp only [Prod.norm_def]
        norm_num
      rw [h_v_norm, mul_one] at h_opnorm
      have h_fderiv_bound := norm_jacobiTheta₂_term_fderiv_le k (↑z / 2) ↑z
      have h_imz_pos : (0 : ℝ) < z.im := z.im_pos
      have h_imz_div2 : |(↑z / 2 : ℂ).im| ≤ z.im / 2 := by
        have h1 : (↑z / 2 : ℂ).im = z.im / 2 := by
          have h2 : (2 : ℂ) = (2 : ℝ) := by norm_cast
          rw [h2]
          simp only [Complex.div_ofReal_im, UpperHalfPlane.coe_im]
        rw [h1, abs_of_pos (by linarith : z.im / 2 > 0)]
      have h_term_bound := norm_jacobiTheta₂_term_le h_imz_pos h_imz_div2 (le_refl z.im) k
      calc ‖(jacobiTheta₂_term_fderiv k (↑z / 2) ↑z) (1 / 2, 1)‖
          ≤ ‖jacobiTheta₂_term_fderiv k (↑z / 2) ↑z‖ := h_opnorm
        _ ≤ 3 * π * ↑|k| ^ 2 * ‖jacobiTheta₂_term k (↑z / 2) ↑z‖ := h_fderiv_bound
        _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * (z.im * ↑k ^ 2 - 2 * (z.im / 2) * ↑|k|)) := by
            apply mul_le_mul_of_nonneg_left h_term_bound
            positivity
        _ = 3 * π * ↑|k| ^ 2 * rexp (-π * z.im * (↑k ^ 2 - ↑|k|)) := by ring_nf
        _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * 1 * (↑k ^ 2 - ↑|k|)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp_of_le
            have hk_sq : (k : ℝ) ^ 2 = (↑|k| : ℝ) ^ 2 := by
              rw [Int.cast_abs, sq_abs]
            have hk_ge : (↑|k| : ℝ) ^ 2 - ↑|k| ≥ 0 := by
              by_cases hk0 : k = 0
              · simp [hk0]
              · have h : (↑|k| : ℝ) ^ 2 - ↑|k| = ↑|k| * (↑|k| - 1) := by ring
                rw [h]
                apply mul_nonneg (by positivity : (0 : ℝ) ≤ ↑|k|)
                have : |k| ≥ 1 := Int.one_le_abs hk0
                have hcast : (1 : ℝ) ≤ ↑|k| := by exact_mod_cast this
                linarith
            rw [hk_sq]
            have h1 : -π * z.im * ((↑|k| : ℝ) ^ 2 - ↑|k|) ≤ -π * 1 * ((↑|k|) ^ 2 - ↑|k|) := by
              by_cases hzero : (↑|k| : ℝ) ^ 2 - ↑|k| = 0
              · simp only [hzero, mul_zero, le_refl]
              · have hpos : (↑|k| : ℝ) ^ 2 - ↑|k| > 0 := lt_of_le_of_ne hk_ge (Ne.symm hzero)
                have hz1 : z.im ≥ 1 := hz
                have hpi_pos : π > 0 := Real.pi_pos
                have : -π * z.im ≤ -π * 1 := by nlinarith
                exact mul_le_mul_of_nonneg_right this (le_of_lt hpos)
            convert h1 using 2
        _ = 3 * π * ↑|k| ^ 2 * rexp (-π * (1 * ↑k ^ 2 - 1 * ↑|k|)) := by ring_nf
  have h_mul := tendsto_const_nhds (x := (2 * π * I)⁻¹).mul h_tsum_tendsto
  simp only [mul_zero] at h_mul
  exact h_mul

-- Helper: D(exp(πiz/4))/exp(πiz/4) = 1/8
-- This follows from D = (2πi)⁻¹·d/dz and d/dz(exp(πiz/4)) = (πi/4)·exp(πiz/4)
-- So D(exp(πiz/4)) = (2πi)⁻¹·(πi/4)·exp(πiz/4) = (1/8)·exp(πiz/4)
theorem D_exp_pi_quarter_div_exp_pi_quarter (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w / 4)) z / cexp (π * Complex.I * z / 4) = 1 / 8 := by
  simp only [D]
  have h_deriv : deriv ((fun w : ℍ => cexp (π * Complex.I * w / 4)) ∘ ⇑ofComplex) (z : ℂ) =
      (π * Complex.I / 4) * cexp (π * Complex.I * z / 4) := by
    have h_exp_deriv : HasDerivAt (fun w : ℂ => cexp (π * Complex.I * w / 4))
        ((π * Complex.I / 4) * cexp (π * Complex.I * z / 4)) (z : ℂ) := by
      have h_at_arg : HasDerivAt cexp (cexp (π * Complex.I * z / 4)) (π * Complex.I * z / 4) :=
        Complex.hasDerivAt_exp (π * Complex.I * z / 4)
      have h_linear : HasDerivAt (fun w : ℂ => π * Complex.I * w / 4)
          (π * Complex.I / 4) (z : ℂ) := by
        have h := (hasDerivAt_id (z : ℂ)).const_mul (π * Complex.I / 4)
        simp only [mul_one, id] at h
        convert h using 1; ring_nf
      exact h_at_arg.scomp (z : ℂ) h_linear
    have h_agree : ((fun w : ℍ => cexp (π * Complex.I * w / 4)) ∘ ⇑ofComplex) =ᶠ[nhds (z : ℂ)]
        (fun w : ℂ => cexp (π * Complex.I * w / 4)) := by
      have him : 0 < (z : ℂ).im := z.2
      have h_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [h_open.mem_nhds him] with w hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk_subtype]
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  have h_exp_ne : cexp (π * Complex.I * z / 4) ≠ 0 := Complex.exp_ne_zero _
  field_simp [h_exp_ne]
  ring

-- Helper: D(Θ₂)/Θ₂ → 1/8 (since Θ₂ has vanishing order 1/8 in q = exp(2πiz))
-- This follows from Θ₂/exp(πiz/4) → 2 and D(exp(πiz/4))/exp(πiz/4) = 1/8.
-- The vanishing order is preserved under taking logarithmic derivatives.
theorem D_Θ₂_div_Θ₂_tendsto :
    Filter.Tendsto (fun z : ℍ => D Θ₂ z / Θ₂ z) atImInfty (nhds ((1 : ℂ) / 8)) := by
  -- Strategy: Θ₂ = exp(πiz/4) · h where h = jacobiTheta₂(z/2, z)
  -- D(Θ₂)/Θ₂ = D(exp(πiz/4))/exp(πiz/4) + D(h)/h = 1/8 + D(h)/h
  -- h → 2 and D(h) → 0, so D(h)/h → 0, hence D(Θ₂)/Θ₂ → 1/8

  -- Step 1: Express Θ₂ as product
  let f : ℍ → ℂ := fun w => cexp (π * Complex.I * w / 4)
  let h : ℍ → ℂ := fun w => Θ₂ w / f w  -- = jacobiTheta₂(z/2, z)

  -- Step 2: D(f)/f = 1/8 (constant)
  have hf_logderiv : ∀ z : ℍ, D f z / f z = 1 / 8 := D_exp_pi_quarter_div_exp_pi_quarter
  -- Step 3: h → 2 as im(z) → ∞
  have hh_tendsto : Filter.Tendsto h atImInfty (nhds (2 : ℂ)) := by
    -- h = Θ₂ / exp(πiz/4) → 2
    exact Θ₂_div_exp_tendsto
  -- Step 4: D(h) → 0 as im(z) → ∞ (since h approaches a constant)
  -- h = Θ₂/f = jacobiTheta₂(z/2, z), so this follows from D_jacobiTheta₂_half_mul_tendsto_zero
  have hDh_tendsto : Filter.Tendsto (fun z => D h z) atImInfty (nhds (0 : ℂ)) := by
    -- h = Θ₂/f = exp(πiz/4)·jacobiTheta₂(z/2,z) / exp(πiz/4) = jacobiTheta₂(z/2,z)
    have h_eq_jac : h = fun w : ℍ => jacobiTheta₂ (w / 2) w := by
      ext w
      simp only [h, f, Θ₂_as_jacobiTheta₂]
      field_simp [Complex.exp_ne_zero]
    have hD_eq : (fun z => D h z) = fun z => D (fun w : ℍ => jacobiTheta₂ (w / 2) w) z := by
      ext z; rw [h_eq_jac]
    rw [hD_eq]
    exact D_jacobiTheta₂_half_mul_tendsto_zero
  -- Step 5: D(h)/h → 0 since D(h) → 0 and h → 2 ≠ 0
  have hDh_div_h_tendsto : Filter.Tendsto (fun z => D h z / h z) atImInfty (nhds (0 : ℂ)) := by
    have h_ne_zero : ∀ᶠ z : ℍ in atImInfty, h z ≠ 0 := by
      -- h → 2, and 2 ≠ 0, so eventually h ≠ 0
      have h_ball : Metric.ball (2 : ℂ) 1 ∈ nhds (2 : ℂ) :=
        Metric.isOpen_ball.mem_nhds (by norm_num : dist (2 : ℂ) 2 < 1)
      have := hh_tendsto.eventually h_ball
      filter_upwards [this] with z hz
      -- hz : dist (h z) 2 < 1
      intro h_eq
      rw [h_eq] at hz
      have : dist (0 : ℂ) 2 = 2 := by simp [dist_eq_norm]
      linarith [this]
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have h_div_tendsto := hDh_tendsto.div hh_tendsto h2
    simp only [zero_div] at h_div_tendsto
    exact h_div_tendsto.congr' (by filter_upwards [h_ne_zero] with z hz; rfl)
  -- Step 6: D(Θ₂)/Θ₂ = D(f·h)/(f·h) = D(f)/f + D(h)/h
  have h_logderiv_eq : ∀ᶠ z : ℍ in atImInfty, D Θ₂ z / Θ₂ z = D f z / f z + D h z / h z := by
    have hf_ne : ∀ z : ℍ, f z ≠ 0 := fun z => Complex.exp_ne_zero _
    have hh_ne : ∀ᶠ z : ℍ in atImInfty, h z ≠ 0 := by
      have h_ball : Metric.ball (2 : ℂ) 1 ∈ nhds (2 : ℂ) :=
        Metric.isOpen_ball.mem_nhds (by norm_num : dist (2 : ℂ) 2 < 1)
      have := hh_tendsto.eventually h_ball
      filter_upwards [this] with z hz
      intro h_eq; rw [h_eq] at hz
      have : dist (0 : ℂ) 2 = 2 := by simp [dist_eq_norm]
      linarith [this]
    filter_upwards [hh_ne] with z hz
    -- Θ₂ = f · h, so D(Θ₂) = D(f·h) = f·D(h) + h·D(f)
    have h_Θ₂_eq : Θ₂ z = f z * h z := by simp only [h, mul_div_cancel₀ _ (hf_ne z)]
    -- Show Θ₂ = f * h as functions
    have h_Θ₂_fn : Θ₂ = f * h := by
      ext w; simp only [h, Pi.mul_apply, mul_div_cancel₀ _ (hf_ne w)]
    -- MDifferentiable for f and h
    have hf_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
      intro τ
      have h_diff : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) (τ : ℂ) :=
        ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp
      simpa [f, Function.comp] using
        (DifferentiableAt_MDifferentiableAt
          (G := fun t : ℂ => cexp (π * I * t / 4)) (z := τ) h_diff)
    have hh_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
      -- h = Θ₂ / f, both holomorphic, f ≠ 0
      intro τ
      suffices h_diff : DifferentiableAt ℂ (h ∘ ofComplex) τ.val by
        have h_eq : (h ∘ ofComplex) ∘ UpperHalfPlane.coe = h := by
          ext x; simp [Function.comp, ofComplex_apply, h]
        rw [← h_eq]
        exact
          DifferentiableAt_MDifferentiableAt (G := h ∘ ofComplex) (z := τ) h_diff
      -- h ∘ ofComplex = (Θ₂ ∘ ofComplex) / (f ∘ ofComplex)
      have hΘ₂_diff : DifferentiableAt ℂ (Θ₂ ∘ ofComplex) τ.val := by
        -- Use the same proof pattern as in hΘ₂_holo below
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        let F : ℂ → ℂ := fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t
        have hF : DifferentiableAt ℂ F τ.val := by
          have h_exp : DifferentiableAt ℂ (fun t : ℂ => cexp ((π * I / 4) * t)) τ.val :=
            (differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp
          have h_theta : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ.val := by
            let f' : ℂ → ℂ × ℂ := fun t : ℂ => (t / 2, t)
            let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
            have hg : DifferentiableAt ℂ g (f' τ.val) :=
              (hasFDerivAt_jacobiTheta₂ (τ.1 / 2) τ.2).differentiableAt
            have hf' : DifferentiableAt ℂ f' τ.val :=
              (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
            exact hg.comp τ.val hf'
          exact h_exp.mul h_theta
        have h_ev : F =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) := by
          refine Filter.eventually_of_mem hU ?_
          intro z hz
          simp only [Function.comp_apply, F]
          have h_arg : cexp ((π * I / 4) * z) = cexp (π * I * z / 4) := by ring_nf
          rw [h_arg, ofComplex_apply_of_im_pos hz, Θ₂_as_jacobiTheta₂]
          simp only [coe_mk_subtype]
        exact hF.congr_of_eventuallyEq h_ev.symm
      have hf_diff : DifferentiableAt ℂ (f ∘ ofComplex) τ.val := by
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        have h_exp_diff : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) τ.val :=
          ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp
        have h_ev : (fun t : ℂ => cexp (π * I * t / 4)) =ᶠ[nhds τ.val] (f ∘ ofComplex) := by
          refine Filter.eventually_of_mem hU ?_
          intro z hz
          simp only [Function.comp_apply, f, ofComplex_apply_of_im_pos hz, coe_mk_subtype]
        exact h_exp_diff.congr_of_eventuallyEq h_ev.symm
      have hf_ne' : (f ∘ ofComplex) τ.val ≠ 0 := by
        simp only [Function.comp_apply, f]
        exact Complex.exp_ne_zero _
      have h_eq' : (h ∘ ofComplex) =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) / (f ∘ ofComplex) := by
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        filter_upwards [hU] with w hw
        simp only [Function.comp_apply, h, Pi.div_apply, ofComplex_apply_of_im_pos hw]
      exact (hΘ₂_diff.div hf_diff hf_ne').congr_of_eventuallyEq h_eq'.symm
    -- Apply product rule: D(f * h) = D f * h + f * D h
    have h_D_prod := D_mul f h hf_md hh_md
    -- Rewrite D Θ₂ using h_Θ₂_fn
    have h_D_Θ₂ : D Θ₂ = D (f * h) := by rw [h_Θ₂_fn]
    calc D Θ₂ z / Θ₂ z
        = D (f * h) z / (f z * h z) := by rw [h_D_Θ₂, h_Θ₂_eq]
      _ = (D f z * h z + f z * D h z) / (f z * h z) := by
          rw [congrFun h_D_prod z]; simp only [Pi.mul_apply, Pi.add_apply]
      _ = D f z / f z + D h z / h z := by field_simp [hf_ne z, hz]
  -- Step 7: Take the limit
  have h_sum_limit : Filter.Tendsto (fun z => D f z / f z + D h z / h z) atImInfty
      (nhds ((1 : ℂ) / 8 + 0)) := by
    have hf_const : Filter.Tendsto (fun z => D f z / f z) atImInfty (nhds ((1 : ℂ) / 8)) := by
      simp_rw [hf_logderiv]
      exact tendsto_const_nhds
    exact hf_const.add hDh_div_h_tendsto
  have h_sum_limit' : Filter.Tendsto (fun z => D f z / f z + D h z / h z) atImInfty
      (nhds ((1 : ℂ) / 8)) := by
    convert h_sum_limit using 2; ring
  refine h_sum_limit'.congr' ?_
  filter_upwards [h_logderiv_eq] with z hz
  exact hz.symm

-- Helper: D(H₂)/H₂ → 1/2 (since H₂ ~ 16·exp(πiz) has vanishing order 1/2)
theorem D_H₂_div_H₂_tendsto :
    Filter.Tendsto (fun z : ℍ => D H₂ z / H₂ z) atImInfty (nhds ((1 : ℂ) / 2)) := by
  -- H₂ = Θ₂⁴, and Θ₂/exp(πiz/4) → 2
  -- D(H₂) = 4·Θ₂³·D(Θ₂), so D(H₂)/H₂ = 4·D(Θ₂)/Θ₂
  -- D(Θ₂)/Θ₂ → 1/8
  -- Therefore D(H₂)/H₂ → 4·(1/8) = 1/2
  -- Step 1: H₂ = Θ₂⁴
  have hH₂_eq : ∀ z : ℍ, H₂ z = (Θ₂ z) ^ 4 := fun z => rfl
  -- Step 2: D(H₂)/H₂ = 4·D(Θ₂)/Θ₂ when Θ₂ ≠ 0
  have h_logderiv : ∀ z : ℍ, Θ₂ z ≠ 0 → D H₂ z / H₂ z = 4 * (D Θ₂ z / Θ₂ z) := by
    intro z hΘ₂
    rw [hH₂_eq]
    -- D(Θ₂⁴) = 4·Θ₂³·D(Θ₂) using power rule
    have h_pow4 : D (fun w => (Θ₂ w) ^ 4) z = 4 * (Θ₂ z) ^ 3 * D Θ₂ z := by
      -- Θ₂⁴ = (Θ₂²)², use D_sq twice
      have hΘ₂_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Θ₂ := by
        -- Θ₂ = exp(πiz/4) · jacobiTheta₂(z/2, z), product of holomorphic functions
        intro τ
        suffices h_diff : DifferentiableAt ℂ (Θ₂ ∘ ofComplex) τ.val by
          have h_eq : (Θ₂ ∘ ofComplex) ∘ UpperHalfPlane.coe = Θ₂ := by
            ext x; simp [Function.comp, ofComplex_apply]
          rw [← h_eq]
          exact
            DifferentiableAt_MDifferentiableAt (G := Θ₂ ∘ ofComplex) (z := τ) h_diff
        have hU : {z : ℂ | 0 < z.im} ∈ nhds τ.val := isOpen_upperHalfPlaneSet.mem_nhds τ.2
        -- Define the function on ℂ
        let F : ℂ → ℂ := fun t => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t
        have hF : DifferentiableAt ℂ F τ.val := by
          have h_exp : DifferentiableAt ℂ (fun t : ℂ => cexp ((π * I / 4) * t)) τ.val := by
            exact (differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp
          have h_theta : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ.val := by
            let f : ℂ → ℂ × ℂ := fun t : ℂ => (t / 2, t)
            let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
            have hg : DifferentiableAt ℂ g (f τ.val) := by
              simpa [f] using (hasFDerivAt_jacobiTheta₂ (τ.1 / 2) τ.2).differentiableAt
            have hf : DifferentiableAt ℂ f τ.val :=
              (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
            simpa [f, g] using (DifferentiableAt.fun_comp' τ.1 hg hf)
          exact h_exp.mul h_theta
        have h_ev : F =ᶠ[nhds τ.val] (Θ₂ ∘ ofComplex) := by
          refine Filter.eventually_of_mem hU ?_
          intro z hz
          simp only [Function.comp_apply, F]
          have h_arg : cexp ((π * I / 4) * z) = cexp (π * I * z / 4) := by
            congr 1; ring
          rw [h_arg, ofComplex_apply_of_im_pos hz, Θ₂_as_jacobiTheta₂]
          simp only [coe_mk_subtype]
        exact DifferentiableAt.congr_of_eventuallyEq hF h_ev.symm
      -- Use D_sq twice: D(Θ₂⁴) = D((Θ₂²)²) = 2·Θ₂²·D(Θ₂²)
      --   = 2·Θ₂²·(2·Θ₂·D(Θ₂)) = 4·Θ₂³·D(Θ₂)
      have hΘ₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Θ₂ ^ 2) := by
        rw [pow_two]; exact MDifferentiable.mul hΘ₂_holo hΘ₂_holo
      have h_pow4_eq : (fun w => (Θ₂ w) ^ 4) = (Θ₂ ^ 2) ^ 2 := by
        ext w; simp only [Pi.pow_apply]; ring
      have h_D_pow4_fn : D ((Θ₂ ^ 2) ^ 2) = 2 * (Θ₂ ^ 2) * D (Θ₂ ^ 2) := D_sq (Θ₂ ^ 2) hΘ₂sq
      have h_D_sq_fn : D (Θ₂ ^ 2) = 2 * Θ₂ * D Θ₂ := D_sq Θ₂ hΘ₂_holo
      calc D (fun w => (Θ₂ w) ^ 4) z
          = D ((Θ₂ ^ 2) ^ 2) z := by rw [h_pow4_eq]
        _ = D (Θ₂ ^ 2) z * (Θ₂ ^ 2) z + (Θ₂ ^ 2) z * D (Θ₂ ^ 2) z := by
            rw [pow_two ((Θ₂ ^ 2) : ℍ → ℂ), congrFun (D_mul (Θ₂ ^ 2) (Θ₂ ^ 2) hΘ₂sq hΘ₂sq) z]
            simp only [Pi.add_apply, Pi.mul_apply]
        _ = 2 * (Θ₂ z) ^ 2 * D (Θ₂ ^ 2) z := by simp only [Pi.pow_apply]; ring
        _ = 2 * (Θ₂ z) ^ 2 * (2 * Θ₂ z * D Θ₂ z) := by
            rw [h_D_sq_fn]; simp only [Pi.mul_apply, Pi.ofNat_apply]
        _ = 4 * (Θ₂ z) ^ 3 * D Θ₂ z := by ring
    -- Now compute the quotient
    -- First show D H₂ = D (fun w => Θ₂ w ^ 4) since H₂ = Θ₂^4
    have h_H₂_eq_fn : H₂ = fun w => (Θ₂ w) ^ 4 := by ext w; rfl
    rw [h_H₂_eq_fn, h_pow4]
    have h_pow4_ne : (Θ₂ z) ^ 4 ≠ 0 := pow_ne_zero 4 hΘ₂
    field_simp [hΘ₂, h_pow4_ne]
  -- Step 3: Θ₂ ≠ 0 eventually (since Θ₂/exp(πiz/4) → 2 ≠ 0)
  have hΘ₂_ne := eventually_ne_zero_of_tendsto_div (by norm_num : (2 : ℂ) ≠ 0) Θ₂_div_exp_tendsto
  -- Step 4: Convert limit: 4 * (1/8) = 1/2
  have h_eq : (4 : ℂ) * (1 / 8) = 1 / 2 := by norm_num
  rw [← h_eq]
  apply (D_Θ₂_div_Θ₂_tendsto.const_mul (4 : ℂ)).congr'
  filter_upwards [hΘ₂_ne] with z hz
  exact (h_logderiv z hz).symm

-- Helper: D(H₂) → 0 (since D(H₂) = 4·Θ₂³·D(Θ₂) and Θ₂ → 0)
-- More precisely: D(H₂) = 4·H₂·(D(Θ₂)/Θ₂) = 4·H₂·(1/8 + o(1)) → 0 since H₂ → 0
theorem D_H₂_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D H₂ z) atImInfty (nhds 0) := by
  -- Strategy: D(H₂) = (D(H₂)/H₂) · H₂, then multiply limits
  -- H₂ ≠ 0 eventually since H₂/exp → 16 ≠ 0
  have hH₂_ne : ∀ᶠ z : ℍ in atImInfty, H₂ z ≠ 0 := by
    have hdiv_ne := H₂_div_exp_tendsto.eventually_ne (by norm_num : (16 : ℂ) ≠ 0)
    filter_upwards [hdiv_ne] with z hz
    intro hzero
    exact hz (by simp [hzero])
  -- D(H₂) = (D(H₂)/H₂) · H₂ eventually
  have h_eq : (fun z => D H₂ z) =ᶠ[atImInfty] fun z => (D H₂ z / H₂ z) * H₂ z := by
    filter_upwards [hH₂_ne] with z hz
    exact (div_mul_cancel₀ (D H₂ z) hz).symm
  -- Limits: D(H₂)/H₂ → 1/2, H₂ → 0, so product → (1/2) * 0 = 0
  have hlim := D_H₂_div_H₂_tendsto.mul H₂_tendsto_atImInfty
  simp only [mul_zero] at hlim
  exact hlim.congr' h_eq.symm

-- Helper: Summability of n² · exp(-πn²) (Gaussian decay dominates polynomial)
-- This is a special case of summable_pow_mul_jacobiTheta₂_term_bound with S = 0, T = 1, k = 2
lemma summable_sq_mul_exp_neg_pi_sq :
    Summable fun n : ℤ ↦ (n : ℝ) ^ 2 * rexp (-π * n ^ 2) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 (by norm_num : (0 : ℝ) < 1) 2
  simp only [mul_zero, one_mul] at h
  convert h using 1
  ext n
  -- Show: (n : ℝ)² * exp(-πn²) = |n|² * exp(-π(n² - 0·|n|))
  congr 1
  · -- (n : ℝ)² = (|n| : ℤ→ℝ)² since x² = |x|² and ↑|n| = |↑n|
    rw [← sq_abs, Int.cast_abs]
  · -- -π * n² = -π * (n² - 0 * |n|)
    ring_nf

-- Helper: D(Θ₄) → 0 (since Θ₄ → 1 and the q-expansion has exponentially decaying terms)
-- Θ₄ = jacobiTheta₂(1/2, z) = Σ (-1)^n · q^(n²), where n=0 gives constant 1
-- D of constant is 0, D of other terms decay exponentially
--
-- Proof strategy (dominated convergence):
-- 1. D(Θ₄) = (2πi)⁻¹ · d/dτ[jacobiTheta₂(1/2, τ)]
-- 2. d/dτ = (jacobiTheta₂_fderiv (1/2) τ) (0, 1) = Σₙ (term_fderiv n (1/2) τ) (0, 1)
-- 3. Each term → 0 as im(τ) → ∞ (by norm_jacobiTheta₂_term_fderiv_le and exp decay)
-- 4. Summable bound from summable_pow_mul_jacobiTheta₂_term_bound
theorem D_Θ₄_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D Θ₄ z) atImInfty (nhds 0) := by
  -- Express D(Θ₄) as (2πi)⁻¹ * (tsum of term_fderiv applied to (0,1))
  have h_D_eq_tsum : ∀ z : ℍ, D Θ₄ z = (2 * π * I)⁻¹ *
      ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (1/2) z) (0, 1) := by
    intro z
    simp only [D, Θ₄_as_jacobiTheta₂, Function.comp_def]
    congr 1
    -- Key: coe ∘ ofComplex =ᶠ id near z (since im(z) > 0)
    have h_eq : (fun x => jacobiTheta₂ (1/2) (↑(ofComplex x) : ℂ)) =ᶠ[nhds (z : ℂ)]
        (fun x => jacobiTheta₂ (1/2) x) :=
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.2).fun_comp (jacobiTheta₂ (1/2))
    rw [h_eq.deriv_eq]
    -- deriv = (fderiv)(0, 1) = Σ (term_fderiv)(0, 1)
    have hFD := hasFDerivAt_jacobiTheta₂ (1/2 : ℂ) z.2
    have h_embed : HasDerivAt (fun t : ℂ => ((1 : ℂ)/2, t)) (0, 1) (z : ℂ) :=
      (hasDerivAt_const (z : ℂ) (1/2)).prodMk (hasDerivAt_id (z : ℂ))
    have h_chain := hFD.comp_hasDerivAt (z : ℂ) h_embed
    simp only [Function.comp_def] at h_chain
    rw [h_chain.deriv]
    exact ((hasSum_jacobiTheta₂_term_fderiv (1/2 : ℂ) z.2).mapL
      (ContinuousLinearMap.apply ℂ ℂ (0, 1))).tsum_eq.symm
  simp_rw [h_D_eq_tsum]
  -- Tsum → 0 via dominated convergence with bound 6π|n|²exp(-πn²)
  -- Key lemmas: norm_jacobiTheta₂_term_fderiv_le, norm_jacobiTheta₂_term_le,
  -- summable_sq_mul_exp_neg_pi_sq, tendsto_tsum_of_dominated_convergence
  have h_tsum_tendsto : Filter.Tendsto
      (fun z : ℍ => ∑' n : ℤ, (jacobiTheta₂_term_fderiv n (1/2) z) (0, 1)) atImInfty (nhds 0) := by
    -- Use dominated convergence with bound 3π|n|² exp(-πn²)
    conv => rhs; rw [show (0 : ℂ) = ∑' (k : ℤ), (0 : ℂ) from tsum_zero.symm]
    apply tendsto_tsum_of_dominated_convergence (α := ℍ) (𝓕 := atImInfty)
      (f := fun z n => (jacobiTheta₂_term_fderiv n (1/2) z) ((0 : ℂ), 1))
      (g := fun _ => 0)
      (bound := fun n => 3 * π * |n| ^ 2 * Real.exp (-π * n ^ 2))
    -- 1. Summability of bound
    · simpa [mul_assoc] using summable_sq_mul_exp_neg_pi_sq.mul_left (3 * π)
    -- 2. Pointwise convergence: each term → 0
    · intro n
      -- The term is: exp(πin + πin²z) * (2πin * 0 + πin² * 1) = exp(πin + πin²z) * πin²
      -- For n=0: πin² = 0, so term is constant 0
      -- For n≠0: exponential decay since (πin + πin²z).re = -πn²·z.im → -∞
      by_cases hn0 : n = 0
      · -- n = 0: term is 0 for all z
        subst hn0
        -- zero_mul is needed but linter reports it unused (false positive: removing it breaks proof)
        set_option linter.unusedSimpArgs false in
        simp only [jacobiTheta₂_term_fderiv, Int.cast_zero, mul_zero, sq,
          zero_mul, zero_smul, add_zero, Complex.exp_zero, one_smul,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
        exact tendsto_const_nhds
      · -- n ≠ 0: exponential decay
        simp only [jacobiTheta₂_term_fderiv, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', smul_eq_mul]
        -- Simplify: (0, 1) applied gives just the second component coefficient πin²
        have h_simp : ∀ z : ℍ,
            cexp (2 * ↑π * I * ↑n * (1/2 : ℂ) + ↑π * I * ↑n ^ 2 * ↑z) *
            (2 * ↑π * I * ↑n * 0 + ↑π * I * ↑n ^ 2 * 1) =
            cexp (↑π * I * ↑n + ↑π * I * ↑n ^ 2 * ↑z) * (↑π * I * ↑n ^ 2) := fun z => by ring
        simp_rw [h_simp]
        -- Now show exp(πin + πin²z) * πin² → 0
        have hnsq_pos : n ^ 2 > 0 := sq_pos_of_ne_zero hn0
        have h_exp_tendsto : Filter.Tendsto
            (fun z : ℍ => cexp ((π : ℂ) * I * n + (π : ℂ) * I * (n : ℂ) ^ 2 * z))
            atImInfty (nhds 0) := by
          rw [Complex.tendsto_exp_nhds_zero_iff]
          -- (πin + πin²z).re = -πn²·z.im since (πin).re = 0 and (πin²z).re = -πn²·z.im
          have h_re_eq : ∀ z : ℍ,
              ((π : ℂ) * I * n + (π : ℂ) * I * (n : ℂ) ^ 2 * z).re = -π * (n : ℝ) ^ 2 * z.im := by
            intro z
            simp only [add_re, mul_re, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im,
              intCast_re, intCast_im, sq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, mul_im]
            ring
          simp_rw [h_re_eq]
          have h_const_neg : -π * (n : ℝ) ^ 2 < 0 := by
            have hnsq' : (0 : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hnsq_pos
            nlinarith [Real.pi_pos]
          rw [Filter.tendsto_const_mul_atBot_of_neg h_const_neg]
          exact Filter.tendsto_im_atImInfty
        convert h_exp_tendsto.mul tendsto_const_nhds using 1; simp
    -- 3. Bound condition: ‖f(z,n)‖ ≤ bound(n) eventually (for z.im ≥ 1)
    · apply Filter.eventually_atImInfty.mpr
      use 1
      intro z hz k
      -- ‖term‖ ≤ ‖term_fderiv‖ ≤ 3π|k|² ‖jacobiTheta₂_term‖ ≤ 3π|k|² exp(-πk²)
      have h_opnorm := ContinuousLinearMap.le_opNorm
        (jacobiTheta₂_term_fderiv k (1/2) ↑z) ((0 : ℂ), 1)
      have h_v_norm : ‖((0 : ℂ), (1 : ℂ))‖ = 1 := by simp [Prod.norm_def]
      rw [h_v_norm, mul_one] at h_opnorm
      have h_fderiv_bound := norm_jacobiTheta₂_term_fderiv_le k (1/2 : ℂ) ↑z
      have h_half_im : |(1/2 : ℂ).im| ≤ 0 := by simp
      have h_term_bound := norm_jacobiTheta₂_term_le z.im_pos h_half_im (le_refl z.im) k
      calc ‖(jacobiTheta₂_term_fderiv k (1/2) ↑z) (0, 1)‖
          ≤ ‖jacobiTheta₂_term_fderiv k (1/2) ↑z‖ := h_opnorm
        _ ≤ 3 * π * ↑|k| ^ 2 * ‖jacobiTheta₂_term k (1/2) ↑z‖ := h_fderiv_bound
        _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * (z.im * ↑k ^ 2 - 2 * 0 * ↑|k|)) := by
            exact mul_le_mul_of_nonneg_left h_term_bound (by positivity)
        _ = 3 * π * ↑|k| ^ 2 * rexp (-π * z.im * ↑k ^ 2) := by ring_nf
        _ ≤ 3 * π * ↑|k| ^ 2 * rexp (-π * 1 * ↑k ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp_of_le
            -- Need: -π * z.im * k² ≤ -π * 1 * k²
            -- Since z.im ≥ 1 and k² ≥ 0, we have -π * z.im * k² ≤ -π * k²
            have hk_sq_nonneg : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
            have hz1 : z.im ≥ 1 := hz
            have hpi_pos : π > 0 := Real.pi_pos
            have h1 : -π * z.im ≤ -π * 1 := by nlinarith
            calc -π * z.im * (k : ℝ) ^ 2
                = (-π * z.im) * (k : ℝ) ^ 2 := by ring
              _ ≤ (-π * 1) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h1 hk_sq_nonneg
              _ = -π * 1 * (k : ℝ) ^ 2 := by ring
        _ = 3 * π * ↑|k| ^ 2 * rexp (-π * ↑k ^ 2) := by ring_nf
  have h_mul := tendsto_const_nhds (x := (2 * π * I)⁻¹).mul h_tsum_tendsto
  simp only [mul_zero] at h_mul
  exact h_mul

-- Helper: D(H₄) → 0 (since D(Θ₄) → 0 and Θ₄ → 1)
theorem D_H₄_tendsto_zero :
    Filter.Tendsto (fun z : ℍ => D H₄ z) atImInfty (nhds 0) := by
  -- H₄ = Θ₄⁴, so D(H₄) = 4·Θ₄³·D(Θ₄)
  -- Θ₄ → 1 and D(Θ₄) → 0, so D(H₄) → 4·1³·0 = 0

  -- Step 1: MDifferentiable for Θ₄
  have hΘ₄_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Θ₄ := by
    intro τ
    have hθ : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) (τ : ℂ) :=
      differentiableAt_jacobiTheta₂_snd (1 / 2 : ℂ) τ.2
    have hMD : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        ((fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) ∘ UpperHalfPlane.coe) τ :=
      DifferentiableAt_MDifferentiableAt (G := fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) hθ
    convert hMD using 1
    ext x; simp [Θ₄_as_jacobiTheta₂, Function.comp]
  -- Step 2: D(Θ₄²) = 2·Θ₄·D(Θ₄)
  have hΘ₄sq_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Θ₄ ^ 2) := by
    rw [pow_two]; exact MDifferentiable.mul hΘ₄_holo hΘ₄_holo
  have h_D_sq : D (Θ₄ ^ 2) = 2 * Θ₄ * D Θ₄ := D_sq Θ₄ hΘ₄_holo
  -- Step 3: Prove D(H₄) z = 4 * (Θ₄ z)³ * D Θ₄ z pointwise (avoids Pi type issues)
  have h_D_H₄_pt : ∀ z, D H₄ z = (4 : ℂ) * (Θ₄ z) ^ 3 * D Θ₄ z := by
    intro z
    -- H₄ = Θ₄⁴ = (Θ₄²)²
    have hH₄_eq : H₄ = (Θ₄ ^ 2) ^ 2 := by ext w; simp only [H₄, Pi.pow_apply]; ring
    have h1 : D H₄ z = D ((Θ₄ ^ 2) ^ 2) z := by rw [hH₄_eq]
    -- D((Θ₄²)²) = 2·(Θ₄²)·D(Θ₄²) at z
    have h2 : D ((Θ₄ ^ 2) ^ 2) z = (2 : ℂ) * (Θ₄ z ^ 2) * D (Θ₄ ^ 2) z := by
      have := congrFun (D_sq (Θ₄ ^ 2) hΘ₄sq_holo) z
      simp only [Pi.mul_apply, Pi.pow_apply] at this
      exact this
    -- D(Θ₄²) = 2·Θ₄·D(Θ₄) at z
    have h3 : D (Θ₄ ^ 2) z = (2 : ℂ) * Θ₄ z * D Θ₄ z := by
      have := congrFun h_D_sq z
      simp only [Pi.mul_apply] at this
      exact this
    rw [h1, h2, h3]
    ring
  -- Step 4: Limit calculation - 4·1³·0 = 0
  simp_rw [h_D_H₄_pt]
  have h_lim := (tendsto_const_nhds (x := (4 : ℂ))).mul
    ((Θ₄_tendsto_atImInfty.pow 3).mul D_Θ₄_tendsto_zero)
  simp only [mul_zero] at h_lim
  convert h_lim using 1
  ext z; ring

theorem D_G_div_G_tendsto :
    Filter.Tendsto (fun z : ℍ => D G z / G z) atImInfty (nhds ((3 : ℂ) / 2)) := by
  -- G = H₂³ · poly where poly = 2H₂² + 5H₂H₄ + 5H₄²
  -- DG/G = D(H₂³)/H₂³ + D(poly)/poly → 3/2 + 0 = 3/2

  -- MDifferentiability lemmas
  have hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  -- Define A = H₂³ and B = 2H₂² + 5H₂H₄ + 5H₄²
  let A : ℍ → ℂ := fun z => H₂ z ^ 3
  let B : ℍ → ℂ := fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2
  -- G = A * B
  have hG_eq : ∀ z, G z = A z * B z := fun z => rfl
  -- MDifferentiability of A, B
  have hH₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by rw [pow_two]; exact hH₂.mul hH₂
  have hH₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by rw [pow_two]; exact hH₄.mul hH₄
  have hA : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) A := hH₂sq.mul hH₂
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := by
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2) := by
      have : (fun z => 2 * H₂ z ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext z; simp [smul_eq_mul]
      rw [this]; exact hH₂sq.const_smul 2
    have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
      have : (fun z => 5 * H₂ z * H₄ z) = (5 : ℂ) • (H₂ * H₄) := by
        ext z; simp [smul_eq_mul, mul_assoc]
      rw [this]; exact (hH₂.mul hH₄).const_smul 5
    have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) := by
      have : (fun z => 5 * H₄ z ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext z; simp [smul_eq_mul]
      rw [this]; exact hH₄sq.const_smul 5
    exact (h1.add h2).add h3
  -- D(A)/A = 3·D(H₂)/H₂
  have h_DA_A : ∀ z, H₂ z ≠ 0 → D A z / A z = 3 * (D H₂ z / H₂ z) := by
    intro z hH₂_ne
    have h_cube : D (fun w => H₂ w ^ 3) z = 3 * H₂ z ^ 2 * D H₂ z := by
      have := congrFun (D_cube H₂ hH₂) z
      simp only [Pi.mul_apply, Pi.pow_apply] at this
      exact this
    simp only [A]
    rw [h_cube]
    field_simp [pow_ne_zero 3 hH₂_ne, pow_ne_zero 2 hH₂_ne]
  -- D(A)/A → 3/2
  have h_DA_A_tendsto : Filter.Tendsto (fun z => D A z / A z) atImInfty (nhds ((3 : ℂ) / 2)) := by
    have h_eq : (3 : ℂ) / 2 = 3 * (1 / 2) := by norm_num
    rw [h_eq]
    have hH₂_ne : ∀ᶠ z in atImInfty, H₂ z ≠ 0 := by
      have hdiv_ne := H₂_div_exp_tendsto.eventually_ne (by norm_num : (16 : ℂ) ≠ 0)
      filter_upwards [hdiv_ne] with z hz hzero
      exact hz (by simp [hzero])
    apply (D_H₂_div_H₂_tendsto.const_mul 3).congr'
    filter_upwards [hH₂_ne] with z hz
    exact (h_DA_A z hz).symm
  -- B → 5 (since H₂ → 0, H₄ → 1)
  have h_B_tendsto : Filter.Tendsto B atImInfty (nhds 5) := by
    -- B = 2H₂² + 5H₂H₄ + 5H₄² → 2·0² + 5·0·1 + 5·1² = 5
    have h := ((H₂_tendsto_atImInfty.pow 2).const_mul 2).add
      (((H₂_tendsto_atImInfty.mul H₄_tendsto_atImInfty).const_mul 5).add
        ((H₄_tendsto_atImInfty.pow 2).const_mul 5))
    simp only [zero_pow two_ne_zero, one_pow, mul_zero, mul_one, zero_add] at h
    refine h.congr' ?_
    filter_upwards with z
    simp only [B, pow_two]; ring
  -- D(B) → 0 (expand and use D_H₂_tendsto_zero, D_H₄_tendsto_zero)
  have h_DB_tendsto : Filter.Tendsto (fun z => D B z) atImInfty (nhds 0) := by
    -- D(B) = 4H₂·D(H₂) + 5(H₂·D(H₄) + D(H₂)·H₄) + 10H₄·D(H₄)
    have h_D_B : ∀ z, D B z =
        4 * H₂ z * D H₂ z + 5 * (H₂ z * D H₄ z + D H₂ z * H₄ z) + 10 * H₄ z * D H₄ z := by
      intro z
      simp only [B]
      -- D(2H₂²) = 4H₂ · D(H₂)
      have h_term1 : D (fun w => 2 * H₂ w ^ 2) z = 4 * H₂ z * D H₂ z := by
        have h1 : (fun w => 2 * H₂ w ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext w; simp [smul_eq_mul]
        have h2 : D ((2 : ℂ) • (H₂ ^ 2)) z = 2 * D (H₂ ^ 2) z := by
          rw [D_smul 2 (H₂ ^ 2) hH₂sq]; simp
        have h3 : D (H₂ ^ 2) z = 2 * H₂ z * D H₂ z := by
          have := congrFun (D_sq H₂ hH₂) z; simp only [Pi.mul_apply] at this; exact this
        rw [h1, h2, h3]; ring
      -- D(5H₂H₄) = 5 · (H₂ · D(H₄) + D(H₂) · H₄)
      have h_term2 : D (fun w => 5 * H₂ w * H₄ w) z = 5 * (H₂ z * D H₄ z + D H₂ z * H₄ z) := by
        have h1 : (fun w => 5 * H₂ w * H₄ w) = (5 : ℂ) • (H₂ * H₄) := by
          ext w; simp [smul_eq_mul, mul_assoc]
        have h2 : D ((5 : ℂ) • (H₂ * H₄)) z = 5 * D (H₂ * H₄) z := by
          rw [D_smul 5 (H₂ * H₄) (hH₂.mul hH₄)]; simp
        have h3 : D (H₂ * H₄) z = D H₂ z * H₄ z + H₂ z * D H₄ z := by
          have := congrFun (D_mul H₂ H₄ hH₂ hH₄) z; simp only [Pi.add_apply, Pi.mul_apply] at this
          exact this
        rw [h1, h2, h3]; ring
      -- D(5H₄²) = 10H₄ · D(H₄)
      have h_term3 : D (fun w => 5 * H₄ w ^ 2) z = 10 * H₄ z * D H₄ z := by
        have h1 : (fun w => 5 * H₄ w ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext w; simp [smul_eq_mul]
        have h2 : D ((5 : ℂ) • (H₄ ^ 2)) z = 5 * D (H₄ ^ 2) z := by
          rw [D_smul 5 (H₄ ^ 2) hH₄sq]; simp
        have h3 : D (H₄ ^ 2) z = 2 * H₄ z * D H₄ z := by
          have := congrFun (D_sq H₄ hH₄) z; simp only [Pi.mul_apply] at this; exact this
        rw [h1, h2, h3]; ring
      -- Put together using D_add
      have h_add1 : D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) z =
          D (fun w => 2 * H₂ w ^ 2) z + D (fun w => 5 * H₂ w * H₄ w) z := by
        have hmd1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => 2 * H₂ w ^ 2) := by
          have : (fun w => 2 * H₂ w ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext w; simp [smul_eq_mul]
          rw [this]; exact hH₂sq.const_smul 2
        have hmd2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => 5 * H₂ w * H₄ w) := by
          have : (fun w => 5 * H₂ w * H₄ w) = (5 : ℂ) • (H₂ * H₄) := by
            ext w; simp [smul_eq_mul, mul_assoc]
          rw [this]; exact (hH₂.mul hH₄).const_smul 5
        have := congrFun (D_add (fun w => 2 * H₂ w ^ 2) (fun w => 5 * H₂ w * H₄ w) hmd1 hmd2) z
        simp only [Pi.add_apply] at this; exact this
      have h_add2 : D B z = D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) z +
          D (fun w => 5 * H₄ w ^ 2) z := by
        have hmd12 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) := by
          have hmd1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => 2 * H₂ w ^ 2) := by
            have : (fun w => 2 * H₂ w ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext w; simp [smul_eq_mul]
            rw [this]; exact hH₂sq.const_smul 2
          have hmd2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => 5 * H₂ w * H₄ w) := by
            have : (fun w => 5 * H₂ w * H₄ w) = (5 : ℂ) • (H₂ * H₄) := by
              ext w; simp [smul_eq_mul, mul_assoc]
            rw [this]; exact (hH₂.mul hH₄).const_smul 5
          exact hmd1.add hmd2
        have hmd3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w => 5 * H₄ w ^ 2) := by
          have : (fun w => 5 * H₄ w ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext w; simp [smul_eq_mul]
          rw [this]; exact hH₄sq.const_smul 5
        have h_B_fn : B = fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w + 5 * H₄ w ^ 2 := rfl
        have := congrFun (D_add (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w)
          (fun w => 5 * H₄ w ^ 2) hmd12 hmd3) z
        simp only [Pi.add_apply] at this
        rw [h_B_fn]; exact this
      rw [h_add2, h_add1, h_term1, h_term2, h_term3]
    simp_rw [h_D_B]
    -- Now compute limits: all terms → 0
    have h_t1 : Filter.Tendsto (fun z => 4 * H₂ z * D H₂ z) atImInfty (nhds 0) := by
      have := (tendsto_const_nhds (x := (4 : ℂ))).mul
        (H₂_tendsto_atImInfty.mul D_H₂_tendsto_zero)
      simp only [mul_zero] at this
      convert this using 1; ext z; ring
    have h_t2 : Filter.Tendsto (fun z => 5 * (H₂ z * D H₄ z + D H₂ z * H₄ z))
        atImInfty (nhds 0) := by
      have h_sub1 := H₂_tendsto_atImInfty.mul D_H₄_tendsto_zero
      have h_sub2 := D_H₂_tendsto_zero.mul H₄_tendsto_atImInfty
      simp only [zero_mul, mul_zero] at h_sub1 h_sub2
      have := (tendsto_const_nhds (x := (5 : ℂ))).mul (h_sub1.add h_sub2)
      simp only [add_zero, mul_zero] at this; exact this
    have h_t3 : Filter.Tendsto (fun z => 10 * H₄ z * D H₄ z) atImInfty (nhds 0) := by
      have := (tendsto_const_nhds (x := (10 : ℂ))).mul
        (H₄_tendsto_atImInfty.mul D_H₄_tendsto_zero)
      simp only [mul_zero] at this
      convert this using 1; ext z; ring
    convert (h_t1.add h_t2).add h_t3 using 1
    simp only [add_zero]
  -- D(B)/B → 0/5 = 0
  have h_DB_B_tendsto : Filter.Tendsto (fun z => D B z / B z) atImInfty (nhds 0) := by
    have h_B_ne : ∀ᶠ z in atImInfty, B z ≠ 0 :=
      h_B_tendsto.eventually_ne (by norm_num : (5 : ℂ) ≠ 0)
    have h := h_DB_tendsto.div h_B_tendsto (by norm_num : (5 : ℂ) ≠ 0)
    simp only [zero_div] at h; exact h
  -- Finally: D(G)/G = D(A)/A + D(B)/B → 3/2 + 0 = 3/2
  have h_DG_G : ∀ z, A z ≠ 0 → B z ≠ 0 → D G z / G z = D A z / A z + D B z / B z := by
    intro z hA_ne hB_ne
    have h_DG : D G z = D A z * B z + A z * D B z := by
      have h_G_fn : G = A * B := by ext w; exact hG_eq w
      have h_D := congrFun (D_mul A B hA hB) z
      simp only [Pi.add_apply, Pi.mul_apply] at h_D
      rw [h_G_fn]  -- rewrite D G z to D (A * B) z
      exact h_D
    rw [hG_eq, h_DG]
    field_simp
  have hA_ne : ∀ᶠ z in atImInfty, A z ≠ 0 := by
    have hH₂_ne := H₂_div_exp_tendsto.eventually_ne (by norm_num : (16 : ℂ) ≠ 0)
    filter_upwards [hH₂_ne] with z hz hzero
    simp only [A] at hzero
    have := eq_zero_of_pow_eq_zero hzero
    exact hz (by simp [this])
  have hB_ne : ∀ᶠ z in atImInfty, B z ≠ 0 :=
    h_B_tendsto.eventually_ne (by norm_num : (5 : ℂ) ≠ 0)
  have h_sum : (3 : ℂ) / 2 = 3 / 2 + 0 := by norm_num
  rw [h_sum]
  apply (h_DA_A_tendsto.add h_DB_B_tendsto).congr'
  filter_upwards [hA_ne, hB_ne] with z hA hB
  exact (h_DG_G z hA hB).symm

/--
If `F` is real on the imaginary axis and MDifferentiable, then `D F` is also real on
the imaginary axis.
-/
theorem D_imag_axis_real_of_imag_axis_real {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hreal : ResToImagAxis.Real F) : ResToImagAxis.Real (D F) := by
  intro t ht
  have hderiv := deriv_resToImagAxis_eq F hF ht
  have hDiff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F hF t ht
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hDiff.hasDerivAt
  have hderiv_im : (deriv F.resToImagAxis t).im = 0 := by
    have : (Complex.imCLM ∘ F.resToImagAxis) = fun _ => 0 := by
      ext s
      simp only [Function.comp_apply, Complex.imCLM_apply]
      by_cases hs : 0 < s
      · exact hreal s hs
      · simp only [Function.resToImagAxis_apply, ResToImagAxis, hs, ↓reduceDIte, zero_im]
    rw [show (deriv F.resToImagAxis t).im = Complex.imCLM (deriv F.resToImagAxis t) from rfl]
    rw [← h.deriv, this, deriv_const']
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  have h2 : (-2 * ↑π * (D F ⟨I * ↑t, by simp [ht]⟩)).im = (deriv F.resToImagAxis t).im := by
    rw [hderiv]
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  have hsimp : (-2 * ↑π * D F ⟨I * ↑t, by simp [ht]⟩).im =
      -2 * π * (D F ⟨I * ↑t, by simp [ht]⟩).im := by
    simp only [neg_mul, neg_im, mul_comm (2 : ℂ), mul_assoc]
    rw [mul_im, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    ring
  rw [hsimp, hderiv_im] at h2
  have hcoef : -2 * π ≠ 0 := by positivity
  exact mul_eq_zero.mp h2 |>.resolve_left hcoef

/--
`L₁,₀(it)` is real for all `t > 0`.
-/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by
  intro t ht
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hL₁₀ := L₁₀_eq_FD_G_sub_F_DG z
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
  rw [hL₁₀]
  have hF_real := F_imag_axis_real t ht
  have hG_real := G_imag_axis_real t ht
  have hDF_real := D_imag_axis_real_of_imag_axis_real F_holo F_imag_axis_real t ht
  have hDG_real := D_imag_axis_real_of_imag_axis_real G_holo G_imag_axis_real t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte]
    at hF_real hG_real hDF_real hDG_real
  simp only [sub_im, mul_im]
  have hz : z = ⟨I * ↑t, by simp [ht]⟩ := rfl
  rw [hz]
  simp only [hG_real, mul_zero, hDF_real, zero_mul, add_zero, hDG_real, hF_real, sub_zero]

/--
`lim_{t→∞} L₁,₀(it)/(F(it)G(it)) = 1/2`.
Blueprint: Lemma 8.11 and vanishing orders 2 and 3/2.
The difference in vanishing orders is 2 - 3/2 = 1/2.
-/
theorem L₁₀_div_FG_tendsto :
    Filter.Tendsto (fun t : ℝ => (L₁₀.resToImagAxis t).re /
      ((F.resToImagAxis t).re * (G.resToImagAxis t).re))
      Filter.atTop (nhds (1/2)) := by
  -- Step 1: Rewrite L₁₀/(FG) as DF/F - DG/G using Wronskian
  -- L₁₀ = DF·G - F·DG (from L₁₀_eq_FD_G_sub_F_DG)
  -- So L₁₀/(FG) = DF/F - DG/G (assuming F, G ≠ 0)
  have h_wronskian : ∀ z : ℍ, F z ≠ 0 → G z ≠ 0 →
      L₁₀ z / (F z * G z) = D F z / F z - D G z / G z := by
    intro z hF hG
    rw [L₁₀_eq_FD_G_sub_F_DG]
    field_simp [hF, hG]
  -- Step 2: Get the complex limit from D_F_div_F_tendsto and D_G_div_G_tendsto
  have hF_lim := D_F_div_F_tendsto
  have hG_lim := D_G_div_G_tendsto
  have h_complex_limit : Filter.Tendsto (fun z : ℍ => D F z / F z - D G z / G z)
      atImInfty (nhds ((2 : ℂ) - 3 / 2)) := hF_lim.sub hG_lim
  -- Step 3: F and G are nonzero for large imaginary part (from vanishing order limits)
  have hF_ne := eventually_ne_zero_of_tendsto_div (by norm_num : (720^2 : ℂ) ≠ 0) F_vanishing_order
  have hG_ne := eventually_ne_zero_of_tendsto_div (by norm_num : (20480 : ℂ) ≠ 0) G_vanishing_order
  -- Step 4: L₁₀/(FG) → 1/2 in ℂ
  have h_L_over_FG : Filter.Tendsto (fun z : ℍ => L₁₀ z / (F z * G z))
      atImInfty (nhds (1 / 2 : ℂ)) := by
    have h_limit_val : (2 : ℂ) - 3 / 2 = 1 / 2 := by norm_num
    rw [← h_limit_val]
    apply h_complex_limit.congr'
    filter_upwards [hF_ne, hG_ne] with z hF hG using (h_wronskian z hF hG).symm
  -- Step 5: Restrict to imaginary axis and take real parts
  -- On the imaginary axis, L₁₀, F, G are all real (L₁₀_imag_axis_real),
  -- so the quotient is real and the real part limit equals 1/2.

  -- Use the epsilon-delta characterization of Tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get the complex limit in metric form using Metric.tendsto_nhds
  rw [Metric.tendsto_nhds] at h_L_over_FG
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atImInfty.mp (h_L_over_FG ε hε)
  -- Get bounds where F, G are nonzero
  obtain ⟨A₁, hA₁⟩ := Filter.eventually_atImInfty.mp hF_ne
  obtain ⟨A₂, hA₂⟩ := Filter.eventually_atImInfty.mp hG_ne
  use max (max (max A₀ A₁) A₂) 1
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have ht_A₀ : A₀ ≤ t :=
    le_trans (le_max_left A₀ A₁) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht))
  have ht_A₁ : A₁ ≤ t :=
    le_trans (le_max_right A₀ A₁) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht))
  have ht_A₂ : A₂ ≤ t := le_trans (le_max_right _ A₂) (le_trans (le_max_left _ _) ht)
  let z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have hz_im : z.im = t := by simp [z, UpperHalfPlane.im]
  have hz_F_ne : F z ≠ 0 := hA₁ z (by rw [hz_im]; exact ht_A₁)
  have hz_G_ne : G z ≠ 0 := hA₂ z (by rw [hz_im]; exact ht_A₂)
  -- Get the complex distance bound
  have h_dist := hA₀ z (by rw [hz_im]; exact ht_A₀)
  -- Need: dist (resToImagAxis expr t) (1/2) < ε
  -- Show the real expression equals the real part of the complex expression
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht_pos, ↓reduceDIte]
  have hL_real := L₁₀_imag_axis_real t ht_pos
  have hF_real := F_imag_axis_real t ht_pos
  have hG_real := G_imag_axis_real t ht_pos
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht_pos, ↓reduceDIte]
    at hL_real hF_real hG_real
  have hz_eq : (⟨Complex.I * t, by simp [ht_pos]⟩ : ℍ) = z := rfl
  rw [hz_eq] at hL_real hF_real hG_real
  -- The complex quotient is real on the imaginary axis
  have h_FG_real : (F z * G z).im = 0 := by rw [Complex.mul_im]; simp [hF_real, hG_real]
  have h_quot_real : (L₁₀ z / (F z * G z)).im = 0 := by
    rw [Complex.div_im]
    simp [hL_real, h_FG_real]
  -- The real part equals the quotient of real parts
  have h_FG_ne : F z * G z ≠ 0 := mul_ne_zero hz_F_ne hz_G_ne
  have h_re_ne : (F z * G z).re ≠ 0 := by
    intro h_re_zero
    apply h_FG_ne
    rw [Complex.ext_iff]
    simp [h_re_zero, h_FG_real]
  have h_quot_eq : (L₁₀ z / (F z * G z)).re = (L₁₀ z).re / (F z * G z).re := by
    rw [Complex.div_re]
    simp only [hL_real, h_FG_real, mul_zero, add_zero, zero_div]
    rw [Complex.normSq_eq_norm_sq]
    have h_norm_eq : ‖F z * G z‖ = |(F z * G z).re| := by
      rw [Complex.norm_def]
      conv_lhs => rw [show Complex.normSq (F z * G z) =
        (F z * G z).re * (F z * G z).re + (F z * G z).im * (F z * G z).im from rfl]
      simp only [h_FG_real, mul_zero, add_zero]
      exact Real.sqrt_mul_self_eq_abs _
    rw [h_norm_eq, sq_abs]
    field_simp [h_re_ne]
  have h_FG_re : (F z * G z).re = (F z).re * (G z).re := by
    rw [Complex.mul_re]; simp [hF_real, hG_real]
  -- dist in ℝ equals dist in ℂ when both are real
  calc dist ((L₁₀ z).re / ((F z).re * (G z).re)) (1 / 2)
      = dist ((L₁₀ z / (F z * G z)).re) ((1 / 2 : ℂ).re) := by
          rw [h_quot_eq, h_FG_re]; norm_num
    _ = |((L₁₀ z / (F z * G z)) - 1 / 2).re| := by
          rw [Real.dist_eq, Complex.sub_re]
    _ ≤ ‖L₁₀ z / (F z * G z) - 1 / 2‖ := abs_re_le_norm _
    _ = dist (L₁₀ z / (F z * G z)) (1 / 2) := by rw [Complex.dist_eq]
    _ < ε := h_dist

theorem L₁₀_eventually_pos_imag_axis : ResToImagAxis.EventuallyPos L₁₀ := by
  refine ⟨L₁₀_imag_axis_real, ?_⟩
  -- From L₁₀_div_FG_tendsto: L₁₀/(FG) → 1/2 > 0, and F, G > 0, so L₁₀ > 0 eventually
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    (L₁₀_div_FG_tendsto.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  refine ⟨max t₀ 1, by positivity, fun t ht => ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hFG_pos := mul_pos (F_imag_axis_pos.2 t ht_pos) (G_imag_axis_pos.2 t ht_pos)
  have h := mul_pos (ht₀ t (le_trans (le_max_left _ _) ht)) hFG_pos
  rwa [div_mul_cancel₀ _ (ne_of_gt hFG_pos)] at h

end MonotoneFG

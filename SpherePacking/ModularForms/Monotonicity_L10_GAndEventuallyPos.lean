/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.ModularForms.Monotonicity_L10_SerreAndF
import SpherePacking.ModularForms.summable_lems

/-!
# G-Side Analysis and Eventually Positive L₁₀

This file contains the G-side vanishing order and log-derivative analysis, the realness of
`L₁₀` on the imaginary axis, and the proof that `L₁₀(it) > 0` for large `t`.

## Main definitions and results

* `D_G_div_G_tendsto` : `(D G)/G → 3/2` as `im(z) → ∞`.
* `L₁₀_imag_axis_real` : `L₁,₀(it)` is real for all `t > 0`.
* `L₁₀_div_FG_tendsto` : `L₁,₀(it)/(F(it)G(it)) → 1/2` as `t → ∞`.
* `L₁₀_eventually_pos_imag_axis` : `L₁,₀(it) > 0` for large `t`.
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

namespace MonotoneFG

/-- G / q^(3/2) → 20480 as im(z) → ∞. Here q^(3/2) = exp(2πi · (3/2) · z). -/
theorem G_vanishing_order :
    Filter.Tendsto (fun z : ℍ => G z / cexp (2 * π * I * (3/2) * z))
      atImInfty (nhds (20480 : ℂ)) := by
  simp only [show ∀ z : ℍ, cexp (2 * π * I * (3 / 2) * z) = cexp (3 * π * I * z) from
    fun z => by ring_nf]
  have h_exp_pow : ∀ z : ℍ, cexp (π * I * z) ^ 3 = cexp (3 * π * I * z) := fun z => by
    simp only [← Complex.exp_nat_mul]; ring_nf
  have h_eq : ∀ z : ℍ, G z / cexp (3 * π * I * z) =
      (H₂ z / cexp (π * I * z)) ^ 3 * (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) := fun z => by
    simp only [G, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.smul_apply,
      Complex.real_smul, div_pow, h_exp_pow]
    push_cast
    field_simp [Complex.exp_ne_zero]
  simp_rw [h_eq]
  have h_poly : Filter.Tendsto (fun z : ℍ => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2)
      atImInfty (nhds 5) := by
    have hpair := H₂_tendsto_atImInfty.prodMk_nhds H₄_tendsto_atImInfty
    have hcont : Continuous (fun p : ℂ × ℂ => 2 * p.1 ^ 2 + 5 * p.1 * p.2 + 5 * p.2 ^ 2) :=
      by continuity
    simpa using hcont.continuousAt.tendsto.comp hpair
  convert (H₂_div_exp_tendsto.pow 3).mul h_poly
  norm_num

/-- D(exp(c*z))/exp(c*z) = c/(2πi) for any coefficient c. -/
theorem D_cexp_div (c : ℂ) (z : ℍ) :
    D (fun w => cexp (c * w)) z / cexp (c * z) = c / (2 * π * I) := by
  simp only [D]
  have h_deriv : deriv ((fun w : ℍ => cexp (c * w)) ∘ ⇑ofComplex) (z : ℂ) =
      c * cexp (c * z) := by
    have h_exp_deriv : HasDerivAt (fun w : ℂ => cexp (c * w))
        (c * cexp (c * z)) (z : ℂ) := by
      have h_at_arg : HasDerivAt cexp (cexp (c * z)) (c * z) := Complex.hasDerivAt_exp (c * z)
      have h_linear : HasDerivAt (fun w : ℂ => c * w) c (z : ℂ) := by
        simpa using (hasDerivAt_id (z : ℂ)).const_mul c
      exact h_at_arg.scomp (z : ℂ) h_linear
    have h_agree := (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.2).fun_comp
      (fun w => cexp (c * w))
    exact h_agree.deriv_eq.trans h_exp_deriv.deriv
  rw [h_deriv]
  field_simp [Complex.exp_ne_zero]

-- Helper: D(exp(πiz))/exp(πiz) = 1/2
theorem D_exp_pi_div_exp_pi (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w)) z / cexp (π * Complex.I * z) = 1 / 2 := by
  simpa [show π * I / (2 * π * I) = (1 : ℂ) / 2 by field_simp] using D_cexp_div (π * I) z

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
    have h_eq : (fun x => jacobiTheta₂ (↑(ofComplex x) / 2) (↑(ofComplex x) : ℂ)) =ᶠ[nhds (z : ℂ)]
        (fun x => jacobiTheta₂ (x / 2) x) := by
      have h := UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.2
      filter_upwards [h] with w hw
      simp only [Function.comp_apply, id_eq] at hw
      simp only [hw]
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
        simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, hf_1]
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
        -- zero_mul is needed but linter reports it unused
        -- (false positive: removing it breaks proof)
        set_option linter.unusedSimpArgs false in
        simp only [hn0, jacobiTheta₂_term_fderiv, Int.cast_zero, mul_zero, sq,
          zero_mul, zero_smul, add_zero, Complex.exp_zero, one_smul]
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
  simpa using tendsto_const_nhds (x := (2 * π * I)⁻¹).mul h_tsum_tendsto

-- Helper: D(exp(πiz/4))/exp(πiz/4) = 1/8
theorem D_exp_pi_quarter_div_exp_pi_quarter (z : ℍ) :
    D (fun w => cexp (π * Complex.I * w / 4)) z / cexp (π * Complex.I * z / 4) = 1 / 8 := by
  simpa only [show ∀ w : ℍ, (π * I / 4 : ℂ) * w = π * I * w / 4 from fun w => by ring,
    show π * I / 4 / (2 * π * I) = (1 : ℂ) / 8 by field_simp; ring] using D_cexp_div (π * I / 4) z

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
  -- h → 2 ≠ 0 implies h ≠ 0 eventually
  have h_ne_zero : ∀ᶠ z : ℍ in atImInfty, h z ≠ 0 :=
    hh_tendsto.eventually_ne (by norm_num : (2 : ℂ) ≠ 0)
  -- Step 5: D(h)/h → 0 since D(h) → 0 and h → 2 ≠ 0
  have hDh_div_h_tendsto : Filter.Tendsto (fun z => D h z / h z) atImInfty (nhds (0 : ℂ)) := by
    have h_div_tendsto := hDh_tendsto.div hh_tendsto (by norm_num : (2 : ℂ) ≠ 0)
    simpa using h_div_tendsto.congr' (by filter_upwards [h_ne_zero] with z _; rfl)
  -- Step 6: D(Θ₂)/Θ₂ = D(f·h)/(f·h) = D(f)/f + D(h)/h
  have h_logderiv_eq : ∀ᶠ z : ℍ in atImInfty, D Θ₂ z / Θ₂ z = D f z / f z + D h z / h z := by
    have hf_ne : ∀ z : ℍ, f z ≠ 0 := fun z => Complex.exp_ne_zero _
    filter_upwards [h_ne_zero] with z hz
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
        -- zero_mul is needed but linter reports it unused
        -- (false positive: removing it breaks proof)
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
            cexp (↑π * I * ↑n + ↑π * I * ↑n ^ 2 * ↑z) * (↑π * I * ↑n ^ 2) := fun z => by ring_nf
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
  simpa using tendsto_const_nhds (x := (2 * π * I)⁻¹).mul h_tsum_tendsto

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
  -- MDifferentiability of A, B and their summands
  have hH₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₂ ^ 2) := by rw [pow_two]; exact hH₂.mul hH₂
  have hH₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (H₄ ^ 2) := by rw [pow_two]; exact hH₄.mul hH₄
  have hA : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) A := hH₂sq.mul hH₂
  have h_2H₂sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2) := by
    have : (fun z => 2 * H₂ z ^ 2) = (2 : ℂ) • (H₂ ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₂sq.const_smul 2
  have h_5H₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₂ z * H₄ z) := by
    have : (fun z => 5 * H₂ z * H₄ z) = (5 : ℂ) • (H₂ * H₄) := by
      ext z; simp [smul_eq_mul, mul_assoc]
    rw [this]; exact (hH₂.mul hH₄).const_smul 5
  have h_5H₄sq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 5 * H₄ z ^ 2) := by
    have : (fun z => 5 * H₄ z ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext z; simp [smul_eq_mul]
    rw [this]; exact hH₄sq.const_smul 5
  have h_2H₂sq_5H₂H₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z) :=
    h_2H₂sq.add h_5H₂H₄
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := (h_2H₂sq.add h_5H₂H₄).add h_5H₄sq
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
          simpa using congrFun (D_sq H₂ hH₂) z
        rw [h1, h2, h3]; ring
      -- D(5H₂H₄) = 5 · (H₂ · D(H₄) + D(H₂) · H₄)
      have h_term2 : D (fun w => 5 * H₂ w * H₄ w) z = 5 * (H₂ z * D H₄ z + D H₂ z * H₄ z) := by
        have h1 : (fun w => 5 * H₂ w * H₄ w) = (5 : ℂ) • (H₂ * H₄) := by
          ext w; simp [smul_eq_mul, mul_assoc]
        have h2 : D ((5 : ℂ) • (H₂ * H₄)) z = 5 * D (H₂ * H₄) z := by
          rw [D_smul 5 (H₂ * H₄) (hH₂.mul hH₄)]; simp
        have h3 : D (H₂ * H₄) z = D H₂ z * H₄ z + H₂ z * D H₄ z := by
          simpa using congrFun (D_mul H₂ H₄ hH₂ hH₄) z
        rw [h1, h2, h3]; ring
      -- D(5H₄²) = 10H₄ · D(H₄)
      have h_term3 : D (fun w => 5 * H₄ w ^ 2) z = 10 * H₄ z * D H₄ z := by
        have h1 : (fun w => 5 * H₄ w ^ 2) = (5 : ℂ) • (H₄ ^ 2) := by ext w; simp [smul_eq_mul]
        have h2 : D ((5 : ℂ) • (H₄ ^ 2)) z = 5 * D (H₄ ^ 2) z := by
          rw [D_smul 5 (H₄ ^ 2) hH₄sq]; simp
        have h3 : D (H₄ ^ 2) z = 2 * H₄ z * D H₄ z := by
          simpa using congrFun (D_sq H₄ hH₄) z
        rw [h1, h2, h3]; ring
      -- Put together using D_add
      have h_add1 : D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) z =
          D (fun w => 2 * H₂ w ^ 2) z + D (fun w => 5 * H₂ w * H₄ w) z := by
        simpa using congrFun (D_add _ _ h_2H₂sq h_5H₂H₄) z
      have h_add2 : D B z = D (fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w) z +
          D (fun w => 5 * H₄ w ^ 2) z := by
        have h_B_fn : B = fun w => 2 * H₂ w ^ 2 + 5 * H₂ w * H₄ w + 5 * H₄ w ^ 2 := rfl
        simpa [h_B_fn] using congrFun (D_add _ _ h_2H₂sq_5H₂H₄ h_5H₄sq) z
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
      simpa using (tendsto_const_nhds (x := (5 : ℂ))).mul (h_sub1.add h_sub2)
    have h_t3 : Filter.Tendsto (fun z => 10 * H₄ z * D H₄ z) atImInfty (nhds 0) := by
      have := (tendsto_const_nhds (x := (10 : ℂ))).mul
        (H₄_tendsto_atImInfty.mul D_H₄_tendsto_zero)
      simp only [mul_zero] at this
      convert this using 1; ext z; ring
    convert (h_t1.add h_t2).add h_t3 using 1
    simp only [add_zero]
  -- D(B)/B → 0/5 = 0
  have h_DB_B_tendsto : Filter.Tendsto (fun z => D B z / B z) atImInfty (nhds 0) := by
    simpa using h_DB_tendsto.div h_B_tendsto (by norm_num : (5 : ℂ) ≠ 0)
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
`L₁,₀(it)` is real for all `t > 0`.
-/
theorem L₁₀_imag_axis_real : ResToImagAxis.Real L₁₀ := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, L₁₀_eq_FD_G_sub_F_DG]
  have hF := F_imag_axis_real t ht
  have hG := G_imag_axis_real t ht
  have hDF := D_real_of_real F_imag_axis_real F_holo t ht
  have hDG := D_real_of_real G_imag_axis_real G_holo t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hF hG hDF hDG
  simp only [sub_im, mul_im, hF, hG, hDF, hDG, mul_zero, zero_mul, add_zero, sub_zero]

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
  have h_re_ne : (F z * G z).re ≠ 0 := by contrapose! h_FG_ne; exact Complex.ext h_FG_ne h_FG_real
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

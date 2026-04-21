module

public import SpherePacking.ModularForms.JacobiTheta.Defs

@[expose] public section

/-!
# Jacobi theta basics

Prove transformation laws, modularity, asymptotics, and the Jacobi identity for the Jacobi theta
functions defined in `Defs.lean`.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

section H_SlashInvariant

/-- Slash action of various elements on H₂, H₃, H₄ -/
lemma H₂_negI_action : (H₂ ∣[(2 : ℤ)] negI.1) = H₂ := modular_slash_negI_of_even H₂ (2: ℤ) even_two
lemma H₃_negI_action : (H₃ ∣[(2 : ℤ)] negI.1) = H₃ := modular_slash_negI_of_even H₃ (2: ℤ) even_two
lemma H₄_negI_action : (H₄ ∣[(2 : ℤ)] negI.1) = H₄ := modular_slash_negI_of_even H₄ (2: ℤ) even_two

/-- These three transformation laws follow directly from tsum definition. -/
lemma H₂_T_action : (H₂ ∣[(2 : ℤ)] T) = -H₂ := by
  ext x
  suffices hΘ₂ : Θ₂ ((1 : ℝ) +ᵥ x) = cexp (π * I / 4) * Θ₂ x by
    simp_rw [modular_slash_T_apply, Pi.neg_apply, H₂, hΘ₂, mul_pow, ← Complex.exp_nat_mul,
      mul_comm ((4 : ℕ) : ℂ), Nat.cast_ofNat, div_mul_cancel₀ (b := (4 : ℂ)) _ (by simp),
      Complex.exp_pi_mul_I, neg_one_mul]
  calc
  _ = ∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * ((1 : ℝ) +ᵥ x)) := by
    simp_rw [Θ₂, Θ₂_term]
  _ = ∑' (n : ℤ), cexp (π * I / 4) * cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    apply tsum_congr fun b ↦ ?_
    rw [coe_vadd, ofReal_one]
    repeat rw [← Complex.exp_add]
    congr
    ring_nf
  _ = cexp (π * I / 4) * ∑' (n : ℤ), cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    rw [tsum_mul_left]
  _ = _ := by
    simp_rw [Θ₂, Θ₂_term]
    congr 1
    apply tsum_congr fun b ↦ ?_
    have : Even (b ^ 2 + b) := by
      convert Int.even_mul_succ_self b using 1
      ring_nf
    norm_cast
    rw [Complex.exp_add]
    rw [mul_comm (π * I), Complex.exp_int_mul, Complex.exp_pi_mul_I, this.neg_one_zpow, one_mul]

lemma H₃_T_action : (H₃ ∣[(2 : ℤ)] T) = H₄ := by
  ext x
  simp_rw [modular_slash_T_apply, H₃, H₄, Θ₃, Θ₄, Θ₃_term, Θ₄_term]
  congr 1
  apply tsum_congr fun b ↦ ?_
  rw [coe_vadd, ofReal_one, mul_add, Complex.exp_add, mul_one, mul_comm (π * I), ← Int.cast_pow,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd b with (hb | hb)
  · rw [hb.neg_one_zpow, Even.neg_one_zpow]
    simp [sq, hb]
  · rw [hb.neg_one_zpow, Odd.neg_one_zpow]
    simp [sq, hb]

lemma H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃ := by
  -- H₄|T = H₃|T^2 = Θ₂(0, z + 2) = Θ₂(0, z) = H₃
  ext x
  simp_rw [← H₃_T_action, modular_slash_T_apply, H₃, Θ₃_as_jacobiTheta₂, coe_vadd, ← add_assoc]
  norm_num
  rw [add_comm, jacobiTheta₂_add_right]

lemma H₂_T_inv_action : (H₂ ∣[(2 : ℤ)] T⁻¹) = -H₂ := by
  nth_rw 1 [← neg_eq_iff_eq_neg.mpr H₂_T_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₃_T_inv_action : (H₃ ∣[(2 : ℤ)] T⁻¹) = H₄ := by
  nth_rw 1 [← H₄_T_action, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₄_T_inv_action : (H₄ ∣[(2 : ℤ)] T⁻¹) = H₃ := by
  nth_rw 1 [← H₃_T_action, ← slash_mul, mul_inv_cancel, slash_one]

/-- Use α = T * T -/
lemma H₂_α_action : (H₂ ∣[(2 : ℤ)] α.1) = H₂ := by
  simp [α_eq_T_sq, sq, slash_mul, H₂_T_action]

lemma H₃_α_action : (H₃ ∣[(2 : ℤ)] α.1) = H₃ := by
  simp [α_eq_T_sq, sq, slash_mul, H₃_T_action, H₄_T_action]

lemma H₄_α_action : (H₄ ∣[(2 : ℤ)] α.1) = H₄ := by
  simp [α_eq_T_sq, sq, slash_mul, H₃_T_action, H₄_T_action]

/-- Use jacobiTheta₂_functional_equation -/
lemma H₂_S_action : (H₂ ∣[(2 : ℤ)] S) = -H₄ := by
  ext ⟨x, hx⟩
  have hx' : x ≠ 0 := by simp [Complex.ext_iff, hx.ne.symm]
  calc
  _ = cexp (-π * I / x) * jacobiTheta₂ (-1 / (2 * x)) (-1 / x) ^ 4 * x ^ (-2 : ℤ) := by
    rw [modular_slash_S_apply, H₂, Θ₂_as_jacobiTheta₂]
    simp only [inv_neg, mul_neg, mul_pow, ← Complex.exp_nat_mul, Nat.cast_ofNat, Int.reduceNeg,
      zpow_neg, neg_mul, mul_eq_mul_right_iff, inv_eq_zero]
    rw [mul_comm 4, div_mul_cancel₀ _ (by norm_num)]
    left
    congr 3
    · rw [← div_eq_mul_inv, neg_div]
    · rw [← one_div, neg_div, div_div, mul_comm, neg_div]
    · rw [← one_div, neg_div]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * (1 / (I / x) ^ ((1 : ℂ) / 2) * cexp (π * I / (4 * x)) * jacobiTheta₂ (1 / 2) x) ^ 4 := by
    rw [mul_right_comm, jacobiTheta₂_functional_equation]
    congr 4
    · ring_nf
    · congr 1
      rw [neg_mul, neg_div, one_div, neg_div, div_neg, neg_mul, neg_div, neg_neg]
      ring_nf
      simp [sq, ← mul_assoc, inv_mul_cancel_right₀ hx']
    · ring_nf; simp [hx']
    · ring_nf; simp [inv_inv]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ ((1 : ℂ) / 2)) ^ 4 * cexp (π * I / (4 * x)) ^ 4
          * jacobiTheta₂ (1 / 2) x ^ 4) := by
    simp [mul_pow]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ (2 : ℂ)) * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4) := by
    congr 3
    simp only [div_pow, one_pow, ← cpow_mul_nat]
    ring_nf
  _ = cexp (-π * I / x) * (x ^ (-2 : ℤ) * (-x ^ (2 : ℤ)))
        * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4 := by
    repeat rw [← mul_assoc]
    congr 4
    rw [cpow_ofNat, div_pow, one_div_div, I_sq, div_neg, div_one]
    rfl
  _ = -cexp (-π * I / x) * cexp (π * I / x) * jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [mul_neg, ← zpow_add₀ hx', neg_add_cancel, mul_neg, zpow_zero, mul_one]
    congr 2
    rw [← Complex.exp_nat_mul]
    ring_nf
  _ = -jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [neg_mul, ← Complex.exp_add, neg_mul (π : ℂ), neg_div, neg_add_cancel, Complex.exp_zero,
      neg_one_mul]
  _ = -H₄ ⟨x, hx⟩ := by
    simp [H₄, Θ₄_as_jacobiTheta₂]

lemma H₃_S_action : (H₃ ∣[(2 : ℤ)] S) = -H₃ := by
  ext x
  have hx' : (x : ℂ) ≠ 0 := by obtain ⟨x, hx⟩ := x; change x ≠ 0; simp [Complex.ext_iff, hx.ne.symm]
  have := jacobiTheta₂_functional_equation 0
  simp [-one_div] at this
  simp [modular_slash_S_apply, Pi.neg_apply, H₃, Θ₃_as_jacobiTheta₂]
  rw [this, mul_pow, neg_div, div_neg, neg_neg, one_div (x : ℂ)⁻¹, inv_inv,
    mul_right_comm, ← neg_one_mul (_ ^ 4)]
  congr
  rw [div_pow, ← cpow_mul_nat, mul_neg, neg_neg]
  ring_nf!
  rw [← mul_inv, cpow_ofNat, sq, ← mul_assoc, zpow_two]
  ring_nf!
  rw [inv_pow, inv_I, even_two.neg_pow, I_sq, mul_neg_one, inv_inv, neg_mul, inv_mul_cancel₀]
  exact pow_ne_zero _ hx'

lemma H₄_S_action : (H₄ ∣[(2 : ℤ)] S) = - H₂ := by
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action, neg_slash, ← slash_mul, modular_S_sq,
    ModularForm.slash_neg' _ _ (by decide), slash_one]

lemma H₂_S_action' (z : ℍ) : H₂ (S • z) = - z ^ 2 * H₄ z := by
  have h := congrFun H₂_S_action z
  simp only [SL_slash_apply, denom_S, zpow_neg, zpow_two, Pi.neg_apply] at h
  field_simp [ne_zero] at h ⊢
  exact h

lemma H₄_S_action' (z : ℍ) : H₄ (S • z) = - z ^ 2 * H₂ z := by
  have h := congrFun H₄_S_action z
  simp only [SL_slash_apply, denom_S, zpow_neg, zpow_two, Pi.neg_apply] at h
  field_simp [ne_zero z] at h ⊢
  exact h

lemma H₂_S_inv_action : (H₂ ∣[(2 : ℤ)] S⁻¹) = -H₄ := by
  rw [← neg_eq_iff_eq_neg.mpr H₄_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₃_S_inv_action : (H₃ ∣[(2 : ℤ)] S⁻¹) = -H₃ := by
  nth_rw 1 [← neg_eq_iff_eq_neg.mpr H₃_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₄_S_inv_action : (H₄ ∣[(2 : ℤ)] S⁻¹) = -H₂ := by
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

/-- Use β = -S * α^(-1) * S -/
lemma H₂_β_action : (H₂ ∣[(2 : ℤ)] β.1) = H₂ := calc
  _ = (((H₂ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₂_negI_action, H₂_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₄_T_inv_action, H₃_T_inv_action, H₄_S_action]

lemma H₃_β_action : (H₃ ∣[(2 : ℤ)] β.1) = H₃ := calc
  _ = (((H₃ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₃_negI_action, H₃_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₄_T_inv_action, H₃_T_inv_action, H₃_S_action]

lemma H₄_β_action : (H₄ ∣[(2 : ℤ)] β.1) = H₄ := calc
  _ = (((H₄ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₄_negI_action, H₄_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₂_T_inv_action, H₂_S_action]

/-- H₂, H₃, H₄ are modular forms of weight 2 and level Γ(2) -/
noncomputable def H₂_SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₂
  slash_action_eq' := slashaction_generators_Γ2 H₂ (2 : ℤ) H₂_α_action H₂_β_action H₂_negI_action

noncomputable def H₃_SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₃
  slash_action_eq' := slashaction_generators_Γ2 H₃ (2 : ℤ) H₃_α_action H₃_β_action H₃_negI_action

noncomputable def H₄_SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₄
  slash_action_eq' := slashaction_generators_Γ2 H₄ (2 : ℤ) H₄_α_action H₄_β_action H₄_negI_action

@[simp] lemma H₂_SIF_coe : (H₂_SIF : ℍ → ℂ) = H₂ := rfl

@[simp] lemma H₃_SIF_coe : (H₃_SIF : ℍ → ℂ) = H₃ := rfl

@[simp] lemma H₄_SIF_coe : (H₄_SIF : ℍ → ℂ) = H₄ := rfl

end H_SlashInvariant

section H_isBoundedAtImInfty

variable (γ : SL(2, ℤ))

-- TODO: Isolate this somewhere
lemma jacobiTheta₂_term_half_apply (n : ℤ) (z : ℂ) :
    jacobiTheta₂_term n (z / 2) z = cexp (π * I * (n ^ 2 + n) * z) := by
  rw [jacobiTheta₂_term]
  ring_nf

lemma jacobiTheta₂_rel_aux (n : ℤ) (t : ℝ) :
    rexp (-π * (n + 1 / 2) ^ 2 * t)
      = rexp (-π * t / 4) * jacobiTheta₂_term n (I * t / 2) (I * t) := by
  rw [jacobiTheta₂_term_half_apply, ofReal_exp, ofReal_exp, ← Complex.exp_add, ofReal_mul]
  congr
  ring_nf
  simp
  ring_nf!

-- lemma Complex.norm_exp (z : ℂ) : ‖cexp z‖ = rexp z.re := by
-- simp [abs_exp]

lemma Complex.norm_exp_mul_I (z : ℂ) : ‖cexp (z * I)‖ = rexp (-z.im) := by
  simp [norm_exp]

theorem isBoundedAtImInfty_H₂ : IsBoundedAtImInfty H₂ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₂, Θ₂]
  use (∑' n : ℤ, rexp (-π * ((n : ℝ) + 1 / 2) ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  calc
    _ = ‖∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * z)‖ := rfl
    _ ≤ ∑' (n : ℤ), ‖cexp (π * I * (n + 1 / 2) ^ 2 * z)‖ := norm_tsum_le_tsum_norm ?_
    _ = ∑' (n : ℤ), ‖cexp (π * I * ((n + 1 / 2) ^ 2 * z : ℂ))‖ := by simp only [← mul_assoc]
    _ = ∑' (n : ℤ), ‖rexp (-π * (((n + 1 / 2) ^ 2 : ℝ) * z : ℂ).im)‖ := by
      apply tsum_congr fun b ↦ ?_
      have (z : ℂ) : ‖cexp z‖ = ‖cexp z.re‖ := by
        nth_rw 1 [← Complex.re_add_im z, Complex.exp_add, norm_mul, norm_exp_ofReal_mul_I, mul_one]
      rw [this, mul_comm (π : ℂ), mul_assoc, I_mul_re, ← ofReal_exp,
        norm_real, Real.norm_eq_abs, im_ofReal_mul, neg_mul]
      simp
    _ = ∑' (n : ℤ), ‖rexp (-π * ((n + 1 / 2) ^ 2 : ℝ) * z.im)‖ := by
      simp_rw [im_ofReal_mul, UpperHalfPlane.im, ← mul_assoc]
    _ ≤ _ := Summable.tsum_le_tsum (fun b ↦ ?_) ?_ ?_
  · -- TODO: simplify and refactor this proof with subproof 3 & 4
    have (n : ℤ) : cexp (π * I * (n + 1 / 2) ^ 2 * z)
        = cexp (π * I * z / 4) * jacobiTheta₂_term n (z / 2) z := by
      rw [jacobiTheta₂_term_half_apply, ← Complex.exp_add]
      ring_nf
    simp_rw [this, ← smul_eq_mul (a := cexp _)]
    apply Summable.norm
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff, coe_im]
    linarith
  · rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_monotone
    repeat rw [neg_mul]
    apply neg_le_neg
    have : (b : ℝ) + 1 / 2 ≠ 0 := by
      intro hb
      rw [add_eq_zero_iff_eq_neg] at hb
      have : (2 * b : ℝ) = -1 := by simp [hb]
      norm_cast at this
      exact Int.not_odd_iff_even.mpr (even_two_mul b) (by rw [this]; simp)
    convert (mul_le_mul_iff_right₀ (mul_pos pi_pos (sq_pos_of_ne_zero this))).mpr hz using 1
    rw [mul_one]
  · apply Summable.norm
    apply summable_ofReal.mp
    simp_rw [jacobiTheta₂_rel_aux, ofReal_exp, ← smul_eq_mul (a := cexp _)]
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff, I_mul_im, ofReal_re]
    linarith
  · apply summable_ofReal.mp
    have (n : ℤ) := jacobiTheta₂_rel_aux n 1
    simp_rw [mul_one] at this
    simp_rw [this, ← smul_eq_mul]
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]
    simp

-- We isolate this lemma out as it's also used in the proof for Θ₄
lemma isBoundedAtImInfty_H₃_aux (z : ℍ) (hz : 1 ≤ z.im) :
    ∑' (n : ℤ), ‖Θ₃_term n z‖ ≤ ∑' (n : ℤ), rexp (-π * n ^ 2) := by
  have h_rw (z : ℍ) (n : ℤ) : -(π * n ^ 2 * z : ℂ).im = -π * n ^ 2 * z.im := by
    rw [mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← ofReal_intCast, im_ofReal_mul]
    simp [← mul_assoc]
  have h_sum (z : ℍ) : Summable fun n : ℤ ↦ rexp (-π * n ^ 2 * z.im) := by
    have := (summable_jacobiTheta₂_term_iff 0 z).mpr z.2
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, norm_exp_mul_I, h_rw]
      at this
    simpa using summable_ofReal.mp this
  calc
    _ = ∑' (n : ℤ), ‖cexp (π * (n : ℂ) ^ 2 * z * I)‖ := by simp_rw [Θ₃_term, mul_right_comm _ I]
    _ = ∑' (n : ℤ), rexp (-π * (n : ℂ) ^ 2 * z).im := by simp_rw [Complex.norm_exp_mul_I]; simp
    _ = ∑' (n : ℤ), rexp (-π * (n : ℝ) ^ 2 * z.im) := by
      congr with n
      rw [← ofReal_neg, ← coe_im, ← im_ofReal_mul]
      simp
    _ ≤ _ := Summable.tsum_le_tsum (fun b ↦ ?_) ?_ ?_
  · apply exp_monotone
    simp only [neg_mul, neg_le_neg_iff]
    exact le_mul_of_one_le_right (by positivity) hz
  · exact h_sum z
  · simpa using h_sum UpperHalfPlane.I

theorem isBoundedAtImInfty_H₃ : IsBoundedAtImInfty H₃ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₃, Θ₃]
  use (∑' n : ℤ, rexp (-π * n ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  -- rw [← ]
  apply (norm_tsum_le_tsum_norm ?_).trans (isBoundedAtImInfty_H₃_aux z hz)
  simp_rw [Θ₃_term_as_jacobiTheta₂_term]
  apply Summable.norm
  rw [summable_jacobiTheta₂_term_iff]
  exact z.2

theorem isBoundedAtImInfty_H₄ : IsBoundedAtImInfty H₄ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₄, Θ₄]
  use (∑' n : ℤ, rexp (-π * n ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  calc
    _ ≤ ∑' (n : ℤ), ‖Θ₄_term n z‖ := norm_tsum_le_tsum_norm ?_
    _ = ∑' (n : ℤ), ‖Θ₃_term n z‖ := by congr with n; simp [Θ₄_term, Θ₃_term]
    _ ≤ _ := isBoundedAtImInfty_H₃_aux z hz
  simp_rw [Θ₄_term_as_jacobiTheta₂_term]
  apply Summable.norm
  rw [summable_jacobiTheta₂_term_iff]
  exact z.2

theorem isBoundedAtImInfty_H_slash : IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] γ)
      ∧ IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] γ) ∧ IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] γ) := by
  apply Subgroup.closure_induction_left (s := {S, T, ↑negI})
      (p := fun γ _ ↦ IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] γ) ∧ IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] γ)
        ∧ IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] γ))
  · simp [isBoundedAtImInfty_H₂, isBoundedAtImInfty_H₃, isBoundedAtImInfty_H₄]
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_action, H₃_S_action, H₄_S_action, neg_slash, isBoundedAtImInfty_neg_iff]
      use h.right.right, h.right.left, h.left
    · simp_rw [H₂_T_action, H₃_T_action, H₄_T_action, neg_slash, isBoundedAtImInfty_neg_iff]
      use h.left, h.right.right, h.right.left
    · rw [SL_slash, H₂_negI_action, H₃_negI_action, H₄_negI_action]
      exact h
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_inv_action, H₃_S_inv_action, H₄_S_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]
      use h.right.right, h.right.left, h.left
    · simp_rw [H₂_T_inv_action, H₃_T_inv_action, H₄_T_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]
      use h.left, h.right.right, h.right.left
    · rw [← Subgroup.coe_inv, modular_negI_inv, SL_slash,
        modular_slash_negI_of_even _ 2 (by decide)]
      rw [H₃_negI_action, H₄_negI_action]
      exact h
  · intro s hs
    simp_rw [Set.mem_setOf_eq, Set.mem_range] at hs
    obtain ⟨s, rfl⟩ := hs
    rw [Set.mem_iInter, SetLike.mem_coe]
    intro hs
    have hs2 : {S, T} ⊆ (s : Set (SL(2, ℤ))) := by
      apply subset_trans _ hs
      simp only [Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        Set.insert_subset_insert]
    simp only [top_le_iff.mp <| SL2Z_generate.symm ▸ (Subgroup.closure_le s).mpr hs2,
      Subgroup.mem_top]

theorem isBoundedAtImInfty_H₂_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').left

theorem isBoundedAtImInfty_H₃_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').right.left

theorem isBoundedAtImInfty_H₄_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').right.right

end H_isBoundedAtImInfty

/-!
## Limits at infinity

We prove the limit of Θᵢ(z) and Hᵢ(z) as z tends to i∞. These results are used in
`JacobiIdentity.lean`.
-/

theorem jacobiTheta₂_half_mul_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (x / 2) x) atImInfty (𝓝 2) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun z (n : ℤ) ↦ cexp (2 * π * I * n * (z / 2) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := Set.indicator {-1, 0} 1)
    (bound := fun n : ℤ ↦ rexp (π / 4) * rexp (-π * ((n : ℝ) + 1 / 2) ^ 2)) ?_ ?_ ?_
  · simp [← tsum_subtype]
  · -- TODO: merge this with proof of isBoundedAtImInfty_H₂
    apply summable_ofReal.mp
    have (n : ℤ) := jacobiTheta₂_rel_aux n 1
    simp_rw [mul_one] at this
    simp_rw [ofReal_mul, this, ← smul_eq_mul]
    apply Summable.const_smul
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]
    simp
  · intro n
    have : n = -1 ∨ n = 0 ∨ n ∉ ({-1, 0} : Set ℤ) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rcases this with (rfl | rfl | hn) <;> ring_nf
    · simp
    · simp
    · simp only [hn, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h₁ (n : ℤ) (z : ℂ) : (π * I * n * z + π * I * n ^ 2 * z) = π * (n + n ^ 2) * z * I := by
        ring_nf
      have h_base' : rexp (-π) ^ ((n : ℝ) + n ^ 2) < 1 := by
        apply Real.rpow_lt_one
        · positivity
        · apply Real.exp_lt_one_iff.mpr (by simp; positivity)
        convert_to 0 < ((n * (n + 1) : ℤ) : ℝ)
        · push_cast
          ring_nf
        · apply Int.cast_pos.mpr
          by_cases hn' : 0 < n
          · apply mul_pos hn' (by omega)
          · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
            exact mul_pos_of_neg_of_neg (by omega) (by omega)
      simp_rw [h₁, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← Int.cast_add,
        ← ofReal_intCast, im_ofReal_mul, ← mul_assoc, Int.cast_add, Int.cast_pow, ← neg_mul,
        Real.exp_mul, coe_im]
      refine (tendsto_rpow_atTop_of_base_lt_one _ ?_ h_base').comp tendsto_im_atImInfty
      exact neg_one_lt_zero.trans (by positivity)
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [← Real.exp_add]
    ring_nf
    trans ‖cexp (((π * k + π * k ^ 2 : ℝ) * z) * I)‖
    · apply le_of_eq
      simpa [add_mul] using by ring_nf
    · rw [norm_exp_mul_I, im_ofReal_mul]
      have (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
        nth_rw 2 [← mul_one n]
        rw [sq, Int.cast_mul, Int.cast_one, ← mul_add]
        rcases lt_trichotomy (-1) n with (hn | rfl | hn)
        · apply mul_nonneg <;> norm_cast; omega
        · norm_num
        · apply mul_nonneg_of_nonpos_of_nonpos <;> norm_cast <;> omega
      simpa using le_mul_of_one_le_right
        (by rw [← mul_add, add_comm]; exact mul_nonneg Real.pi_nonneg (this k)) hz

theorem jacobiTheta₂_zero_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ 0 x) atImInfty (𝓝 1) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term, mul_zero, zero_add]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ cexp (π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    simp only
    split_ifs with hk
    · subst hk
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [mul_right_comm _ I, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← ofReal_intCast,
        ← ofReal_pow, im_ofReal_mul, ← mul_assoc]
      simpa using tendsto_im_atImInfty.const_mul_atTop (by positivity)
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    simp only
    simp_rw [mul_right_comm _ I, norm_exp_mul_I]
    simpa [← ofReal_intCast, ← ofReal_pow] using le_mul_of_one_le_right (by positivity) hz

theorem jacobiTheta₂_half_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (1 / 2 : ℂ) x) atImInfty (𝓝 1) := by
  have hnorm (z : ℍ) (k : ℤ) :
      ‖cexp (2 * π * I * k * (1 / 2 : ℂ) + π * I * k ^ 2 * z)‖ = rexp (-π * k ^ 2 * z.im) := by
    simpa [jacobiTheta₂_term, coe_im] using
      (norm_jacobiTheta₂_term k (1 / 2 : ℂ) (z : ℂ))
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ cexp (2 * π * I * n * (1 / 2 : ℂ) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    simp only
    split_ifs with hk
    · subst hk
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hnorm]
      have hk2_pos : 0 < (k : ℝ) ^ 2 := by
        exact sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)
      exact (Real.tendsto_exp_atBot).comp
        (tendsto_im_atImInfty.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos, hk2_pos]))
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    rw [hnorm]
    have hcoef_nonpos : (-π * (k : ℝ) ^ 2) ≤ 0 := by
      nlinarith [Real.pi_pos, sq_nonneg (k : ℝ)]
    have hmul : (-π * (k : ℝ) ^ 2) * z.im ≤ (-π * (k : ℝ) ^ 2) * 1 := by
      exact mul_le_mul_of_nonpos_left hz hcoef_nonpos
    simpa using Real.exp_le_exp.mpr hmul

theorem Θ₂_tendsto_atImInfty : Tendsto Θ₂ atImInfty (𝓝 0) := by
  rw [funext Θ₂_as_jacobiTheta₂, ← zero_mul (2 : ℂ)]
  refine Tendsto.mul ?_ jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  -- simp_rw directly below fails
  have (z : ℍ) : ‖cexp (π * I * z / 4)‖ = rexp (-π * z.im / 4) := by
    rw [mul_right_comm, mul_div_right_comm, norm_exp_mul_I]
    simp [neg_div]
  simp_rw [this]
  exact (Real.tendsto_exp_atBot).comp <|
    -- TODO: tendsto_div_const_atBot_of_pos and its friends should be aliased under Tendsto.
    (tendsto_div_const_atBot_of_pos zero_lt_four).mpr
      (tendsto_im_atImInfty.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))

theorem Θ₃_tendsto_atImInfty : Tendsto Θ₃ atImInfty (𝓝 1) := by
  simpa [funext Θ₃_as_jacobiTheta₂] using jacobiTheta₂_zero_apply_tendsto_atImInfty

theorem Θ₄_tendsto_atImInfty : Tendsto Θ₄ atImInfty (𝓝 1) := by
  simpa [funext Θ₄_as_jacobiTheta₂] using jacobiTheta₂_half_apply_tendsto_atImInfty

theorem H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0) := by
  convert Θ₂_tendsto_atImInfty.pow 4
  norm_num

theorem H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1) := by
  convert Θ₃_tendsto_atImInfty.pow 4
  norm_num

theorem H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1) := by
  convert Θ₄_tendsto_atImInfty.pow 4
  norm_num

/-!
## Imaginary Axis Properties

Properties of theta functions when restricted to the positive imaginary axis z = I*t.
-/

section ImagAxisProperties

/-- `im` distributes over tsum when each term has zero imaginary part. -/
lemma Complex.im_tsum_eq_zero_of_im_eq_zero {ι : Type*} {f : ι → ℂ}
    (hf : Summable f) (him : ∀ n, (f n).im = 0) :
    (∑' n, f n).im = 0 := by
  rw [Complex.im_tsum hf]; simp [him]

private lemma summable_Θ₂_term_imagAxis (t : ℝ) (ht : 0 < t) :
    Summable fun n : ℤ => Θ₂_term n ⟨I * t, by simp [ht]⟩ := by
  simp_rw [Θ₂_term_as_jacobiTheta₂_term]
  apply Summable.mul_left
  rw [summable_jacobiTheta₂_term_iff]
  exact (⟨I * t, by simp [ht]⟩ : ℍ).im_pos

private lemma summable_Θ₄_term_imagAxis (t : ℝ) (ht : 0 < t) :
    Summable fun n : ℤ => Θ₄_term n ⟨I * t, by simp [ht]⟩ := by
  simp_rw [Θ₄_term_as_jacobiTheta₂_term, summable_jacobiTheta₂_term_iff]
  exact (⟨I * t, by simp [ht]⟩ : ℍ).im_pos

/-- Each term `Θ₂_term n (I*t)` has zero imaginary part for `t > 0`. -/
lemma Θ₂_term_imag_axis_real (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂_term n ⟨I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₂_term
  change (cexp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * t))).im = 0
  rw [show Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * ↑t) =
        ((-(Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) from by
      push_cast
      linear_combination ((Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * ↑t) * I_sq]
  exact exp_ofReal_im _

/-- `Θ₂(I*t)` has zero imaginary part for `t > 0`. -/
lemma Θ₂_imag_axis_real (t : ℝ) (ht : 0 < t) :
    (Θ₂ ⟨I * t, by simp [ht]⟩).im = 0 :=
  Complex.im_tsum_eq_zero_of_im_eq_zero (summable_Θ₂_term_imagAxis t ht)
    (fun n => Θ₂_term_imag_axis_real n t ht)

/-- `(-1 : ℂ)^n` has zero imaginary part for any integer n. -/
lemma neg_one_zpow_im_eq_zero (n : ℤ) : ((-1 : ℂ) ^ n).im = 0 := by
  rcases Int.even_or_odd n with hn | hn <;> (rw [hn.neg_one_zpow]; simp)

/-- Each term `Θ₄_term n (I*t)` has zero imaginary part for `t > 0`. -/
lemma Θ₄_term_imag_axis_real (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₄_term n ⟨I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₄_term
  change ((-1 : ℂ) ^ n * cexp (Real.pi * I * (n : ℂ) ^ 2 * (I * t))).im = 0
  rw [show Real.pi * I * (n : ℂ) ^ 2 * (I * ↑t) = ((-(Real.pi * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) by
      push_cast
      linear_combination ((Real.pi : ℂ) * (n : ℂ) ^ 2 * ↑t) * I_sq]
  simp only [Complex.mul_im, neg_one_zpow_im_eq_zero, exp_ofReal_im,
    mul_zero, zero_mul, add_zero]

/-- `Θ₄(I*t)` has zero imaginary part for `t > 0`. -/
lemma Θ₄_imag_axis_real (t : ℝ) (ht : 0 < t) :
    (Θ₄ ⟨I * t, by simp [ht]⟩).im = 0 :=
  Complex.im_tsum_eq_zero_of_im_eq_zero (summable_Θ₄_term_imagAxis t ht)
    (fun n => Θ₄_term_imag_axis_real n t ht)

/--
`H₂(it)` is real for all `t > 0`.
Blueprint: Follows from the q-expansion having real coefficients.
Proof strategy: H₂ = Θ₂^4 where Θ₂(it) = ∑ₙ exp(-π(n+1/2)²t) is a sum of real
exponentials.
-/
@[fun_prop]
theorem H₂_imag_axis_real : ResToImagAxis.Real H₂ := fun t ht => by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
  exact Complex.im_pow_eq_zero_of_im_eq_zero (Θ₂_imag_axis_real t ht) 4

/-- Each term `Θ₂_term n (I*t)` has real part `exp(-π(n+1/2)²t)` for `t > 0`. -/
lemma Θ₂_term_imag_axis_re (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂_term n ⟨I * t, by simp [ht]⟩).re =
      Real.exp (-Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) := by
  unfold Θ₂_term
  change (cexp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * t))).re = _
  rw [show Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * ↑t) =
        ((-(Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) by
      push_cast
      linear_combination ((Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * ↑t) * I_sq,
    Complex.exp_ofReal_re]
  ring_nf

/-- Each term `Θ₂_term n (I*t)` has positive real part for `t > 0`. -/
lemma Θ₂_term_imag_axis_re_pos (n : ℤ) (t : ℝ) (ht : 0 < t) :
    0 < (Θ₂_term n ⟨I * t, by simp [ht]⟩).re := by
  rw [Θ₂_term_imag_axis_re n t ht]
  exact Real.exp_pos _

/-- `Θ₂(I*t)` has positive real part for `t > 0`.
Each term `Θ₂_term n (I*t) = exp(-π(n+1/2)²t)` is a positive real, so the tsum is too. -/
lemma Θ₂_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < (Θ₂ ⟨I * t, by simp [ht]⟩).re := by
  have hsum := summable_Θ₂_term_imagAxis t ht
  rw [Θ₂, Complex.re_tsum hsum]
  exact (Complex.hasSum_re hsum.hasSum).summable.tsum_pos
    (fun n => (Θ₂_term_imag_axis_re_pos n t ht).le) 0 (Θ₂_term_imag_axis_re_pos 0 t ht)

/--
`H₂(it) > 0` for all `t > 0`.
Blueprint: Lemma 6.43 - H₂ is positive on the imaginary axis.
Proof strategy: Each term exp(-π(n+1/2)²t) > 0, so Θ₂(it) > 0, hence H₂ = Θ₂^4 > 0.
-/
@[fun_prop]
theorem H₂_imag_axis_pos : ResToImagAxis.Pos H₂ := by
  refine ⟨H₂_imag_axis_real, fun t ht => ?_⟩
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
  set z := Θ₂ ⟨I * t, by simp [ht]⟩ with hz_def
  have hcast : z = (z.re : ℂ) :=
    Complex.ext rfl ((Θ₂_imag_axis_real t ht).trans (ofReal_im _).symm)
  rw [hcast, ← Complex.ofReal_pow, ofReal_re]
  exact pow_pos (Θ₂_imag_axis_re_pos t ht) 4

/--
`H₄(it)` is real for all `t > 0`.
Blueprint: Corollary 6.43 - follows from Θ₄ being real on the imaginary axis.
-/
@[fun_prop]
theorem H₄_imag_axis_real : ResToImagAxis.Real H₄ := fun t ht => by
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₄]
  exact Complex.im_pow_eq_zero_of_im_eq_zero (Θ₄_imag_axis_real t ht) 4

/--
`H₄(it) > 0` for all `t > 0`.
Blueprint: Corollary 6.43 - H₄ is positive on the imaginary axis.

Proof strategy: Use the modular S-transformation relating H₄ and H₂.
From `H₄_S_action : (H₄ ∣[2] S) = -H₂` and `ResToImagAxis.SlashActionS`, we get
`H₂(i/t) = t² · H₄(it)`, so `H₄(it) > 0` follows from `H₂(i/t) > 0`.
-/
@[fun_prop]
theorem H₄_imag_axis_pos : ResToImagAxis.Pos H₄ := by
  refine ⟨H₄_imag_axis_real, fun t ht => ?_⟩
  have ht' : 0 < 1 / t := one_div_pos.mpr ht
  have hSlash := ResToImagAxis.SlashActionS H₄ 2 ht'
  rw [H₄_S_action] at hSlash
  have hI2 : (I : ℂ) ^ (-2 : ℤ) = -1 := by
    change (I ^ 2)⁻¹ = -1; rw [I_sq]; norm_num
  have h1t2 : ((1 / t : ℝ) : ℂ) ^ (-2 : ℤ) = (t : ℂ) ^ 2 := by
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [one_div, ofReal_inv, zpow_neg]; field_simp
  have hNeg : (-H₂).resToImagAxis (1 / t) = -(H₂.resToImagAxis (1 / t)) := by
    simp only [Function.resToImagAxis_apply, ResToImagAxis, ht', ↓reduceDIte, Pi.neg_apply]
  rw [hNeg, hI2, h1t2, one_div_one_div] at hSlash
  have hEq : H₂.resToImagAxis (1 / t) = (t : ℂ) ^ 2 * H₄.resToImagAxis t := by
    linear_combination -hSlash
  have hH₂_pos := H₂_imag_axis_pos.2 (1 / t) ht'
  rw [hEq, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hH₂_pos
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ht)).mp hH₂_pos

end ImagAxisProperties

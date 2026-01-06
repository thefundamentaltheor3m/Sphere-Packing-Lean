import SpherePacking.ForMathlib.AtImInfty
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ModularForms.IsCuspForm

/-!
# Limits at infinity

In this file we prove the limit of Θᵢ(z) as z tends to i∞. This will be useful as we do
computations with Fourier coefficients, e.g. comparing two q-expansions. This is also useful when we
compute limits of forms later on (following Seewoo's approach).
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Asymptotics Topology Filter Manifold SlashInvariantForm Matrix ModularGroup
  SlashAction

lemma Int.ne_half (a : ℤ) : ↑a ≠ (1 / 2 : ℝ) :=
  ne_of_apply_ne Int.fract <| by
    rw [fract_intCast, fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    norm_num

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
  simp_rw [jacobiTheta₂, jacobiTheta₂_term, mul_right_comm _ _ (1 / 2 : ℂ), ← mul_div_assoc,
    mul_one, div_self (G₀ := ℂ) two_ne_zero, one_mul, exp_add, mul_comm (π * I), exp_int_mul,
    exp_pi_mul_I, mul_comm, mul_comm I]
  -- I tried converting this to the formula for jacobiTheta₂ 0 x above, but couldn't
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ (-1) ^ n * cexp (π * I * n ^ 2 * z))
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
      simp_rw [mul_right_comm _ I, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
        norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← ofReal_intCast, ← ofReal_pow, im_ofReal_mul,
        ← mul_assoc]
      simpa using tendsto_im_atImInfty.const_mul_atTop (by positivity)
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    simp only
    simp_rw [mul_right_comm _ I, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
      norm_exp_mul_I]
    simpa [← ofReal_intCast, ← ofReal_pow] using le_mul_of_one_le_right (by positivity) hz

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
## Jacobi identity asymptotics

We prove that g := H₂ + H₄ - H₃ → 0 at i∞, hence f := g² → 0.
Combined with the dimension vanishing for weight 4 cusp forms, this proves jacobi_identity.
-/

/-- The function g := H₂ + H₄ - H₃ tends to 0 at i∞.
    Since H₂ → 0, H₃ → 1, H₄ → 1, we have g → 0 + 1 - 1 = 0. -/
theorem jacobi_g_tendsto_atImInfty : Tendsto jacobi_g atImInfty (𝓝 0) := by
  convert (H₂_tendsto_atImInfty.add H₄_tendsto_atImInfty).sub H₃_tendsto_atImInfty using 1
  norm_num

/-- The function f := g² tends to 0 at i∞. -/
theorem jacobi_f_tendsto_atImInfty : Tendsto jacobi_f atImInfty (𝓝 0) := by
  convert jacobi_g_tendsto_atImInfty.pow 2 using 1
  norm_num

/-- jacobi_f is bounded at i∞ (follows from tending to 0) -/
lemma isBoundedAtImInfty_jacobi_f : IsBoundedAtImInfty jacobi_f :=
  IsZeroAtImInfty.isBoundedAtImInfty jacobi_f_tendsto_atImInfty

/-- jacobi_f slash by any SL₂(ℤ) element equals jacobi_f (for use with bounded_at_cusps) -/
lemma jacobi_f_slash_eq (A' : SL(2, ℤ)) :
    jacobi_f ∣[(4 : ℤ)] (SpecialLinearGroup.mapGL ℝ A') = jacobi_f := by
  simpa [ModularForm.SL_slash] using jacobi_f_SL2Z_invariant A'

/-- jacobi_f slash by any SL₂(ℤ) element is bounded at i∞ -/
lemma isBoundedAtImInfty_jacobi_f_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (jacobi_f ∣[(4 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  rw [← hA, jacobi_f_slash_eq A']
  exact isBoundedAtImInfty_jacobi_f

/-- jacobi_f as a ModularForm of weight 4 and level Γ(1) -/
noncomputable def jacobi_f_MF : ModularForm (CongruenceSubgroup.Gamma 1) 4 := {
  jacobi_f_SIF with
  holo' := jacobi_f_SIF_MDifferentiable
  bdd_at_cusps' := fun hc =>
    bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_jacobi_f_slash
}

/-!
## Completing the Jacobi identity proof

With jacobi_f → 0 at i∞, we can show jacobi_f_MF is a cusp form and apply
the dimension vanishing lemma to conclude f = 0, hence g = 0, hence H₂ + H₄ = H₃.
-/

/-- jacobi_f_MF is a cusp form because it vanishes at i∞ -/
theorem jacobi_f_MF_IsCuspForm : IsCuspForm (CongruenceSubgroup.Gamma 1) 4 jacobi_f_MF := by
  rw [IsCuspForm_iff_coeffZero_eq_zero, ModularFormClass.qExpansion_coeff]; simp
  exact IsZeroAtImInfty.cuspFunction_apply_zero jacobi_f_tendsto_atImInfty
    (by norm_num : (0 : ℝ) < 1)

/-- The main dimension vanishing: jacobi_f_MF = 0 -/
theorem jacobi_f_MF_eq_zero : jacobi_f_MF = 0 :=
  IsCuspForm_weight_lt_eq_zero 4 (by norm_num) jacobi_f_MF jacobi_f_MF_IsCuspForm

/-- jacobi_f = 0 as a function -/
theorem jacobi_f_eq_zero : jacobi_f = 0 :=
  congr_arg (·.toFun) jacobi_f_MF_eq_zero

/-- jacobi_g = 0 as a function (from g² = 0) -/
theorem jacobi_g_eq_zero : jacobi_g = 0 := by
  ext z
  simpa [jacobi_f] using congr_fun jacobi_f_eq_zero z

-- jacobi_identity is proved in ThetaDerivIdentities.lean using jacobi_g_eq_zero

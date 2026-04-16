module

public import SpherePacking.ModularForms.JacobiTheta.MDifferentiable

@[expose] public section

/-!
# Jacobi theta identities

This file proves the Jacobi identity `H₂ + H₄ = H₃` and the discriminant identity
`Delta = (H₂ * H₃ * H₄)^2 / 256`.

The proof strategy:
1. Define `g := H₂ + H₄ - H₃` and `f := g²`.
2. Show `f` is a weight-4 level-1 modular form.
3. Show `f` vanishes at `i∞` using the asymptotic lemmas from `Basic.lean`.
4. Apply cusp form vanishing in weight 4 to deduce `f = 0`, hence `g = 0`.
5. Use the weight-12 analogue for `(H₂ * H₃ * H₄)^2` to identify `Delta`.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

section JacobiIdentity

/-- The difference `g := H₂ + H₄ - H₃`. -/
noncomputable def jacobi_g : ℍ → ℂ := H₂ + H₄ - H₃

/-- The squared difference `f := g²`. -/
noncomputable def jacobi_f : ℍ → ℂ := jacobi_g ^ 2

/-- S-action on `g`: `g|[2]S = -g`. -/
lemma jacobi_g_S_action : (jacobi_g ∣[(2 : ℤ)] S) = -jacobi_g := by
  simp only [jacobi_g, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z; simp only [Pi.add_apply, Pi.neg_apply]; ring

/-- T-action on `g`: `g|[2]T = -g`. -/
lemma jacobi_g_T_action : (jacobi_g ∣[(2 : ℤ)] T) = -jacobi_g := by
  simp only [jacobi_g, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z; simp only [Pi.add_apply, Pi.neg_apply]; ring

/-- Rewrite `jacobi_f` as a pointwise product. -/
lemma jacobi_f_eq_mul : jacobi_f = jacobi_g * jacobi_g := sq jacobi_g

/-- S-invariance of `f`: `f|[4]S = f`, because `g|[2]S = -g`. -/
lemma jacobi_f_S_action : (jacobi_f ∣[(4 : ℤ)] S) = jacobi_f := by
  simp only [jacobi_f_eq_mul, (by norm_num : (4 : ℤ) = 2 + 2),
    mul_slash_SL2 2 2 S _ _, jacobi_g_S_action, neg_mul_neg]

/-- T-invariance of `f`: `f|[4]T = f`, because `g|[2]T = -g`. -/
lemma jacobi_f_T_action : (jacobi_f ∣[(4 : ℤ)] T) = jacobi_f := by
  simp only [jacobi_f_eq_mul, (by norm_num : (4 : ℤ) = 2 + 2),
    mul_slash_SL2 2 2 T _ _, jacobi_g_T_action, neg_mul_neg]

/-- Full `SL₂(ℤ)` invariance of `f` with weight 4. -/
lemma jacobi_f_SL2Z_invariant : ∀ γ : SL(2, ℤ), jacobi_f ∣[(4 : ℤ)] γ = jacobi_f :=
  slashaction_generators_SL2Z jacobi_f 4 jacobi_f_S_action jacobi_f_T_action

/-- `jacobi_f` as a slash-invariant form of weight 4 and level `Γ(1)`. -/
noncomputable def jacobi_f_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 4 where
  toFun := jacobi_f
  slash_action_eq' := slashaction_generators_GL2R jacobi_f 4 jacobi_f_S_action jacobi_f_T_action

/-- `jacobi_f` is holomorphic since `jacobi_g` is. -/
lemma jacobi_f_MDifferentiable : MDiff jacobi_f := by unfold jacobi_f jacobi_g; fun_prop

end JacobiIdentity

/-!
## Jacobi identity proof

We prove that `g := H₂ + H₄ - H₃ → 0` at `i∞`, hence `f := g² → 0`.
Combined with the dimension-vanishing theorem for weight-4 cusp forms, this proves the Jacobi
identity.
-/

/-- The function `g := H₂ + H₄ - H₃` tends to `0` at `i∞`. -/
theorem jacobi_g_tendsto_atImInfty : Tendsto jacobi_g atImInfty (𝓝 0) := by
  have := H₂_tendsto_atImInfty
  have := H₃_tendsto_atImInfty
  have := H₄_tendsto_atImInfty
  change Tendsto (fun z => H₂ z + H₄ z - H₃ z) atImInfty (𝓝 0)
  tendsto_cont

/-- The function `f := g²` tends to `0` at `i∞`. -/
theorem jacobi_f_tendsto_atImInfty : Tendsto jacobi_f atImInfty (𝓝 0) := by
  have := jacobi_g_tendsto_atImInfty
  change Tendsto (fun z => jacobi_g z ^ 2) atImInfty (𝓝 0)
  tendsto_cont

private noncomputable def jacobi_f_CF : CuspForm (Γ 1) 4 :=
  cuspFormOfSIFTendstoZero jacobi_f_SIF jacobi_f_MDifferentiable jacobi_f_tendsto_atImInfty

/-- `jacobi_f = 0` by dimension argument: weight-4 cusp forms vanish. -/
theorem jacobi_f_eq_zero : jacobi_f = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 4 (by norm_num)) jacobi_f_CF)

/-- `jacobi_g = 0` as a function, from `g² = 0`. -/
theorem jacobi_g_eq_zero : jacobi_g = 0 := by
  ext z
  simpa [jacobi_f] using congr_fun jacobi_f_eq_zero z

/-- Jacobi identity: `H₂ + H₄ = H₃` (Blueprint Lemma 6.41). -/
theorem jacobi_identity : H₂ + H₄ = H₃ := by
  ext z
  simpa [jacobi_g, sub_eq_zero] using congr_fun jacobi_g_eq_zero z

private noncomputable def theta_prod : ℍ → ℂ := H₂ * H₃ * H₄

private lemma theta_prod_S_action : (theta_prod ∣[(6 : ℤ)] S) = -theta_prod := by
  simp only [theta_prod, (by norm_num : (6 : ℤ) = 2 + 2 + 2),
    mul_slash_SL2 (2 + 2) 2 S _ _, mul_slash_SL2 2 2 S _ _,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z; simp [Pi.mul_apply, Pi.neg_apply]; ring

private lemma theta_prod_T_action : (theta_prod ∣[(6 : ℤ)] T) = -theta_prod := by
  simp only [theta_prod, (by norm_num : (6 : ℤ) = 2 + 2 + 2),
    mul_slash_SL2 (2 + 2) 2 T _ _, mul_slash_SL2 2 2 T _ _,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z; simp [Pi.mul_apply, Pi.neg_apply]; ring

private noncomputable def theta_prod_sq : ℍ → ℂ := (H₂ * H₃ * H₄) ^ 2

private lemma theta_prod_sq_eq_mul : theta_prod_sq = theta_prod * theta_prod := sq theta_prod

private lemma theta_prod_sq_S_action : (theta_prod_sq ∣[(12 : ℤ)] S) = theta_prod_sq := by
  rw [theta_prod_sq_eq_mul, (by norm_num : (12 : ℤ) = 6 + 6),
    mul_slash_SL2 6 6 S _ _, theta_prod_S_action, neg_mul_neg]

private lemma theta_prod_sq_T_action : (theta_prod_sq ∣[(12 : ℤ)] T) = theta_prod_sq := by
  rw [theta_prod_sq_eq_mul, (by norm_num : (12 : ℤ) = 6 + 6),
    mul_slash_SL2 6 6 T _ _, theta_prod_T_action, neg_mul_neg]

private lemma theta_prod_sq_SL2Z_invariant :
    ∀ γ : SL(2, ℤ), theta_prod_sq ∣[(12 : ℤ)] γ = theta_prod_sq :=
  slashaction_generators_SL2Z theta_prod_sq 12
    theta_prod_sq_S_action theta_prod_sq_T_action

private lemma theta_prod_sq_MDifferentiable : MDiff theta_prod_sq := by
  unfold theta_prod_sq; fun_prop

private lemma theta_prod_sq_tendsto_atImInfty : Tendsto theta_prod_sq atImInfty (𝓝 0) := by
  change Tendsto (fun z => (H₂ z * H₃ z * H₄ z) ^ 2) atImInfty (𝓝 0)
  have := H₂_tendsto_atImInfty
  have := H₃_tendsto_atImInfty
  have := H₄_tendsto_atImInfty
  tendsto_cont

private noncomputable def theta_prod_sq_SIF :
    SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := theta_prod_sq
  slash_action_eq' := slashaction_generators_GL2R theta_prod_sq 12
    theta_prod_sq_S_action theta_prod_sq_T_action

private noncomputable def theta_prod_sq_CF : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  cuspFormOfSIFTendstoZero theta_prod_sq_SIF theta_prod_sq_MDifferentiable
    theta_prod_sq_tendsto_atImInfty

private lemma theta_prod_sq_CF_apply (z : ℍ) :
    theta_prod_sq_CF z = theta_prod_sq z := rfl

private lemma finrank_cuspform_12 :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) 12) = 1 := by
  apply Module.finrank_eq_of_rank_eq
  rw [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12)]
  simp
  exact ModularForm.levelOne_weight_zero_rank_one

private lemma theta_prod_sq_proportional :
    ∃ c : ℂ, c • Delta = theta_prod_sq_CF :=
  (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp finrank_cuspform_12 theta_prod_sq_CF

private lemma H₂_div_exp_tendsto :
    Tendsto (fun z : ℍ ↦ H₂ z / cexp (↑π * I * ↑z)) atImInfty (nhds 16) := by
  have h_eq : ∀ z : ℍ, H₂ z / cexp (↑π * I * ↑z) = (jacobiTheta₂ (↑z / 2) ↑z) ^ 4 := by
    intro z
    rw [H₂, Θ₂_as_jacobiTheta₂, mul_pow,
      show cexp (↑π * I * ↑z / 4) ^ 4 = cexp (↑π * I * ↑z) from by
        rw [← Complex.exp_nat_mul]; ring_nf,
      mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  simp_rw [h_eq]
  convert jacobiTheta₂_half_mul_apply_tendsto_atImInfty.pow 4 using 1; norm_num

lemma Delta_eq_H₂_H₃_H₄ : (Delta : ℍ → ℂ) = (1 / 256 : ℂ) • (H₂ * H₃ * H₄) ^ 2 := by
  obtain ⟨c, hc⟩ := theta_prod_sq_proportional
  have hc_pw : ∀ z : ℍ, c * Delta z = theta_prod_sq z :=
    fun z => (DFunLike.congr_fun hc z).trans (theta_prod_sq_CF_apply z)
  have hc_eq : c = 256 := by
    have hD_asymp : Tendsto (fun z : ℍ ↦ Delta z / cexp (2 * ↑π * I * ↑z)) atImInfty (nhds 1) := by
      have h_eq : ∀ z : ℍ, Delta z / cexp (2 * ↑π * I * ↑z) =
          ∏' (n : ℕ), (1 - cexp (2 * ↑π * I * (↑n + 1) * ↑z)) ^ 24 := by
        intro z
        rw [Delta_apply, Δ, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
      simp_rw [h_eq]
      exact Delta_boundedfactor
    have hP_asymp : Tendsto (fun z : ℍ ↦ theta_prod_sq z / cexp (2 * ↑π * I * ↑z))
        atImInfty (nhds 256) := by
      have h_rewrite : ∀ z : ℍ, theta_prod_sq z / cexp (2 * ↑π * I * ↑z) =
          (H₂ z / cexp (↑π * I * ↑z)) ^ 2 * (H₃ z) ^ 2 * (H₄ z) ^ 2 := by
        intro z
        simp only [theta_prod_sq, Pi.mul_apply, Pi.pow_apply]
        rw [show cexp (2 * ↑π * I * ↑z) = cexp (↑π * I * ↑z) ^ 2 from by
          rw [← Complex.exp_nat_mul]; ring_nf]
        field_simp
      simp_rw [h_rewrite]
      have : (256 : ℂ) = 16 ^ 2 * 1 ^ 2 * 1 ^ 2 := by norm_num
      rw [this]
      have := H₂_div_exp_tendsto
      have := H₃_tendsto_atImInfty
      have := H₄_tendsto_atImInfty
      tendsto_cont
    have h_eq_fns : ∀ z : ℍ, c * (Delta z / cexp (2 * ↑π * I * ↑z)) =
        theta_prod_sq z / cexp (2 * ↑π * I * ↑z) := by
      intro z
      rw [← mul_div_assoc, hc_pw]
    have hc_lim : Tendsto (fun z : ℍ ↦ c * (Delta z / cexp (2 * ↑π * I * ↑z)))
        atImInfty (nhds c) := by simpa using hD_asymp.const_mul c
    exact tendsto_nhds_unique (hc_lim.congr h_eq_fns) hP_asymp
  ext z
  have h := hc_pw z
  rw [hc_eq] at h
  simp only [theta_prod_sq, Pi.mul_apply, Pi.pow_apply] at h
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  linear_combination (1 / (256 : ℂ)) * h

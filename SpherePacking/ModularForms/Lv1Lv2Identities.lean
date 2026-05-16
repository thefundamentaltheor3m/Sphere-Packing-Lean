module
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.ModularForms.EisensteinBase
import SpherePacking.ModularForms.CuspFormIsoModforms
import SpherePacking.Tactic.FunPropExt

/-!
# Level 1 / Level 2 identities

This file formalizes Blueprint Lemma `lv1-lv2-identities`, relating the level-1 Eisenstein
series `E₄`, `E₆` to the level-2 theta modular forms `H₂`, `H₃`, `H₄`.

We follow the same strategy as in the proof of `jacobi_identity`:
1. Build the theta-polynomials and prove they are SL₂(ℤ)-invariant using the explicit S/T action.
2. Compare them with `E₄`, `E₆` by showing the difference is a weight-`<12` cusp form, hence zero.

## Main statements
* `E₄_eq_thetaE4`
* `E₆_eq_thetaE6`
-/
namespace SpherePacking.ModularForms

open scoped MatrixGroups CongruenceSubgroup ModularForm Manifold Topology

open UpperHalfPlane hiding I
open Complex Filter TopologicalSpace
open ModularForm hiding E₄ E₆
open ModularGroup SlashAction MatrixGroups
open SlashInvariantFormClass ModularFormClass

local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

private lemma one_mem_strictPeriods_Gamma1 :
    (1 : ℝ) ∈ ((Γ(1) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma]

/-- A weight-`k` modular form on `Γ(1)` tends to its constant `q`-coefficient at `i∞`. -/
private lemma tendsto_modularForm_q_coeff_zero (k : ℤ) (f : ModularForm Γ(1) k)
    (h : (qExpansion (1 : ℝ) f).coeff 0 = 1) :
    Tendsto (fun z : ℍ => f z) atImInfty (𝓝 (1 : ℂ)) := by
  have hper : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := f) one_mem_strictPeriods_Gamma1
  have hcoeff :
      (qExpansion (1 : ℝ) f).coeff 0 = UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) :=
    qExpansion_coeff_zero (f := (f : ℍ → ℂ)) (h := (1 : ℝ)) (by positivity)
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f)
        (by positivity) one_mem_strictPeriods_Gamma1) hper
  have hval : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 1 := by simpa [hcoeff] using h
  simpa [hval] using modularForm_tendsto_atImInfty 1 f

/-! ## The `E₄` identity -/

/-- The theta-polynomial giving `E₄` (Blueprint equation (e4theta)). -/
@[expose] public noncomputable def thetaE4 : ℍ → ℂ :=
  H₂ ^ 2 + H₂ * H₄ + H₄ ^ 2

-- Helper: avoid `k1+k2` ambiguity in rewriting slashes of products.
private lemma mul_slash_SL2_2_2 (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[(4 : ℤ)] A = f ∣[(2 : ℤ)] A * g ∣[(2 : ℤ)] A := by
  simpa using (ModularForm.mul_slash_SL2 (k1 := 2) (k2 := 2) A f g)

lemma thetaE4_S_action : (thetaE4 ∣[(4 : ℤ)] S) = thetaE4 := by
  ext z
  simp [thetaE4, pow_two, add_slash, mul_slash_SL2_2_2, H₂_S_action, H₄_S_action]
  ring_nf

lemma thetaE4_T_action : (thetaE4 ∣[(4 : ℤ)] T) = thetaE4 := by
  ext z
  simp [thetaE4, pow_two, add_slash, mul_slash_SL2_2_2, H₂_T_action, H₄_T_action,
    jacobi_identity.symm]
  ring_nf

lemma thetaE4_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) thetaE4 := by
  have hH2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  simpa [thetaE4] using ((hH2.pow 2).add (hH2.mul hH4)).add (hH4.pow 2)

lemma thetaE4_tendsto_atImInfty : Tendsto thetaE4 atImInfty (𝓝 (1 : ℂ)) := by
  have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hsum : Tendsto (H₂ ^ 2 + H₂ * H₄) atImInfty (𝓝 (0 : ℂ)) := by
    simpa [Pi.add_apply, zero_mul] using (hH2.pow 2).add (by simpa [zero_mul] using hH2.mul hH4)
  simpa [thetaE4, Pi.add_apply, add_assoc, zero_add] using hsum.add (by simpa using hH4.pow 2)

/-- The Eisenstein series `E₄` tends to `1` at the cusp `∞`. -/
public lemma tendsto_E₄_atImInfty : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
  tendsto_modularForm_q_coeff_zero 4 E₄ E4_q_exp_zero

noncomputable def thetaE4_SIF : SlashInvariantForm (Γ 1) 4 where
  toFun := thetaE4
  slash_action_eq' := slashaction_generators_GL2R thetaE4 4 thetaE4_S_action thetaE4_T_action

/-- The theta-polynomial `thetaE4` agrees with the Eisenstein series `E₄`. -/
public theorem E₄_eq_thetaE4 : (E₄ : ℍ → ℂ) = thetaE4 := by
  -- Build `(E₄ - thetaE4)` as a weight-4 cusp form on `Γ(1)`, then apply
  -- the dimension-0 vanishing theorem for weight-4 cusp forms.
  let diffSIF : SlashInvariantForm (Γ 1) 4 := E₄.toSlashInvariantForm - thetaE4_SIF
  let diffCF : CuspForm (Γ 1) 4 :=
    cuspFormOfSIFTendstoZero diffSIF (E₄.holo'.sub thetaE4_MDifferentiable)
      (by simpa [diffSIF, sub_eq_add_neg] using
        tendsto_E₄_atImInfty.sub thetaE4_tendsto_atImInfty)
  have hzero : diffCF = 0 :=
    rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 4 (by norm_num)) diffCF
  funext z
  have h : diffSIF.toFun z = 0 := congrFun (congrArg (·.toFun) hzero) z
  simpa [diffSIF, sub_eq_zero] using h

/-! ## The `E₆` identity -/

/-- The theta-polynomial giving `E₆` (Blueprint equation (e6theta), second form). -/
@[expose] public noncomputable def thetaE6 : ℍ → ℂ :=
  (1 / 2 : ℂ) • ((H₂ + (2 : ℂ) • H₄) * (((2 : ℂ) • H₂ + H₄) * (H₄ - H₂)))

lemma thetaE6_S_action : (thetaE6 ∣[(6 : ℤ)] S) = thetaE6 := by
  ext z
  simp [thetaE6, add_slash, sub_eq_add_neg, SlashAction.neg_slash, SL_smul_slash,
    mul_slash_SL2_2_2, mul_slash_SL2_2_4, H₂_S_action, H₄_S_action, smul_eq_mul]
  ring_nf

lemma thetaE6_T_action : (thetaE6 ∣[(6 : ℤ)] T) = thetaE6 := by
  ext z
  simp [thetaE6, add_slash, sub_eq_add_neg, SlashAction.neg_slash, SL_smul_slash,
    mul_slash_SL2_2_2, mul_slash_SL2_2_4, H₂_T_action, H₄_T_action, jacobi_identity.symm,
    smul_eq_mul]
  ring_nf

lemma thetaE6_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) thetaE6 := by
  have hH2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂ := H₂_SIF_MDifferentiable
  have hH4 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄ := H₄_SIF_MDifferentiable
  simpa [thetaE6, mul_assoc] using
    (((hH2.add (hH4.const_smul (2 : ℂ))).mul
      (((hH2.const_smul (2 : ℂ)).add hH4).mul (hH4.sub hH2))).const_smul (1 / 2 : ℂ))

lemma thetaE6_tendsto_atImInfty : Tendsto thetaE6 atImInfty (𝓝 (1 : ℂ)) := by
  have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have h2 : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ)) := tendsto_const_nhds
  have h2H2 : Tendsto ((2 : ℂ) • H₂) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using h2.smul hH2
  have h2H4 : Tendsto ((2 : ℂ) • H₄) atImInfty (𝓝 (2 : ℂ)) := by
    simpa using h2.smul hH4
  have hA : Tendsto (H₂ + (2 : ℂ) • H₄) atImInfty (𝓝 (2 : ℂ)) := by
    simpa using hH2.add h2H4
  have hB : Tendsto ((2 : ℂ) • H₂ + H₄) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using h2H2.add hH4
  have hC : Tendsto (H₄ - H₂) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using hH4.sub hH2
  have hBC : Tendsto (((2 : ℂ) • H₂ + H₄) * (H₄ - H₂)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa [mul_assoc] using hB.mul hC
  have hmul :
      Tendsto ((H₂ + (2 : ℂ) • H₄) * (((2 : ℂ) • H₂ + H₄) * (H₄ - H₂))) atImInfty (𝓝 (2 : ℂ)) := by
    simpa [mul_assoc] using hA.mul hBC
  simpa [thetaE6, smul_eq_mul, mul_assoc] using (tendsto_const_nhds : Tendsto (fun _ : ℍ =>
    (1 / 2 : ℂ)) atImInfty (𝓝 (1 / 2 : ℂ))).smul hmul

/-- The Eisenstein series `E₆` tends to `1` at the cusp `∞`. -/
public lemma tendsto_E₆_atImInfty : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) :=
  tendsto_modularForm_q_coeff_zero 6 E₆ E6_q_exp_zero

noncomputable def thetaE6_SIF : SlashInvariantForm (Γ 1) 6 where
  toFun := thetaE6
  slash_action_eq' := slashaction_generators_GL2R thetaE6 6 thetaE6_S_action thetaE6_T_action

/-- The theta-polynomial `thetaE6` agrees with the Eisenstein series `E₆`. -/
public theorem E₆_eq_thetaE6 : (E₆ : ℍ → ℂ) = thetaE6 := by
  let diffSIF : SlashInvariantForm (Γ 1) 6 := E₆.toSlashInvariantForm - thetaE6_SIF
  let diffCF : CuspForm (Γ 1) 6 :=
    cuspFormOfSIFTendstoZero diffSIF (E₆.holo'.sub thetaE6_MDifferentiable)
      (by simpa [diffSIF, sub_eq_add_neg] using
        tendsto_E₆_atImInfty.sub thetaE6_tendsto_atImInfty)
  have hzero : diffCF = 0 :=
    rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 6 (by norm_num)) diffCF
  funext z
  have h : diffSIF.toFun z = 0 := congrFun (congrArg (·.toFun) hzero) z
  simpa [diffSIF, sub_eq_zero] using h

end SpherePacking.ModularForms

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

import SpherePacking.ModularForms.SlashActionAuxil

/-!
# Jacobi theta functions

Define Jacobi theta functions Θ₂, Θ₃, Θ₄ and their fourth powers H₂, H₃, H₄.
Prove that H₂, H₃, H₄ are modualar forms of weight 2 and level Γ(2).
Also Jacobi identity: Θ₂^4 + Θ₄^4 = Θ₃^4.
-/

open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix

open scoped UpperHalfPlane ModularForm MatrixGroups


/-- Define Θ₂, Θ₃, Θ₄ as series. -/
noncomputable def Θ₂ (τ : ℂ) : ℂ := ∑' n : ℤ, cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)
noncomputable def Θ₃ (τ : ℂ) : ℂ := ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ)
noncomputable def Θ₄ (τ : ℂ) : ℂ := ∑' n : ℤ, (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)
noncomputable def H₂ (τ : ℍ) : ℂ := (Θ₂ τ) ^ 4
noncomputable def H₃ (τ : ℍ) : ℂ := (Θ₃ τ) ^ 4
noncomputable def H₄ (τ : ℍ) : ℂ := (Θ₄ τ) ^ 4

/-- Theta functions as specializations of jacobiTheta₂ -/
theorem Θ₂_as_jacobiTheta₂ (τ : ℂ) (hτ : 0 < τ.im) :
    Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (-τ/2) τ := by
  simp_rw [Θ₂, jacobiTheta₂, jacobiTheta₂_term, ← smul_eq_mul (a := cexp _)]
  rw [← (Equiv.subRight 1).tsum_eq, ← tsum_const_smul]
  · simp_rw [Equiv.subRight_apply]
    apply tsum_congr
    intro b
    have : ((b - 1 : ℤ) : ℂ) + 1 / 2 = b - 1 / 2 := by
      push_cast
      nth_rw 1 [← add_halves 1]
      ring_nf
    rw [this, smul_eq_mul, ← Complex.exp_add]
    ring_nf
  · exact (summable_jacobiTheta₂_term_iff _ _).mpr hτ

theorem Θ₃_as_jacobiTheta₂ (τ : ℂ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, jacobiTheta₂, jacobiTheta₂_term, mul_zero, zero_add]

theorem Θ₄_as_jacobiTheta₂ (τ : ℂ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, jacobiTheta₂, jacobiTheta₂_term]
  apply tsum_congr
  intro b
  ring_nf
  rw [Complex.exp_add, ← exp_pi_mul_I, ← exp_int_mul, mul_comm (b : ℂ)]

/-- Slash action of various elements on H₂, H₃, H₄ -/
lemma H₂_negI_action : (H₂ ∣[(2 : ℤ)] negI) = H₂ := even_weight_negI_action H₂ (2: ℤ) even_two
lemma H₃_negI_action : (H₃ ∣[(2 : ℤ)] negI) = H₃ := even_weight_negI_action H₃ (2: ℤ) even_two
lemma H₄_negI_action : (H₄ ∣[(2 : ℤ)] negI) = H₄ := even_weight_negI_action H₄ (2: ℤ) even_two

lemma H₂_T_action : (H₂ ∣[(2 : ℤ)] T) = -H₂ := by sorry
lemma H₃_T_action : (H₃ ∣[(2 : ℤ)] T) = H₄ := by sorry
lemma H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃ := by sorry

/-- Use α = T * T -/
lemma H₂_α_action : (H₂ ∣[(2 : ℤ)] α) = H₂ := calc
  (H₂ ∣[(2 : ℤ)] α) = (H₂ ∣[(2 : ℤ)] (T * T)) := sorry
  _ = ((H₂ ∣[(2 : ℤ)] T)∣[(2 : ℤ)] T) := sorry
  _ = ((-H₂) ∣[(2 : ℤ)] T) := by rw [H₂_T_action]
  _ = (-H₂ ∣[(2 : ℤ)] T) := sorry
  _ = H₂ := by rw [H₂_T_action, neg_neg]

lemma H₃_α_action : (H₃ ∣[(2 : ℤ)] α) = H₃ := calc
  (H₃ ∣[(2 : ℤ)] α) = (H₃ ∣[(2 : ℤ)] (T * T)) := sorry
  _ = ((H₃ ∣[(2 : ℤ)] T)∣[(2 : ℤ)] T) := sorry
  _ = (H₄ ∣[(2 : ℤ)] T) := by rw [H₃_T_action]
  _ = H₃ := H₄_T_action

lemma H₄_α_action : (H₄ ∣[(2 : ℤ)] α) = H₄ := calc
  (H₄ ∣[(2 : ℤ)] α) = (H₄ ∣[(2 : ℤ)] (T * T)) := sorry
  _ = ((H₄ ∣[(2 : ℤ)] T)∣[(2 : ℤ)] T) := sorry
  _ = (H₃ ∣[(2 : ℤ)] T) := by rw [H₄_T_action]
  _ = H₄ := H₃_T_action

/-- Use jacobiTheta₂_functional_equation -/
lemma H₂_S_action : (H₂ ∣[(2 : ℤ)] S) = - H₄ := by sorry
lemma H₃_S_action : (H₃ ∣[(2 : ℤ)] S) = - H₃ := by sorry
lemma H₄_S_action : (H₄ ∣[(2 : ℤ)] S) = - H₂ := by sorry

/-- Use β = -S * α^(-1) * S -/
lemma H₂_β_action : (H₂ ∣[(2 : ℤ)] β) = H₂ := calc
  (H₂ ∣[(2 : ℤ)] β) = (H₂ ∣[(2 : ℤ)] (negI * S * α^(-1 : ℤ) * S)) := sorry
  _ = (((H₂ ∣[(2 : ℤ)] negI) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := sorry
  _ = ((H₂ ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := by rw [H₂_negI_action]
  _ = ((-H₄) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := by rw [H₂_S_action]
  _ = (- H₄ ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := sorry
  _ = - H₄ ∣[(2 : ℤ)] S := sorry
  _ = H₂ := by rw [H₄_S_action, neg_neg]

lemma H₃_β_action : (H₃ ∣[(2 : ℤ)] β) = H₃ := calc
  (H₃ ∣[(2 : ℤ)] β) = (H₃ ∣[(2 : ℤ)] (negI * S * α^(-1 : ℤ) * S)) := sorry
  _ = (((H₃ ∣[(2 : ℤ)] negI) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := sorry
  _ = ((H₃ ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := by rw [H₃_negI_action]
  _ = ((-H₃) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := by rw [H₃_S_action]
  _ = (- H₃ ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := sorry
  _ = - H₃ ∣[(2 : ℤ)] S := sorry
  _ = H₃ := by rw [H₃_S_action, neg_neg]

lemma H₄_β_action : (H₄ ∣[(2 : ℤ)] β) = H₄ := calc
  (H₄ ∣[(2 : ℤ)] β) = (H₄ ∣[(2 : ℤ)] (negI * S * α^(-1 : ℤ) * S)) := sorry
  _ = (((H₄ ∣[(2 : ℤ)] negI) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := sorry
  _ = ((H₄ ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := by rw [H₄_negI_action]
  _ = ((-H₂) ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := by rw [H₄_S_action]
  _ = (- H₂ ∣[(2 : ℤ)] α^(-1 : ℤ)) ∣[(2 : ℤ)] S := sorry
  _ = - H₂ ∣[(2 : ℤ)] S := sorry
  _ = H₄ := by rw [H₂_S_action, neg_neg]

/-- H₂, H₃, H₄ are modular forms of weight 2 and level Γ(2) -/
noncomputable def H₂_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 2) 2 where
  toFun := H₂
  slash_action_eq' := slashaction_generators_Γ2 H₂ (2 : ℤ) H₂_α_action H₂_β_action H₂_negI_action

noncomputable def H₃_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 2) 2 where
  toFun := H₃
  slash_action_eq' := slashaction_generators_Γ2 H₃ (2 : ℤ) H₃_α_action H₃_β_action H₃_negI_action

noncomputable def H₄_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 2) 2 where
  toFun := H₄
  slash_action_eq' := slashaction_generators_Γ2 H₄ (2 : ℤ) H₄_α_action H₄_β_action H₄_negI_action


open UpperHalfPlane

noncomputable def H₂_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂_SIF := by sorry

noncomputable def H₃_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₃_SIF := by sorry

noncomputable def H₄_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₄_SIF := by sorry

theorem isBoundedAtImInfty_H₂_SIF
    (A : SL(2, ℤ)) : IsBoundedAtImInfty (H₂_SIF.toFun ∣[(2:ℤ)] A) := by sorry

theorem isBoundedAtImInfty_H₃_SIF
    (A : SL(2, ℤ)) : IsBoundedAtImInfty (H₃_SIF.toFun ∣[(2:ℤ)] A) := by sorry

theorem isBoundedAtImInfty_H₄_SIF
    (A : SL(2, ℤ)) : IsBoundedAtImInfty (H₄_SIF.toFun ∣[(2:ℤ)] A) := by sorry


noncomputable def H₂_MF : ModularForm (CongruenceSubgroup.Gamma 2) 2 := {
  H₂_SIF with
  holo' := H₂_SIF_MDifferentiable
  bdd_at_infty' := isBoundedAtImInfty_H₂_SIF
}

noncomputable def H₃_MF : ModularForm (CongruenceSubgroup.Gamma 2) 2 := {
  H₃_SIF with
  holo' := H₃_SIF_MDifferentiable
  bdd_at_infty' := isBoundedAtImInfty_H₃_SIF
}

noncomputable def H₄_MF : ModularForm (CongruenceSubgroup.Gamma 2) 2 := {
  H₄_SIF with
  holo' := H₄_SIF_MDifferentiable
  bdd_at_infty' := isBoundedAtImInfty_H₄_SIF
}

/-- Jacobi identity -/
theorem jacobi_identity (τ : ℍ) : (Θ₂ τ) ^ 4 + (Θ₄ τ) ^ 4 = (Θ₃ τ) ^ 4 := by
  rw [← H₂, ← H₃, ← H₄]
  -- prove that the dimension of M₂(Γ(2)) is 2. Compare the first two q-coefficients.
  sorry

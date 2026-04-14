module

public import SpherePacking.ModularForms.JacobiTheta.Basic
public import SpherePacking.ForMathlib.SlashActions

@[expose] public section

/-!
# Jacobi theta differentiability

This file contains the `MDiff` results for the Jacobi theta functions and the resulting modular
form constructions `H₂_MF`, `H₃_MF`, and `H₄_MF`.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

section H_MDifferentiable

@[fun_prop]
lemma H₃_MDifferentiable : MDiff H₃ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hθ : DifferentiableOn ℂ (fun z => jacobiTheta₂ (0 : ℂ) z) {z | 0 < z.im} := by
    intro x hx
    exact (differentiableAt_jacobiTheta₂_snd 0 (by simpa using hx)).differentiableWithinAt
  have hθ4 : DifferentiableOn ℂ (fun z => (jacobiTheta₂ (0 : ℂ) z) ^ 4) {z | 0 < z.im} := by
    apply DifferentiableOn.pow
    intro x hx
    exact hθ x hx
  exact hθ4.congr fun _ hz => by
    simp [Function.comp, H₃, Θ₃_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]

@[fun_prop]
lemma H₄_MDifferentiable : MDiff H₄ := by
  simpa [H₃_T_action] using H₃_MDifferentiable.slash_SL2 (k := 2) T

@[fun_prop]
lemma H₂_MDifferentiable : MDiff H₂ := by
  have hneg : MDiff (-H₂) := by
    simpa [H₄_S_action] using H₄_MDifferentiable.slash_SL2 (k := 2) S
  simpa using hneg.neg

lemma H₂_SIF_MDifferentiable : MDiff H₂_SIF := by
  simpa [H₂_SIF, SlashInvariantForm.coe_mk] using H₂_MDifferentiable

lemma H₃_SIF_MDifferentiable : MDiff H₃_SIF := by
  simpa [H₃_SIF, SlashInvariantForm.coe_mk] using H₃_MDifferentiable

lemma H₄_SIF_MDifferentiable : MDiff H₄_SIF := by
  simpa [H₄_SIF, SlashInvariantForm.coe_mk] using H₄_MDifferentiable

end H_MDifferentiable

noncomputable def H₂_MF : ModularForm (Γ 2) 2 := {
  H₂_SIF with
  holo' := H₂_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₂_slash
}

noncomputable def H₃_MF : ModularForm (Γ 2) 2 := {
  H₃_SIF with
  holo' := H₃_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₃_slash
}

noncomputable def H₄_MF : ModularForm (Γ 2) 2 := {
  H₄_SIF with
  holo' := H₄_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₄_slash
}

@[simp] lemma H₂_MF_coe : (H₂_MF : ℍ → ℂ) = H₂ := rfl

@[simp] lemma H₃_MF_coe : (H₃_MF : ℍ → ℂ) = H₃ := rfl

@[simp] lemma H₄_MF_coe : (H₄_MF : ℍ → ℂ) = H₄ := rfl

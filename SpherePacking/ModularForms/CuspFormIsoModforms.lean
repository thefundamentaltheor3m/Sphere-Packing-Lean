module
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.QExpansionLemmas


/-!
# Cusp forms vs. modular forms

This file transports mathlib's `CuspForm.discriminantEquiv` (the equivalence between cusp forms
of weight `k` and modular forms of weight `k - 12` for `𝒮ℒ`, given by division by `Δ`) to the
project's `Γ(1)` setting and uses mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` to derive
the level-one weight `< 12` vanishing statements.
-/

open scoped MatrixGroups CongruenceSubgroup

open ModularForm UpperHalfPlane Complex

noncomputable section

namespace CongruenceSubgroup

/-- Type-level transport `CuspForm Γ(1) k ≃ CuspForm 𝒮ℒ k` along `Gamma_one_coe_eq_SL`. -/
noncomputable def cuspFormCopyToSL (k : ℤ) : CuspForm Γ(1) k ≃ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun f := f.copy (⇑f) rfl Gamma_one_coe_eq_SL.symm
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun f := f.copy (⇑f) rfl Gamma_one_coe_eq_SL
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- Type-level transport `ModularForm Γ(1) k ≃ ModularForm 𝒮ℒ k` along `Gamma_one_coe_eq_SL`. -/
noncomputable def modularFormCopyToSL (k : ℤ) : ModularForm Γ(1) k ≃ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun f := f.copy (⇑f) rfl Gamma_one_coe_eq_SL.symm
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun f := f.copy (⇑f) rfl Gamma_one_coe_eq_SL
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

end CongruenceSubgroup

/-- Division by the discriminant yields a linear equivalence between cusp forms of weight `k` and
modular forms of weight `k - 12` (transport of mathlib's `CuspForm.discriminantEquiv` through
`Gamma_one_coe_eq_SL`). -/
public def CuspForms_iso_Modforms (k : ℤ) :
    CuspForm Γ(1) k ≃ₗ[ℂ] ModularForm Γ(1) (k - 12) :=
  ((CongruenceSubgroup.cuspFormCopyToSL k).trans CuspForm.discriminantEquiv).trans
    (CongruenceSubgroup.modularFormCopyToSL (k - 12)).symm

/-- Transport mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` from `𝒮ℒ` to `Γ(1)`. -/
public lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) :
    Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  rw [(CongruenceSubgroup.cuspFormCopyToSL k).rank_eq]
  exact CuspForm.rank_eq_zero_of_weight_lt_twelve hk

/-- A modular form of level `Γ(1)` and weight `< 12` which is a cusp form is identically zero. -/
public lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  obtain ⟨g, hg⟩ := hf
  let g' : CuspForm 𝒮ℒ k := CongruenceSubgroup.cuspFormCopyToSL k g
  have hg'_zero : g' = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) g'
  ext z
  rw [← hg]; simpa [g', CongruenceSubgroup.cuspFormCopyToSL] using DFunLike.congr_fun hg'_zero z

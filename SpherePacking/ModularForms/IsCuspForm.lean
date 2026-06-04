/-
Copyright (c) 2025 Sphere Packing Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Lean contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

public import SpherePacking.ForMathlib.Cusps
public import SpherePacking.ModularForms.QExpansionLemmas

/-!
# Cusp forms

Aliases mathlib's `ModularForm.IsCuspForm` as `IsCuspForm`, and provides a `Γ(1)`-flavoured
constructor `cuspFormOfSIFTendstoZero` together with the level-one characterisation
`IsCuspForm_iff_coeffZero_eq_zero`.
-/

open scoped MatrixGroups CongruenceSubgroup Topology

open ModularForm UpperHalfPlane Set Filter Function Complex Manifold
open SlashInvariantFormClass ModularFormClass

noncomputable section Definitions

variable {k : ℤ} {Γ : Subgroup SL(2, ℤ)}

/-- A modular form is a cusp form if it lies in `cuspFormSubmodule` (alias for
`ModularForm.IsCuspForm`). -/
@[expose] public abbrev IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f.IsCuspForm

/-- Build a `CuspForm` from a `SlashInvariantForm` that is holomorphic and tends to 0. -/
@[expose] public noncomputable def cuspFormOfSIFTendstoZero {k : ℤ}
    (f_SIF : SlashInvariantForm Γ(1) k)
    (h_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f_SIF.toFun)
    (h_zero : Tendsto f_SIF.toFun atImInfty (𝓝 0)) : CuspForm Γ(1) k where
  toSlashInvariantForm := f_SIF
  holo' := h_mdiff
  zero_at_cusps' hc := by
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    rw [f_SIF.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩]
    exact h_zero

/-- For level one, `IsCuspForm` is equivalent to vanishing of the constant `q`-coefficient.
Transported from mathlib's `ModularForm.isCuspForm_iff_coeffZero_eq_zero`. -/
public lemma IsCuspForm_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  let f' : ModularForm 𝒮ℒ k := f.copy (⇑f) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  rw [show qExpansion (1 : ℝ) (⇑f) = qExpansion (1 : ℝ) (⇑f') from rfl,
    ← ModularForm.isCuspForm_iff_coeffZero_eq_zero (f := f')]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨g.copy (⇑f) (by ext z; simpa [f'] using DFunLike.congr_fun hg.symm z)
      CongruenceSubgroup.Gamma_one_coe_eq_SL.symm, by ext z; rfl⟩,
    fun ⟨g, hg⟩ ↦ ⟨g.copy (⇑f) (by ext z; simpa [f'] using DFunLike.congr_fun hg.symm z)
      CongruenceSubgroup.Gamma_one_coe_eq_SL, by ext z; rfl⟩⟩

end Definitions

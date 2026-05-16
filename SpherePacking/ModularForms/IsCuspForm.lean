module
public import SpherePacking.ModularForms.QExpansionLemmas

public import SpherePacking.ForMathlib.Cusps
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule


/-!
# Cusp forms as a submodule

This file aliases mathlib's `ModularForm.IsCuspForm`, `ModularForm.cuspFormSubmodule`, and
`CuspForm.toModularFormₗ` under project-local names for `Γ : Subgroup SL(2, ℤ)`, and provides a
`Γ(1)`-flavoured constructor `cuspFormOfSIFTendstoZero` together with the level-one
characterisation `IsCuspForm_iff_coeffZero_eq_zero`.
-/

open scoped MatrixGroups CongruenceSubgroup Topology

open ModularForm UpperHalfPlane Set Filter Function Complex Manifold
open SlashInvariantFormClass ModularFormClass

noncomputable section Definitions

variable {k : ℤ} {Γ : Subgroup SL(2, ℤ)}

/-- Coerce a cusp form to a modular form (alias for `CuspForm.toModularFormₗ` as a function). -/
@[expose] public abbrev ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) :
    ModularForm Γ k := CuspForm.toModularFormₗ f

/-- The linear inclusion of cusp forms into modular forms (alias for `CuspForm.toModularFormₗ`). -/
@[expose] public abbrev CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    CuspForm Γ k →ₗ[ℂ] ModularForm Γ k := CuspForm.toModularFormₗ

/-- The submodule of modular forms coming from cusp forms (alias for
`ModularForm.cuspFormSubmodule`). -/
@[expose] public abbrev CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    Submodule ℂ (ModularForm Γ k) := ModularForm.cuspFormSubmodule Γ k

/-- A modular form is a cusp form if it lies in `CuspFormSubmodule` (alias for
`ModularForm.IsCuspForm`). -/
@[expose] public abbrev IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f.IsCuspForm

/-- Extract a cusp form from a proof of `IsCuspForm`. -/
@[expose] public def IsCuspForm_to_CuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : ModularForm Γ k) (hf : IsCuspForm Γ k f) : CuspForm Γ k := hf.choose

/-- The extracted cusp form has the same underlying function as the original modular form. -/
@[simp] public lemma CuspForm_to_ModularForm_Fun_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : ModularForm Γ k) (hf : IsCuspForm Γ k f) :
    (IsCuspForm_to_CuspForm Γ k f hf).toFun = f.toFun :=
  congrArg DFunLike.coe hf.choose_spec

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

/-- Build a `CuspForm Γ(1) k` from a modular form whose q-expansion has vanishing constant term.
Defined by transporting `ModularForm.toCuspForm` along `Gamma_one_coe_eq_SL`. -/
@[expose] public noncomputable def cuspFormOfCoeffZero {k : ℤ} (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm Γ(1) k :=
  (ModularForm.toCuspForm (f.copy (⇑f) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm)
      (by simpa using h)).copy (⇑f) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL

/-- For level one, `IsCuspForm` is equivalent to vanishing of the constant `q`-coefficient.
Transported from mathlib's `ModularForm.isCuspForm_iff_coeffZero_eq_zero`. -/
public lemma IsCuspForm_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  let f' : ModularForm 𝒮ℒ k := f.copy (⇑f) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  have hQ : qExpansion 1 (⇑f' : ℍ → ℂ) = qExpansion 1 (⇑f : ℍ → ℂ) := rfl
  rw [show IsCuspForm Γ(1) k f ↔ f'.IsCuspForm from ?_,
    ModularForm.isCuspForm_iff_coeffZero_eq_zero, hQ]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · refine ⟨g.copy (⇑f) (by ext z; simpa [f'] using (DFunLike.congr_fun hg z).symm)
      CongruenceSubgroup.Gamma_one_coe_eq_SL.symm, ?_⟩
    ext z; rfl
  · refine ⟨g.copy (⇑f) (by ext z; simpa [f'] using (DFunLike.congr_fun hg z).symm)
      CongruenceSubgroup.Gamma_one_coe_eq_SL, ?_⟩
    ext z; rfl

end Definitions

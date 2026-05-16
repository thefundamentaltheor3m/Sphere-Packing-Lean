module
public import SpherePacking.ModularForms.QExpansionLemmas

public import SpherePacking.ForMathlib.Cusps


/-!
# Cusp forms as a submodule

This file treats cusp forms as a submodule of modular forms via the linear map
`CuspForm_to_ModularForm`. It also defines the predicate `IsCuspForm` for modular forms and
records a characterization for level one in terms of the constant `q`-coefficient.

## Main declarations
* `ModForm_mk`, `CuspForm_to_ModularForm`, `CuspFormSubmodule`
* `IsCuspForm`, `IsCuspForm_to_CuspForm`
* `IsCuspForm_iff_coeffZero_eq_zero`
-/

open scoped MatrixGroups CongruenceSubgroup Topology

open ModularForm UpperHalfPlane Set Filter Function Complex Manifold
open SlashInvariantFormClass ModularFormClass

noncomputable section Definitions

variable {α ι : Type*}

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

/-!
## Cusp forms as a range submodule
-/

/-- Coerce a cusp form to a modular form by forgetting the vanishing-at-cusps data. -/
@[expose] public def ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) :
    ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_cusps' := fun hc ↦ bdd_at_cusps f hc

/-- The linear map sending a cusp form to the underlying modular form. -/
@[expose] public def CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    CuspForm Γ k →ₗ[ℂ] ModularForm Γ k
  where
  toFun := ModForm_mk Γ k
  map_add' := by intro f g; rfl
  map_smul' := by intro m f; rfl

/-- The submodule of modular forms coming from cusp forms.

This is the range of `CuspForm_to_ModularForm`.
-/
@[expose] public def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm_to_ModularForm Γ k)

/-- `CuspFormSubmodule` is a function space `ℍ → ℂ` by coercion. -/
public instance (priority := 100) CuspFormSubmodule.funLike :
    FunLike (CuspFormSubmodule Γ k) ℍ ℂ where
  coe f := f.1.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

/-- The range submodule inherits a `CuspFormClass` structure. -/
public instance (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspFormClass (CuspFormSubmodule Γ k) Γ k where
  slash_action_eq f := f.1.slash_action_eq'
  holo f := f.1.holo'
  zero_at_cusps := by
    rintro ⟨_, ⟨g, rfl⟩⟩ c hc
    simpa [CuspForm_to_ModularForm, ModForm_mk] using g.zero_at_cusps' hc

/-!
## The predicate `IsCuspForm`
-/

/-- A modular form is a cusp form if it lies in `CuspFormSubmodule`. -/
@[expose] public def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f ∈ CuspFormSubmodule Γ k

/-- Extract a cusp form from a proof of `IsCuspForm`. -/
@[expose] public def IsCuspForm_to_CuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : CuspForm Γ k := by
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  exact hf.choose

/-- The extracted cusp form has the same underlying function as the original modular form. -/
@[simp] public lemma CuspForm_to_ModularForm_Fun_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toFun =
    f.toFun := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  exact congrArg DFunLike.coe hf.choose_spec

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

private lemma isZeroAtImInfty_of_coeffZero {k : ℤ}
    (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) :
    IsZeroAtImInfty f := by
  rw [qExpansion_coeff] at h
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
  have := modform_tendto_ndhs_zero f 1
  simp only [Nat.cast_one, h] at this
  have := (this.comp (Function.Periodic.qParam_tendsto (h := 1) Real.zero_lt_one)).comp
    tendsto_coe_atImInfty
  rw [IsZeroAtImInfty, ZeroAtFilter]
  apply this.congr'
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨⊤, univ_mem, fun y _ => ?_⟩
  simp only [comp_apply]
  obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period (h := 1)
    (Ne.symm (zero_ne_one' ℝ)) y
  have := (periodic_comp_ofComplex (h := 1) f (by simp)).int_mul m y
  simp only [comp_apply, ofReal_one, mul_one, ofComplex_apply] at *
  rwa [hm]

/-- Build a `CuspForm` from a modular form whose q-expansion has vanishing constant term. -/
@[expose] public noncomputable def cuspFormOfCoeffZero {k : ℤ}
    (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm Γ(1) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' hc := by
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    rw [f.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩]
    exact isZeroAtImInfty_of_coeffZero f h

/-- For level one, `IsCuspForm` is equivalent to vanishing of the constant `q`-coefficient. -/
public lemma IsCuspForm_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  constructor
  · intro h
    rw [qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at h
    obtain ⟨g, hg⟩ := h
    have := CuspFormClass.cuspFunction_apply_zero (h := 1) g (by positivity) (by simp)
    simp only [CuspForm_to_ModularForm, ModForm_mk, LinearMap.coe_mk, AddHom.coe_mk] at hg
    rw [← hg]
    exact this
  · intro h
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range]
    exact ⟨cuspFormOfCoeffZero f h, by ext; rfl⟩

end Definitions

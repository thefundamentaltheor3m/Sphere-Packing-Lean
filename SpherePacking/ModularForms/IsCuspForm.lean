module
public import SpherePacking.ModularForms.qExpansion_lems

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

open scoped MatrixGroups CongruenceSubgroup

open ModularForm UpperHalfPlane Set Filter Function
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

lemma ModForm_mk_inj (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) (hf : f ≠ 0) :
  ModForm_mk _ _ f ≠ 0 := by
  rw [@DFunLike.ne_iff] at *
  obtain ⟨x, hx⟩ := hf
  use x
  simp only [CuspForm.zero_apply, ne_eq, ModForm_mk, zero_apply] at *
  exact hx

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

def CuspForm_iso_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    CuspForm Γ k ≃ₗ[ℂ] CuspFormSubmodule Γ k := by
  apply LinearEquiv.ofInjective
  rw [@injective_iff_map_eq_zero]
  intro f hf
  rw [CuspForm_to_ModularForm] at hf
  simp only [ModForm_mk, LinearMap.coe_mk, AddHom.coe_mk] at hf
  ext z
  have := congr_fun (congr_arg (fun x => x.toFun) hf) z
  simpa using this

lemma mem_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : f ∈ CuspFormSubmodule Γ k) :
    ∃ g : CuspForm Γ k, f = CuspForm_to_ModularForm Γ k g := by
  rw [CuspFormSubmodule, LinearMap.mem_range] at hf
  aesop

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

lemma CuspForm_to_ModularForm_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toSlashInvariantForm =
    f.toSlashInvariantForm := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp_rw [CuspForm_to_ModularForm] at hg
  have hgg := congr_arg (fun x ↦ x.toSlashInvariantForm) hg
  simp only [ModForm_mk, LinearMap.coe_mk, AddHom.coe_mk] at *
  exact hgg

/-- The extracted cusp form has the same underlying function as the original modular form. -/
@[simp] public lemma CuspForm_to_ModularForm_Fun_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toFun =
    f.toFun := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  simpa [CuspForm_to_ModularForm, ModForm_mk] using congrArg (fun x ↦ x.toFun) hf.choose_spec

/-- For level one, `IsCuspForm` is equivalent to vanishing of the constant `q`-coefficient. -/
public lemma IsCuspForm_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  constructor
  · intro h
    rw [qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    rcases (by simpa [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] using h) with ⟨g, rfl⟩
    have := CuspFormClass.cuspFunction_apply_zero (h := 1) g (by positivity) (by simp)
    simpa [CuspForm_to_ModularForm, ModForm_mk]
  · intro h
    rw [IsCuspForm]
    rw [CuspFormSubmodule, LinearMap.mem_range]
    use ⟨f.toSlashInvariantForm , f.holo', ?_⟩
    · simp only [CuspForm_to_ModularForm]; rfl
    · intro c hc
      apply zero_at_cusps_of_zero_at_infty hc
      intro A ⟨A', hA'⟩
      have hf := f.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩
      simp only [ SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe] at *
      rw [hf]
      rw [qExpansion_coeff] at h
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
      have := modform_tendto_ndhs_zero f 1
      simp only [Nat.cast_one, comp_apply, h] at this
      have hgg2 := this.comp (Function.Periodic.qParam_tendsto (h := 1) ( Real.zero_lt_one))
      have hgg3 := hgg2.comp tendsto_coe_atImInfty
      rw [IsZeroAtImInfty, ZeroAtFilter]
      refine hgg3.congr' <| Filter.Eventually.of_forall fun y => ?_
      have h5 := periodic_comp_ofComplex (h := 1) f (by simp)
      rcases Function.Periodic.qParam_left_inv_mod_period (h := 1) (Ne.symm (zero_ne_one' ℝ)) y with
        ⟨m, hm⟩
      simpa [Periodic, Complex.ofReal_one, ofComplex_apply, Function.comp, hm] using
        (Function.Periodic.int_mul h5 m y)

end Definitions

lemma CuspFormSubmodule_mem_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    f ∈ CuspFormSubmodule Γ(1) k ↔ (qExpansion 1 f).coeff 0 = 0 := by
  have := IsCuspForm_iff_coeffZero_eq_zero k f
  apply this

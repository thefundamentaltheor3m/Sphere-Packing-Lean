import Mathlib.Analysis.CStarAlgebra.Module.Defs
import SpherePacking.ModularForms.qExpansion_lems

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


noncomputable section Definitions



variable {α ι : Type*}

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

def ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_infty' A := (f.zero_at_infty' A).boundedAtFilter

lemma ModForm_mk_inj (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) (hf : f ≠ 0) :
  ModForm_mk _ _ f ≠ 0 := by
  rw [@DFunLike.ne_iff] at *
  obtain ⟨x, hx⟩ := hf
  use x
  simp [ModForm_mk] at *
  exact hx

def CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k
  where
  toFun f := ModForm_mk Γ k f
  map_add' := by
    intro f g
    simp only [ModForm_mk, CuspForm.coe_add]
    rfl
  map_smul' := by
    intro m f
    simp only [ModForm_mk, CuspForm.coe_smul, RingHom.id_apply]
    rfl

def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm_to_ModularForm Γ k)

def CuspForm_iso_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    CuspForm Γ k ≃ₗ[ℂ] CuspFormSubmodule Γ k := by
  apply LinearEquiv.ofInjective
  rw [@injective_iff_map_eq_zero]
  intro f hf
  rw [CuspForm_to_ModularForm] at hf
  simp [ModForm_mk] at hf
  ext z
  have := congr_fun (congr_arg (fun x => x.toFun) hf) z
  simpa using this

lemma mem_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : f ∈ CuspFormSubmodule Γ k) :
    ∃ g : CuspForm Γ k, f = CuspForm_to_ModularForm Γ k g := by
  rw [CuspFormSubmodule, LinearMap.mem_range] at hf
  aesop

instance (priority := 100) CuspFormSubmodule.funLike : FunLike (CuspFormSubmodule Γ k) ℍ ℂ where
  coe f := f.1.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspFormClass (CuspFormSubmodule Γ k) Γ k where
  slash_action_eq f := f.1.slash_action_eq'
  holo f := f.1.holo'
  zero_at_infty f := by
    have hf := f.2
    have := mem_CuspFormSubmodule Γ k f hf
    obtain ⟨g, hg⟩ := this
    convert g.zero_at_infty'
    ext y
    aesop

def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f ∈ CuspFormSubmodule Γ k

def IsCuspForm_to_CuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
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
  simp [ModForm_mk] at *
  exact hgg

lemma CuspForm_to_ModularForm_Fun_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toFun =
    f.toFun := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp_rw [CuspForm_to_ModularForm] at hg
  have hgg := congr_arg (fun x ↦ x.toFun) hg
  simp [ModForm_mk] at *
  exact hgg


lemma IsCuspForm_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  constructor
  · intro h
    rw [qExpansion_coeff]
    simp
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at h
    obtain ⟨g, hg⟩ := h
    have := CuspFormClass.cuspFunction_apply_zero 1 g
    simp [CuspForm_to_ModularForm, ModForm_mk] at hg
    rw [← hg]
    exact this
  · intro h
    rw [IsCuspForm]
    rw [CuspFormSubmodule, LinearMap.mem_range]
    use ⟨f.toSlashInvariantForm , f.holo', ?_⟩
    · simp only [CuspForm_to_ModularForm, ModForm_mk]
      rfl
    · intro A
      have hf := f.slash_action_eq' A (CongruenceSubgroup.mem_Gamma_one A)
      simp only [ SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, SL_slash] at *
      rw [hf]
      rw [qExpansion_coeff] at h
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
      have := modform_tendto_ndhs_zero f 1
      rw [h] at this
      have hgg : (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (1 : ℕ) x)) = ((⇑f ∘ ↑ofComplex) ∘
        (Periodic.invQParam (1 : ℕ))) := by
        rfl
      rw [hgg] at this
      have hgg2 := this.comp (Function.Periodic.qParam_tendsto (h := 1) ( Real.zero_lt_one))
      have hgg3 := hgg2.comp tendsto_coe_atImInfty
      rw [IsZeroAtImInfty, ZeroAtFilter]
      apply hgg3.congr'
      rw [Filter.eventuallyEq_iff_exists_mem]
      use ⊤
      simp only [top_eq_univ, univ_mem, Nat.cast_one, eqOn_univ, true_and]
      ext y
      simp only [comp_apply]
      have h5 := periodic_comp_ofComplex 1 f
      have := Function.Periodic.qParam_left_inv_mod_period (h := 1) (Ne.symm (zero_ne_one' ℝ)) y
      obtain ⟨m, hm⟩ := this
      have h6 := Function.Periodic.int_mul h5 m y
      simp only [Nat.cast_one, comp_apply, Periodic, ofReal_one, mul_one, ofComplex_apply] at *
      rw [← hm] at h6
      exact h6


lemma CuspFormSubmodule_mem_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    f ∈ CuspFormSubmodule Γ(1) k ↔ (qExpansion 1 f).coeff 0 = 0 := by
  have := IsCuspForm_iff_coeffZero_eq_zero k f
  apply this

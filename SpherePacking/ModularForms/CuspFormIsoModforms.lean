module
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.QExpansionLemmas


/-!
# Cusp forms vs. modular forms

This file builds the linear equivalence `CuspForms_iso_Modforms : CuspForm Γ(1) k ≃ₗ ModularForm
Γ(1) (k - 12)` (via multiplication/division by `Δ`) and uses mathlib's
`CuspForm.rank_eq_zero_of_weight_lt_twelve` (transported through `Gamma_one_coe_eq_SL`) to derive
the level-one weight `< 12` vanishing statements.
-/

open scoped MatrixGroups CongruenceSubgroup

open ModularForm UpperHalfPlane Complex

noncomputable section

def mul_Delta_map (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    ModularForm (CongruenceSubgroup.Gamma 1) k :=
  ModularForm.mcast (by ring) (f.mul (ModForm_mk _ 12 Delta))

lemma mul_Delta_map_eq_mul (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    ((mul_Delta_map k f) : ℍ → ℂ) = (f.mul (ModForm_mk _ 12 Delta)) := by rfl

lemma mul_Delta_IsCuspForm (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    IsCuspForm (CongruenceSubgroup.Gamma 1) k (mul_Delta_map k f) := by
  rw [IsCuspForm_iff_coeffZero_eq_zero, qExpansion_ext2 _ _ (mul_Delta_map_eq_mul k f)]
  rw [show (qExpansion (1 : ℝ) ((f.mul (ModForm_mk Γ(1) 12 Delta) : ℍ → ℂ))).coeff 0 =
      (qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff 0 *
        (qExpansion (1 : ℝ) ((ModForm_mk Γ(1) 12 Delta : ℍ → ℂ))).coeff 0 by
    simpa [PowerSeries.coeff_mul] using
      congrArg (fun p : PowerSeries ℂ => p.coeff 0)
        (qExpansion_mul_coeff (n := 1) (a := k - 12) (b := 12) f (ModForm_mk Γ(1) 12 Delta))]
  have hDelta0 :
      (qExpansion (1 : ℝ) ((ModForm_mk Γ(1) 12 Delta : ℍ → ℂ))).coeff 0 = 0 :=
    (IsCuspForm_iff_coeffZero_eq_zero (k := 12) (f := ModForm_mk Γ(1) 12 Delta)).1 (by
      exact ⟨Delta, rfl⟩)
  simp [hDelta0]

def Modform_mul_Delta' (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    CuspForm (CongruenceSubgroup.Gamma 1) k :=
  IsCuspForm_to_CuspForm _ k (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)

lemma Modform_mul_Delta_apply (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12))
    (z : ℍ) : (Modform_mul_Delta' k f) z = f z * Delta z := by
  simpa [Modform_mul_Delta'] using congrFun (CuspForm_to_ModularForm_Fun_coe _ _ _ _) z

/-- Division by the discriminant yields a linear equivalence between cusp forms of weight `k` and
modular forms of weight `k - 12`. -/
public def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
  toFun f := CuspForm_div_Discriminant k f
  map_add' a b := CuspForm_div_Discriminant_Add k a b
  map_smul' := by
    intro m a
    ext z
    simp [CuspForm_div_Discriminant_apply, mul_div_assoc]
  invFun := Modform_mul_Delta' k
  left_inv := by
    intro f
    ext z
    simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply, Delta_apply, Δ_ne_zero]
  right_inv := by
    intro f
    ext z
    simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply, Delta_apply, Δ_ne_zero]

/-- Transport mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` from `𝒮ℒ` to `Γ(1)`. -/
public lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) :
    Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  let e : CuspForm Γ(1) k ≃ₗ[ℂ] CuspForm 𝒮ℒ k :=
    { toFun := fun f => f.copy (⇑f) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl
      invFun := fun f => f.copy (⇑f) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  rw [e.rank_eq]; exact CuspForm.rank_eq_zero_of_weight_lt_twelve hk

/-- A modular form of level `Γ(1)` and weight `< 12` which is a cusp form is identically zero. -/
public lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  obtain ⟨g, hg⟩ := hf
  let g' : CuspForm 𝒮ℒ k := g.copy (⇑g) rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  have hg'_zero : g' = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) g'
  ext z
  rw [← hg]; simpa [g'] using DFunLike.congr_fun hg'_zero z

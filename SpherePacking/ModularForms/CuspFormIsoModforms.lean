module
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.NumberTheory.ModularForms.LevelOne
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.qExpansion_lems


/-!
# Cusp forms vs. modular forms

This file defines `mul_Delta_map`, `Modform_mul_Delta`, `CuspForms_iso_Modforms`, and lemmas.
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
  rw [show (ModularFormClass.qExpansion (1 : ℝ) (f.mul (ModForm_mk Γ(1) 12 Delta))).coeff 0 =
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff 0 *
        (ModularFormClass.qExpansion (1 : ℝ) (ModForm_mk Γ(1) 12 Delta)).coeff 0 by
    simpa [PowerSeries.coeff_mul] using
      congrArg (fun p : PowerSeries ℂ => p.coeff 0)
        (qExpansion_mul_coeff (n := 1) (a := k - 12) (b := 12) f (ModForm_mk Γ(1) 12 Delta))]
  have hDelta0 :
      (ModularFormClass.qExpansion (1 : ℝ) (ModForm_mk Γ(1) 12 Delta)).coeff 0 = 0 :=
    (IsCuspForm_iff_coeffZero_eq_zero (k := 12) (f := ModForm_mk Γ(1) 12 Delta)).1 (by
      rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range]
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

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) :
    Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  simpa [LinearEquiv.rank_eq (CuspForms_iso_Modforms k)] using
    (ModularForm.levelOne_neg_weight_rank_zero (k := k - 12) (by linarith))

/-- A modular form of level `Γ(1)` and weight `< 12` which is a cusp form is identically zero. -/
public lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hzero : IsCuspForm_to_CuspForm Γ(1) k f hf = 0 :=
    rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero k hk)
      (IsCuspForm_to_CuspForm Γ(1) k f hf)
  ext z
  simpa [hzero] using
    (congr_fun (CuspForm_to_ModularForm_Fun_coe (Γ := Γ(1)) (k := k) f hf) z).symm

module
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.Algebra.Group.Int.Even
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.ModularForms.CuspFormIsoModforms
public import SpherePacking.ModularForms.Eisenstein

/-!
# Dimension Formulas

This file proves identities for `Delta` in terms of `E₄`/`E₆` and derives rank/dimension statements
for level-one modular forms.
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup ArithmeticFunction.sigma

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

noncomputable section

/-- The pointwise formula `Delta(z) = (1/1728) * (E₄(z)^3 - E₆(z)^2)`. -/
public lemma Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq (z : ℍ) :
    (Delta z : ℂ) = (1 / 1728 : ℂ) * ((E₄ z) ^ (3 : ℕ) - (E₆ z) ^ (2 : ℕ)) := by
  rw [show (Delta z : ℂ) = ModularForm.discriminant z from rfl,
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  change _ = _ * (((ModularForm.E₄ : ℍ → ℂ) z) ^ 3 - ((ModularForm.E₆ : ℍ → ℂ) z) ^ 2)
  ring

private lemma qExpansion_Delta_eq_smul :
    qExpansion 1 (Delta : ℍ → ℂ) =
      (1 / 1728 : ℂ) • ((qExpansion 1 (E₄ : ℍ → ℂ)) ^ 3 - (qExpansion 1 (E₆ : ℍ → ℂ)) ^ 2) := by
  have hf : (Delta : ℍ → ℂ) =
      ⇑((1 / 1728 : ℂ) • (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 -
        (DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12 : ModularForm Γ(1) 12)) := by
    ext z
    rw [Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq z]
    change _ = (1 / 1728 : ℂ) * ((((DirectSum.of (ModularForm _) 4) E₄ ^ 3) 12) z -
      (((DirectSum.of (ModularForm _) 6) E₆ ^ 2) 12) z)
    have hE4 : ((DirectSum.of (ModularForm Γ(1)) 4) E₄) ^ 3 =
        (DirectSum.of (ModularForm _) 12) ((E₄.mul E₄).mul E₄) := by
      rw [pow_succ, sq, DirectSum.of_mul_of, DirectSum.of_mul_of]; rfl
    have hE6 : ((DirectSum.of (ModularForm _) 6) E₆) ^ 2 =
        (DirectSum.of (ModularForm _) 12) (E₆.mul E₆) := by
      rw [sq, DirectSum.of_mul_of]; rfl
    rw [hE4, hE6, DirectSum.of_eq_same, DirectSum.of_eq_same]
    change _ = _ * (E₄ z * E₄ z * E₄ z - E₆ z * E₆ z)
    ring
  rw [qExpansion_ext2 Delta _ hf]
  simp only [one_div, ModularForm.IsGLPos.coe_smul, DirectSum.sub_apply, ModularForm.coe_sub]
  have hsmul := (by
    simpa using qExpansion_smul2 (n := 1) (a := (1728⁻¹ : ℂ))
      (f := ((((DirectSum.of (ModularForm Γ(1)) 4) E₄) ^ 3) 12 -
        (((DirectSum.of (ModularForm Γ(1)) 6) E₆) ^ 2) 12)))
  rw [← hsmul, qExpansion_sub1,
    show qExpansion (1 : ℝ) (⇑(((DirectSum.of (ModularForm _) 4) E₄ ^ 3) 12)) =
        qExpansion 1 ⇑E₄ ^ 3 from qExpansion_pow E₄ 3,
    show qExpansion (1 : ℝ) (⇑(((DirectSum.of (ModularForm _) 6) E₆ ^ 2) 12)) =
        qExpansion 1 ⇑E₆ ^ 2 from qExpansion_pow E₆ 2]

/-- The second `q`-coefficient of `Delta` is `-24`. -/
public lemma Delta_q_exp_two : (qExpansion 1 Delta).coeff 2 = (-24 : ℂ) := by
  rw [qExpansion_Delta_eq_smul]
  have hσ3 : (σ 3 2 : ℕ) = 9 := by decide
  have hσ5 : (σ 5 2 : ℕ) = 33 := by decide
  have hE4_2 : (qExpansion 1 E₄).coeff 2 = (240 : ℂ) * (9 : ℂ) := by
    simpa [hσ3] using congr_fun E4_q_exp 2
  have hE6_2 : (qExpansion 1 E₆).coeff 2 = (-(504 : ℂ)) * (33 : ℂ) := by
    simpa [hσ5] using congr_fun E6_q_exp 2
  have hanti2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  have hanti1 : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  simp only [PowerSeries.coeff_smul, smul_eq_mul, map_sub]
  simp [pow_three, pow_two, PowerSeries.coeff_mul, hanti2, hanti1,
    E4_q_exp_zero, E4_q_exp_one, hE4_2, E6_q_exp_zero, E6_q_exp_one, hE6_2]
  norm_num


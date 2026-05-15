module
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
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

private lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux := by
  have hrank : Module.rank ℂ (ModularForm Γ(1) (0 : ℤ)) = 1 := by
    refine rank_eq_one (ModularForm.const 1) (by simp [DFunLike.ne_iff]) fun g ↦ ?_
    have : ModularFormClass (ModularForm Γ(1) 0) 𝒮ℒ 0 :=
      CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ inferInstance
    obtain ⟨c', hc'⟩ := ModularFormClass.levelOne_weight_zero_const (F := ModularForm Γ(1) 0) g
    refine ⟨c', ?_⟩
    ext z
    have := congr_fun hc' z
    simp only [Function.const_apply] at this
    simp [ModularForm.const_apply, this]
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 :=
    Module.finrank_eq_of_rank_eq <| by
      simpa [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12)] using hrank
  exact (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).1 hr Delta_E4_E6_aux

/-- The discriminant cusp form as a scaled version of `E₄^3 - E₆^2`. -/
public lemma Delta_E4_E6_eq : ModForm_mk _ _ Delta_E4_E6_aux =
  ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12 )) := by
  ext
  rfl

private lemma qExpansion_Delta_E4_E6_aux_eq :
    qExpansion 1 Delta_E4_E6_aux = qExpansion 1 (ModForm_mk Γ(1) 12 Delta_E4_E6_aux) := by
  simpa [ModForm_mk] using qExpansion_ext2 Delta_E4_E6_aux
    (ModForm_mk Γ(1) 12 Delta_E4_E6_aux) rfl

lemma Delta_E4_E6_aux_q_one_term : (qExpansion 1 Delta_E4_E6_aux).coeff 1 = 1 := by
  rw [qExpansion_Delta_E4_E6_aux_eq, Delta_E4_E6_eq]
  -- Coefficient `q` of `E₄^3 - E₆^2` is `1728`, so scaling by `1/1728` gives `1`.
  simp only [one_div, DirectSum.sub_apply, ModularForm.IsGLPos.coe_smul, ModularForm.coe_sub]
  have hsmul :=
    (by
      simpa using qExpansion_smul2 (n := 1) (a := (1728⁻¹ : ℂ))
        (f := (((DirectSum.of (ModularForm Γ(1)) 4) E₄) ^ 3) 12 -
          (((DirectSum.of (ModularForm Γ(1)) 6) E₆) ^ 2) 12))
  rw [← hsmul]
  simp only [qExpansion_sub1, map_smul, map_sub, smul_eq_mul]
  have h4 : qExpansion 1 ⇑(((DirectSum.of (ModularForm _) 4) E₄ ^ 3) 12) =
      qExpansion 1 ⇑E₄ ^ 3 := qExpansion_pow E₄ 3
  have h6 : qExpansion 1 ⇑(((DirectSum.of (ModularForm _) 6) E₆ ^ 2) 12) =
      qExpansion 1 ⇑E₆ ^ 2 := qExpansion_pow E₆ 2
  rw [h4, h6]
  have hE4c : PowerSeries.constantCoeff (qExpansion 1 E₄) = (1 : ℂ) := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1)
  have hE6c : PowerSeries.constantCoeff (qExpansion 1 E₆) = (1 : ℂ) := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1)
  have hcoeff :
      (((qExpansion 1 E₄) ^ 3 - (qExpansion 1 E₆) ^ 2) : PowerSeries ℂ).coeff 1 = 1728 := by
    simp [map_sub, PowerSeries.coeff_one_pow, hE4c, hE6c, E4_q_exp_one, E6_q_exp_one]
    norm_num
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  have hcoeff' :
      ((qExpansion 1 E₄ ^ 3).coeff 1 - (qExpansion 1 E₆ ^ 2).coeff 1) = (1728 : ℂ) := by
    simpa [map_sub] using hcoeff
  rw [hcoeff']
  simp [h1728]

/-- Identify `Delta` with the auxiliary cusp form `Delta_E4_E6_aux`. -/
public theorem Delta_E4_eqn : Delta = Delta_E4_E6_aux := by
  ext z
  obtain ⟨c, H⟩ := delta_eq_E4E6_const
  have h1 := Delta_q_one_term
  have h2 := Delta_E4_E6_aux_q_one_term
  have hc : c = 1 := by
    have hsmul : (qExpansion 1 (c • Delta)).coeff 1 = c * (qExpansion 1 Delta).coeff 1 := by
      simpa [smul_eq_mul, CuspForm.coe_smul] using
        congrArg (fun p : PowerSeries ℂ => p.coeff 1)
          (by simpa using (qExpansion_smul2 (n := 1) (a := c)
            (f := ModForm_mk (CongruenceSubgroup.Gamma 1) 12 Delta)).symm)
    -- Compare `q`-coefficients at `1`.
    have h2' : (qExpansion 1 (c • Delta)).coeff 1 = 1 := by simpa [← H] using h2
    have : c * (qExpansion 1 Delta).coeff 1 = 1 := by simpa [hsmul] using h2'
    simpa [h1] using this
  simpa [hc] using congrArg (fun f => (f z : ℂ)) H

/-- The pointwise formula `Delta(z) = (1/1728) * (E₄(z)^3 - E₆(z)^2)`. -/
public lemma Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq (z : ℍ) :
    (Delta z : ℂ) = (1 / 1728 : ℂ) * ((E₄ z) ^ (3 : ℕ) - (E₆ z) ^ (2 : ℕ)) := by
  have hΔ : (Delta z : ℂ) = (Delta_E4_E6_aux z : ℂ) := by
    simpa using congrArg (fun f => (f z : ℂ)) Delta_E4_eqn
  have hE : (Delta_E4_E6_aux z : ℂ) =
      (1 / 1728 : ℂ) * ((E₄ z) ^ (3 : ℕ) - (E₆ z) ^ (2 : ℕ)) := by
    have h : Delta_E4_E6_aux z = (1 / 1728 : ℂ) *
        ((((DirectSum.of (ModularForm _) 4) E₄ ^ 3) 12) z -
          (((DirectSum.of (ModularForm _) 6) E₆ ^ 2) 12) z) :=
      congrArg (fun F : ModularForm Γ(1) 12 => (F z : ℂ)) Delta_E4_E6_eq
    have hE4 : ((DirectSum.of (ModularForm _) 4) E₄) ^ 3 =
        (DirectSum.of (ModularForm _) 12) ((E₄.mul E₄).mul E₄) := by
      rw [pow_succ, sq, DirectSum.of_mul_of, DirectSum.of_mul_of]; rfl
    have hE6 : ((DirectSum.of (ModularForm _) 6) E₆) ^ 2 =
        (DirectSum.of (ModularForm _) 12) (E₆.mul E₆) := by
      rw [sq, DirectSum.of_mul_of]; rfl
    rw [h, hE4, hE6, DirectSum.of_eq_same, DirectSum.of_eq_same]
    change 1 / 1728 * (E₄ z * E₄ z * E₄ z - E₆ z * E₆ z) = _
    ring
  exact hΔ.trans hE

/-- The second `q`-coefficient of `Delta` is `-24`. -/
public lemma Delta_q_exp_two : (qExpansion 1 Delta).coeff 2 = (-24 : ℂ) := by
  rw [Delta_E4_eqn]
  rw [qExpansion_Delta_E4_E6_aux_eq, Delta_E4_E6_eq]
  simp only [one_div, DirectSum.sub_apply, ModularForm.IsGLPos.coe_smul, ModularForm.coe_sub]
  have hsmul :=
    (by
      simpa using qExpansion_smul2 (n := 1) (a := (1728⁻¹ : ℂ))
        (f := (((DirectSum.of (ModularForm Γ(1)) 4) E₄) ^ 3) 12 -
          (((DirectSum.of (ModularForm Γ(1)) 6) E₆) ^ 2) 12))
  rw [← hsmul]
  simp only [qExpansion_sub1, map_smul, map_sub, smul_eq_mul]
  have h4 : qExpansion 1 ⇑(((DirectSum.of (ModularForm _) 4) E₄ ^ 3) 12) =
      qExpansion 1 ⇑E₄ ^ 3 := qExpansion_pow E₄ 3
  have h6 : qExpansion 1 ⇑(((DirectSum.of (ModularForm _) 6) E₆ ^ 2) 12) =
      qExpansion 1 ⇑E₆ ^ 2 := qExpansion_pow E₆ 2
  rw [h4, h6]
  have hσ3 : (σ 3 2 : ℕ) = 9 := by decide
  have hσ5 : (σ 5 2 : ℕ) = 33 := by decide
  have hE4_2 : (qExpansion 1 E₄).coeff 2 = (240 : ℂ) * (9 : ℂ) := by
    simpa [hσ3] using congr_fun E4_q_exp 2
  have hE6_2 : (qExpansion 1 E₆).coeff 2 = (-(504 : ℂ)) * (33 : ℂ) := by
    simpa [hσ5] using congr_fun E6_q_exp 2
  have hanti2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  suffices h :
      1728⁻¹ *
          (240 * 9 + (240 * 240 + 240 * 9) +
                (240 *
                      (∑ p ∈ Finset.antidiagonal 1,
                          (qExpansion 1 E₄).coeff p.1 * (qExpansion 1 E₄).coeff p.2) +
                    240 * 9) -
              (-(504 * 33) + (504 * 504 + -(504 * 33)))) = (-24 : ℂ) by
    simpa [pow_three, pow_two, PowerSeries.coeff_mul, hanti2, E4_q_exp_zero, E4_q_exp_one, hE4_2,
      E6_q_exp_zero, E6_q_exp_one, hE6_2] using h
  have hanti1 : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  have hs :
      (∑ x ∈ Finset.antidiagonal 1, (qExpansion 1 E₄).coeff x.1 * (qExpansion 1 E₄).coeff x.2) =
        (480 : ℂ) := by
    rw [hanti1]
    suffices h : (240 : ℂ) + 240 = 480 by
      simpa [E4_q_exp_zero, E4_q_exp_one] using h
    norm_num
  simp [hs]
  norm_num


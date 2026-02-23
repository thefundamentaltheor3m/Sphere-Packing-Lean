module
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.ModularForms.LevelOne
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

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

noncomputable section

def mul_Delta_map (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    ModularForm (CongruenceSubgroup.Gamma 1) k := by
  have := (f.mul (ModForm_mk _ 12 Delta))
  have hk : k - 12 + 12 = k := by ring
  exact ModularForm.mcast hk this

lemma mcast_apply {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) (z : ℍ) :
  (ModularForm.mcast h f) z = f z := by
  rfl

lemma mul_Delta_map_eq (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) (z : ℍ) :
  (mul_Delta_map k f) z = f z * Delta z := by
  rw [mul_Delta_map, mcast_apply ]
  rfl

lemma mul_Delta_map_eq_mul (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
  ((mul_Delta_map k f) : ℍ → ℂ) = (f.mul (ModForm_mk _ 12 Delta)) := by
  ext z
  rw [mul_Delta_map, mcast_apply ]

/-
lemma mul_Delta_IsCuspForm (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
  IsCuspForm (CongruenceSubgroup.Gamma 1) k (mul_Delta_map k f) := by
  rw [IsCuspForm_iff_coeffZero_eq_zero]
  rw [qExpansion_ext2 _ _ (mul_Delta_map_eq_mul k f)]
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff_zero]
  simp only [mul_eq_zero]
  right
  rw [Nat.cast_one, ← IsCuspForm_iff_coeffZero_eq_zero]
  rw [IsCuspForm, CuspFormSubmodule, CuspForm_to_ModularForm]
  simp

def Modform_mul_Delta' (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    CuspForm (CongruenceSubgroup.Gamma 1) k :=
  IsCuspForm_to_CuspForm _ k (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)

theorem mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z := rfl

lemma Modform_mul_Delta_apply (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12))
    (z : ℍ) : (Modform_mul_Delta' k f) z = f z * Delta z := by
  rw [Modform_mul_Delta']
  have := congr_fun
    (CuspForm_to_ModularForm_Fun_coe _ _ (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)) z
  simp at *
  rw [mul_Delta_map_eq] at this
  exact this

def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
      toFun f := CuspForm_div_Discriminant k f
      map_add' a b := CuspForm_div_Discriminant_Add k a b
      map_smul' := by
        intro m a
        ext z
        simp only [CuspForm_div_Discriminant_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul,
          RingHom.id_apply, IsGLPos.smul_apply]
        exact mul_div_assoc m (a z) (Δ z)
      invFun := Modform_mul_Delta' k
      left_inv := by
        intro f
        ext z
        simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply ]
        rw [Delta_apply]
        rw [div_mul_cancel₀ ]
        apply Δ_ne_zero
      right_inv := by
        intro f
        ext z
        simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply ]
        rw [Delta_apply]
        rw [mul_div_cancel_right₀]
        apply Δ_ne_zero
-/

lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux := by
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 :=
    Module.finrank_eq_of_rank_eq <| by
      simpa [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12)] using
        ModularForm.levelOne_weight_zero_rank_one
  exact (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).1 hr Delta_E4_E6_aux

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) : Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  have := CuspForms_iso_Modforms k
  --apply Module.finrank_eq_of_rank_eq
  rw [LinearEquiv.rank_eq this]
  apply ModularForm.levelOne_neg_weight_rank_zero
  linarith

/-
lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2:= CuspForm_to_ModularForm_coe _ _ f hf
  ext z
  simp only [ModularForm.zero_apply] at *
  have hy := congr_arg (fun x ↦ x.1) hfc2
  have hz := congr_fun hy z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
  toSlashInvariantForm_coe] at hz
  rw [← hz]
  have := rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero k hk)
    (IsCuspForm_to_CuspForm Γ(1) k f hf)
  rw [this]
  simp only [CuspForm.zero_apply]
-/

/-- The discriminant cusp form as a scaled version of `E₄^3 - E₆^2`. -/
public lemma Delta_E4_E6_eq : ModForm_mk _ _ Delta_E4_E6_aux =
  ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12 )) := by
  ext z
  simpa [ModForm_mk, Delta_E4_E6_aux, one_div, IsGLPos.smul_apply, sub_apply, smul_eq_mul] using
    congrArg (fun F => (F z : ℂ))
      (CuspForm_to_ModularForm_Fun_coe _ _
        ((1 / 1728 : ℂ) •
          (((DirectSum.of _ 4 E₄) ^ 3 - (DirectSum.of _ 6 E₆) ^ 2) 12)) (by
          rw [IsCuspForm_iff_coeffZero_eq_zero]
          exact E4E6_coeff_zero_eq_zero))

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
  have h4 := qExpansion_pow E₄ 3
  have h6 := qExpansion_pow E₆ 2
  simp only [Nat.cast_ofNat, Int.reduceMul] at h4 h6
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
    have h := congrArg (fun F : ModularForm Γ(1) 12 => (F z : ℂ)) Delta_E4_E6_eq
    simpa [ModForm_mk, one_div, IsGLPos.smul_apply, sub_apply, DirectSum.sub_apply, smul_eq_mul,
      pow_two, pow_three, DirectSum.of_mul_of, mul_assoc] using h
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
  have h4 := qExpansion_pow E₄ 3
  have h6 := qExpansion_pow E₆ 2
  simp only [Nat.cast_ofNat, Int.reduceMul] at h4 h6
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
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  field_simp [h1728]
  norm_num

/-
lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 := by
  rw [rank_eq_one_iff ]
  refine ⟨E₆,E6_ne_zero, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) 6 f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero 6 (by norm_num) f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff 0 with hc
    have hcusp : IsCuspForm Γ(1) 6 (E₆ - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]
      rw [← Nat.cast_one (R := ℝ), qExpansion_sub]
      have := modularForm_normalise f hf2
      simp only [ne_eq, map_sub] at *
      rw [hc, this]
      rw [E6_q_exp_zero]
      exact sub_eq_zero_of_eq rfl
    have := IsCuspForm_weight_lt_eq_zero 6 (by norm_num) (E₆ - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop


lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 := by
  rw [rank_eq_one_iff ]
  refine ⟨E₄,E4_ne_zero, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) 4 f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff 0 with hc
    have hcusp : IsCuspForm Γ(1) 4 (E₄ - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]
      rw [← Nat.cast_one (R := ℝ), qExpansion_sub]
      have := modularForm_normalise f hf2
      simp only [ne_eq, map_sub] at *
      rw [hc, this]
      rw [E4_q_exp_zero]
      exact sub_eq_zero_of_eq rfl
    have := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) (E₄ - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop

lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_eq_one_iff ]
  refine ⟨E k hk ,Ek_ne_zero k hk hk2, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) k f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero k (by simpa using hk3) f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff 0 with hc
    have hcusp : IsCuspForm Γ(1) k (E k hk - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]
      rw [← Nat.cast_one (R := ℝ), qExpansion_sub]
      have := modularForm_normalise f hf2
      simp only [ne_eq, map_sub] at *
      rw [hc, this]
      have hE := Ek_q_exp_zero k hk hk2
      simp at *
      rw [hE]
      exact sub_eq_zero_of_eq rfl
    have := IsCuspForm_weight_lt_eq_zero k (by simpa using hk3) (E k hk - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop

lemma weight_two_zero (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := by
/- cant be a cuspform from the above, so let a be its constant term, then f^2 = a^2 E₄ and
f^3 = a^3 E₆, but now this would mean that Δ = 0 or a = 0, which is a contradiction. -/
  by_cases hf : IsCuspForm (CongruenceSubgroup.Gamma 1) 2 f
  --have hfc := IsCuspForm_to_CuspForm _ _ f hf
  · have hfc2:= CuspForm_to_ModularForm_coe _ _ f hf
    ext z
    simp only [ModularForm.zero_apply] at *
    have hy := congr_arg (fun x ↦ x.1) hfc2
    have hz := congr_fun hy z
    simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
      toSlashInvariantForm_coe] at hz
    rw [← hz]
    have := rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 2 (by norm_num))
      (IsCuspForm_to_CuspForm Γ(1) 2 f hf)
    rw [this]
    simp only [CuspForm.zero_apply]
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf h
    obtain ⟨c6, hc6⟩ := exists_smul_eq_of_rank_one' weight_six_one_dimensional E6_ne_zero
      ((f.mul f).mul f)
    have hc6e : c6 = ((qExpansion 1 f).coeff 0)^3 := by
      have := qExpansion_mul_coeff 1 4 2 (f.mul f) f
      have h2 := qExpansion_mul_coeff 1 2 2 f f
      rw [← hc6] at this
      rw [← qExpansion_smul2 1 c6, h2] at this
      have hh := congr_arg (fun x => x.coeff 0) this
      simp only [_root_.map_smul, smul_eq_mul] at hh
      rw [Nat.cast_one, E6_q_exp_zero] at hh
      rw [pow_three]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, ne_eq, Int.reduceAdd, mul_one,
        map_mul] at *
      rw [← mul_assoc]
      exact hh
    obtain ⟨c4, hc4⟩ := exists_smul_eq_of_rank_one' weight_four_one_dimensional E4_ne_zero
      (f.mul f)
    have hc4e : c4 = ((qExpansion 1 f).coeff 0)^2 := by
      have := qExpansion_mul_coeff 1 2 2 f f
      rw [← hc4] at this
      rw [← qExpansion_smul2 1 c4] at this
      have hh := congr_arg (fun x => x.coeff 0) this
      simp only [_root_.map_smul, smul_eq_mul] at hh
      rw [Nat.cast_one, E4_q_exp_zero] at hh
      rw [pow_two]
      simpa using hh
    exfalso
    let F := DirectSum.of _ 2 f
    let D := DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) 12
    have : D ≠ 0 := by
      have HD := ModForm_mk_inj _ _ _ Delta_ne_zero
      apply HD
    have HF2 : (F^2) = c4 • (DirectSum.of _ 4 E₄) := by
      rw [← DirectSum.of_smul, hc4]
      simp [F]
      rw [pow_two, DirectSum.of_mul_of]
      rfl
    have HF3 : (F^3) = c6 • (DirectSum.of _ 6 E₆) := by
      rw [← DirectSum.of_smul, hc6]
      simp [F]
      rw [pow_three, ← mul_assoc, DirectSum.of_mul_of, DirectSum.of_mul_of]
      rfl
    have HF12 : (((F^2)^3) 12) = ((qExpansion 1 f).coeff 0)^6 • (E₄.mul (E₄.mul E₄)) := by
      rw [HF2, pow_three]
      simp
      rw [DirectSum.of_mul_of, DirectSum.of_mul_of, hc4e, smul_smul, smul_smul]
      ring_nf
      rw [@DirectSum.smul_apply]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, DirectSum.of_eq_same]
      rfl
    have hF2 : (((F^3)^2) 12) = ((qExpansion 1 f).coeff 0)^6 • ((E₆.mul E₆)) := by
      rw [HF3, pow_two]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Int.reduceAdd,
        PowerSeries.coeff_zero_eq_constantCoeff]
      rw [DirectSum.of_mul_of, hc6e, smul_smul]
      ring_nf
      rw [@DirectSum.smul_apply]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, DirectSum.of_eq_same]
      rfl
    have V : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = ((qExpansion 1 f).coeff 0)^6 • D
      := by
      rw [HF12, hF2]
      simp only [one_div, Int.reduceAdd, PowerSeries.coeff_zero_eq_constantCoeff,
        DirectSum.of_eq_same, D]
      rw [Delta_E4_eqn, Delta_E4_E6_eq, pow_two, pow_three, DirectSum.of_mul_of,
        DirectSum.of_mul_of,DirectSum.of_mul_of]
      simp only [one_div, Int.reduceAdd, DirectSum.sub_apply, DirectSum.of_eq_same]
      ext y
      simp only [IsGLPos.smul_apply, sub_apply, Int.reduceAdd, smul_eq_mul]
      ring_nf
      rfl
    have ht : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = 0 := by
      ext y
      simp only [one_div, IsGLPos.smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_eq_zero,
        inv_eq_zero, OfNat.ofNat_ne_zero, false_or, F]
      ring_nf
    rw [ht] at V
    have hr := congr_fun (congr_arg (fun x ↦ x.toFun) V) UpperHalfPlane.I
    simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, zero_apply,
      PowerSeries.coeff_zero_eq_constantCoeff, DirectSum.of_eq_same, IsGLPos.smul_apply,
      smul_eq_mul, zero_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      D] at hr
    rcases hr with h | h
    · simp only [PowerSeries.coeff_zero_eq_constantCoeff, ne_eq, Int.reduceAdd, one_div,
      isUnit_iff_ne_zero, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.smul_eq_zero,
      F, D] at *
      exact hc1 h
    · simp only [ModForm_mk] at h
      have hDelta := Δ_ne_zero UpperHalfPlane.I
      rw [← Delta_apply] at hDelta
      exact hDelta h

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
    have h1 : Module.rank ℂ (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k) =
      Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
      apply LinearEquiv.rank_eq
      have := CuspForm_iso_CuspFormSubmodule Γ(1) k
      exact _root_.id this.symm
    rw [← h1, ← Submodule.rank_quotient_add_rank (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k)]
    congr
    rw [rank_eq_one_iff ]
    refine ⟨Submodule.Quotient.mk (E k (by linarith)), ?_, ?_⟩
    · intro hq
      rw [Submodule.Quotient.mk_eq_zero] at hq
      have := IsCuspForm_iff_coeffZero_eq_zero k (E k (by linarith))
      rw [IsCuspForm] at this
      rw [this, Ek_q_exp_zero k hk hk2] at hq
      aesop
    intro v
    have := Quotient.exists_rep v
    obtain ⟨f, hf⟩ := this
    use ((qExpansion 1 f).coeff 0)
    rw [← Submodule.Quotient.mk_smul, ← hf ]
    have : ⟦f⟧ = Submodule.Quotient.mk f
      (p := (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k) ):= by rfl
    rw [this, Submodule.Quotient.eq, CuspFormSubmodule_mem_iff_coeffZero_eq_zero,
      ← Nat.cast_one (R := ℝ), qExpansion_sub, ← Nat.cast_one (R := ℝ), ← qExpansion_smul2]
    have hc := Ek_q_exp_zero k hk hk2
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_sub, PowerSeries.constantCoeff_smul,
      smul_eq_mul] at *
    rw [Nat.cast_one, hc]
    ring

theorem dim_weight_two : Module.rank ℂ (ModularForm Γ(1) ↑2) = 0 := by
  rw [@rank_zero_iff_forall_zero]
  intro f
  apply weight_two_zero f

lemma floor_lem1 (k a : ℚ) (ha : 0 < a) (hak : a ≤ k) :
    1 + Nat.floor ((k - a) / a) = Nat.floor (k / a) := by
  rw [div_sub_same (Ne.symm (ne_of_lt ha))]
  have := Nat.floor_sub_one (k/a)
  norm_cast at *
  rw [this]
  refine Nat.add_sub_cancel' ?_
  refine Nat.le_floor ?_
  refine (le_div_iff₀ ha).mpr ?_
  simpa using hak

lemma dim_modforms_lvl_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  rw [dim_modforms_eq_one_add_dim_cuspforms (k) (by omega) hk2 ,
    LinearEquiv.rank_eq (CuspForms_iso_Modforms (((k)) : ℤ))]
  by_cases HK : (3 : ℤ) ≤ (((k : ℤ) - 12))
  · have iH := ihn (k - 12) (by omega) ?_ ?_
    · have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by
        norm_cast
        refine Eq.symm (Int.subNatNat_of_le ?_)
        omega
      rw [hk12] at iH
      have : ((k - 12) : ℕ) = (k : ℚ) - 12 := by
        norm_cast
      rw [iH, this]
      by_cases h12 : 12 ∣ ((k) : ℤ) - 2
      · have h12k : 12 ∣ (k : ℤ) -12 - 2 := by
          omega
        simp only [h12k, ↓reduceIte, h12]
        have := floor_lem1 k 12 (by norm_num)
        norm_cast at *
        apply this
        omega
      · have h12k : ¬ 12 ∣ (k : ℤ) -12 - 2 := by
          omega
        simp only [h12k, ↓reduceIte, Nat.cast_add, Nat.cast_one, h12]
        have := floor_lem1 k 12 (by norm_num)
        norm_cast at *
        rw [← add_assoc, this]
        omega
    · omega
    · refine (Nat.even_sub ?_).mpr ?_
      · omega
      simp only [hk2, true_iff]
      decide
  · simp only [not_le] at HK
    have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
      simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]
      omega
    have : Finset.filter Even (Finset.Icc 3 14) = ({4,6,8,10,12, 14} : Finset ℕ) := by
        decide
    rw [this] at hkop
    fin_cases hkop
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
      have h8 : -8 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
      have h8 : -6 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
      have h8 : -4 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
      have h8 : -2 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_self, Nat.floor_one, Nat.reduceAdd, Nat.cast_ite, Nat.cast_one]
      rw [ModularForm.levelOne_weight_zero_rank_one]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, dim_weight_two, add_zero, dvd_refl, ↓reduceIte]
      norm_cast

public lemma ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  apply dim_modforms_lvl_one k hk hk2

public lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry
--use the norm to turn it into a level one question.
-/

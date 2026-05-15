module
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.ModularForms.LevelOne
public import Mathlib.Algebra.Group.Int.Even
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.ModularForms.DimGenCongLevels.NormTransfer
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

lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux := by
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 :=
    Module.finrank_eq_of_rank_eq <| by
      simpa [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12)] using
        ModularForm.levelOne_weight_zero_rank_one
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

private lemma qExpansion_coeff_zero_ne_zero_of_not_cusp {k : ℤ} (f : ModularForm Γ(1) k)
    (hf : ¬ IsCuspForm Γ(1) k f) : (qExpansion 1 f).coeff 0 ≠ 0 := by
  exact fun h0 => hf ((IsCuspForm_iff_coeffZero_eq_zero k f).2 h0)

private lemma isCuspForm_sub_normalise {k : ℤ} (E f : ModularForm Γ(1) k)
    (hf : ¬ IsCuspForm Γ(1) k f) (hE0 : (qExpansion 1 E).coeff 0 = 1) :
    IsCuspForm Γ(1) k (E - ((qExpansion 1 f).coeff 0)⁻¹ • f) := by
  rw [IsCuspForm_iff_coeffZero_eq_zero]
  have hnorm : (qExpansion 1 (((qExpansion 1 f).coeff 0)⁻¹ • f)).coeff 0 = 1 :=
    modularForm_normalise (k := k) f hf
  have hE0' : PowerSeries.constantCoeff (qExpansion 1 E) = 1 := by simpa using hE0
  have hnorm' :
      PowerSeries.constantCoeff
          (qExpansion 1 ((PowerSeries.constantCoeff (qExpansion 1 f))⁻¹ • f)) = 1 := by
    simpa using hnorm
  simpa [map_sub, hE0', hnorm'] using
    congrArg (fun p : PowerSeries ℂ => p.coeff 0)
      (qExpansion_sub1 (f := E) (g := ((qExpansion 1 f).coeff 0)⁻¹ • f))

private lemma weight_lt_twelve_one_dimensional {k : ℤ} (E : ModularForm Γ(1) k)
    (hEne : E ≠ 0) (hE0 : (qExpansion 1 E).coeff 0 = 1) (hk : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_eq_one_iff]
  refine ⟨E, hEne, fun f => ?_⟩
  by_cases hf : IsCuspForm Γ(1) k f
  · refine ⟨0, ?_⟩
    simp [IsCuspForm_weight_lt_eq_zero k (by simpa using hk) f hf]
  · set c : ℂ := (qExpansion 1 f).coeff 0
    have hc : c ≠ 0 := by
      simpa [c] using qExpansion_coeff_zero_ne_zero_of_not_cusp (k := k) f hf
    have hcusp : IsCuspForm Γ(1) k (E - c⁻¹ • f) := by
      simpa [c] using isCuspForm_sub_normalise (k := k) (E := E) (f := f) hf hE0
    have hEq : E = c⁻¹ • f := by
      simpa [sub_eq_zero] using
        IsCuspForm_weight_lt_eq_zero k (by simpa using hk) (E - c⁻¹ • f) hcusp
    refine ⟨c, by simp [hEq, smul_smul, hc]⟩

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 := by
  simpa using
    weight_lt_twelve_one_dimensional (k := 6) (E := E₆) E6_ne_zero E6_q_exp_zero (by norm_num)

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 := by
  simpa using
    weight_lt_twelve_one_dimensional (k := 4) (E := E₄) E4_ne_zero E4_q_exp_zero (by norm_num)

lemma weight_two_zero (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := by
-- Let `a` be the constant term; then `f^2 = a^2 E₄` and `f^3 = a^3 E₆`, forcing `a = 0` or `Δ = 0`.
  by_cases hf : IsCuspForm (CongruenceSubgroup.Gamma 1) 2 f
  · exact IsCuspForm_weight_lt_eq_zero 2 (by norm_num) f hf
  · have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 :=
      fun h => hf ((IsCuspForm_iff_coeffZero_eq_zero 2 f).2 h)
    set a : ℂ := (qExpansion 1 f).coeff 0 with ha_def
    have ha : a ≠ 0 := by simpa [ha_def] using hc1
    have r6 : ∀ g : ModularForm Γ(1) 6, ∃ c : ℂ, c • E₆ = g :=
      (finrank_eq_one_iff_of_nonzero' E₆ E6_ne_zero).1
        ((Module.rank_eq_one_iff_finrank_eq_one).1 weight_six_one_dimensional)
    rcases r6 ((f.mul f).mul f) with ⟨c6, hc6⟩
    have hc6e : c6 = a ^ 3 := by
      have h1 := qExpansion_mul_coeff 1 4 2 (f.mul f) f
      have h2 := qExpansion_mul_coeff 1 2 2 f f
      simp only [Nat.cast_one] at h1 h2
      have hmul3 : (qExpansion 1 ((f.mul f).mul f)).coeff 0 = a ^ 3 := h1 ▸ h2 ▸ by
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, a, pow_three, mul_assoc]
      have h0 : (qExpansion 1 ((f.mul f).mul f)).coeff 0 = c6 := by
        have hsm := (qExpansion_smul2 (n := 1) (a := c6) (f := E₆)).symm
        simp only [Nat.cast_one] at hsm
        have hcoe : qExpansion 1 ((f.mul f).mul f) = c6 • qExpansion 1 E₆ := by
          conv_lhs => rw [← hc6]
          exact hsm
        rw [hcoe]; simp [show (qExpansion 1 E₆).coeff 0 = 1 from E6_q_exp_zero]
      exact h0.symm.trans hmul3
    have r4 : ∀ g : ModularForm Γ(1) 4, ∃ c : ℂ, c • E₄ = g :=
      (finrank_eq_one_iff_of_nonzero' E₄ E4_ne_zero).1
        ((Module.rank_eq_one_iff_finrank_eq_one).1 weight_four_one_dimensional)
    rcases r4 (f.mul f) with ⟨c4, hc4⟩
    have hc4e : c4 = a ^ 2 := by
      have h1 := qExpansion_mul_coeff 1 2 2 f f
      simp only [Nat.cast_one] at h1
      have hmul2 : (qExpansion 1 (f.mul f)).coeff 0 = a ^ 2 := h1 ▸ by
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, a, pow_two]
      have h0 : (qExpansion 1 (f.mul f)).coeff 0 = c4 := by
        have hsm := (qExpansion_smul2 (n := 1) (a := c4) (f := E₄)).symm
        simp only [Nat.cast_one] at hsm
        have hcoe : qExpansion 1 (f.mul f) = c4 • qExpansion 1 E₄ := by
          conv_lhs => rw [← hc4]
          exact hsm
        rw [hcoe]; simp [show (qExpansion 1 E₄).coeff 0 = 1 from E4_q_exp_zero]
      exact h0.symm.trans hmul2
    exfalso
    let F := DirectSum.of _ 2 f
    let D : ModularForm Γ(1) 12 := ModForm_mk Γ(1) 12 Delta
    have HF2 : (F^2) = c4 • (DirectSum.of _ 4 E₄) := by
      rw [← DirectSum.of_smul, hc4]
      dsimp [F]
      rw [pow_two, DirectSum.of_mul_of]
      rfl
    have HF3 : (F^3) = c6 • (DirectSum.of _ 6 E₆) := by
      rw [← DirectSum.of_smul, hc6]
      dsimp [F]
      rw [pow_three, ← mul_assoc, DirectSum.of_mul_of, DirectSum.of_mul_of]
      rfl
    have HF12 : (((F^2)^3) 12) = a ^ 6 • (E₄.mul (E₄.mul E₄)) := by
      rw [HF2, pow_three]
      rw [show c4 • (DirectSum.of (ModularForm _) 4) E₄ *
            (c4 • (DirectSum.of (ModularForm _) 4) E₄ *
              c4 • (DirectSum.of (ModularForm _) 4) E₄) =
            (c4 * (c4 * c4)) •
              (DirectSum.of (ModularForm _) 12) (E₄.mul (E₄.mul E₄)) by
        simp only [smul_mul_smul_comm, DirectSum.of_mul_of]; rfl]
      rw [DirectSum.smul_apply, DirectSum.of_eq_same, hc4e]
      ring_nf
      rfl
    have hF2 : (((F^3)^2) 12) = a ^ 6 • (E₆.mul E₆) := by
      rw [HF3, pow_two]
      simp [DirectSum.smul_apply, DirectSum.of_mul_of, hc6e, smul_smul]
      ring_nf
      rfl
    have V : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = a ^ 6 • D
      := by
      rw [HF12, hF2]
      simp only [one_div, Int.reduceAdd, D]
      rw [Delta_E4_eqn, Delta_E4_E6_eq, pow_two, pow_three, DirectSum.of_mul_of,
        DirectSum.of_mul_of,DirectSum.of_mul_of]
      simp only [one_div, Int.reduceAdd, DirectSum.sub_apply]
      ext y
      simp only [IsGLPos.smul_apply, sub_apply, smul_eq_mul]
      ring_nf
      rfl
    have ht : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = 0 := by
      ext y
      simp only [one_div, IsGLPos.smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_eq_zero,
        inv_eq_zero, OfNat.ofNat_ne_zero, false_or, F]
      ring_nf
    rw [ht] at V
    have hr := congrArg (fun g : ModularForm Γ(1) 12 => g UpperHalfPlane.I) V
    simp only [D, ModForm_mk, IsGLPos.smul_apply, smul_eq_mul, zero_apply, zero_eq_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at hr
    rcases hr with h | h
    · exact ha h
    · have hDelta : Delta UpperHalfPlane.I ≠ 0 := by
        simpa [Delta_apply] using Δ_ne_zero UpperHalfPlane.I
      exact hDelta h

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
    have h1 : Module.rank ℂ (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k) =
      Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
      apply LinearEquiv.rank_eq
      have := CuspForm_iso_CuspFormSubmodule Γ(1) k
      exact id this.symm
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
    rcases Quotient.exists_rep v with ⟨f, rfl⟩
    refine ⟨(qExpansion 1 f).coeff 0, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    change
      Submodule.Quotient.mk ((qExpansion 1 f).coeff 0 • E k (by linarith)) =
        Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq, CuspFormSubmodule_mem_iff_coeffZero_eq_zero]
    -- Reduce to the constant coefficient computation.
    simp only [ModularForm.coe_sub]
    rw [qExpansion_sub1]
    simp only [ModularForm.IsGLPos.coe_smul]
    rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, Nat.cast_one]
    have hc := Ek_q_exp_zero k hk hk2
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_sub, PowerSeries.constantCoeff_smul,
      smul_eq_mul] at *
    rw [hc]
    ring

theorem dim_weight_two : Module.rank ℂ (ModularForm Γ(1) ↑2) = 0 := by
  rw [@rank_zero_iff_forall_zero]
  exact weight_two_zero

lemma floor_lem1 (k a : ℚ) (ha : 0 < a) (hak : a ≤ k) :
    1 + Nat.floor ((k - a) / a) = Nat.floor (k / a) := by
  rw [div_sub_same (Ne.symm (ne_of_lt ha))]
  have := Nat.floor_sub_one (k/a)
  norm_cast at *
  rw [this]
  refine Nat.add_sub_cancel' (Nat.le_floor <| (le_div_iff₀ ha).2 ?_)
  simpa using hak

public lemma ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | _ k ihn =>
  rw [dim_modforms_eq_one_add_dim_cuspforms (k) (by omega) hk2 ,
    LinearEquiv.rank_eq (CuspForms_iso_Modforms (k : ℤ))]
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
    -- Each finite case reduces by computing the rank for that specific small weight.
    have neg : ∀ {n : ℕ}, ((n : ℤ) - 12 < 0) →
        1 + Module.rank ℂ (ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1))
          (↑n - 12)) = 1 + 0 := fun h => by
      rw [ModularForm.levelOne_neg_weight_rank_zero h]
    fin_cases hkop
    · exact (neg (by decide : ((4 : ℕ) : ℤ) - 12 < 0)).trans (by norm_cast)
    · exact (neg (by decide : ((6 : ℕ) : ℤ) - 12 < 0)).trans (by norm_cast)
    · exact (neg (by decide : ((8 : ℕ) : ℤ) - 12 < 0)).trans (by norm_cast)
    · exact (neg (by decide : ((10 : ℕ) : ℤ) - 12 < 0)).trans (by norm_cast)
    · have h : 1 + Module.rank ℂ (ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
          Γ(1)) (↑(12 : ℕ) - 12)) = 1 + 1 := by
        rw [show ((12 : ℕ) : ℤ) - 12 = 0 by decide, ModularForm.levelOne_weight_zero_rank_one]
      exact h.trans (by norm_cast)
    · have h : 1 + Module.rank ℂ (ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
          Γ(1)) (↑(14 : ℕ) - 12)) = 1 + 0 := by
        rw [show ((14 : ℕ) : ℤ) - 12 = 2 by decide, dim_weight_two]
      exact h.trans (by norm_cast)

lemma finiteDimensional_of_subsingleton (V : Type*) [AddCommGroup V] [Module ℂ V] [Subsingleton V] :
    FiniteDimensional ℂ V := by
  refine (Module.finite_def).2 ?_
  simpa [Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule ℂ V))] using
    (Submodule.fg_bot : (⊥ : Submodule ℂ V).FG)

lemma finiteDimensional_of_rank_lt_aleph0 (V : Type*) [AddCommGroup V] [Module ℂ V]
    (h : Module.rank ℂ V < Cardinal.aleph0) : FiniteDimensional ℂ V := by
  haveI : Module.Free ℂ V := by infer_instance
  simpa using (Module.rank_lt_aleph0_iff (R := ℂ) (M := V)).1 h

/-- Level-one modular forms of odd weight are identically zero, via invariance under `-I`. -/
lemma ModularForm.levelOne_eq_zero_of_odd_weight {k : ℤ} (hk : Odd k) (f : ModularForm Γ(1) k) :
    f = 0 := by
  ext z
  have h' : f z = -f z := by
    have h : f z = (-1 : ℂ) ^ k * f z := by
      simpa [denom, show (-1 : SL(2, ℤ)) • z = z by simp] using
        (SlashInvariantForm.slash_action_eqn_SL'' (f := f) (γ := (-1 : SL(2, ℤ)))
          (hγ := CongruenceSubgroup.mem_Gamma_one (-1 : SL(2, ℤ))) z)
    simpa [hk.neg_one_zpow, neg_one_mul] using h
  simpa using (CharZero.eq_neg_self_iff (a := f z)).1 h'

lemma finiteDimensional_modularForm_level_one (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ(1) k) := by
  by_cases hkneg : k < 0
  · have hr : Module.rank ℂ (ModularForm Γ(1) k) = 0 :=
      ModularForm.levelOne_neg_weight_rank_zero (k := k) hkneg
    exact Module.finite_of_rank_eq_zero hr
  · have hk0le : 0 ≤ k := le_of_not_gt hkneg
    by_cases hk0 : k = 0
    · subst hk0
      refine finiteDimensional_of_rank_lt_aleph0 (V := ModularForm Γ(1) (0 : ℤ)) ?_
      simp [ModularForm.levelOne_weight_zero_rank_one, Cardinal.one_lt_aleph0]
    · have hkpos : 0 < k := lt_of_le_of_ne hk0le (Ne.symm hk0)
      rcases Int.even_or_odd k with hk2 | hk2
      · set kN : ℕ := Int.toNat k
        have hkNat : (kN : ℤ) = k := by
          simpa [kN] using (Int.toNat_of_nonneg hk0le)
        have hk2Nat : Even (Int.toNat k) := by
          have : Even (kN : ℤ) := by simpa [hkNat, kN] using hk2
          simpa [kN] using (Int.even_coe_nat kN).1 this
        by_cases hk2' : k = 2
        · subst hk2'
          have hr : Module.rank ℂ (ModularForm Γ(1) (2 : ℤ)) = 0 := by
            simpa using dim_weight_two
          refine finiteDimensional_of_rank_lt_aleph0 (V := ModularForm Γ(1) (2 : ℤ)) ?_
          simpa [hr] using (Cardinal.natCast_lt_aleph0 (n := 0))
        · have hkNat_ge3 : (3 : ℤ) ≤ (Int.toNat k : ℤ) := by
            grind only [= Int.even_iff]
          have hr :
              Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) kN) =
                if 12 ∣ ((kN : ℤ) - 2) then Nat.floor ((kN : ℚ) / 12) else
                  Nat.floor ((kN : ℚ) / 12) + 1 := by
            simpa [kN] using ModularForm.dimension_level_one (k := kN) hkNat_ge3 hk2Nat
          have hr' :
              Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) kN) < Cardinal.aleph0 := by
            by_cases hdiv : 12 ∣ ((kN : ℤ) - 2)
            · simp [hr, hdiv]
            · simpa [hr, hdiv] using
                (Cardinal.add_lt_aleph0
                  (Cardinal.natCast_lt_aleph0 (n := Nat.floor ((kN : ℚ) / 12)))
                  Cardinal.one_lt_aleph0)
          haveI : FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (kN : ℤ)) :=
            finiteDimensional_of_rank_lt_aleph0
              (V := ModularForm (CongruenceSubgroup.Gamma 1) (kN : ℤ)) hr'
          haveI : FiniteDimensional ℂ (ModularForm Γ(1) (kN : ℤ)) := by infer_instance
          exact hkNat ▸ (show FiniteDimensional ℂ (ModularForm Γ(1) (kN : ℤ)) by infer_instance)
      · have hz : ∀ f : ModularForm Γ(1) k, f = 0 := fun f =>
          ModularForm.levelOne_eq_zero_of_odd_weight (k := k) hk2 f
        haveI : Subsingleton (ModularForm Γ(1) k) := subsingleton_of_forall_eq 0 hz
        exact finiteDimensional_of_subsingleton (V := ModularForm Γ(1) k)

lemma finiteDimensional_modularForm_congr {k : ℤ} {H K : Subgroup (GL (Fin 2) ℝ)}
    (h : H = K) [H.HasDetOne] [K.HasDetOne] (hH : FiniteDimensional ℂ (ModularForm H k)) :
    FiniteDimensional ℂ (ModularForm K k) := by
  cases h; simpa using hH

lemma finiteDimensional_modularForm_SL2Z (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒮ℒ k) := by
  let f : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ
  change FiniteDimensional ℂ (ModularForm f.range k)
  have hΓ1 : FiniteDimensional ℂ (ModularForm (Subgroup.map f (Γ(1) : Subgroup SL(2, ℤ))) k) := by
    simpa [f] using (finiteDimensional_modularForm_level_one (k := k))
  have htop : FiniteDimensional ℂ (ModularForm (Subgroup.map f (⊤ : Subgroup SL(2, ℤ))) k) := by
    have hΓ : (Γ(1) : Subgroup SL(2, ℤ)) = ⊤ := by
      simpa using (CongruenceSubgroup.Gamma_one_top : CongruenceSubgroup.Gamma 1 = ⊤)
    exact finiteDimensional_modularForm_congr (congrArg (Subgroup.map f) hΓ) hΓ1
  have hrange : f.range = Subgroup.map f (⊤ : Subgroup SL(2, ℤ)) := by
    simpa [f] using (MonoidHom.range_eq_map f)
  exact finiteDimensional_modularForm_congr (k := k) hrange.symm htop

open SpherePacking.ModularForms.NormReduction

public lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  by_cases hkneg : k < 0
  · exact SpherePacking.ModularForms.finiteDimensional_modularForm_neg_weight Γ hΓ k hkneg
  · have hk0le : 0 ≤ k := le_of_not_gt hkneg
    by_cases hk0 : k = 0
    · subst hk0
      exact SpherePacking.ModularForms.finiteDimensional_modularForm_weight_zero Γ hΓ
    · haveI : Γ.FiniteIndex := ⟨hΓ⟩
      let GΓ : Subgroup (GL (Fin 2) ℝ) := SpherePacking.ModularForms.NormReduction.G Γ
      let h : ℝ := SpherePacking.ModularForms.NormReduction.cuspWidth (Γ := Γ)
      have hh : 0 < h := SpherePacking.ModularForms.NormReduction.cuspWidth_pos (Γ := Γ) hΓ
      have hperΓ : h ∈ GΓ.strictPeriods := by
        simpa [h] using
          SpherePacking.ModularForms.NormReduction.cuspWidth_mem_strictPeriods (Γ := Γ)
      have hperSL : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
        simpa [h] using
          SpherePacking.ModularForms.NormReduction.cuspWidth_mem_strictPeriods_levelOne (Γ := Γ)
      haveI : GΓ.IsArithmetic :=
        SpherePacking.ModularForms.NormReduction.instIsArithmetic (Γ := Γ) hΓ
      haveI : GΓ.IsFiniteRelIndex 𝒮ℒ :=
        Subgroup.IsArithmetic.isFiniteRelIndexSL
          (𝒢 := GΓ)
      let w : ℤ := k * Nat.card (SpherePacking.ModularForms.NormReduction.Q Γ)
      haveI : FiniteDimensional ℂ (ModularForm 𝒮ℒ w) := by
        simpa [w] using (finiteDimensional_modularForm_SL2Z (k := w))
      obtain ⟨N, hNinj⟩ :=
        SpherePacking.ModularForms.exists_qCoeff_injective
          (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (k := w) (h := h) hh hperSL
      let trunc : ModularForm GΓ k →ₗ[ℂ] (Fin N → ℂ) :=
      { toFun := fun f => fun n => (qExpansion h f).coeff n
        map_add' := by
          intro f g
          ext n
          simp [qExpansion_add hh hperΓ f g]
        map_smul' := by
          intro a f
          ext n
          simp [qExpansion_smul hh hperΓ a f] }
      have htrunc_inj : Function.Injective trunc := by
        intro f g hfg
        have hcoeff : ∀ m < N, (qExpansion h (f - g)).coeff m = 0 := by
          intro m hm
          have hsub : trunc (f - g) = 0 := by
            have hmap : trunc (f - g) = trunc f - trunc g := trunc.map_sub f g
            have hdiff : trunc f - trunc g = 0 := by simp [hfg]
            simp [hmap, hdiff]
          have := congrArg (fun t : Fin N → ℂ => t ⟨m, hm⟩) hsub
          simpa [trunc] using this
        have hcoeff_norm : ∀ m < N,
            (qExpansion h (ModularForm.norm 𝒮ℒ (f - g))).coeff m = 0 := by
          have qCoeffNorm :=
            qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero (Γ := Γ) (k := k)
          intro m hm
          exact qCoeffNorm (f := (f - g)) (N := N) (n := m) hm hcoeff
        have hfun :
            (fun n : Fin N => (qExpansion h (ModularForm.norm 𝒮ℒ (f - g))).coeff n) =
          fun n : Fin N => (qExpansion h (0 : ModularForm 𝒮ℒ w)).coeff n := by
          ext n
          simpa [qExpansion_zero h] using hcoeff_norm (n : ℕ) n.isLt
        have hnorm : ModularForm.norm 𝒮ℒ (f - g) = (0 : ModularForm 𝒮ℒ w) :=
          hNinj hfun
        have : (f - g : ModularForm GΓ k) = 0 := by
          have := (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := (f - g)) (k := k))
          have hf0 :
              ((f - g : ModularForm GΓ k) : ℍ → ℂ) = 0 :=
            this.1 (by simpa using hnorm)
          exact (coe_eq_zero_iff (f - g)).mp hf0
        simpa [sub_eq_zero] using this
      haveI : FiniteDimensional ℂ (Fin N → ℂ) := by infer_instance
      simpa using (FiniteDimensional.of_injective trunc htrunc_inj)

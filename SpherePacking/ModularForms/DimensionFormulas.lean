/-
Copyright (c) 2025 Sphere Packing Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Lean contributors
-/
module
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import SpherePacking.ModularForms.Eisenstein

/-!
# Dimension formulas for level-one modular forms

Mathlib (≥ v4.30.0) proves the level-one dimension formulas in
`Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula`
(`ModularForm.dimension_level_one`, the rank lemmas for small weights, and
`CuspForm.discriminantEquiv`) and the identity `Δ = (E₄³ - E₆²) / 1728` in
`Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing`. Those results are stated for the
subgroup `𝒮ℒ`; this file transports the ones the project uses to the `Γ(1)`-indexed
spaces used here (`CongruenceSubgroup.Gamma_one_coe_eq_SL`).
-/

@[expose] public section

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

noncomputable section

private theorem slashInvariantForm_mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)}
    (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z := rfl

/-- `Module.rank` of a `ModularForm` space is invariant under equality of the underlying subgroup.
Bridges the project's `Γ(1)`-indexed spaces to mathlib's `𝒮ℒ`-indexed level-one dimension lemmas
(`𝒮ℒ = (mapGL ℝ).range = ↑Γ(1)`, via `CongruenceSubgroup.Gamma_one_coe_eq_SL`). -/
private lemma rank_modularForm_congr {k : ℤ} {G₁ G₂ : Subgroup (GL (Fin 2) ℝ)}
    [G₁.HasDetOne] [G₂.HasDetOne] (h : G₁ = G₂) :
    Module.rank ℂ (ModularForm G₁ k) = Module.rank ℂ (ModularForm G₂ k) := by
  subst h; rfl

/-- `CuspForm` analogue of `rank_modularForm_congr`. -/
private lemma rank_cuspForm_congr {k : ℤ} {G₁ G₂ : Subgroup (GL (Fin 2) ℝ)}
    [G₁.HasDetOne] [G₂.HasDetOne] (h : G₁ = G₂) :
    Module.rank ℂ (CuspForm G₁ k) = Module.rank ℂ (CuspForm G₂ k) := by
  subst h; rfl

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) : Module.rank ℂ (CuspForm Γ(1) k) = 0 :=
  (rank_cuspForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL).trans
    (CuspForm.rank_eq_zero_of_weight_lt_twelve hk)

/-
lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2 := CuspForm_to_ModularForm_coe _ _ f hf
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
  ext
  rfl

theorem Delta_E4_eqn : Delta = Delta_E4_E6_aux := by
  ext z
  have hE4 : ModularForm.E₄ z = E₄ z := rfl
  have hE6 : ModularForm.E₆ z = E₆ z := rfl
  have hl : Delta z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728 := by
    rw [Delta_apply, show Δ = ModularForm.discriminant from Δ_eq_discriminant, ← hE4, ← hE6]
    exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  have hr : Delta_E4_E6_aux z =
      ((1 / 1728 : ℂ) • (((DirectSum.of _ 4 E₄) ^ 3 - (DirectSum.of _ 6 E₆) ^ 2) 12)) z :=
    congr_fun (congr_arg (fun (f : ModularForm Γ(1) 12) => (f : ℍ → ℂ)) Delta_E4_E6_eq) z
  have h3 : (((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ 3) 12) z = E₄ z ^ 3 := by
    rw [show (12 : ℤ) = 4 + (4 + 4) by norm_num, pow_three, DirectSum.of_mul_of,
      DirectSum.of_mul_of, DirectSum.of_eq_same]
    change E₄ z * (E₄ z * E₄ z) = E₄ z ^ 3
    ring
  have h2 : (((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ 2) 12) z = E₆ z ^ 2 := by
    rw [show (12 : ℤ) = 6 + 6 by norm_num, pow_two, DirectSum.of_mul_of, DirectSum.of_eq_same]
    change E₆ z * E₆ z = E₆ z ^ 2
    ring
  rw [hl, hr]
  simp only [IsGLPos.smul_apply, DirectSum.sub_apply, ModularForm.sub_apply, h3, h2, smul_eq_mul]
  ring

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 :=
  (rank_modularForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL).trans
    ModularForm.levelOne_weight_six_rank_one

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 :=
  (rank_modularForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL).trans
    ModularForm.levelOne_weight_four_rank_one

lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_modularForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL,
    ModularForm.rank_eq_one_add_rank_cuspForm (by exact_mod_cast hk) hk2,
    CuspForm.rank_eq_zero_of_weight_lt_twelve (by exact_mod_cast hk3)]
  simp

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

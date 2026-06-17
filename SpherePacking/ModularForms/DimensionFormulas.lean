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

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

theorem mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁)
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

lemma Delta_E4_E6_eq : ModForm_mk _ _ Delta_E4_E6_aux =
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

lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry
--use the norm to turn it into a level one question.

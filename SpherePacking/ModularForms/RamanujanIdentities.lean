/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import SpherePacking.ModularForms.EisensteinAsymptotics
public import SpherePacking.Tactic.TendstoCont

/-!
# Ramanujan Identities for Eisenstein Series

This file contains the fundamental Ramanujan identities for Eisenstein series
(Blueprint Theorem 6.50).

## Main results (Serre derivative forms)

* `ramanujan_E₂'` : `serre_D 1 E₂ = -E₄/12` (requires explicit computation since E₂ is not modular)
* `ramanujan_E₄'` : `serre_D 4 E₄ = -E₆/3` (uses dimension formula for weight-6 forms)
* `ramanujan_E₆'` : `serre_D 6 E₆ = -E₄²/2` (uses dimension formula for weight-8 forms)

## Derived identities (D-derivative forms)

* `ramanujan_E₂` : `D E₂ = (E₂² - E₄)/12`
* `ramanujan_E₄` : `D E₄ = (E₂·E₄ - E₆)/3`
* `ramanujan_E₆` : `D E₆ = (E₂·E₆ - E₄²)/2`

## Proof Strategy

Uses dimension formulas: dim M_k(Γ(1)) = 1 for k = 4, 6, 8.
Since serre_D k E_k is a modular form in the 1-dimensional space,
it must be a scalar multiple of the unique generator.
The scalar is determined by comparing limits as z → i∞.
-/

@[expose] public section

open UpperHalfPlane

open scoped MatrixGroups

noncomputable section

/-! ## The Ramanujan Identities

These are the main theorems. The primed versions are in terms of serre_D,
the non-primed versions are in terms of D. -/

/-- In a rank-one module, every element is a scalar multiple of any nonzero element. -/
private lemma exists_smul_eq_of_rank_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, f = c • e :=
  ((finrank_eq_one_iff_of_nonzero' e he).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f).imp fun _ hc => hc.symm

private lemma smul_modularForm_eq_pointwise {Γ : Subgroup SL(2, ℤ)} {k : ℤ}
    {f g : ModularForm Γ k} {c : ℂ} (h : f = c • g) (z : ℍ) :
    (f : ℍ → ℂ) z = c * (g : ℍ → ℂ) z := by simp [h]

/-- Determine scalar coefficient from limits: if `f = c * g` pointwise,
`f → L` at i∞, and `g → 1` at i∞, then `c = L`.

This captures the "uniqueness of limits" argument used in dimension-1 proofs. -/
lemma scalar_eq_of_tendsto {f g : ℍ → ℂ} {c L : ℂ} (hfun : ∀ z, f z = c * g z)
    (hf_lim : Filter.Tendsto f atImInfty (nhds L)) (hg_lim : Filter.Tendsto g atImInfty (nhds 1)) :
    c = L := by
  simpa using tendsto_nhds_unique
    ((tendsto_const_nhds.mul hg_lim).congr fun z => (hfun z).symm) hf_lim

/--
Serre derivative of E₂: `serre_D 1 E₂ = - 12⁻¹ * E₄`.

This is the hardest identity because E₂ is not modular.
The proof uses:
1. `serre_DE₂_slash_invariant`: serre_D 1 E₂ is weight-4 slash-invariant
2. Bounded at infinity: serre_D 1 E₂ = D E₂ - (1/12) E₂², both terms bounded
3. Dimension formula: weight-4 forms are 1-dimensional, spanned by E₄
4. Constant term: serre_D 1 E₂(iy) → -1/12 as y → ∞
-/
theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_rank_one weight_four_one_dimensional E4_ne_zero
    serre_DE₂_ModularForm
  have hfun : ∀ z, serre_D 1 E₂ z = c * E₄.toFun z := smul_modularForm_eq_pointwise hc
  have hc_val : c = -(1/12 : ℂ) :=
    scalar_eq_of_tendsto hfun serre_DE₂_tendsto_atImInfty E₄_tendsto_one_atImInfty
  ext z
  simp only [hfun z, hc_val, Pi.mul_apply]
  norm_num

/-- Serre derivative of E₄: `serre_D 4 E₄ = - 3⁻¹ * E₆`.

Uses the dimension argument:
1. serre_D 4 E₄ is a weight-6 modular form (serre_DE₄_ModularForm)
2. Weight-6 modular forms are 1-dimensional (weight_six_one_dimensional)
3. Constant term is -1/3 (from D E₄ → 0, E₂ → 1, E₄ → 1)
-/
theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_rank_one weight_six_one_dimensional E6_ne_zero
    serre_DE₄_ModularForm
  have hfun : ∀ z, serre_D 4 E₄.toFun z = c * E₆.toFun z := smul_modularForm_eq_pointwise hc
  have hc_val : c = -(1/3 : ℂ) :=
    scalar_eq_of_tendsto hfun serre_DE₄_tendsto_atImInfty E₆_tendsto_one_atImInfty
  ext z
  simp only [hfun z, hc_val, Pi.mul_apply]
  norm_num

/-- Serre derivative of E₆: `serre_D 6 E₆ = - 2⁻¹ * E₄²`.

Uses the dimension argument:
1. serre_D 6 E₆ is weight-8 slash-invariant (by serre_D_slash_invariant)
2. Weight-8 modular forms are 1-dimensional, spanned by E₄²
3. Constant term is -1/2 (from D E₆ → 0, E₂ → 1, E₆ → 1)
-/
theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by
  let E₄_sq : ModularForm (CongruenceSubgroup.Gamma 1) 8 :=
    (by norm_num : (4 : ℤ) + 4 = 8) ▸ E₄.mul E₄
  have hE₄_sq_ne : E₄_sq ≠ 0 := fun h => E4_ne_zero <| by
    ext z
    have := congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) h) z
    simp at this
    exact mul_self_eq_zero.mp this
  obtain ⟨c, hc⟩ := exists_smul_eq_of_rank_one
    (weight_eight_one_dimensional 8 (by norm_num) ⟨4, rfl⟩ (by norm_num)) hE₄_sq_ne
    serre_DE₆_ModularForm
  have hfun : ∀ z, serre_D 6 E₆.toFun z = c * (E₄.toFun z * E₄.toFun z) := fun z =>
    smul_modularForm_eq_pointwise hc z
  have hc_val : c = -(1/2 : ℂ) := scalar_eq_of_tendsto hfun serre_DE₆_tendsto_atImInfty
    (by tendsto_cont [E₄_tendsto_one_atImInfty])
  ext z
  simp only [hfun z, hc_val, Pi.mul_apply]
  ring_nf
  norm_num

/-! ## Derived Ramanujan identities (D instead of serre_D) -/

/-- Relationship between D and serre_D: `D f = serre_D k f + k/12 * E₂ * f`. -/
lemma D_eq_serre_D_add (k : ℂ) (f : ℍ → ℂ) (z : ℍ) :
    D f z = serre_D k f z + k * 12⁻¹ * E₂ z * f z := by
  simp only [serre_D_apply]; ring

@[simp]
theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  ext z
  rw [D_eq_serre_D_add 1 E₂ z]
  simp only [congrFun ramanujan_E₂' z, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.inv_apply,
    Pi.ofNat_apply]
  ring

@[simp]
theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  ext z
  rw [D_eq_serre_D_add 4 E₄.toFun z]
  simp only [congrFun ramanujan_E₄' z, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.inv_apply,
    Pi.ofNat_apply]
  ring

@[simp]
theorem ramanujan_E₆ : D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  rw [D_eq_serre_D_add 6 E₆.toFun z]
  simp only [congrFun ramanujan_E₆' z, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.inv_apply,
    Pi.ofNat_apply]
  ring

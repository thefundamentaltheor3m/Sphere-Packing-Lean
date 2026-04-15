module
public import SpherePacking.ModularForms.SerreDerivativeSlash
public import SpherePacking.ModularForms.DimensionFormulas
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Asymptotic Behavior of Eisenstein Series

This file establishes the asymptotic behavior of Eisenstein series as z → i∞,
and constructs the ModularForm structures for Serre derivatives.

## Main definitions

* `serre_DE₄_ModularForm`, `serre_DE₆_ModularForm`, `serre_DE₂_ModularForm` :
  Package serre derivatives as modular forms

## Main results

* `D_tendsto_zero_of_tendsto_const` : Cauchy estimate: D f → 0 at i∞ if f is bounded
* `E₂_tendsto_one_atImInfty` : E₂ → 1 at i∞
* `serre_DE₄_tendsto_atImInfty`, `serre_DE₆_tendsto_atImInfty`,
  `serre_DE₂_tendsto_atImInfty` : Limits of serre derivatives (for determining scalars)
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## Limits of Eisenstein series at infinity -/

/-- exp(-c * y) → 0 as y → +∞ (for c > 0). -/
public lemma tendsto_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-c * y)) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun y => -c * y) Filter.atTop Filter.atBot := by
    simpa using Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact Real.tendsto_exp_atBot.comp this

/-- If f = O(exp(-c * Im z)) as z → i∞ for c > 0, then f → 0 at i∞. -/
public lemma tendsto_zero_of_exp_decay {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Filter.Tendsto f atImInfty (nhds 0) :=
  hO.trans_tendsto ((tendsto_exp_neg_mul_atTop hc).comp tendsto_im_atImInfty)

/-- A modular form tends to its value at infinity as z → i∞. -/
public lemma modular_form_tendsto_atImInfty {k : ℤ} (f : ModularForm (Gamma 1) k) :
    Filter.Tendsto f.toFun atImInfty (nhds ((qExpansion 1 f).coeff 0)) := by
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  rw [qExpansion_coeff_zero f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods_SL2Z]
  simpa using (tendsto_zero_of_exp_decay hc hO).add_const (valueAtInfty f.toFun)

/-- E₂ → 1 at i∞. -/
public lemma E₂_tendsto_one_atImInfty : Filter.Tendsto E₂ atImInfty (nhds 1) := tendsto_E₂_atImInfty

/-- E₄ → 1 at i∞. -/
public lemma E₄_tendsto_one_atImInfty : Filter.Tendsto E₄.toFun atImInfty (nhds 1) :=
  E4_q_exp_zero ▸ modular_form_tendsto_atImInfty E₄

/-- E₆ → 1 at i∞. -/
public lemma E₆_tendsto_one_atImInfty : Filter.Tendsto E₆.toFun atImInfty (nhds 1) :=
  E6_q_exp_zero ▸ modular_form_tendsto_atImInfty E₆

/-! ## Boundedness lemmas -/

/-- E₆ is bounded at infinity (as a modular form). -/
public lemma E₆_isBoundedAtImInfty : IsBoundedAtImInfty E₆.toFun :=
  ModularFormClass.bdd_at_infty E₆

/-- serre_D 1 E₂ is bounded at infinity. -/
public lemma serre_DE₂_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 1 E₂) :=
  serre_D_isBoundedAtImInfty 1 E₂_holo' E₂_isBoundedAtImInfty

/-! ## Construction of ModularForm from serre_D -/

/-- serre_D 4 E₄ is a weight-6 modular form. -/
public def serre_DE₄_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 6 :=
  serre_D_ModularForm 4 E₄

/-- serre_D 6 E₆ is a weight-8 modular form. -/
public def serre_DE₆_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 8 :=
  serre_D_ModularForm 6 E₆

/-! ## Limit of serre_D at infinity (for determining scalar) -/

/-- General limit: if `f → c` at i∞ and f is holomorphic and bounded, then `serre_D k f → -k*c/12`.

This is the continuous mapping theorem applied to `serre_D k f = D f - (k/12) * E₂ * f`:
- D f → 0 (Cauchy estimate from boundedness)
- E₂ → 1
- f → c
Therefore `serre_D k f → 0 - (k/12) * 1 * c = -k*c/12`. -/
lemma serre_D_tendsto_of_tendsto (k : ℤ) (f : ℍ → ℂ) (c : ℂ)
    (hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds c)) :
    Filter.Tendsto (serre_D k f) atImInfty (nhds (-(k : ℂ) * c / 12)) := by
  rw [show serre_D k f = fun z => D f z - (k : ℂ) * 12⁻¹ * E₂ z * f z from serre_D_eq k f]
  have hD := D_tendsto_zero_of_isBoundedAtImInfty hf_holo hf_bdd
  have hprod := E₂_tendsto_one_atImInfty.mul hf_lim
  have hlim : (0 : ℂ) - (k : ℂ) * 12⁻¹ * 1 * c = -(k : ℂ) * c / 12 := by ring
  rw [← hlim]
  refine hD.sub ?_
  have hconst : Filter.Tendsto (fun _ : ℍ => (k : ℂ) * 12⁻¹)
      atImInfty (nhds ((k : ℂ) * 12⁻¹)) := tendsto_const_nhds
  convert hconst.mul hprod using 1 <;> ring_nf

/-- Special case: if `f → 1` at i∞, then `serre_D k f → -k/12`. -/
lemma serre_D_tendsto_neg_k_div_12 (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 1)) :
    Filter.Tendsto (serre_D k f) atImInfty (nhds (-(k : ℂ) / 12)) := by
  simpa using serre_D_tendsto_of_tendsto k f 1 hf_holo hf_bdd hf_lim

/-- Special case: if `f → 0` at i∞, then `serre_D k f → 0`. -/
lemma serre_D_tendsto_zero_of_tendsto_zero (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 0)) :
    Filter.Tendsto (serre_D k f) atImInfty (nhds 0) := by
  simpa using serre_D_tendsto_of_tendsto k f 0 hf_holo hf_bdd hf_lim

/-- serre_D 4 E₄ → -1/3 at i∞. -/
public lemma serre_DE₄_tendsto_atImInfty :
    Filter.Tendsto (serre_D 4 E₄.toFun) atImInfty (nhds (-(1/3 : ℂ))) := by
  convert serre_D_tendsto_neg_k_div_12 4 E₄.toFun E₄.holo'
    (ModularFormClass.bdd_at_infty E₄) E₄_tendsto_one_atImInfty using 2
  norm_num

/-- serre_D 6 E₆ → -1/2 at i∞. -/
public lemma serre_DE₆_tendsto_atImInfty :
    Filter.Tendsto (serre_D 6 E₆.toFun) atImInfty (nhds (-(1/2 : ℂ))) := by
  convert serre_D_tendsto_neg_k_div_12 6 E₆.toFun E₆.holo'
    E₆_isBoundedAtImInfty E₆_tendsto_one_atImInfty using 2
  norm_num

/-- serre_D 1 E₂ is a weight-4 modular form.
Note: E₂ itself is NOT a modular form, but serre_D 1 E₂ IS. -/
public def serre_DE₂_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 4 where
  toSlashInvariantForm := {
    toFun := serre_D 1 E₂
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, rfl⟩ := hγ
      exact serre_DE₂_slash_invariant γ'
  }
  holo' := serre_D_differentiable E₂_holo'
  bdd_at_cusps' := fun hc =>
    bounded_at_cusps_of_bounded_at_infty hc fun _ hA => by
      obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hA
      exact (serre_DE₂_slash_invariant A').symm ▸ serre_DE₂_isBoundedAtImInfty

/-- serre_D 1 E₂ → -1/12 at i∞. -/
public lemma serre_DE₂_tendsto_atImInfty :
    Filter.Tendsto (serre_D 1 E₂) atImInfty (nhds (-(1/12 : ℂ))) := by
  have h := serre_D_tendsto_neg_k_div_12 1 E₂ E₂_holo'
    E₂_isBoundedAtImInfty E₂_tendsto_one_atImInfty
  simp only [Int.cast_one, neg_div] at h
  exact h

/-! ## Generic q-expansion summability and derivative bounds -/


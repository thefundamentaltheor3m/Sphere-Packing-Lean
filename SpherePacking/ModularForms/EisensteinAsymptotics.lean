/-
Copyright (c) 2024 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import SpherePacking.ModularForms.Derivative
public import SpherePacking.ModularForms.DimensionFormulas
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Asymptotic Behavior of Eisenstein Series

This file establishes the asymptotic behavior of Eisenstein series and of Serre derivatives as
`z → i∞`. (`E₂ → 1` is Mathlib's `EisensteinSeries.tendsto_E2_atImInfty`.)

## Main results

* `E₂_sub_one_isBigO_exp` : `E₂ - 1 = O(exp(-2π im z))` at `i∞`
* `E₄_tendsto_one_atImInfty`, `E₆_tendsto_one_atImInfty` : `E₄, E₆ → 1` at `i∞`
* `serreDerivative_tendsto_of_tendsto` : the limit of `∂ₖ f` at `i∞` from that of `f`
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm hiding E₄ E₆
open Real Complex CongruenceSubgroup Filter SlashInvariantFormClass ModularFormClass

open scoped Manifold MatrixGroups
open Derivative

noncomputable section

/-! ## Limits of Eisenstein series at infinity -/

/-- If f = O(exp(-c * Im z)) as z → i∞ for c > 0, then f → 0 at i∞. -/
lemma tendsto_zero_of_exp_decay {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Filter.Tendsto f atImInfty (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => Real.exp (-c * y)) Filter.atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  exact hO.trans_tendsto (h.comp tendsto_im_atImInfty)

/-- A modular form tends to its value at infinity as z → i∞. -/
lemma modular_form_tendsto_atImInfty {k : ℤ} (f : ModularForm (Gamma 1) k) :
    Filter.Tendsto f.toFun atImInfty (nhds ((qExpansion 1 f).coeff 0)) := by
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  have hΓ : (1 : ℝ) ∈ (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ one_mem_strictPeriods_SL
  rw [qExpansion_coeff_zero (by norm_num : (0 : ℝ) < 1)
    (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) hΓ)
    (periodic_comp_ofComplex f hΓ)]
  simpa using (tendsto_zero_of_exp_decay hc hO).add_const (valueAtInfty f.toFun)

/-- E₂ - 1 = O(exp(-2π·Im z)) at infinity. -/
lemma E₂_sub_one_isBigO_exp : (fun z : ℍ => E₂ z - 1) =O[atImInfty]
    fun z => Real.exp (-(2 * π) * z.im) := by
  have h := exp_decay_sub_atImInfty one_pos EisensteinSeries.E2_periodic
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  simpa [neg_mul, show valueAtInfty E₂ = 1 from
    EisensteinSeries.tendsto_E2_atImInfty.limUnder_eq] using h

/-- E₄ → 1 at i∞. -/
lemma E₄_tendsto_one_atImInfty : Filter.Tendsto E₄.toFun atImInfty (nhds 1) :=
  E4_q_exp_zero ▸ modular_form_tendsto_atImInfty E₄

/-- E₆ → 1 at i∞. -/
lemma E₆_tendsto_one_atImInfty : Filter.Tendsto E₆.toFun atImInfty (nhds 1) :=
  E6_q_exp_zero ▸ modular_form_tendsto_atImInfty E₆

/-! ## Boundedness lemmas -/

/-- E₄ is bounded at infinity (as a modular form). -/
lemma E₄_isBoundedAtImInfty : IsBoundedAtImInfty E₄.toFun :=
  ModularFormClass.bdd_at_infty E₄

/-- E₆ is bounded at infinity (as a modular form). -/
lemma E₆_isBoundedAtImInfty : IsBoundedAtImInfty E₆.toFun :=
  ModularFormClass.bdd_at_infty E₆

/-! ## Limit of the Serre derivative at infinity -/

/-- General limit: if `f → c` at i∞ and f is holomorphic and bounded, then `∂ₖ f → -k*c/12`.

This is the continuous mapping theorem applied to `∂ₖ f = D f - (k/12) * E₂ * f`:
- D f → 0 (Cauchy estimate from boundedness)
- E₂ → 1
- f → c
Therefore `∂ₖ f → 0 - (k/12) * 1 * c = -k*c/12`. -/
lemma serreDerivative_tendsto_of_tendsto (k : ℤ) (f : ℍ → ℂ) (c : ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds c)) :
    Filter.Tendsto (serreDerivative k f) atImInfty (nhds (-(k : ℂ) * c / 12)) := by
  rw [show serreDerivative k f = fun z => D f z - (k : ℂ) * 12⁻¹ * E₂ z * f z from
    serreDerivative_eq k f, show -(k : ℂ) * c / 12 = 0 - (k : ℂ) * 12⁻¹ * 1 * c by ring]
  exact Filter.Tendsto.sub (isZeroAtImInfty_normalizedDerivOfComplex hf_holo hf_bdd)
    ((tendsto_const_nhds.mul EisensteinSeries.tendsto_E2_atImInfty).mul hf_lim)

/-- Special case: if `f → 1` at i∞, then `∂ₖ f → -k/12`. -/
lemma serreDerivative_tendsto_neg_k_div_12 (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 1)) :
    Filter.Tendsto (serreDerivative k f) atImInfty (nhds (-(k : ℂ) / 12)) := by
  simpa using serreDerivative_tendsto_of_tendsto k f 1 hf_holo hf_bdd hf_lim

/-- Special case: if `f → 0` at i∞, then `∂ₖ f → 0`. -/
lemma serreDerivative_tendsto_zero_of_tendsto_zero (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 0)) :
    Filter.Tendsto (serreDerivative k f) atImInfty (nhds 0) := by
  simpa using serreDerivative_tendsto_of_tendsto k f 0 hf_holo hf_bdd hf_lim

/-! ## Generic q-expansion summability -/

/-- Summability of (m+1)^k * exp(-2πm) via comparison with shifted sum. -/
lemma summable_pow_shift (k : ℕ) :
    Summable fun m : ℕ => (m + 1 : ℝ) ^ k * rexp (-2 * π * m) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul k (by positivity : 0 < 2 * π)
  have h_eq : ∀ m : ℕ, (m + 1 : ℝ) ^ k * rexp (-2 * π * m) =
      rexp (2 * π) * ((m + 1) ^ k * rexp (-2 * π * (m + 1))) := fun m => by
    rw [show (-2 : ℝ) * π * m = 2 * π + -2 * π * (m + 1) by ring, Real.exp_add]
    ring
  simp_rw [h_eq]
  exact ((h.comp_injective Nat.succ_injective).congr fun i => by
    simp [Function.comp_apply, Nat.succ_eq_add_one]).mul_left _

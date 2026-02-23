module
public import SpherePacking.ModularForms.DimGenCongLevels.NormReduction

import Mathlib.Analysis.Complex.Periodic

/-!
# Transfer of `q`-coefficient vanishing under norm

This file proves the "norm step" in `dim_gen_cong_levels`: if the first `N` `q`-coefficients of a
modular form on a finite-index subgroup vanish at `∞`, then the same coefficients vanish for the
norm of that form to level one.

## Main statement
* `qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero`
-/

namespace SpherePacking.ModularForms.NormReduction

open scoped MatrixGroups Topology BigOperators
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass Filter

noncomputable section
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

@[reducible] noncomputable def τfun (h : ℝ) : ℂ → ℍ :=
  fun q : ℂ => UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q)

lemma tendsto_τfun_atImInfty {h : ℝ} (hh : 0 < h) :
    Tendsto (τfun h) (𝓝[≠] (0 : ℂ)) UpperHalfPlane.atImInfty := by
  simpa [τfun] using
    UpperHalfPlane.tendsto_comap_im_ofComplex.comp
      (Function.Periodic.invQParam_tendsto (h := h) hh)

lemma cuspFunction_eq_eval_τfun_of_ne_zero
    {Γ' : Subgroup (GL (Fin 2) ℝ)} {k' : ℤ} {h : ℝ} (f : ModularForm Γ' k') {q : ℂ}
    (hq : q ≠ 0) : cuspFunction h f q = f (τfun h q) := by
  simp [cuspFunction, Function.Periodic.cuspFunction, τfun, hq]

lemma norm_apply_eq_mul_restProd
    (Γ : Subgroup SL(2, ℤ)) [(G Γ).IsFiniteRelIndex 𝒮ℒ] (f : ModularForm (G Γ) k) (τ : ℍ) :
    (ModularForm.norm 𝒮ℒ f) τ = f τ * restProd (Γ := Γ) (k := k) f τ := by
  letI : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  letI : DecidableEq (Q Γ) := Classical.decEq (Q Γ)
  set q₁ : Q Γ := (⟦(1 : 𝒮ℒ)⟧ : Q Γ)
  have hmem : q₁ ∈ (Finset.univ : Finset (Q Γ)) := by simp [q₁]
  have hnorm :
      (ModularForm.norm 𝒮ℒ f) τ =
        ∏ q : Q Γ,
          (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) τ := by
    simp [ModularForm.coe_norm]
  have hsplit :
      (∏ q : Q Γ,
          (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) τ) =
        (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q₁) τ *
          ∏ q ∈ (Finset.univ : Finset (Q Γ)).erase q₁,
            (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) τ := by
    simpa using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Q Γ)))
        (f := fun q =>
          (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) τ) hmem).symm
  have hone :
      (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q₁) τ = f τ := by
    simp [q₁, SlashInvariantForm.quotientFunc_mk]
  have hrest :
      (∏ q ∈ (Finset.univ : Finset (Q Γ)).erase q₁,
          (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) τ) =
        restProd (Γ := Γ) (k := k) f τ := by
    simp [NormReduction.restProd, q₁, Finset.prod_apply]
    rfl
  simp_all

lemma cuspFunction_norm_eq_mul_restProd_of_ne_zero
    (Γ : Subgroup SL(2, ℤ)) [(G Γ).IsFiniteRelIndex 𝒮ℒ] (f : ModularForm (G Γ) k) {h : ℝ} {q : ℂ}
    (hq : q ≠ 0) :
    cuspFunction h (ModularForm.norm 𝒮ℒ f) q =
      cuspFunction h f q * restProd (Γ := Γ) (k := k) f (τfun h q) := by
  rw [cuspFunction_eq_eval_τfun_of_ne_zero (f := ModularForm.norm 𝒮ℒ f) (hq := hq),
    cuspFunction_eq_eval_τfun_of_ne_zero (f := f) (hq := hq)]
  simpa [mul_assoc] using norm_apply_eq_mul_restProd (Γ := Γ) (k := k) f (τfun h q)

lemma isBigO_nhds_of_isBigO_punctured {f : ℂ → ℂ} {g : ℂ → ℝ}
    (hO : f =O[𝓝[≠] (0 : ℂ)] g) (hf0 : ‖f 0‖ = 0) :
    f =O[𝓝 (0 : ℂ)] g := by
  rcases hO.exists_nonneg with ⟨C, hC0, hC⟩
  refine Asymptotics.IsBigO.of_bound C ?_
  have hC' : ∀ᶠ q : ℂ in 𝓝 (0 : ℂ), q ≠ 0 → ‖f q‖ ≤ C * ‖(g q : ℝ)‖ := by
    simpa [eventually_nhdsWithin_iff] using hC.bound
  filter_upwards [hC'] with q hq
  by_cases hq0 : q = 0
  · subst hq0
    simpa [hf0] using mul_nonneg hC0 (norm_nonneg (g 0))
  · exact hq hq0

lemma valueAtInfty_norm_eq_zero_of_valueAtInfty_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : ModularForm (G Γ) k)
    (hΓ : Subgroup.index Γ ≠ 0) (hval0 : valueAtInfty f = 0) :
    valueAtInfty (ModularForm.norm 𝒮ℒ f) = 0 := by
  have hh : 0 < cuspWidth (Γ := Γ) := cuspWidth_pos (Γ := Γ) hΓ
  have hperΓ : cuspWidth (Γ := Γ) ∈ (G Γ).strictPeriods :=
    cuspWidth_mem_strictPeriods (Γ := Γ)
  have hperSL : cuspWidth (Γ := Γ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    cuspWidth_mem_strictPeriods_levelOne (Γ := Γ)
  haveI : (G Γ).IsArithmetic := instIsArithmetic (Γ := Γ) hΓ
  haveI : (G Γ).IsFiniteRelIndex 𝒮ℒ :=
    Subgroup.IsArithmetic.isFiniteRelIndexSL (𝒢 := (G Γ))
  have ht_f :
      Tendsto (fun τ : ℍ => f τ) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    simpa [hval0] using
      (modularForm_tendsto_valueAtInfty (f := f) (h := cuspWidth (Γ := Γ)) hh hperΓ)
  have hbd_rest_im :
      IsBoundedUnder (· ≤ ·) UpperHalfPlane.atImInfty
        (fun τ : ℍ => ‖restProd (Γ := Γ) (k := k) f τ‖) := by
    have hbd :
        (fun τ : ℍ => restProd (Γ := Γ) (k := k) f τ) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
      simpa [UpperHalfPlane.IsBoundedAtImInfty, Filter.BoundedAtFilter] using
        (restProd_isBoundedAtImInfty (Γ := Γ) (k := k) hΓ f)
    simpa [Function.comp] using hbd.isBoundedUnder_le
  have ht_mul :
      Tendsto (fun τ : ℍ => f τ * restProd (Γ := Γ) (k := k) f τ) UpperHalfPlane.atImInfty
        (𝓝 (0 : ℂ)) := by
    simpa [smul_eq_mul] using
      (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded (l := UpperHalfPlane.atImInfty)
        (ε := fun τ : ℍ => f τ) (f := fun τ : ℍ => restProd (Γ := Γ) (k := k) f τ) ht_f
        hbd_rest_im)
  have ht_norm :
      Tendsto (fun τ : ℍ => (ModularForm.norm 𝒮ℒ f) τ) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    simpa [norm_apply_eq_mul_restProd (Γ := Γ) (k := k) f] using ht_mul
  have ht_val :
      Tendsto (fun τ : ℍ => (ModularForm.norm 𝒮ℒ f) τ) UpperHalfPlane.atImInfty
        (𝓝 (valueAtInfty (ModularForm.norm 𝒮ℒ f))) :=
    modularForm_tendsto_valueAtInfty (f := ModularForm.norm 𝒮ℒ f)
      (h := cuspWidth (Γ := Γ)) hh hperSL
  exact (tendsto_nhds_unique ht_norm ht_val).symm

/-- Vanishing of the first `N` `q`-coefficients is preserved under taking the norm to level one. -/
public lemma qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : ModularForm (G Γ) k) (N n : ℕ)
    (hn : n < N) (hcoeff : ∀ m < N, (qExpansion (cuspWidth (Γ := Γ)) f).coeff m = 0) :
    (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ f)).coeff n = 0 := by
  have hΓ : Subgroup.index Γ ≠ 0 := Subgroup.FiniteIndex.index_ne_zero (H := Γ)
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le n) hn
  have hh : 0 < cuspWidth (Γ := Γ) := cuspWidth_pos (Γ := Γ) hΓ
  have hperΓ : cuspWidth (Γ := Γ) ∈ (G Γ).strictPeriods :=
    cuspWidth_mem_strictPeriods (Γ := Γ)
  have hperSL : cuspWidth (Γ := Γ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    cuspWidth_mem_strictPeriods_levelOne (Γ := Γ)
  haveI : (G Γ).IsArithmetic := instIsArithmetic (Γ := Γ) hΓ
  haveI : (G Γ).IsFiniteRelIndex 𝒮ℒ := Subgroup.IsArithmetic.isFiniteRelIndexSL (𝒢 := (G Γ))
  letI : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  letI : DecidableEq (Q Γ) := Classical.decEq _
  -- Step 1: the vanishing of coefficients for `f` gives a `O(‖q‖^N)` bound for `cuspFunction`.
  have hO_f :
      cuspFunction (cuspWidth (Γ := Γ)) f =O[𝓝 (0 : ℂ)] fun q : ℂ =>
        ‖q‖ ^ N :=
    cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero (f := f) hh hperΓ N hcoeff
  -- Step 2: `restProd` is bounded at `∞`, hence bounded after composing with `invQParam`.
  have hbd_rest :
      Filter.BoundedAtFilter (𝓝[≠] (0 : ℂ))
        (fun q : ℂ => restProd (Γ := Γ) (k := k) f (τfun (cuspWidth (Γ := Γ)) q)) := by
    simpa [UpperHalfPlane.IsBoundedAtImInfty, τfun] using
      (restProd_isBoundedAtImInfty (Γ := Γ) (k := k) hΓ f).comp_tendsto
        (tendsto_τfun_atImInfty (h := cuspWidth (Γ := Γ)) hh)
  -- Step 3: on `𝓝[≠] 0`, use the product formula and boundedness of the remaining factor.
  have hEq :
      (fun q : ℂ =>
          cuspFunction (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ f) q) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun q : ℂ =>
          cuspFunction (cuspWidth (Γ := Γ)) f q *
            restProd (Γ := Γ) (k := k) f (τfun (cuspWidth (Γ := Γ)) q) := by
    have hne : ∀ᶠ q : ℂ in 𝓝[≠] (0 : ℂ), q ∈ ({0}ᶜ : Set ℂ) := self_mem_nhdsWithin
    filter_upwards [hne] with q hq
    have hq0 : q ≠ 0 := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hq
    exact cuspFunction_norm_eq_mul_restProd_of_ne_zero Γ f hq0
  have hO_prod_punct :
      (fun q : ℂ =>
          cuspFunction (cuspWidth (Γ := Γ)) f q *
            restProd (Γ := Γ) (k := k) f (τfun (cuspWidth (Γ := Γ)) q)) =O[𝓝[≠] (0 : ℂ)]
        fun q : ℂ => ‖q‖ ^ N :=
    by
      simpa [Filter.BoundedAtFilter, mul_one] using (hO_f.mono nhdsWithin_le_nhds).mul hbd_rest
  have hO_norm_punct :
      cuspFunction (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ f) =O[𝓝[≠] (0 : ℂ)] fun q : ℂ =>
        ‖q‖ ^ N :=
    (hO_prod_punct.congr' hEq.symm Filter.EventuallyEq.rfl)
  -- Step 4: show the value at `q = 0` is `0`, so we can upgrade to a bound on `𝓝 0`.
  have hval0 : valueAtInfty f = 0 := by
    have h0 :
        (qExpansion (cuspWidth (Γ := Γ)) f).coeff 0 = valueAtInfty f :=
      ModularFormClass.qExpansion_coeff_zero (f := f) (h := cuspWidth (Γ := Γ)) hh hperΓ
    simpa [h0] using hcoeff 0 hNpos
  have hnorm0 : valueAtInfty (ModularForm.norm 𝒮ℒ f) = 0 :=
    valueAtInfty_norm_eq_zero_of_valueAtInfty_eq_zero (k := k) Γ f hΓ hval0
  have hcf0 : ‖cuspFunction (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ f) 0‖ = 0 := by
    have h0 :=
      ModularFormClass.cuspFunction_apply_zero (f := ModularForm.norm 𝒮ℒ f) hh hperSL
    simp_all
  have hO_norm :
      cuspFunction (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ f) =O[𝓝 (0 : ℂ)] fun q : ℂ =>
        ‖q‖ ^ N :=
    isBigO_nhds_of_isBigO_punctured hO_norm_punct hcf0
  -- Step 5: apply the analytic lemma that `O(‖q‖^N)` forces vanishing of coefficients below `N`.
  exact qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow (f := ModularForm.norm 𝒮ℒ f)
    (hh := hh) (hΓ := hperSL) (n := n) (N := N) hn hO_norm

end

end SpherePacking.ModularForms.NormReduction

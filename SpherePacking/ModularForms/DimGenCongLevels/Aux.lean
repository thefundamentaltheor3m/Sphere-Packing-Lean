module
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Auxiliary lemmas for dimension formulas

This file contains auxiliary material for proving
`SpherePacking/ModularForms/DimensionFormulas.lean:517` (`dim_gen_cong_levels`).

Strategy: reduce finite-dimensionality for a finite-index subgroup `Γ ≤ SL(2,ℤ)` to the level-one
case via the norm map `ModularForm.norm`, and use the `q`-expansion principle at `∞` to construct a
finite-dimensional embedding.
-/

namespace SpherePacking.ModularForms

open scoped Topology Real BigOperators
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass Filter

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

section Tendsto

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- Values of a modular form tend to `valueAtInfty` along `atImInfty`. -/
public lemma modularForm_tendsto_valueAtInfty [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (valueAtInfty f)) := by
  have hcont : ContinuousAt (cuspFunction h f) 0 := by
    simpa [cuspFunction] using
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ).continuousAt
  have ht :
      Tendsto (fun τ : ℍ ↦ cuspFunction h f (𝕢 h τ)) atImInfty (𝓝 (cuspFunction h f 0)) :=
    hcont.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hh)
  have ht' : Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (cuspFunction h f 0)) := by
    refine Filter.Tendsto.congr (fun τ ↦ ?_) ht
    simpa [SlashInvariantFormClass.cuspFunction] using
      (SlashInvariantFormClass.eq_cuspFunction (f := f) (h := h) τ hΓ hh.ne')
  simpa [ModularFormClass.cuspFunction_apply_zero (f := f) hh hΓ] using ht'

end Tendsto

section BigO

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- If the first `N` `q`-coefficients vanish, then the cusp function is `O(‖q‖^N)` near `0`. -/
public lemma cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (N : ℕ)
    (hcoeff : ∀ n < N, (qExpansion h f).coeff n = 0) :
  cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ => ‖q‖ ^ N) := by
  -- Use Taylor's theorem for the analytic cusp function at `0`.
  have hfps :
      HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 :=
    (ModularFormClass.hasFPowerSeries_cuspFunction (f := f) hh hΓ).hasFPowerSeriesAt
  have hrem := hfps.isBigO_sub_partialSum_pow N
  -- The partial sum is zero because all coefficients below `N` are zero.
  have hps : (qExpansionFormalMultilinearSeries h f).partialSum N = 0 := by
    ext q
    refine Finset.sum_eq_zero fun n hn => by
      simp [hcoeff n (by simpa [Finset.mem_range] using hn)]
  simpa [zero_add, hps] using hrem

/-!
### From `O(‖q‖^N)` bounds to vanishing of `q`-coefficients

This is a small analytic lemma used in the norm argument: if an analytic cusp function is
`O(‖q‖^N)` at `0`, then all `q`-coefficients below `N` vanish.
-/

lemma norm_cuspFunction_div_pow_le_of_ball_bound
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) {C' δ : ℝ} {N n : ℕ} (hn : n < N)
    (hC' : 0 ≤ C')
    (hδ : Metric.ball (0 : ℂ) δ ⊆ {z | ‖cuspFunction h f z‖ ≤ C' * ‖z‖ ^ N})
    {R : ℝ} (hR0 : 0 < R) (hRltδ : R < δ) (hRlt1 : R < 1) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) R) :
    ‖cuspFunction h f z / z ^ (n + 1)‖ ≤ C' := by
  have hzR : ‖z‖ = R := by simpa [mem_sphere_zero_iff_norm] using hz
  have hz_norm_ne : (‖z‖ : ℝ) ≠ 0 := by simpa [hzR] using (ne_of_gt hR0)
  have hzle1 : ‖z‖ ≤ 1 := by simpa [hzR] using (le_of_lt hRlt1)
  have hcz : ‖cuspFunction h f z‖ ≤ C' * ‖z‖ ^ N := by
    refine hδ ?_
    have : ‖z‖ < δ := by simpa [hzR] using hRltδ
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hpow_le : ‖z‖ ^ N ≤ ‖z‖ ^ (n + 1) :=
    pow_le_pow_of_le_one (norm_nonneg _) hzle1 (Nat.succ_le_of_lt hn)
  have hden0 : (‖z‖ ^ (n + 1) : ℝ) ≠ 0 := pow_ne_zero _ hz_norm_ne
  calc
    ‖cuspFunction h f z / z ^ (n + 1)‖
        = ‖cuspFunction h f z‖ / ‖z ^ (n + 1)‖ := by simp
    _ = ‖cuspFunction h f z‖ / (‖z‖ ^ (n + 1)) := by simp
    _ ≤ (C' * ‖z‖ ^ N) / (‖z‖ ^ (n + 1)) := by
      exact div_le_div_of_nonneg_right hcz (pow_nonneg (norm_nonneg _) _)
    _ ≤ (C' * ‖z‖ ^ (n + 1)) / (‖z‖ ^ (n + 1)) := by
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
      exact mul_le_mul_of_nonneg_left hpow_le hC'
    _ = C' := by field_simp [hden0]

lemma norm_circleIntegral_cuspFunction_div_pow_le
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) {C' δ : ℝ} {N n : ℕ} (hn : n < N)
    (hC' : 0 ≤ C')
    (hδ : Metric.ball (0 : ℂ) δ ⊆ {z | ‖cuspFunction h f z‖ ≤ C' * ‖z‖ ^ N})
    {R : ℝ} (hR0 : 0 < R) (hRltδ : R < δ) (hRlt1 : R < 1) :
    ‖∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)‖ ≤ 2 * π * R * C' := by
  refine circleIntegral.norm_integral_le_of_norm_le_const hR0.le (fun z hz => ?_)
  exact norm_cuspFunction_div_pow_le_of_ball_bound (f := f) (hn := hn)
    (hC' := hC') hδ hR0 hRltδ hRlt1 hz

/-- If `cuspFunction h f = O(‖q‖^N)` near `0`, then the `n`-th `q`-coefficient vanishes. -/
public lemma qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {N n : ℕ} (hn : n < N)
    (hO : cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ => ‖q‖ ^ N)) :
    (qExpansion h f).coeff n = 0 := by
  -- Unpack the `O(‖q‖^N)` bound.
  rcases (Asymptotics.isBigO_iff.1 hO) with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC' : ∀ᶠ q : ℂ in 𝓝 (0 : ℂ), ‖cuspFunction h f q‖ ≤ C' * ‖q‖ ^ N := by
    filter_upwards [hC] with q hq
    have hq' : ‖cuspFunction h f q‖ ≤ C * ‖q‖ ^ N := by simpa using hq
    have hle : C ≤ C' := le_max_left _ _
    exact hq'.trans (by gcongr)
  -- Extract a radius `δ` on which the estimate holds.
  rcases Metric.mem_nhds_iff.1 hC' with ⟨δ, hδ0, hδ⟩
  -- Contradiction argument: if the coefficient is nonzero, take a small circle where the Cauchy
  -- integral estimate forces the coefficient norm to be arbitrarily small.
  by_contra hne
  have hnorm_pos : 0 < ‖(qExpansion h f).coeff n‖ := norm_pos_iff.2 hne
  set ε : ℝ := ‖(qExpansion h f).coeff n‖ / 2
  have hε : 0 < ε := by simpa [ε] using half_pos hnorm_pos
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  -- We'll use a coarse bound in the Cauchy integral formula and choose `R` so that `K * R < ε`.
  set K : ℝ := ‖((2 * π * (Complex.I) : ℂ)⁻¹)‖ * (2 * π * C')
  have hKpos : 0 < K := by
    have h1 : 0 < ‖((2 * π * (Complex.I) : ℂ)⁻¹)‖ := by
      simp [Real.pi_ne_zero]
    have h2 : 0 < (2 * π * C') := by positivity
    exact mul_pos h1 h2
  -- Choose a small radius `R < δ` and `R < 1` with `R ≤ ε / (2K)`.
  set R : ℝ := min (δ / 2) (min (1 / 2) (ε / (2 * K)))
  have hR0 : 0 < R := by
    have h1 : 0 < δ / 2 := by linarith
    have h2 : 0 < (1 / 2 : ℝ) := by norm_num
    have h3 : 0 < ε / (2 * K) := div_pos hε (by positivity)
    exact lt_min h1 (lt_min h2 h3)
  have hRltδ : R < δ := by
    have hRle : R ≤ δ / 2 := min_le_left _ _
    have hδ2 : δ / 2 < δ := by linarith [hδ0]
    exact lt_of_le_of_lt hRle hδ2
  have hRlt1 : R < 1 := by
    have : R ≤ (1 / 2 : ℝ) := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hRle : R ≤ ε / (2 * K) := le_trans (min_le_right _ _) (min_le_right _ _)
  -- Apply the circle integral formula for the coefficient at radius `R`.
  have hcoeff :=
    (ModularFormClass.qExpansion_coeff_eq_circleIntegral (f := f) (Γ := Γ) (k := k) (h := h)
      hh hΓ n (hR := hR0) (hR' := hRlt1))
  -- Bound the circle integral using the estimate on `‖cuspFunction‖`.
  have hbound_int :
      ‖∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)‖
        ≤ 2 * π * R * C' :=
    norm_circleIntegral_cuspFunction_div_pow_le (f := f) (hn := hn)
      (hC' := le_of_lt hC'pos) hδ hR0 hRltδ hRlt1
  -- Convert the bound on the integral into a bound on the coefficient.
  have hcoeff_le : ‖(qExpansion h f).coeff n‖ ≤ K * R := by
    have h' :
        ‖(qExpansion h f).coeff n‖
          ≤ ‖((2 * π * (Complex.I) : ℂ)⁻¹)‖ * (2 * π * R * C') := by
      simp_all
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using h'
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hRlt : R < ε / K := by
    have hKlt : K < 2 * K := by nlinarith [hKpos]
    have hdiv : ε / (2 * K) < ε / K := div_lt_div_of_pos_left hε hKpos hKlt
    exact lt_of_le_of_lt hRle hdiv
  have hcoeff_lt : ‖(qExpansion h f).coeff n‖ < ε := by
    have hKRlt : K * R < ε := by
      have := mul_lt_mul_of_pos_left hRlt hKpos
      simpa [div_eq_mul_inv, hKne, mul_assoc, mul_left_comm, mul_comm] using this
    exact lt_of_le_of_lt hcoeff_le hKRlt
  have : ‖(qExpansion h f).coeff n‖ < ‖(qExpansion h f).coeff n‖ / 2 := by
    simpa [ε] using hcoeff_lt
  linarith

end BigO

section Linearity

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}

open scoped ComplexConjugate

lemma valueAtInfty_add
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f g : ModularForm Γ k) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    valueAtInfty (f + g) = valueAtInfty f + valueAtInfty g := by
  have hf :=
    modularForm_tendsto_valueAtInfty (Γ := Γ) (k := k) (h := h) (f := f) hh hΓ
  have hg :=
    modularForm_tendsto_valueAtInfty (Γ := Γ) (k := k) (h := h) (f := g) hh hΓ
  simpa [UpperHalfPlane.valueAtInfty, Pi.add_apply] using (hf.add hg).limUnder_eq

lemma valueAtInfty_smul
    [DiscreteTopology Γ] [Γ.HasDetOne]
    (a : ℂ) (f : ModularForm Γ k) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    valueAtInfty (a • f) = a • valueAtInfty f := by
  have hf :=
    modularForm_tendsto_valueAtInfty (Γ := Γ) (k := k) (h := h) (f := f) hh hΓ
  simpa [UpperHalfPlane.valueAtInfty, Pi.smul_apply] using (hf.const_smul a).limUnder_eq

lemma cuspFunction_add
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f g : ModularForm Γ k) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h (f + g) = fun q ↦ cuspFunction h f q + cuspFunction h g q := by
  simpa [Pi.add_apply] using
    (_root_.cuspFunction_add (h := h)
      (f := (f : ℍ → ℂ)) (g := (g : ℍ → ℂ))
      (by
        simpa [cuspFunction] using
          (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ).continuousAt)
      (by
        simpa [cuspFunction] using
          (ModularFormClass.analyticAt_cuspFunction_zero (f := g) hh hΓ).continuousAt))

lemma cuspFunction_smul
    [DiscreteTopology Γ] [Γ.HasDetOne]
    (a : ℂ) (f : ModularForm Γ k) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h (a • f) = fun q ↦ a • cuspFunction h f q := by
  simpa [Pi.smul_apply] using
    (_root_.cuspFunction_smul (h := h) (f := (f : ℍ → ℂ))
      (by
        simpa [cuspFunction] using
          (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ).continuousAt)
      a)

end Linearity

end

end SpherePacking.ModularForms

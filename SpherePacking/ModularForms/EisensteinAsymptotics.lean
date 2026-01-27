import SpherePacking.ModularForms.SerreDerivativeSlash
import SpherePacking.ModularForms.DimensionFormulas
import Mathlib.Analysis.Real.Pi.Bounds

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

/-! ## Cauchy estimates and limits at infinity -/

/-- If f is holomorphic and bounded at infinity, then D f → 0 at i∞.

**Proof via Cauchy estimates:**
For z with large Im, consider the ball B(z, Im(z)/2) in ℂ.
- Ball is contained in upper half plane: all points have Im > Im(z)/2 > 0
- f ∘ ofComplex is holomorphic on the ball (from MDifferentiable)
- f is bounded by M for Im ≥ A (from IsBoundedAtImInfty)
- By Cauchy: |deriv(f ∘ ofComplex)(z)| ≤ M / (Im(z)/2) = 2M/Im(z)
- D f = (2πi)⁻¹ * deriv(...), so |D f(z)| ≤ M/(π·Im(z)) → 0 -/
lemma D_tendsto_zero_of_tendsto_const {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    Filter.Tendsto (D f) atImInfty (nhds 0) := by
  rw [isBoundedAtImInfty_iff] at hbdd
  obtain ⟨M, A, hMA⟩ := hbdd
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.Eventually, atImInfty, Filter.mem_comap]
  use Set.Ici (max (2 * max A 0 + 1) (|M| / (π * ε) + 1))
  constructor
  · exact Filter.mem_atTop _
  · intro z hz
    simp only [Set.mem_preimage, Set.mem_Ici] at hz
    have hz_ge_A : z.im / 2 > max A 0 := by linarith [le_trans (le_max_left _ _) hz]
    have hz_ge_bound : z.im > |M| / (π * ε) := by linarith [le_trans (le_max_right _ _) hz]
    have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
      diffContOnCl_comp_ofComplex_of_mdifferentiable hf (closedBall_center_subset_upperHalfPlane z)
    have hR_pos : 0 < z.im / 2 := by positivity
    have hmax_nonneg : 0 ≤ max A 0 := le_max_right _ _
    have hA_le_max : A ≤ max A 0 := le_max_left _ _
    have hf_bdd_sphere : ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
      intro w hw
      have hw_im_pos : 0 < w.im :=
        closedBall_center_subset_upperHalfPlane z (Metric.sphere_subset_closedBall hw)
      have hw_im_ge_A : A ≤ w.im := by
        have habs : |w.im - z.im| ≤ z.im / 2 := by
          calc |w.im - z.im|
            _ = |(w - z).im| := by simp [Complex.sub_im]
            _ ≤ ‖w - z‖ := abs_im_le_norm _
            _ = dist w z := (dist_eq_norm _ _).symm
            _ = z.im / 2 := Metric.mem_sphere.mp hw
        have hlower : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
        have hA_lt : A < w.im := calc A ≤ max A 0 := hA_le_max
          _ < z.im / 2 := hz_ge_A
          _ ≤ w.im := hlower
        linarith
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw_im_pos]
      exact hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
    have hDf_bound : ‖D f z‖ ≤ M / (π * z.im) := by
      have h := norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
      calc ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) := h
        _ = M / (π * z.im) := by ring
    have hM_nonneg : 0 ≤ M := by
      have hA_le_z : A ≤ z.im := by linarith [hA_le_max, hmax_nonneg, hz_ge_A]
      exact le_trans (norm_nonneg _) (hMA z hA_le_z)
    simp only [dist_zero_right]
    by_cases hM_zero : M = 0
    · calc ‖D f z‖
        _ ≤ M / (π * z.im) := hDf_bound
        _ = 0 := by simp [hM_zero]
        _ < ε := hε
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
      calc ‖D f z‖
        _ ≤ M / (π * z.im) := hDf_bound
        _ = |M| / (π * z.im) := by rw [abs_of_pos hM_pos]
        _ < |M| / (π * (|M| / (π * ε))) := by
            apply div_lt_div_of_pos_left (abs_pos.mpr hM_zero)
            · positivity
            · apply mul_lt_mul_of_pos_left hz_ge_bound Real.pi_pos
        _ = ε := by field_simp

/-! ## Limits of Eisenstein series at infinity -/

/-- exp(-c * y) → 0 as y → +∞ (for c > 0). -/
lemma tendsto_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-c * y)) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun y => -c * y) Filter.atTop Filter.atBot := by
    simpa using Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact Real.tendsto_exp_atBot.comp this

/-- If f = O(exp(-c * Im z)) as z → i∞ for c > 0, then f → 0 at i∞. -/
lemma tendsto_zero_of_exp_decay {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Filter.Tendsto f atImInfty (nhds 0) := by
  apply Asymptotics.IsBigO.trans_tendsto hO
  rw [atImInfty]
  exact (tendsto_exp_neg_mul_atTop hc).comp Filter.tendsto_comap

/-- A modular form tends to its value at infinity as z → i∞. -/
lemma modular_form_tendsto_atImInfty {k : ℤ} (f : ModularForm (Gamma 1) k) :
    Filter.Tendsto f.toFun atImInfty (nhds ((qExpansion 1 f).coeff 0)) := by
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  rw [qExpansion_coeff_zero f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods_SL2Z]
  simpa using (tendsto_zero_of_exp_decay hc hO).add_const (valueAtInfty f.toFun)

/-- E₂ - 1 = O(exp(-2π·Im z)) at infinity. -/
lemma E₂_sub_one_isBigO_exp : (fun z : ℍ => E₂ z - 1) =O[atImInfty]
    fun z => Real.exp (-(2 * π) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨192, Filter.eventually_atImInfty.mpr ⟨1, fun z hz => ?_⟩⟩
  -- E₂ z - 1 = -24 * ∑' n, n·qⁿ/(1-qⁿ)
  have hsub : E₂ z - 1 = -24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) := by rw [E₂_eq z]; ring
  rw [hsub, norm_mul, show ‖(-24 : ℂ)‖ = 24 by simp, Real.norm_of_nonneg (Real.exp_pos _).le]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  -- Rewrite sum in terms of q^n
  simp_rw [show ∀ n : ℕ, cexp (2 * π * Complex.I * n * z) = q ^ n by
    intro n; rw [← Complex.exp_nat_mul]; congr 1; ring]
  -- Key bounds: ‖q‖ ≤ exp(-2π) < 1/2
  have hq_bound : ‖q‖ ≤ Real.exp (-2 * π) := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  have hexp_lt_half : Real.exp (-2 * π) < 1 / 2 := by
    have : 1 < 2 * π := by nlinarith [pi_gt_three]
    calc Real.exp (-2 * π) < Real.exp (-1) := Real.exp_strictMono (by linarith)
      _ < 1 / 2 := by
        rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)]
        have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
  have hq_lt_half : ‖q‖ < 1 / 2 := lt_of_le_of_lt hq_bound hexp_lt_half
  have hone_sub_q_gt_half : 1 / 2 < 1 - ‖q‖ := by linarith
  -- Use norm_tsum_logDeriv_expo_le and bound r/(1-r)³ ≤ 8r for r < 1/2
  have htsum_bound := norm_tsum_logDeriv_expo_le (norm_exp_two_pi_I_lt_one z)
  have hsum_le_8q : ‖q‖ / (1 - ‖q‖) ^ 3 ≤ 8 * ‖q‖ := by
    have h1 : (1 / 8 : ℝ) ≤ (1 - ‖q‖) ^ 3 := by nlinarith [sq_nonneg (1 - ‖q‖)]
    calc ‖q‖ / (1 - ‖q‖) ^ 3 ≤ ‖q‖ / (1 / 8) := by
          apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h1
      _ = 8 * ‖q‖ := by ring
  have hq_eq_exp : ‖q‖ = Real.exp (-2 * π * z.im) := by
    have hre : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
      rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
      simp [Complex.I_re, Complex.I_im, mul_comm]
    rw [Complex.norm_exp, hre]
  calc 24 * ‖∑' n : ℕ+, ↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ 24 * (‖q‖ / (1 - ‖q‖) ^ 3) := by gcongr
    _ ≤ 24 * (8 * ‖q‖) := by gcongr
    _ = 192 * ‖q‖ := by ring
    _ = 192 * Real.exp (-(2 * π) * z.im) := by rw [hq_eq_exp]; ring_nf

/-- E₂ → 1 at i∞. -/
lemma E₂_tendsto_one_atImInfty : Filter.Tendsto E₂ atImInfty (nhds 1) := by
  suffices h : Filter.Tendsto (fun z : ℍ => E₂ z - 1) atImInfty (nhds 0) by
    simpa using h.add_const 1
  exact tendsto_zero_of_exp_decay (by positivity : 0 < 2 * π) E₂_sub_one_isBigO_exp

/-- E₄ → 1 at i∞. -/
lemma E₄_tendsto_one_atImInfty : Filter.Tendsto E₄.toFun atImInfty (nhds 1) :=
  E4_q_exp_zero ▸ modular_form_tendsto_atImInfty E₄

/-- E₆ → 1 at i∞. -/
lemma E₆_tendsto_one_atImInfty : Filter.Tendsto E₆.toFun atImInfty (nhds 1) :=
  E6_q_exp_zero ▸ modular_form_tendsto_atImInfty E₆

/-! ## Boundedness lemmas -/

/-- E₆ is bounded at infinity (as a modular form). -/
lemma E₆_isBoundedAtImInfty : IsBoundedAtImInfty E₆.toFun :=
  ModularFormClass.bdd_at_infty E₆

/-- serre_D 1 E₂ is bounded at infinity. -/
lemma serre_DE₂_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 1 E₂) :=
  serre_D_isBoundedAtImInfty_of_bounded 1 E₂_holo' E₂_isBoundedAtImInfty

/-- D E₄ is bounded at infinity (by Cauchy estimate: D f → 0 when f is bounded). -/
lemma DE₄_isBoundedAtImInfty : IsBoundedAtImInfty (D E₄.toFun) :=
  D_isBoundedAtImInfty_of_bounded E₄.holo' E₄_isBoundedAtImInfty

/-- serre_D 4 E₄ is bounded at infinity. -/
lemma serre_DE₄_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 4 E₄.toFun) :=
  serre_D_isBoundedAtImInfty_of_bounded 4 E₄.holo' E₄_isBoundedAtImInfty

/-! ## Construction of ModularForm from serre_D -/

/-- serre_D 4 E₄ is a weight-6 modular form. -/
def serre_DE₄_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 6 :=
  serre_D_ModularForm 4 E₄

/-- serre_D 6 E₆ is bounded at infinity. -/
lemma serre_DE₆_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 6 E₆.toFun) :=
  serre_D_isBoundedAtImInfty_of_bounded 6 E₆.holo' E₆_isBoundedAtImInfty

/-- serre_D 6 E₆ is a weight-8 modular form. -/
def serre_DE₆_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 8 :=
  serre_D_ModularForm 6 E₆

/-! ## Limit of serre_D at infinity (for determining scalar) -/

/-- General limit: if `f → 1` at i∞ and f is holomorphic and bounded, then `serre_D k f → -k/12`. -/
lemma serre_D_tendsto_neg_k_div_12 (k : ℤ) (f : ℍ → ℂ)
    (hf_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hf_bdd : IsBoundedAtImInfty f)
    (hf_lim : Filter.Tendsto f atImInfty (nhds 1)) :
    Filter.Tendsto (serre_D k f) atImInfty (nhds (-(k : ℂ) / 12)) := by
  rw [show serre_D k f = fun z => D f z - (k : ℂ) * 12⁻¹ * E₂ z * f z from serre_D_eq k f]
  have hD := D_tendsto_zero_of_tendsto_const hf_holo hf_bdd
  have hprod := E₂_tendsto_one_atImInfty.mul hf_lim
  have hlim : (0 : ℂ) - (k : ℂ) * 12⁻¹ * 1 * 1 = -(k : ℂ) / 12 := by ring
  rw [← hlim]
  refine hD.sub ?_
  have hconst : Filter.Tendsto (fun _ : ℍ => (k : ℂ) * 12⁻¹)
      atImInfty (nhds ((k : ℂ) * 12⁻¹)) := tendsto_const_nhds
  convert hconst.mul hprod using 1 <;> ring_nf

/-- serre_D 4 E₄ → -1/3 at i∞. -/
lemma serre_DE₄_tendsto_atImInfty :
    Filter.Tendsto (serre_D 4 E₄.toFun) atImInfty (nhds (-(1/3 : ℂ))) := by
  convert serre_D_tendsto_neg_k_div_12 4 E₄.toFun E₄.holo'
    (ModularFormClass.bdd_at_infty E₄) E₄_tendsto_one_atImInfty using 2
  norm_num

/-- serre_D 6 E₆ → -1/2 at i∞. -/
lemma serre_DE₆_tendsto_atImInfty :
    Filter.Tendsto (serre_D 6 E₆.toFun) atImInfty (nhds (-(1/2 : ℂ))) := by
  convert serre_D_tendsto_neg_k_div_12 6 E₆.toFun E₆.holo'
    E₆_isBoundedAtImInfty E₆_tendsto_one_atImInfty using 2
  norm_num

/-- serre_D 1 E₂ is a weight-4 modular form.
Note: E₂ itself is NOT a modular form, but serre_D 1 E₂ IS. -/
def serre_DE₂_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 4 where
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
lemma serre_DE₂_tendsto_atImInfty :
    Filter.Tendsto (serre_D 1 E₂) atImInfty (nhds (-(1/12 : ℂ))) := by
  have h := serre_D_tendsto_neg_k_div_12 1 E₂ E₂_holo'
    E₂_isBoundedAtImInfty E₂_tendsto_one_atImInfty
  simp only [Int.cast_one, neg_div] at h
  exact h

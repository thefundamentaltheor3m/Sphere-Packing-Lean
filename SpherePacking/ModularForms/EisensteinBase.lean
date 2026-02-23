module
public import SpherePacking.ModularForms.Eisensteinqexpansions
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.qExpansion_lems
public import SpherePacking.ModularForms.SummableLemmas.Basic
public import SpherePacking.ModularForms.SummableLemmas.Cotangent
public import SpherePacking.ModularForms.SummableLemmas.G2
public import SpherePacking.ModularForms.SummableLemmas.QExpansion
public import SpherePacking.ModularForms.SummableLemmas.IntPNat
import SpherePacking.Tactic.NormNumI


/-!
# Level-one Eisenstein series and auxiliary ratios

This file packages the level-one Eisenstein series `E₄` and `E₆`, defines the auxiliary ratios
`φ₀`, `φ₂'`, `φ₄'` (and their extensions to `ℂ`), and proves the basic `q`-expansion and
imaginary-axis lemmas needed later in the sphere packing argument.
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
open scoped ArithmeticFunction.sigma

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex Real MatrixGroups

noncomputable section

section Definitions

/-! ## Level-one Eisenstein series -/

/-- The normalized level-one Eisenstein series of weight `4` as a modular form. -/
@[expose] public def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by decide) standardcongruencecondition -- normalization

/-- The normalized level-one Eisenstein series of weight `6` as a modular form. -/
@[expose] public def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by decide) standardcongruencecondition

/-- `E₄` is definitionally the Eisenstein series `E 4`. -/
public lemma E4_eq : E₄ = E 4 (by decide) := rfl

/-- `E₆` is definitionally the Eisenstein series `E 6`. -/
public lemma E6_eq : E₆ = E 6 (by decide) := rfl

/-- Evaluation of `E₄` agrees with `E 4` pointwise. -/
@[simp] public lemma E4_apply (z : ℍ) : E₄ z = E 4 (by decide) z := rfl

/-- Evaluation of `E₆` agrees with `E 6` pointwise. -/
@[simp] public lemma E6_apply (z : ℍ) : E₆ z = E 6 (by decide) z := rfl

/-- E₄ is 1-periodic: E₄(z + 1) = E₄(z). This follows from E₄ being a modular form for Γ(1). -/
public lemma E₄_periodic (z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z :=
  by simpa using SlashInvariantForm.vAdd_width_periodic 1 4 1 E₄.toSlashInvariantForm z

/-- E₆ is 1-periodic: E₆(z + 1) = E₆(z). This follows from E₆ being a modular form for Γ(1). -/
public lemma E₆_periodic (z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z :=
  by simpa using SlashInvariantForm.vAdd_width_periodic 1 6 1 E₆.toSlashInvariantForm z

/-- E₄ transforms under S as: E₄(-1/z) = z⁴ · E₄(z) -/
private lemma ModularForm.S_transform_of_level_one (m : ℕ)
    (F : ModularForm (CongruenceSubgroup.Gamma ↑1) (m : ℤ)) (z : ℍ) :
    F (ModularGroup.S • z) = z ^ m * F z := by
  have h : (F.toFun ∣[(m : ℤ)] ModularGroup.S) z = F.toFun z := by
    simpa using
      congrFun (by
        apply F.slash_action_eq'
        simp only [Subgroup.mem_map, CongruenceSubgroup.mem_Gamma_one]
        use ModularGroup.S) z
  simp [SL_slash_apply, ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  exact h

/-- The `S`-transformation formula for `E₄`. -/
public lemma E₄_S_transform (z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := by
  simpa using (ModularForm.S_transform_of_level_one 4 E₄ z)

/-- E₆ transforms under S as: E₆(-1/z) = z⁶ · E₆(z) -/
public lemma E₆_S_transform (z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := by
  simpa using (ModularForm.S_transform_of_level_one 6 E₆ z)

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

end Definitions

/-! ## Auxiliary ratios `φ` -/

/-- The ratio `φ₀ = (E₂ * E₄ - E₆)^2 / Δ` on `ℍ`. -/
@[expose] public def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)

/-- The ratio `φ₂' = E₄ * (E₂ * E₄ - E₆) / Δ` on `ℍ`. -/
@[expose] public def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)

/-- The ratio `φ₄' = E₄^2 / Δ` on `ℍ`. -/
@[expose] public def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)

/-- Extend `φ₀` to a function `ℂ → ℂ` by setting it to `0` outside the upper half-plane. -/
@[expose] public def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0

/-- Extend `φ₂'` to a function `ℂ → ℂ` by setting it to `0` outside the upper half-plane. -/
@[expose] public def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0

/-- Extend `φ₄'` to a function `ℂ → ℂ` by setting it to `0` outside the upper half-plane. -/
@[expose] public def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

/-- Unfold `φ₀''` on the upper half-plane. -/
@[simp] public lemma φ₀''_def {z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by
  simp [φ₀'', hz]

/-- Unfold `φ₀''` on an upper-half-plane point `z : ℍ`. -/
@[simp] public lemma φ₀''_coe_upperHalfPlane (z : ℍ) : φ₀'' (z : ℂ) = φ₀ z := by
  simp [φ₀'', UpperHalfPlane.im_pos z]

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

local notation "𝕢" => Periodic.qParam

theorem cuspfunc_lim_coef {k : ℤ} {F : Type u_1} [inst : FunLike F ℍ ℂ] (n : ℕ) (c : ℕ → ℂ) (f : F)
  [inst_1 : ModularFormClass F Γ(n) k] [inst_2 : NeZero n] (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢
    ↑n ↑τ ^ m) (f τ))
  (q : ℂ) (hq : ‖q‖ < 1) (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q) := by
  have hq2 := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) hq hq1
  have hft := hf ⟨(Periodic.invQParam (↑n) q), hq2⟩
  have := eq_cuspFunction (h := n) f
    ⟨(Periodic.invQParam (↑n) q), hq2⟩ (by simp) (by simp [inst_2.1])
  simp only [smul_eq_mul, ne_eq] at *
  rw [Function.Periodic.qParam_right_inv] at this hft
  · rw [← this] at hft
    exact hft
  · simpa [Nat.cast_eq_zero] using (NeZero.ne n)
  · exact hq1
  · simpa [Nat.cast_eq_zero] using (NeZero.ne n)
  · exact hq1

theorem summable_zero_pow {G} [NormedField G] (f : ℕ → G) : Summable (fun m ↦ f m * 0 ^ m) := by
  refine summable_of_finite_support ((Set.finite_singleton (0 : ℕ)).subset ?_)
  intro m hm
  cases m with
  | zero => simp
  | succ m =>
      exact False.elim (hm (by simp))

lemma tsum_zero_pow (f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0 := by
  simpa using (tsum_eq_single (f := fun m => f m * 0 ^ m) 0 fun m hm => by
    cases m with
    | zero => cases hm rfl
    | succ m => simp)

private lemma tendsto_tsum_mul_pow_nhdsWithin_ne_zero_half (c : ℕ → ℂ)
    (hc : Summable fun m : ℕ ↦ ‖c m‖ * (1 / 2 : ℝ) ^ m) :
    Tendsto (fun q : ℂ ↦ ∑' m : ℕ, c m * q ^ m) (𝓝[≠] (0 : ℂ)) (𝓝 (c 0)) := by
  -- As `q → 0` (with `q ≠ 0`), the power series tends to its constant term.
  simpa [tsum_zero_pow] using
    (tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[≠] (0 : ℂ)))
      (f := fun q : ℂ => fun m : ℕ => c m * q ^ m)
      (g := fun m : ℕ => c m * (0 : ℂ) ^ m)
      (bound := fun m : ℕ => ‖c m‖ * (1 / 2 : ℝ) ^ m) (by
        simpa using hc) (by
        intro m
        exact (tendsto_const_nhds.mul
          ((((continuous_pow m (M := ℂ)).tendsto) 0).mono_left nhdsWithin_le_nhds))) (by
        have hq : {q : ℂ | ‖q‖ < (1 / 2 : ℝ)} ∈ (𝓝[≠] (0 : ℂ)) :=
          mem_nhdsWithin_of_mem_nhds <| by
            simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0 : ℂ) (by norm_num)
        filter_upwards [hq] with q hq m
        simp only [norm_mul, norm_pow]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (c m))
        exact pow_le_pow_left₀ (norm_nonneg q) (le_of_lt hq) m))

lemma modfom_q_exp_cuspfunc (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k] [NeZero n]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) : ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun m : ℕ ↦ c m • q ^ m) (cuspFunction n f q) := by
  intro q hq
  by_cases hq1 : q ≠ 0
  · apply cuspfunc_lim_coef n c f hf q hq hq1
  · have h2 : cuspFunction n f 0 = c 0 := by
      rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
      refine Filter.Tendsto.limUnder_eq ?_
      have hsum :
          Summable fun m : ℕ ↦ ‖c m‖ * (1 / 2 : ℝ) ^ m := by
        have h :=
          (cuspfunc_lim_coef n c f hf (1 / 2 : ℂ) (by norm_num)
              (by
                refine one_div_ne_zero ?_
                exact (NeZero.ne' 2).symm)).summable.norm
        simpa [smul_eq_mul, norm_mul, norm_pow] using h
      have htt : Tendsto (fun q : ℂ ↦ ∑' m : ℕ, c m * q ^ m) (𝓝[≠] (0 : ℂ)) (𝓝 (c 0)) :=
        tendsto_tsum_mul_pow_nhdsWithin_ne_zero_half c hsum
      -- Use the explicit `HasSum` formula for `q ≠ 0` in a punctured neighborhood.
      refine htt.congr' ?_
      have hmem : {y : ℂ | y ≠ 0 ∧ ‖y‖ < (1 : ℝ)} ∈ (𝓝[≠] (0 : ℂ)) := by
        refine (mem_nhdsWithin_iff_exists_mem_nhds_inter).2 ?_
        refine ⟨{y : ℂ | ‖y‖ < (1 : ℝ)}, ?_, ?_⟩
        · simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0 : ℂ) (by norm_num)
        · intro y hy
          exact ⟨hy.2, hy.1⟩
      filter_upwards [hmem] with y hy
      simpa [smul_eq_mul] using (cuspfunc_lim_coef n c f hf y hy.2 hy.1).tsum_eq
    have hq0 : q = 0 := by simpa using (not_not.mp hq1)
    subst hq0
    rw [h2]
    simpa [smul_eq_mul] using
      (summable_zero_pow (f := c)).hasSum_iff.2 (by simpa using (tsum_zero_pow c))


lemma qParam_surj_onto_ball (r : ℝ) (hr : 0 < r) (hr2 : r < 1) [NeZero n] : ∃ (z : ℍ), ‖𝕢 n z‖ = r
    := by
  use ⟨(Periodic.invQParam n r), ?_⟩
  · have hq := Function.Periodic.qParam_right_inv (h := n) (q := r) ?_ ?_
    · rw [hq]
      simp [hr.le]
    · exact Ne.symm (NeZero.ne' _)
    · simpa [ne_eq, ofReal_eq_zero] using (ne_of_gt hr)
  rw [Function.Periodic.im_invQParam]
  simp only [norm_real, norm_eq_abs, log_abs]
  rw [mul_pos_iff]
  right
  constructor
  · refine div_neg_of_neg_of_pos ?_ ?_
    · simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact Nat.pos_of_neZero n
    exact two_pi_pos
  rw [propext (log_neg_iff hr)]
  exact hr2


lemma q_exp_unique (c : ℕ → ℂ) (f : ModularForm Γ(n) k) [hn : NeZero n]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) :
    c = (fun m => (qExpansion n f).coeff m) := by
  ext m
  let qExpansion2 : PowerSeries ℂ := .mk fun m ↦ c m
  let qq : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun m ↦ (qExpansion2).coeff m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  have hqq2 : ∀ m , ‖qq m‖ = ‖(qExpansion2).coeff m‖ := by
    intro m
    simp only [qq]
    rw [
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
    simp only [map_smul, smul_eq_mul, norm_mul,
      LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  have H2 : HasFPowerSeriesOnBall (cuspFunction n f) qq 0 1 := by
    have H21 : 1 ≤ qq.radius := by
        refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
        lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        conv =>
          enter [1]
          intro n
          rw [hqq2]
        simp only [PowerSeries.coeff_mk, qExpansion2]
        by_cases hr0 : r = 0
        · rw [hr0]
          apply summable_zero_pow
        obtain ⟨z, hz⟩ := qParam_surj_onto_ball n r
          (by simpa [NNReal.coe_pos] using (pos_iff_ne_zero.mpr hr0)) (by simpa using hr)
        rw [← hz]
        have hfz := summable_norm_iff.mpr (hf z).summable
        simpa using hfz
    refine ⟨H21, zero_lt_one, ?_⟩
    intro y hy
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm] at hy
    simp only [zero_add]
    have hs : HasSum (fun m : ℕ ↦ c m • y ^ m) (cuspFunction n f y) :=
      modfom_q_exp_cuspfunc n c f hf y hy
    have hs' : HasSum (fun m : ℕ ↦ (qq m) fun _ ↦ y) (cuspFunction n f y) := by
      refine HasSum.congr_fun hs ?_
      intro m
      simp [qq, qExpansion2, smul_eq_mul, ContinuousMultilinearMap.smul_apply,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    exact hs'
  have h3 : HasFPowerSeriesAt (cuspFunction n f) qq 0 := H2.hasFPowerSeriesAt
  have h4 : HasFPowerSeriesAt (cuspFunction n f) (qExpansionFormalMultilinearSeries n f) 0 :=
    (ModularFormClass.hasFPowerSeries_cuspFunction (h := n) (f := f)
        (by have := hn.1; positivity) (by simp)).hasFPowerSeriesAt
  have := HasFPowerSeriesAt.eq_formalMultilinearSeries h3 h4
  rw [@FormalMultilinearSeries.ext_iff] at this
  have h5 := this m
  simp only [PowerSeries.coeff_mk, qExpansionFormalMultilinearSeries, qq, qExpansion2] at h5
  have htv : (c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun =
    ( (PowerSeries.coeff m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m
      ℂ).toFun := by
    simpa [FormalMultilinearSeries.ofScalars] using congrArg (fun t => t.toFun) h5
  have h6 := congrFun htv m
  simpa only [ContinuousMultilinearMap.toMultilinearMap_smul, Pi.natCast_def,
    MultilinearMap.toFun_eq_coe, MultilinearMap.smul_apply, ContinuousMultilinearMap.coe_coe,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, and_not_self,
    or_false, qExpansion2, qq] using h6

/-- A crude upper bound on the divisor sum `σ k n`. -/
public lemma sigma_bound (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  have : ∑ d ∈ n.divisors, d ^ k ≤ ∑ d ∈ n.divisors, n ^ k := by
    apply Finset.sum_le_sum
    intro i hi
    gcongr
    exact Nat.divisor_le hi
  apply le_trans this
  simp only [Finset.sum_const, smul_eq_mul]
  rw [pow_add, mul_comm]
  gcongr
  simpa using Nat.card_divisors_le_self n

def Ek_q (k : ℕ) : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)

lemma qexpsummable (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    Summable fun m ↦ Ek_q k m • 𝕢 ↑1 ↑z ^ m := by
  rw [← summable_nat_add_iff 1]
  simp only [Ek_q, Nat.add_eq_zero_iff, one_ne_zero, and_false, reduceIte, one_div, neg_mul,
    Periodic.qParam, ofReal_one, div_one, smul_eq_mul]
  let C : ℂ := (1 / riemannZeta k) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!)
  let f : ℕ → ℝ := fun a ↦ (a : ℝ) ^ k * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ a‖
  have hs0 : Summable f := by
    simpa [f, norm_mul, norm_pow, Complex.norm_natCast, mul_assoc, mul_left_comm, mul_comm] using
      summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z)
  have hs :
      Summable fun a : ℕ ↦
        (↑(a + 1) : ℝ) ^ k * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (a + 1)‖ := by
    simpa [f, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1 (f := f)).2 hs0
  have hσ :
      Summable fun m : ℕ ↦
        (σ (k - 1) (m + 1) : ℂ) * cexp (2 * ↑π * Complex.I * ↑z) ^ (m + 1) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hs
    have hk1 : 1 ≤ k := by
      have : (1 : ℤ) ≤ k := le_trans (by decide : (1 : ℤ) ≤ 3) hk
      exact_mod_cast this
    have hsigma : (σ (k - 1) (m + 1) : ℝ) ≤ (↑(m + 1) : ℝ) ^ k := by
      have hσ' : σ (k - 1) (m + 1) ≤ (m + 1) ^ k := by
        simpa [Nat.sub_add_cancel hk1] using (sigma_bound (k := k - 1) (n := m + 1))
      exact_mod_cast hσ'
    calc
      ‖(σ (k - 1) (m + 1) : ℂ) * cexp (2 * ↑π * Complex.I * ↑z) ^ (m + 1)‖
          = ‖(σ (k - 1) (m + 1) : ℂ)‖ * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (m + 1)‖ := by
              simp
      _ = (σ (k - 1) (m + 1) : ℝ) * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (m + 1)‖ := by
            simp only [Complex.norm_natCast]
      _ ≤ (↑(m + 1) : ℝ) ^ k * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (m + 1)‖ := by
            exact mul_le_mul_of_nonneg_right hsigma (norm_nonneg _)
  -- reassociate to use `Summable.mul_left`
  simpa [C, mul_assoc] using (Summable.mul_left (a := C) hσ)


lemma Ek_q_exp (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    (fun m => (qExpansion 1 (E k hk)).coeff m) =
    fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m) := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
      (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)
  have h := q_exp_unique 1 c (E k hk) ?_
  · rw [← Nat.cast_one (R := ℝ), ← h]
  intro z
  have := E_k_q_expansion k hk hk2 z
  have hSummable : Summable fun n ↦ c n * 𝕢 (1 : ℝ) ↑z ^ n := by
    have hs : Summable fun m ↦ Ek_q k m • 𝕢 ↑1 ↑z ^ m := qexpsummable k hk z
    have hs' : Summable fun m ↦ Ek_q k m * 𝕢 (1 : ℝ) ↑z ^ m := by
      refine hs.congr fun m => ?_
      simp [smul_eq_mul]
    refine hs'.congr fun m => ?_
    simp [c, Ek_q]
  rw [Summable.hasSum_iff]
  · rw [this, tsum_eq_zero_add']
    · have V := tsum_pnat_eq_tsum_succ (f := fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
      simp only [Nat.cast_one, pow_zero, smul_eq_mul, mul_one] at *
      rw [← V]
      simp only [c, PNat.ne_zero, reduceIte, one_div, neg_mul]
      refine (add_left_cancel_iff).2 ?_
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro b
      ring_nf
      field_simp
      congr
      rw [Function.Periodic.qParam, ← Complex.exp_nsmul]
      congr
      simp
      ring
    have hr := (summable_nat_add_iff 1 (f := fun n : ℕ ↦ c (n) • 𝕢 (1 : ℝ) ↑z ^ (n)))
    simp only [Nat.cast_one, smul_eq_mul] at *
    rw [hr]
    simpa using hSummable
  · simpa using hSummable

private lemma E4_q_exp_const :
    (1 / (riemannZeta (4 : ℕ))) * ((-2 * (π : ℂ) * Complex.I) ^ 4 / (4 - 1)!) = (240 : ℂ) := by
  have hz : riemannZeta (4 : ℕ) = (π : ℂ) ^ 4 / 90 := by
    simpa using (riemannZeta_four : riemannZeta (4 : ℂ) = π ^ 4 / 90)
  have hpi4 : (π : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (by simp : (π : ℂ) ≠ 0)
  have hfac : (4 - 1)! = 6 := by decide
  rw [hz, hfac]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  field_simp [hpi4]
  norm_num

/-- Explicit `q`-coefficients for `E₄`. -/
public lemma E4_q_exp : (fun m => (qExpansion 1 E₄).coeff m) =
    fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  have hE :
      (fun m => (qExpansion 1 (E 4 (by decide : 3 ≤ (4 : ℤ)))).coeff m) =
        fun m => if m = 0 then 1 else
          (1 / (riemannZeta (4 : ℕ))) * ((-2 * (π : ℂ) * Complex.I) ^ 4 / (4 - 1)!) * (σ 3 m) := by
    simpa using (Ek_q_exp 4 (by decide : 3 ≤ (4 : ℤ)) (by decide : Even 4))
  -- Reduce to the general `E k` coefficient formula, then evaluate the constant factor.
  rw [E4_eq, hE]
  funext m
  by_cases hm : m = 0
  · subst hm; simp
  · have hconst := congrArg (fun t : ℂ => t * (σ 3 m : ℂ)) E4_q_exp_const
    simpa [hm, mul_assoc, mul_left_comm, mul_comm] using hconst

/-- The constant `q`-coefficient of `E₄` is `1`. -/
public lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1 := by
  simpa using congr_fun E4_q_exp 0

@[simp]
theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    (by decide : Nat.choose 5 2 = 10)]

@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    (by decide : Nat.choose 6 4 = 15), (by decide : Nat.choose 6 2 = 15)]

private lemma riemannZeta_six :
    riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have Z :
      riemannZeta 6 =
        (-1) ^ (3 + 1) * (2 : ℂ) ^ (2 * 3 - 1) * (π : ℂ) ^ (2 * 3) * bernoulli (2 * 3) /
          (2 * 3)! := by
    simpa [show (2 : ℂ) * 3 = 6 by norm_num] using
      (riemannZeta_two_mul_nat (k := 3) (by decide : (3 : ℕ) ≠ 0))
  rw [Z]
  have hfac : (6 : ℕ)! = 720 := by decide
  simp [bernoulli, bernoulli'_six, hfac]
  ring_nf

private lemma E6_q_exp_const :
    (1 / riemannZeta 6) * ((-2 * (π : ℂ) * Complex.I) ^ 6 / (6 - 1)!) = (-(504 : ℂ)) := by
  have hpi6 : (π : ℂ) ^ 6 ≠ 0 := pow_ne_zero 6 (by simp : (π : ℂ) ≠ 0)
  have hfac : (6 - 1)! = 120 := by decide
  rw [riemannZeta_six, hfac]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  field_simp [hpi6]
  norm_num

/-- Explicit `q`-coefficients for `E₆`. -/
public lemma E6_q_exp : (fun m => (qExpansion 1 E₆).coeff m) =
    fun m => if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  have hE :
      (fun m => (qExpansion 1 (E 6 (by decide : 3 ≤ (6 : ℤ)))).coeff m) =
        fun m => if m = 0 then 1 else
          (1 / riemannZeta 6) * ((-2 * (π : ℂ) * Complex.I) ^ 6 / (6 - 1)!) * (σ 5 m) := by
    simpa using (Ek_q_exp 6 (by decide : 3 ≤ (6 : ℤ)) (by decide : Even 6))
  rw [E6_eq, hE]
  funext m
  by_cases hm : m = 0
  · subst hm; simp
  · have hconst := congrArg (fun t : ℂ => t * (σ 5 m : ℂ)) E6_q_exp_const
    simpa [hm, mul_assoc, mul_left_comm, mul_comm] using hconst

/-- The constant `q`-coefficient of `E₆` is `1`. -/
public lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1 := by
  simpa using congr_fun E6_q_exp 0

/-- The constant coefficient of `(1/1728) * (E₄^3 - E₆^2)` vanishes, hence it is a cusp form. -/
public theorem E4E6_coeff_zero_eq_zero :
  (PowerSeries.coeff 0)
      (qExpansion 1
        ((1 / 1728 : ℂ) • ((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 - (DirectSum.of (ModularForm
          Γ(1)) 6) E₆ ^ 2) 12)) =
    0 := by
  simp only [one_div, DirectSum.sub_apply]
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2]
  rw [Nat.cast_one (R := ℝ)]
  have hsub :
      (⇑((((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12 -
              ((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)) : ℍ → ℂ) =
        (⇑(((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) -
          ⇑(((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)) := rfl
  simp_rw [hsub]
  rw [qExpansion_sub1]
  simp only [map_smul, map_sub, smul_eq_mul,
    mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) = E₄.mul (E₄.mul E₄) := by
    ext z
    rw [pow_three]
    rw [@DirectSum.of_mul_of, DirectSum.of_mul_of]
    simp only [Int.reduceAdd, DirectSum.of_eq_same]
    rw [DFunLike.congr_arg (GradedMonoid.GMul.mul E₄ (GradedMonoid.GMul.mul E₄ E₄)) rfl]
    rfl
  have hd6 : ((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12 = E₆.mul E₆ := by
    ext z
    rw [pow_two]
    rw [@DirectSum.of_mul_of]
    simp only [Int.reduceAdd, DirectSum.of_eq_same]
    rw [DFunLike.congr_arg (GradedMonoid.GMul.mul E₆ E₆) rfl]
    rfl
  rw [hds, hd6]
  rw [← Nat.cast_one (R := ℝ)]
  rw [qExpansion_mul_coeff, qExpansion_mul_coeff, qExpansion_mul_coeff, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul,]
  simp only [Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton, Prod.fst_zero,
    Prod.snd_zero]
  rw [Nat.cast_one]
  simp_rw [E4_q_exp_zero, E6_q_exp_zero]
  rw [PowerSeries.coeff_mul]
  simp only [Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton, Prod.fst_zero,
    Prod.snd_zero, one_mul, mul_one]
  rw [E4_q_exp_zero]
  simp

/-- The cusp form `(1/1728) * (E₄^3 - E₆^2)` of weight `12`. -/
@[expose] public def Delta_E4_E6_aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 := by
  let F := DirectSum.of _ 4 E₄
  let G := DirectSum.of _ 6 E₆
  apply IsCuspForm_to_CuspForm _ _ ((1/ 1728 : ℂ) • (F^3 - G^2) 12 )
  rw [IsCuspForm_iff_coeffZero_eq_zero]
  exact E4E6_coeff_zero_eq_zero

lemma Delta_cuspFuntion_eq : Set.EqOn (cuspFunction 1 Delta)
     (fun y => (y : ℂ) * ∏' i, ((1 : ℂ) - y ^ (i + 1)) ^ 24) (Metric.ball 0 (2⁻¹ : ℝ)) := by
  rw [cuspFunction]
  intro y hy
  by_cases hyn0 : y = 0
  · rw [hyn0]
    simpa [cuspFunction] using
      (CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp))
  · rw [Function.Periodic.cuspFunction_eq_of_nonzero]
    · simp only [comp_apply]
      have hz := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := 1) (by exact
        Real.zero_lt_one) (q := y) ?_ ?_
      · rw [ofComplex_apply_of_im_pos hz]
        rw [Delta_apply, Δ]
        have hq :=
          Function.Periodic.qParam_right_inv (h := 1)
            (by simp) (q := y) hyn0
        have : cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y) = y := by
          nth_rw 2 [← hq]
          congr 1
          simp
        rw [this]
        congr
        ext n
        congr
        have : cexp (2 * ↑π * Complex.I * (↑n + 1) * Periodic.invQParam 1 y) =
            (cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y)) ^ (n + 1) := by
          rw [← Complex.exp_nsmul]
          congr
          ring
        rw [this]
        congr
      · have hy' : ‖y‖ < (2⁻¹ : ℝ) := by
          simpa [mem_ball, dist_zero_right] using hy
        exact lt_trans hy' (by norm_num)
      · exact hyn0
    exact hyn0

/-- Uniform convergence of finite products to the infinite product `∏' (1 - y^(i+1))`. -/
public lemma tendstoLocallyUniformlyOn_prod_range_one_sub_pow :
    TendstoLocallyUniformlyOn (fun n : ℕ ↦ ∏ x ∈ Finset.range n,
    fun y : ℂ ↦ (1 - y ^ (x + 1))) (fun x ↦ ∏' i, (1 - x ^ (i + 1))) atTop (Metric.ball 0 (2⁻¹ : ℝ))
      := by
  have hprod :
      (fun n : ℕ ↦ ∏ x ∈ Finset.range n, fun y : ℂ ↦ (1 + -(y ^ (x + 1)))) =
        fun n y ↦ ∏ x ∈ Finset.range n, (1 + -(y ^ (x + 1))) := by
    funext n y
    simp
  have h :=
    (prod_tendstoUniformlyOn_tprod' (Metric.closedBall 0 (2⁻¹ : ℝ))
          (f := fun n : ℕ => fun y : ℂ => -(y ^ (n + 1)))
          (isCompact_closedBall 0 (2⁻¹ : ℝ)) (fun n => (2⁻¹ : ℝ) ^ (n + 1)) ?_ ?_ ?_)
        |>.tendstoLocallyUniformlyOn
  · have h' := h.mono (s := Metric.closedBall 0 (2⁻¹ : ℝ)) ball_subset_closedBall
    simpa [sub_eq_add_neg, hprod] using h'
  · rw [@summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
    simp only [norm_inv, Real.norm_ofNat]
    exact two_inv_lt_one
  · intro n x hx
    have hx' : ‖x‖ ≤ (2⁻¹ : ℝ) := by
      have : dist x 0 ≤ (2⁻¹ : ℝ) := (Metric.mem_closedBall).1 hx
      simpa [dist_zero_right] using this
    simpa [norm_pow, inv_pow] using pow_le_pow_left₀ (norm_nonneg x) hx' (n + 1)
  fun_prop

theorem diffwithinat_prod_1 :
    DifferentiableWithinAt ℂ (fun (y : ℂ) ↦ ∏' (i : ℕ), (1 - y ^ (i + 1)) ^ 24)
      (ball (0 : ℂ) (2⁻¹ : ℝ)) 0
    := by
  suffices
      DifferentiableWithinAt ℂ (fun (n : ℂ) ↦ (∏' (i : ℕ), (1 - n ^ (i + 1))) ^ 24)
        (ball (0 : ℂ) (2⁻¹ : ℝ)) 0 by
    apply this.congr
    · intro x hx
      rw [← tprod_pow _ <|
        multipliable_lt_one x ((Metric.ball_subset_ball (by norm_num : (2⁻¹ : ℝ) ≤ 1)) hx)]
    simp
  apply DifferentiableWithinAt.pow
  have hu :
      DifferentiableOn ℂ (fun x : ℂ ↦ ∏' i, (1 - x ^ (i + 1))) (Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) := by
    refine tendstoLocallyUniformlyOn_prod_range_one_sub_pow.differentiableOn ?_ isOpen_ball
    refine eventually_atTop.2 ⟨0, fun n _ => ?_⟩
    refine DifferentiableOn.finset_prod (u := Finset.range n)
      (f := fun x : ℕ => fun y : ℂ => 1 - y ^ (x + 1))
      (s := Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) ?_
    intro i hi
    fun_prop
  exact hu 0 (mem_ball_self (by norm_num : (0 : ℝ) < (2⁻¹ : ℝ)))


/-- The first nontrivial `q`-coefficient of `Delta` is `1`. -/
public lemma Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1 := by
  rw [qExpansion_coeff]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, iteratedDeriv_one, one_mul]
  rw [← derivWithin_of_isOpen (s := Metric.ball 0 (2⁻¹ : ℝ)) (isOpen_ball) (by simp) ]
  rw [derivWithin_congr Delta_cuspFuntion_eq]
  · rw [derivWithin_fun_mul]
    · have huniq : UniqueDiffWithinAt ℂ (Metric.ball 0 (2⁻¹ : ℝ)) (0 : ℂ) :=
        isOpen_ball.uniqueDiffWithinAt (mem_ball_self (by norm_num))
      simp [huniq, derivWithin_id']
    · exact differentiableWithinAt_id'
    apply diffwithinat_prod_1
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    sub_zero, one_pow, tprod_one, mul_one]
  exact CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]

/-- The `q`-coefficient of `E₄` at `n = 1` is `240`. -/
public lemma E4_q_exp_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  simpa using congr_fun E4_q_exp 1

/-- The `q`-coefficient of `E₆` at `n = 1` is `-504`. -/
public lemma E6_q_exp_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  simpa using congr_fun E6_q_exp 1

open ArithmeticFunction

section Ramanujan_Formula

-- In this section, we state some simplifications that are used in Cor 7.5-7.7 of the blueprint

end Ramanujan_Formula


section ImagAxisProperties

open _root_.Complex hiding I

/-- `(-2πi)^k` is real for even k. -/
lemma neg_two_pi_I_pow_even_real (k : ℕ) (hk : Even k) :
    ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 := by
  have h : (-2 * Real.pi * Complex.I) ^ k = (-(2 * Real.pi) : ℂ) ^ k * Complex.I ^ k := by ring
  rw [h]
  have h1 : ((-(2 * Real.pi)) ^ k : ℂ).im = 0 := by norm_cast
  have h2 : (Complex.I ^ k : ℂ).im = 0 := by
    obtain ⟨m, rfl⟩ := hk
    simp only [← two_mul, pow_mul, I_sq]
    -- (-1)^m is real: ±1
    rcases m.even_or_odd with hm | hm <;> simp [hm.neg_one_pow]
  simp [Complex.mul_im, h1, h2]

/-- On imaginary axis z = I*t, the q-expansion exponent 2πi·n·z reduces to -(2πnt).
This is useful for reusing the same algebraic simplification across `E₂`, `E₄`, `E₆`. -/
lemma exp_imag_axis_arg (t : ℝ) (ht : 0 < t) (n : ℕ+) :
    2 * Real.pi * Complex.I * (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * n =
    (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
  push_cast
  ring_nf
  simp [I_sq]

/-- `ζ(2k)` is real for all `k ≥ 1`. -/
public lemma riemannZeta_even_im_eq_zero (k : ℕ) (hk : k ≠ 0) :
    (riemannZeta (2 * k : ℕ)).im = 0 := by
  rw [Nat.cast_mul, Nat.cast_two, riemannZeta_two_mul_nat hk]
  -- The RHS is the coercion of a real expression
  have : ((-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (↑Real.pi : ℂ) ^ (2 * k) *
         ↑(bernoulli (2 * k)) / ↑((2 * k)! : ℕ)) =
         ↑((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) *
           bernoulli (2 * k) / (2 * k)!) := by push_cast; ring
  rw [this]
  exact ofReal_im _

/-- `E_k(it)` is real for all `t > 0` when `k` is even and `k ≥ 4`.
This is the generalized theorem from which `E₄_imag_axis_real` and `E₆_imag_axis_real` follow. -/
theorem E_even_imag_axis_real (k : ℕ) (hk : (3 : ℤ) ≤ k) (hk2 : Even k) :
    ResToImagAxis.Real (E k hk).toFun := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E k hk z).im = 0
  have hq := E_k_q_expansion k hk hk2 z
  simp only at hq ⊢
  rw [hq]
  simp only [add_im, one_im, zero_add]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * z * n = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [z] using exp_imag_axis_arg (t := t) ht n
    rw [hexp_arg]
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    simp only [mul_im, exp_ofReal_im, natCast_im, mul_zero, zero_mul, add_zero]
  -- Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    · intro n
      calc ‖↑((ArithmeticFunction.sigma (k - 1)) ↑n) * cexp (2 * ↑Real.pi * Complex.I * z * n)‖
          = ‖(↑((ArithmeticFunction.sigma (k - 1)) ↑n) : ℂ)‖ *
            ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := norm_mul _ _
        _ ≤ ‖(↑n : ℂ) ^ k‖ * ‖cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := by
          apply mul_le_mul_of_nonneg_right
          · rw [Complex.norm_natCast, Complex.norm_pow, Complex.norm_natCast]
            have hbound := sigma_bound (k - 1) n
            have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
            rw [hk'] at hbound
            exact_mod_cast hbound
          · exact norm_nonneg _
        _ = ‖(↑n : ℂ) ^ k * cexp (2 * ↑Real.pi * Complex.I * z * n)‖ := (norm_mul _ _).symm
    · have := a33 k 1 z
      simp only [PNat.val_ofNat, Nat.cast_one, mul_one] at this
      exact summable_norm_iff.mpr this
  -- The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑((ArithmeticFunction.sigma (k - 1)) ↑n) *
      cexp (2 * ↑Real.pi * Complex.I * z * n)).im = 0 := by
    rw [im_tsum hsum]
    simp [hterm_im]
  -- Step 4: Show the coefficient is real and product with sum is real
  have hpow_im : ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0 :=
    neg_two_pi_I_pow_even_real k hk2
  have hfact_im : ((k - 1).factorial : ℂ).im = 0 := by simp
  -- For ζ(k) when k is even and ≥ 4, it's real
  obtain ⟨m, _⟩ := hk2
  have hzeta_im : (riemannZeta k).im = 0 := by
    rw [show k = 2 * m by omega]
    exact riemannZeta_even_im_eq_zero m (by omega)
  have hinv_zeta_im : (1 / riemannZeta k).im = 0 := by simp [hzeta_im]
  simp only [mul_im, div_im, hinv_zeta_im, hsum_im, hpow_im, hfact_im]
  ring

/-- `E₄(it)` is real for all `t > 0`. -/
public theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun :=
  E_even_imag_axis_real 4 (by decide) (by decide)

/-- `E₆(it)` is real for all `t > 0`. -/
public theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun :=
  E_even_imag_axis_real 6 (by decide) (by decide)

/-- `E₂(it)` is real for all `t > 0`. -/
public theorem E₂_imag_axis_real : ResToImagAxis.Real E₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  change (E₂ z).im = 0
  have hq := E₂_eq z
  rw [hq]
  simp only [sub_im, one_im, zero_sub]
  -- Step 1: Show each term in the sum is real on the imaginary axis
  have hterm_im : ∀ n : ℕ+, (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    intro n
    have hexp_arg : 2 * ↑Real.pi * Complex.I * n * z = (-(2 * Real.pi * (n : ℝ) * t) : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, z] using exp_imag_axis_arg (t := t) ht n
    -- Using simp only: `simp` gives false positive linter warning but args are needed
    have hone_sub_real : (1 - cexp (2 * ↑Real.pi * Complex.I * ↑↑n * ↑z)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, hexp_arg, exp_ofReal_im, sub_zero]
    have hnum_real : (↑n * cexp (2 * ↑Real.pi * Complex.I * n * z)).im = 0 := by
      simp only [mul_im, natCast_im, hexp_arg, exp_ofReal_im, mul_zero, zero_mul, add_zero]
    simp [Complex.div_im, hnum_real, hone_sub_real]
  -- Step 2: Summability of the series
  have hsum : Summable fun n : ℕ+ => ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z)) := by
    set r : ℂ := cexp (2 * ↑Real.pi * Complex.I * z) with hr
    have hr_norm : ‖r‖ < 1 := by
      simpa [hr] using exp_upperHalfPlane_lt_one z
    have hs : Summable fun n : ℕ => (n : ℂ) * r ^ n / (1 - r ^ n) :=
      logDeriv_q_expo_summable r hr_norm
    refine (hs.comp_injective PNat.coe_injective).congr ?_
    intro n
    have hpow : r ^ (n : ℕ) = cexp (2 * ↑Real.pi * Complex.I * (↑n : ℂ) * z) := by
      rw [hr]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * ↑Real.pi * Complex.I * z) (n : ℕ)).symm
    simp [hpow]
  -- Step 3: The sum has zero imaginary part
  have hsum_im : (∑' (n : ℕ+), ↑n * cexp (2 * ↑Real.pi * Complex.I * n * z) /
      (1 - cexp (2 * ↑Real.pi * Complex.I * n * z))).im = 0 := by
    rw [Complex.im_tsum hsum]
    simp [hterm_im]
  -- 24 * sum is real, so its imaginary part is 0
  simp [Complex.mul_im, hsum_im]

end ImagAxisProperties

/-! ## Boundedness of E₂. -/

/-- For im(z) ≥ 1, ‖exp(2πiz)‖ ≤ exp(-2π); useful for q-expansion bounds. -/
public lemma norm_exp_two_pi_I_le_exp_neg_two_pi (z : ℍ) (hz : 1 ≤ z.im) :
    ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
  have h : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
    simp [mul_assoc, mul_left_comm, mul_comm, Complex.mul_re, Complex.mul_im]
  rw [Complex.norm_exp, h, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- For ‖q‖ < 1, ‖∑ n·qⁿ/(1-qⁿ)‖ ≤ ‖q‖/(1-‖q‖)³. -/
public lemma norm_tsum_logDeriv_expo_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := by
  set r : ℝ := ‖q‖
  have hr_norm_lt_one : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
  have hsumm_majorant : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    simpa [div_eq_mul_inv] using (hsumm_nat.subtype _).mul_right (1 - r)⁻¹
  have hterm_bound (n : ℕ+) :
      ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ n * r ^ (n : ℕ) / (1 - r) := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hdenom_lower : 1 - r ≤ ‖1 - q ^ (n : ℕ)‖ := calc
      1 - r ≤ 1 - r ^ (n : ℕ) := by
        have : r ^ (n : ℕ) ≤ r := by simpa using pow_le_pow_of_le_one (norm_nonneg _) hq.le n.one_le
        linarith
      _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow]
      _ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ)); simp only [norm_one] at this; linarith
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖ ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - r) := by
          exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
            (sub_pos.mpr hq) hdenom_lower
      _ = ↑n * r ^ (n : ℕ) / (1 - r) := by rw [norm_pow]
  have hsumm_norms : Summable (fun n : ℕ+ => ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bound hsumm_majorant
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ := norm_tsum_le_tsum_norm hsumm_norms
    _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
        hsumm_norms.tsum_le_tsum hterm_bound hsumm_majorant
    _ = r / (1 - r) ^ 3 := by
        simp only [div_eq_mul_inv, tsum_mul_right, tsum_pnat_coe_mul_geometric hr_norm_lt_one,
          pow_succ]
        field_simp

/-- Monotone version of `norm_tsum_logDeriv_expo_le`: if ‖q‖ ≤ r < 1, then
‖∑ n·qⁿ/(1-qⁿ)‖ ≤ r/(1-r)³. Useful when we have a uniform bound on ‖q‖. -/
public lemma norm_tsum_logDeriv_expo_le_of_norm_le {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ r / (1 - r) ^ 3 := by
  have hq : ‖q‖ < 1 := lt_of_le_of_lt hqr hr
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg q) hqr
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le hq
    _ ≤ r / (1 - r) ^ 3 := by
        have := sub_pos.mpr hr
        have := sub_pos.mpr hq
        gcongr

/-!
## Boundedness and limit at infinity

We use `E₂_eq` to bound the tail series in terms of `q = exp(2π i z)` when `Im z ≥ 1`.
-/

/-- `E₂` is bounded at `Im z → ∞`. -/
public lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E₂ := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set r₀ : ℝ := Real.exp (-2 * π)
  have hr₀_lt_one : r₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, fun z hz => ?_⟩
  rw [E₂_eq]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  have hq_bound : ‖q‖ ≤ r₀ := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  -- Rewrite sum in terms of q^n
  set S := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hS_eq : ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) = S := by
    congr 1; ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := by
      change _ = (cexp (2 * π * Complex.I * z)) ^ (n : ℕ)
      rw [← Complex.exp_nat_mul]; ring_nf
    simp [this]
  calc ‖1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      = ‖1 - 24 * S‖ := by rw [hS_eq]
    _ ≤ 1 + 24 * ‖S‖ := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖24 * S‖ := norm_sub_le _ _
          _ = _ := by simp
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := by
        gcongr; exact norm_tsum_logDeriv_expo_le_of_norm_le hq_bound hr₀_lt_one

lemma E₂_isZeroAtImInfty_sub_one : IsZeroAtImInfty (fun z : ℍ => E₂ z - 1) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  set δ : ℝ := min (1 / 2) (ε / 192)
  have hδ_pos : 0 < δ := by
    refine lt_min (by norm_num) ?_
    nlinarith
  have hδ_event : ∀ᶠ x : ℝ in atTop, Real.exp (-((2 * Real.pi) * x)) < δ := by
    refine (tendsto_exp_neg_atTop_nhds_zero.comp ?_).eventually (Iio_mem_nhds hδ_pos)
    exact tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < (2 * Real.pi))
  rcases (Filter.eventually_atTop.1 hδ_event) with ⟨A₀, hA₀⟩
  refine ⟨max A₀ 1, fun z hz => ?_⟩
  have hzA₀ : A₀ ≤ z.im := le_trans (le_max_left A₀ 1) hz
  set q : ℂ := cexp (2 * π * Complex.I * z)
  set S : ℂ := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hT_eq :
      (∑' n : ℕ+, (n : ℂ) * cexp (2 * π * Complex.I * n * z) /
          (1 - cexp (2 * π * Complex.I * n * z))) = S := by
    congr 1; ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := by
      change _ = (cexp (2 * π * Complex.I * z)) ^ (n : ℕ)
      simpa [q, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * π * Complex.I * z) (n : ℕ))
    simp [this]
  have hq_norm : ‖q‖ = Real.exp (-((2 * Real.pi) * z.im)) := by
    simp [q, Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm, mul_re]
  have hqδ : ‖q‖ ≤ δ := by
    refine le_trans ?_ (le_of_lt (hA₀ A₀ le_rfl))
    simpa [hq_norm] using Real.exp_le_exp.2 (by nlinarith [hzA₀, Real.pi_pos])
  have hq_half : ‖q‖ ≤ (1 / 2 : ℝ) := le_trans hqδ (min_le_left _ _)
  have hq_small : ‖q‖ ≤ ε / 192 := le_trans hqδ (min_le_right _ _)
  have hq_lt_one : ‖q‖ < 1 := lt_of_le_of_lt hq_half (by norm_num)
  have hS_bound :
      ‖S‖ ≤ 8 * ‖q‖ := by
    have hS₁ : ‖S‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le (q := q) hq_lt_one
    have hpow : (1 / 2 : ℝ) ^ 3 ≤ (1 - ‖q‖) ^ 3 := by
      have : (1 / 2 : ℝ) ≤ 1 - ‖q‖ := by linarith
      gcongr
    have hdiv : ‖q‖ / (1 - ‖q‖) ^ 3 ≤ ‖q‖ / ((1 / 2 : ℝ) ^ 3) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hpow
    have hdiv' : ‖q‖ / ((1 / 2 : ℝ) ^ 3) = 8 * ‖q‖ := by ring_nf
    exact hS₁.trans (hdiv.trans_eq hdiv')
  have hE₂_sub_one : E₂ z - 1 = -24 * S := by
    calc
      E₂ z - 1 = (1 - 24 * S) - 1 := by simp [E₂_eq, hT_eq]
      _ = -24 * S := by ring
  -- take norms and bound
  calc
    ‖E₂ z - 1‖ = ‖-24 * S‖ := by simp [hE₂_sub_one]
    _ = 24 * ‖S‖ := by simp
    _ ≤ 24 * (8 * ‖q‖) := by gcongr
    _ ≤ 24 * (8 * (ε / 192)) := by gcongr
    _ = ε := by
        nlinarith

/-- `E₂ z` tends to `1` as `Im z → ∞`. -/
public theorem tendsto_E₂_atImInfty : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := by
  have h0 : Tendsto (fun z : ℍ => E₂ z - 1) atImInfty (𝓝 (0 : ℂ)) :=
    E₂_isZeroAtImInfty_sub_one
  have h1 : Tendsto (fun z : ℍ => (E₂ z - 1) + 1) atImInfty (𝓝 ((0 : ℂ) + 1)) :=
    h0.add tendsto_const_nhds
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1

end

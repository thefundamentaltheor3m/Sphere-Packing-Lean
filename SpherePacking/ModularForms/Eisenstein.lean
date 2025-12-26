import SpherePacking.ModularForms.Eisensteinqexpansions
import SpherePacking.ModularForms.IsCuspForm

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section Definitions

/- The Eisenstein Series E₄ and E₆ -/

def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition /-they need 1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition

lemma E4_eq : E₄ = E 4 (by norm_num) := rfl

lemma E6_eq : E₆ = E 6 (by norm_num) := rfl

lemma E4_apply (z : ℍ) : E₄ z = E 4 (by norm_num) z := rfl

lemma E6_apply (z : ℍ) : E₆ z = E 6 (by norm_num) z := rfl

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

end Definitions

open Complex Real

noncomputable section

/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0

instance : atImInfty.NeBot := by
  rw [atImInfty, Filter.comap_neBot_iff ]
  simp only [mem_atTop_sets, ge_iff_le, forall_exists_index]
  intro t x hx
  have := ENNReal.nhdsGT_ofNat_neBot
  let z : ℂ := Complex.mk (0 : ℝ) (|x| + 1)
  have h0 : 0 ≤ |x| := by
    apply abs_nonneg
  have hz : 0 < z.im := by
    positivity
  use ⟨z, hz⟩
  apply hx
  simp only [UpperHalfPlane.im, coe_mk_subtype]
  have : x ≤ |x| := by
    apply le_abs_self
  apply le_trans this
  simp only [le_add_iff_nonneg_right, zero_le_one, z]

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
  simp only [smul_eq_mul, ne_eq, coe_mk_subtype] at *
  rw [Function.Periodic.qParam_right_inv] at this hft
  · rw [← this] at hft
    exact hft
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1

theorem summable_zero_pow {G : Type*} [NormedField G] (f : ℕ → G) : Summable fun m ↦ f m * 0 ^ m :=
  by
  rw [← summable_nat_add_iff 1]
  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
  apply summable_zero

lemma tsum_zero_pow (f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0 := by
  rw [Summable.tsum_eq_zero_add]
  · simp only [pow_zero, mul_one, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, mul_zero, tsum_zero, add_zero]
  apply summable_zero_pow

lemma cuspfunc_Zero [hn : NeZero n] [ModularFormClass F Γ(n) k] : cuspFunction n f 0 =
    (qExpansion n f).coeff 0 := by
  have := ModularFormClass.hasSum_qExpansion_of_norm_lt (h := n) (q := 0) f
    (by have := hn.1; positivity) (by simp)
  simp only [norm_zero, zero_lt_one, smul_eq_mul, forall_const] at this
  rw [Summable.hasSum_iff] at this
  · rw [tsum_zero_pow] at this
    apply this.symm
  rw [← summable_nat_add_iff 1]
  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
  apply summable_zero

lemma modfom_q_exp_cuspfunc (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k] [NeZero n]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) : ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun m : ℕ ↦ c m • q ^ m) (cuspFunction n f q) := by
  intro q hq
  by_cases hq1 : q ≠ 0
  · apply cuspfunc_lim_coef n c f hf q hq hq1
  · have h2 : cuspFunction n f 0 = c 0 := by
      rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
      apply Filter.Tendsto.limUnder_eq
      have := cuspfunc_lim_coef n c f hf
      rw [cuspFunction] at this
      have htt : Tendsto (fun q => ∑' m, c m * q ^ m) (𝓝[≠] 0) (𝓝 (c 0)) := by
        have hD := tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[≠] (0 : ℂ)))
          (f := fun q : ℂ => fun m : ℕ => c m * q ^ m) (g := fun m : ℕ => c m * 0 ^ m)
          (bound := fun m => ‖c m‖ * (1 / 2 ) ^ m ) ?_ ?_ ?_
        · convert hD
          simp only
          rw [tsum_zero_pow]
        · have ht3 := (this (1/2) (by norm_num)
            (by apply one_div_ne_zero; exact Ne.symm (NeZero.ne' 2))).summable.norm
          simpa using ht3
        · intro k
          apply Tendsto.const_mul
          have := ((continuous_pow k (M := ℂ) ).tendsto) 0
          apply Filter.Tendsto.mono_left this
          exact nhdsWithin_le_nhds
        rw [eventually_iff_exists_mem]
        use {z | (z : ℂ) ≠ 0 ∧ ‖z‖ < 1 / 2}
        constructor
        · rw [@mem_nhdsWithin_iff]
          refine ⟨1/2, by norm_num, ?_⟩
          intro y hy
          simp only [smul_eq_mul, ne_eq, Decidable.not_not, one_div,
            mem_inter_iff, mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff,
            mem_setOf_eq] at *
          refine ⟨hy.2, hy.1⟩
        · intro y hy k
          simp only [norm_mul, norm_pow, one_div, inv_pow]
          gcongr
          have hy2 := hy.2.le
          rw [← inv_pow]
          gcongr
          simpa only [ one_div] using hy2
      apply htt.congr'
      rw [@eventuallyEq_nhdsWithin_iff, eventually_nhds_iff_ball]
      use 1
      simp only [gt_iff_lt, zero_lt_one, mem_ball, dist_zero_right,
        mem_compl_iff, mem_singleton_iff, true_and]
      intro y hy hy0
      exact (this y hy hy0).tsum_eq
    simp only [ne_eq, Decidable.not_not] at hq1
    simp_rw [hq1]
    rw [h2]
    simp only [smul_eq_mul]
    rw [Summable.hasSum_iff]
    · apply tsum_zero_pow
    rw [← summable_nat_add_iff 1]
    simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
    apply summable_zero


lemma qParam_surj_onto_ball (r : ℝ) (hr : 0 < r) (hr2 : r < 1) [NeZero n] : ∃ (z : ℍ), ‖𝕢 n z‖ = r
    := by
  use ⟨(Periodic.invQParam n r), ?_⟩
  · have hq := Function.Periodic.qParam_right_inv (h := n) (q := r) ?_ ?_
    · simp only [UpperHalfPlane.coe]
      rw [hq]
      simp [hr.le]
    · exact Ne.symm (NeZero.ne' _)
    simp
    exact ne_of_gt hr
  rw [Function.Periodic.im_invQParam]
  simp
  rw [mul_pos_iff]
  right
  constructor
  · refine div_neg_of_neg_of_pos ?_ ?_
    · simp
      exact Nat.pos_of_neZero n
    exact two_pi_pos
  rw [propext (log_neg_iff hr)]
  exact hr2


lemma q_exp_unique (c : ℕ → ℂ) (f : ModularForm Γ(n) k) [hn : NeZero n]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) :
    c = (fun m => (qExpansion n f).coeff m) := by
  ext m
  have h := hasFPowerSeries_cuspFunction (h := n) f (by have := hn.1; positivity) (by simp)
  let qExpansion2 : PowerSeries ℂ := .mk fun m ↦ c m
  let qq : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun m ↦ (qExpansion2).coeff m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  have hqq2 : ∀ m , ‖qq m‖ = ‖(qExpansion2).coeff m‖ := by
    intro m
    simp only [qq]
    rw [
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
    simp only [_root_.map_smul, smul_eq_mul, norm_mul,
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
        obtain ⟨z, hz⟩ := qParam_surj_onto_ball n r (by simp; exact pos_iff_ne_zero.mpr hr0 )
          (by simpa using hr)
        rw [← hz]
        have hfz := summable_norm_iff.mpr (hf z).summable
        simpa using hfz
    refine ⟨H21 , zero_lt_one, ?_⟩
    intro y hy
    rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff, ←
      NNReal.coe_lt_one,
    coe_nnnorm] at hy
    simp
    have := modfom_q_exp_cuspfunc n c f hf y hy
    apply this.congr
    intro S
    congr
    ext b
    simp only [smul_eq_mul, PowerSeries.coeff_mk, qq, qExpansion2]
    rw [mul_comm]
    congr
    rw [FormalMultilinearSeries.coeff.eq_1 ]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      smul_eq_mul]
    rw [@Fin.prod_ofFn]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
  have h3 : HasFPowerSeriesAt (cuspFunction n f) qq 0 := by
    rw [HasFPowerSeriesAt]
    use 1
  have h4 : HasFPowerSeriesAt (cuspFunction n f) (qExpansionFormalMultilinearSeries n f) 0 := by
    rw [HasFPowerSeriesAt]
    use 1
  have := HasFPowerSeriesAt.eq_formalMultilinearSeries h3 h4
  rw [@FormalMultilinearSeries.ext_iff] at this
  have h5 := this m
  simp only [PowerSeries.coeff_mk, qExpansionFormalMultilinearSeries, qq, qExpansion2] at h5
  let t := c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ m
  let v := (PowerSeries.coeff m) (qExpansion n f) •
    ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ m
  have htv : (c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun =
    ( (PowerSeries.coeff m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m
      ℂ).toFun := by
    rw [h5]
  have h6 := congrFun htv m
  simpa only [ContinuousMultilinearMap.toMultilinearMap_smul, Pi.natCast_def,
    MultilinearMap.toFun_eq_coe, MultilinearMap.smul_apply, ContinuousMultilinearMap.coe_coe,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, and_not_self,
    or_false, qExpansion2, qq] using h6

lemma deriv_mul_eq (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (f * g) = deriv f * g + f * deriv g := by
  ext y
  exact deriv_mul (hf y) (hg y)

lemma auxasdf (n : ℕ) : (PowerSeries.coeff n) ((qExpansion 1 E₄) * (qExpansion 1 E₆)) =
    ∑ p ∈ Finset.antidiagonal n, (PowerSeries.coeff p.1)
    ((qExpansion 1 E₄)) * (PowerSeries.coeff p.2) ((qExpansion 1 E₆)) := by
  apply PowerSeries.coeff_mul

lemma sigma_bound (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  have : ∑ d ∈ n.divisors, d ^ k ≤ ∑ d ∈ n.divisors, n ^ k := by
    apply Finset.sum_le_sum
    intro i hi
    gcongr
    exact Nat.divisor_le hi
  apply le_trans this
  simp
  rw [pow_add]
  rw [mul_comm]
  gcongr
  simp
  exact Nat.card_divisors_le_self n

def Ek_q (k : ℕ) : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)

lemma qexpsummable (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
  Summable fun m ↦ Ek_q k m • 𝕢 ↑1 ↑z ^ m := by
  rw [← summable_nat_add_iff 1]
  simp [Ek_q, Function.Periodic.qParam]
  conv =>
    enter [1]
    ext m
    rw [mul_assoc]
  apply Summable.mul_left
  rw [ArithmeticFunction.sigma]
  simp
  apply Summable.of_norm
  have hs : Summable fun a : ℕ ↦ ((a + 1) ^ k) * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (a + 1)‖ := by
    conv =>
      enter [1]
      ext a
      rw [show ((a : ℝ) + 1) = ((a + 1) : ℕ) by simp]
    have := summable_nat_add_iff 1
        (f := fun a : ℕ ↦ (((a) : ℝ) ^ k) * ‖cexp (2 * ↑π * Complex.I * ↑z) ^ (a)‖)
    simp at *
    rw [this]
    have ht : ‖cexp (2 * ↑π * Complex.I * ↑z)‖ < 1 := by
      exact norm_exp_two_pi_I_lt_one z
    have := summable_norm_pow_mul_geometric_of_norm_lt_one k ht
    simp at *
    apply this
  apply Summable.of_nonneg_of_le _ _ hs
  · simp
  intro b
  simp at *
  have hr : ‖∑ x ∈ (b + 1).divisors, (x : ℂ) ^ (k - 1)‖ ≤
    ‖∑ x ∈ (b + 1).divisors, ((b + 1) : ℂ) ^ (k - 1)‖ := by
    apply le_trans (norm_sum_le (b + 1).divisors _ )
    simp only [norm_pow, Complex.norm_natCast, Finset.sum_const, nsmul_eq_mul, Complex.norm_mul]
    have h2 : ∑ x ∈ (b + 1).divisors, (x : ℝ) ^ (k - 1) ≤
      ∑ x ∈ (b + 1).divisors, (b + 1) ^ (k - 1) := by
      norm_cast
      apply Finset.sum_le_sum
      intro i hi
      simp at *
      refine Nat.pow_le_pow_left ?_ (k - 1)
      apply Nat.le_of_dvd _ hi
      omega
    apply le_trans h2
    simp only [Finset.sum_const, smul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_pos, Finset.card_pos, Nat.nonempty_divisors, ne_eq,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, mul_le_mul_iff_right₀]
    norm_cast
  apply le_trans hr
  simp
  norm_cast
  nth_rw 2 [show k = 1 + (k - 1) by omega]
  rw [pow_add]
  gcongr
  simp
  simpa using Nat.card_divisors_le_self (b + 1)


lemma Ek_q_exp_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : (qExpansion 1 (E k hk)).coeff 0 =
    1 := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (σ (k-1) m)
  have h := q_exp_unique 1 c (E k hk) ?_
  · have hc := congr_fun h 0
    rw [Nat.cast_one] at hc
    rw [← hc]
    simp [c]
  intro z
  have := E_k_q_expansion k hk hk2 z
  rw [Summable.hasSum_iff]
  · simp at this
    rw [this, tsum_eq_zero_add']
    · have V := tsum_pnat_eq_tsum_succ (f := fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
      simp at *
      rw [← V]
      simp [c]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro b
      ring_nf
      field_simp
      congr
      rw [Function.Periodic.qParam]
      rw [← Complex.exp_nsmul]
      congr
      simp
      ring
    have hr := (summable_nat_add_iff 1 (f := fun n : ℕ ↦ c (n) • 𝕢 (1 : ℝ) ↑z ^ (n)))
    simp at *
    rw [hr]
    have := qexpsummable k hk z
    simp [c, Ek_q] at *
    apply this
  have := qexpsummable k hk z
  simp [c, Ek_q] at *
  apply this


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
  rw [Summable.hasSum_iff]
  · simp at this
    rw [this, tsum_eq_zero_add']
    · have V := tsum_pnat_eq_tsum_succ (f := fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
      simp at *
      rw [← V]
      simp [c]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro b
      ring_nf
      field_simp
      congr
      rw [Function.Periodic.qParam]
      rw [← Complex.exp_nsmul]
      congr
      simp
      ring
    have hr := (summable_nat_add_iff 1 (f := fun n : ℕ ↦ c (n) • 𝕢 (1 : ℝ) ↑z ^ (n)))
    simp at *
    rw [hr]
    have := qexpsummable k hk z
    simp [c, Ek_q] at *
    apply this
  have := qexpsummable k hk z
  simp [c, Ek_q] at *
  apply this

lemma E4_q_exp : (fun m => (qExpansion 1 E₄).coeff m) =
    fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  have HH := Ek_q_exp 4 (by norm_num) (by exact Nat.even_iff.mpr rfl)
  rw [E4_eq]
  simp at *
  rw [HH]
  have Z := riemannZeta_two_mul_nat (k := 2) (by norm_num)
  simp at Z
  rw [ show 2 * 2 = (4 : ℂ) by ring] at Z
  rw [Z]
  ext m
  simp_all only [inv_div]
  split
  next h =>
    subst h
    simp_all only
  next h =>
    simp_all only [mul_eq_mul_right_iff, Nat.cast_eq_zero]
    left
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul,
      Nat.cast_ofNat, bernoulli, bernoulli'_four, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
      Rat.cast_one, Rat.cast_div, Rat.cast_ofNat]
    ring_nf
    rw [Complex.I_pow_four ]
    have pin : (π : ℂ) ≠ 0 := by simp
    field_simp

lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff 0 = 1 := by
  simpa using congr_fun E4_q_exp 0


@[simp]
theorem Complex.I_pow_six : Complex.I ^ 6 = -1 := by
  rw [(by norm_num : 6 = 2 * 3), pow_mul, I_sq]
  ring

@[simp]
theorem bernoulli'_five : bernoulli' 5 = 0 := by
  have : Nat.choose 5 2 = 10 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, this]

@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h1 : Nat.choose 6 4 = 15 := by decide -- shrug
  have h2 : Nat.choose 6 2 = 15 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h1, h2]

lemma E6_q_exp : (fun m => (qExpansion 1 E₆).coeff m) =
    fun m => if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  have HH := Ek_q_exp 6 (by norm_num) (by exact Nat.even_iff.mpr rfl)
  rw [E6_eq]
  simp at *
  rw [HH]
  have Z := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  simp at Z
  rw [ show 2 * 3 = (6 : ℂ) by ring] at Z
  rw [Z]
  ext m
  simp_all only [inv_div]
  split
  · rfl
  simp only [bernoulli, bernoulli'_six, one_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_inv, Rat.cast_ofNat, Nat.factorial,
    Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul, Nat.cast_ofNat]
  ring_nf
  rw [Complex.I_pow_six ]
  have pin : (π : ℂ) ≠ 0 := by simp
  field_simp

lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff 0 = 1 := by
  simpa using congr_fun E6_q_exp 0

theorem E4E6_coeff_zero_eq_zero :
  (PowerSeries.coeff 0)
      (qExpansion 1
        ((1 / 1728 : ℂ) • ((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 - (DirectSum.of (ModularForm
          Γ(1)) 6) E₆ ^ 2) 12)) =
    0 := by
  simp only [one_div, DirectSum.sub_apply]
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, qExpansion_sub]
  simp only [_root_.map_smul, map_sub, smul_eq_mul,
    mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3) 12) = E₄.mul (E₄.mul E₄) := by
    ext z
    rw [pow_three]
    rw [@DirectSum.of_mul_of, DirectSum.of_mul_of]
    simp
    rw [DFunLike.congr_arg (GradedMonoid.GMul.mul E₄ (GradedMonoid.GMul.mul E₄ E₄)) rfl]
    rfl
  have hd6 : ((DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12 = E₆.mul E₆ := by
    ext z
    rw [pow_two]
    rw [@DirectSum.of_mul_of]
    simp
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

def Delta_E4_E6_aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 := by
  let foo : ModularForm Γ(1) 12 := (E₄).mul ((E₄).mul E₄)
  let bar : ModularForm Γ(1) 12 := (E₆).mul E₆
  let F := DirectSum.of _ 4 E₄
  let G := DirectSum.of _ 6 E₆
  apply IsCuspForm_to_CuspForm _ _ ((1/ 1728 : ℂ) • (F^3 - G^2) 12 )
  rw [IsCuspForm_iff_coeffZero_eq_zero]
  exact E4E6_coeff_zero_eq_zero

lemma Delta_cuspFuntion_eq : Set.EqOn (cuspFunction 1 Delta)
     (fun y => (y : ℂ) * ∏' i, ((1 : ℂ) - y ^ (i + 1)) ^ 24) (Metric.ball 0 (1/2)) := by
  rw [cuspFunction]
  intro y hy
  by_cases hyn0 : y = 0
  · rw [hyn0]
    simp
    have := CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)
    rw [cuspFunction] at this
    simpa using this
  · rw [Function.Periodic.cuspFunction_eq_of_nonzero]
    · simp
      have hz := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := 1) (by exact
        Real.zero_lt_one) (q := y) ?_ ?_
      · rw [ofComplex_apply_of_im_pos hz]
        rw [Delta_apply, Δ]
        have hq := Function.Periodic.qParam_right_inv (h := 1) ?_ (q := y) hyn0
        · simp
          have : cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y) = y := by
            nth_rw 2 [← hq]
            congr 1
            simp
          rw [this]
          congr
          ext n
          congr
          have : cexp (2 * ↑π * Complex.I * (↑n + 1) * Periodic.invQParam 1 y) =
            (cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y)) ^ (n+1) := by
            rw [← Complex.exp_nsmul]
            congr
            ring
          rw [this]
          congr
        exact Ne.symm (zero_ne_one' ℝ)
      · simp at hy
        apply lt_trans hy
        linarith
      · exact hyn0
    exact hyn0

lemma Delta_ne_zero : Delta ≠ 0 := by
  have := Δ_ne_zero UpperHalfPlane.I
  rw [@DFunLike.ne_iff]
  refine ⟨UpperHalfPlane.I, this⟩

lemma asdf : TendstoLocallyUniformlyOn (fun n : ℕ ↦ ∏ x ∈ Finset.range n,
    fun y : ℂ ↦ (1 - y ^ (x + 1))) (fun x ↦ ∏' i, (1 - x ^ (i + 1))) atTop (Metric.ball 0 (1/2 : ℝ))
      := by
  have := prod_tendstoUniformlyOn_tprod' ( Metric.closedBall 0 (1/2)) (f:= fun x : ℕ => fun y : ℂ =>
    -y ^ (x + 1) )
    (by exact isCompact_closedBall 0 (1 / 2)) (fun n => (1/2)^(n +1)) ?_ ?_ ?_
  · apply TendstoLocallyUniformlyOn.mono (s := Metric.closedBall 0 (1/2))
    · simp at *
      have H:= this.tendstoLocallyUniformlyOn
      conv =>
        enter [1]
        ext y
        conv =>
          enter [2]
          ext n y
          rw [sub_eq_add_neg]
      conv =>
        enter [2]
        ext y
        conv =>
          enter [1]
          ext n
          rw [sub_eq_add_neg]
      convert H
      simp
    exact ball_subset_closedBall
  · rw [@summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
    simp
    exact two_inv_lt_one
  · intro n x hx
    simp at *
    rw [← inv_pow]
    apply pow_le_pow_left₀
    · exact norm_nonneg x
    exact hx
  fun_prop

theorem diffwithinat_prod_1 :
    DifferentiableWithinAt ℂ (fun (y : ℂ) ↦ ∏' (i : ℕ), (1 - y ^ (i + 1)) ^ 24) (ball 0 (1 / 2)) 0
    := by
  suffices DifferentiableWithinAt ℂ (fun (n : ℂ) ↦ (∏' (i : ℕ), (1 - n ^ (i + 1))) ^ 24) (ball 0 (1
    / 2)) 0 by
    apply this.congr
    · intro x hx
      rw [← tprod_pow _ (by apply multipliable_lt_one x (by simp at *; apply lt_trans hx; exact
        two_inv_lt_one))]
    simp
  apply DifferentiableWithinAt.pow
  have hu := asdf.differentiableOn ?_ ?_
  · apply hu
    simp
  · simp
    use 0
    intro b hb
    have := DifferentiableOn.finset_prod (u := Finset.range b)
      (f := fun x : ℕ => fun y : ℂ => 1 - y ^ (x + 1))
      (s := Metric.ball 0 (1/2)) ?_
    · simp at this
      convert this
    simp
    intro i hi
    fun_prop
  exact isOpen_ball


lemma Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1 := by
  rw [qExpansion_coeff]
  simp
  rw [← derivWithin_of_isOpen (s := Metric.ball 0 (1 / 2 : ℝ)) (isOpen_ball) (by simp) ]
  rw [derivWithin_congr Delta_cuspFuntion_eq]
  · rw [derivWithin_fun_mul]
    · simp
      have := derivWithin_id' ( 0 * ∏' (i : ℕ), (1 - 0 ^ (i + 1)) ^ 24 : ℂ)
        (Metric.ball 0 (1 / 2 : ℝ)) ?_
      · simp at *
        rw [this]
      simp
      apply IsOpen.uniqueDiffWithinAt
      · exact isOpen_ball
      refine mem_ball_self (by norm_num)
    · exact differentiableWithinAt_id'
    apply diffwithinat_prod_1
  simp
  exact CuspFormClass.cuspFunction_apply_zero (h := 1) Delta zero_lt_one (by simp)

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]

lemma E4_q_exp_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  have := E4_q_exp
  have H := congr_fun this 1
  simp at H
  rw [H]

lemma E6_q_exp_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  have := E6_q_exp
  have H := congr_fun this 1
  simp at H
  rw [H]

lemma antidiagonal_one : Finset.antidiagonal 1 = {(1,0), (0,1)} := by
  ext ⟨x,y⟩
  simp
  omega

lemma E4_pow_q_exp_one : (qExpansion 1 ((E₄).mul ((E₄).mul E₄))).coeff 1 = 3 * 240 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff, qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  simp
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  have := E4_q_exp_zero
  simp at *
  simp_rw [E4_q_exp_one, this]
  ring

lemma Ek_ne_zero (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : E k hk ≠ 0 := by
  have := Ek_q_exp_zero k hk hk2
  intro h
  rw [h, ← Nat.cast_one (R := ℝ), qExpansion_zero] at this
  simp at this

/-This is in the mod forms repo-/
lemma E4_ne_zero : E₄ ≠ 0 := by
  apply Ek_ne_zero 4 (by norm_num) (by exact Nat.even_iff.mpr rfl)

lemma E6_ne_zero : E₆ ≠ 0 := by
    apply Ek_ne_zero 6 (by norm_num) (by exact Nat.even_iff.mpr rfl)

lemma modularForm_normalise (f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) :
    (qExpansion 1 (((qExpansion 1 f).coeff 0)⁻¹ • f)).coeff 0 = 1 := by
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2, Nat.cast_one]
  refine inv_mul_cancel₀ ?_
  intro h
  rw [← (IsCuspForm_iff_coeffZero_eq_zero k f)] at h
  exact hf h

lemma PowerSeries.coeff_add (f g : PowerSeries ℂ) (n : ℕ) :
    (f + g).coeff n = (f.coeff n) + (g.coeff n) := by
  exact rfl

open ArithmeticFunction

-- E₂_mul_E₄_sub_E₆ moved to RamanujanIdentities.lean (uses ramanujan_E₄)

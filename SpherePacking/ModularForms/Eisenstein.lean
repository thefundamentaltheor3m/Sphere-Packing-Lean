/-
The purpose of this file is to define the Eisenstein series we are interested in using more
convenient notation. We will also state results with `sorry`s that should be proved and eventually
moved elsewhere in the project.
-/
import Mathlib
import SpherePacking.ModularForms.Cauchylems
import SpherePacking.ModularForms.tendstolems
import SpherePacking.ModularForms.Icc_Ico_lems
import SpherePacking.ModularForms.limunder_lems
import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.eta
import SpherePacking.ModularForms.logDeriv_lems
import SpherePacking.ModularForms.multipliable_lems
import SpherePacking.ModularForms.Delta

-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0



-- private lemma aux4 : (3 : ℤ) ≤ 4 := by norm_num
-- private lemma aux6 : (3 : ℤ) ≤ 6 := by norm_num

/- The Eisenstein Series E₂, E₄ and E₆ -/

def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition

lemma E4_apply (z : ℍ) : E₄ z = E 4 (by norm_num) z := rfl

lemma E6_apply (z : ℍ) : E₆ z = E 6 (by norm_num) z := rfl


variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)




/- variable {ι κ α : Type*}
variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι → α}

@[to_additive]
theorem le_hasProd_of_le_prod_ev [ClosedIciTopology α]
    (hf : HasProd f a) (h : ∀ᶠ s : Finset ι in atTop, c ≤ ∏ i ∈ s, f i)  : c ≤ a :=
  ge_of_tendsto hf h

@[to_additive]
theorem le_hasProd_of_le_prod_ev_range [ClosedIciTopology α] [T2Space α] (f : ℕ → α) (hm : Multipliable f)
    (hf : HasProd f a) (h : ∀ᶠ s : ℕ in atTop, c ≤ ∏ i ∈ Finset.range s, f i)  : c ≤ a := by
  rw [Multipliable.hasProd_iff_tendsto_nat hm] at hf
  apply ge_of_tendsto hf h -/



/- theorem logDeriv_tprod_eq_tsumb  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend :TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    rw [← Complex.cexp_tsum_eq_tprod]
    rw [logDeriv]
    simp
    rw [deriv_comp]
    simp
    rw [deriv_tsum ]
    simp
    congr
    ext n


    all_goals{sorry} -/





    --DifferentiableAt.finset_prod
    --logDeriv_tendsto

    --Summable.hasSum_iff_tendsto_nat





end Definitions

noncomputable section Holomorphicity

-- Try and get the desired holomorphicity results for φ₀, φ₂ and φ₄ in terms of the Eᵢ

end Holomorphicity

noncomputable section Integrability

-- Here, we show that

end Integrability

open Complex Real
/-
lemma deriv_eq_iff (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv f = deriv g ↔ ∃z, f = g + (fun _ => z) := by
  constructor
  intro h
  rw [← sub_eq_zero] at h
  have h0 := fun z => congrFun h z
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  have h2 := is_const_of_deriv_eq_zero (f := f - g)
  simp only [Pi.sub_apply] at *
  use f 1 - g 1
  ext x
  simp only [Pi.add_apply]
  have h43 := h2 ?_ ?_ x 1
  rw [← h43]
  simp only [add_sub_cancel]
  apply Differentiable.sub hf hg
  · intro t
    have h1 :=  deriv_sub (f := f) (g := g) (x := t) ?_ ?_
    have h2 := h0 t
    rw [← h2]
    have h3 : f - g = fun y => f y - g y := by rfl
    rw [h3]
    exact h1
    · exact hf.differentiableAt (x := t)
    · exact hg.differentiableAt (x := t)
  intro h
  obtain ⟨z, hz⟩ := h
  rw [hz]
  have ht : g + (fun _ => z) = fun x => g x + (fun _ => z) x := by rfl
  rw [ht]
  simp only [deriv_add_const'] -/

/- lemma func_div_ext (a b c d : ℂ → ℂ) (hb : ∀ x, b x ≠ 0) (hd : ∀ x, d x ≠ 0) :
     a / b = c /d ↔ a * d = b * c := by
  constructor
  intro h
  have h0 := fun z => congrFun h z
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  ext x
  have h1 := h0 x
  simp only [Pi.div_apply] at h1
  have e1 := hb x
  have e2 := hd x
  simp only [Pi.mul_apply]
  rw [div_eq_div_iff] at h1
  nth_rw 2 [mul_comm]
  exact h1
  exact e1
  exact e2
  intro h
  ext x
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  have hj := congrFun h x
  simp only [Pi.mul_apply] at hj
  nth_rw 2 [mul_comm]
  exact hj
  apply hb x
  apply hd x -/

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



/-
lemma tendstozero_mul_bounded (f g : ℍ → ℂ) (r : ℝ) (hf : Tendsto f atImInfty (𝓝 0)) (hg : ∀ z, ‖g z‖ ≤ r) :
  Tendsto (fun z => f z * g z) atImInfty (𝓝 0) := by
  rw [Metric.tendsto_nhds] at *
  simp only [dist_zero_right, comp_apply] at *
  by_cases hr : r = 0
  · rw [hr] at hg
    simp at hg
    sorry
  intro ε hε
  have hrp : 0 < r := by

    sorry
  have hf2 := hf (ε / r) (div_pos hε hrp)
  rw [Filter.eventually_iff_exists_mem ] at *
  obtain ⟨a, ha0, ha⟩ := hf2
  use a
  refine ⟨ha0, ?_⟩
  intro b hb
  have haa := ha b hb
  rw [norm_mul]
  have hbg := hg b
  have := mul_lt_mul' hbg haa (norm_nonneg (f b)) hrp
  rw [mul_comm]
  convert this
  field_simp -/


/- lemma tendstozero_mul_bounded2 (f g : ℍ → ℂ) (r : ℝ) (hr : 0 < r) (hf : Tendsto f atImInfty (𝓝 0))
   (hg : ∀ᶠ z in atImInfty, ‖g z‖ ≤ r) :
  Tendsto (fun z => f z * g z) atImInfty (𝓝 0) := by
  rw [Metric.tendsto_nhds] at *
  simp only [dist_zero_right, comp_apply] at *
  intro ε hε
  have hf2 := hf (ε / r) (div_pos hε hr)
  rw [Filter.eventually_iff_exists_mem ] at *
  obtain ⟨a, ha0, ha⟩ := hf2
  obtain ⟨a2, ha2, hA2⟩ := hg
  use min a a2
  refine ⟨by rw [atImInfty] at *; simp at *; refine ⟨ha0, ha2⟩, ?_⟩
  intro b hb
  have haa := ha b (by exact mem_of_mem_inter_left hb)
  have hbg:= hA2 b (by exact mem_of_mem_inter_right hb)
  rw [norm_mul]
  have := mul_lt_mul' hbg haa (by exact norm_nonneg (f b)) hr
  rw [mul_comm]
  convert this
  field_simp -/


variable  {a a₁ a₂ : ℝ}
/-
lemma tprod_eventually_bounded (g : ℕ → ℝ) (h : ∀ᶠ i in atTop, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) :
  ∃ C : ℝ, ∏' i, g i ≤ C := by
  --have := tprod_le_of_prod_range_le (α := ℝ)

  sorry -/

/-
lemma tendsto_prod_of_dominated_convergence {α β G : Type*} {𝓕 : Filter ℍ}
    {f : ℕ → ℍ → ℝ} {g : ℕ → ℝ}
    (hab : ∀ k : ℕ, Tendsto (f k ·)  𝓕 (𝓝 (g k)))
    (h_bound : TendstoLocallyUniformly (fun n ↦ ∏ i ∈ Finset.range n, fun x ↦ f i x)
    (fun x : ℍ ↦ ∏' (i : ℕ), f i x) atTop) :
    Tendsto (∏' k, f k ·) 𝓕 (𝓝 (∏' k, g k)) := by
    --have := TendstoLocallyUniformly.tendsto_comp (F := fun n ↦ ∏ i ∈ Finset.range n, fun x ↦ f x i) (f := (fun x : ℍ ↦ ∏' (i : ℕ), f x i)) (g := g)
    --have h2 := h_bound.comp
    have hh : Multipliable f := by sorry
    have h2 := hh.hasProd
    rw [hh.hasProd_iff_tendsto_nat] at h2
    have ht : Tendsto (fun x => fun n ↦ ∏ i ∈ Finset.range n, f i x) 𝓕 (𝓝 ((fun n ↦ ∏ i ∈ Finset.range n, g n))) := by sorry
    have hg : Multipliable g := by sorry
    have h3 := hg.hasProd
    rw [hg.hasProd_iff_tendsto_nat] at h3

    rw [Metric.tendsto_nhds] at *
    rw [Metric.tendstoLocallyUniformly_iff] at *
    conv at hab =>
      enter [2]
      rw [Metric.tendsto_nhds]
    simp at *

    sorry -/



/- theorem extracted_rre7 :
  Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty (𝓝 1) := by
  have ht : ∀ k : ℕ, Tendsto (fun x : ℍ ↦ ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24)) atImInfty (𝓝 1) := by
    sorry
  have hmultipliable : ∀ x : ℍ, Multipliable (fun k : ℕ => (1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * x)) ^ 24) := by
    sorry
  have hbound : TendstoLocallyUniformly (fun n ↦ ∏ i ∈ Finset.range n, fun x : ℍ ↦ (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ^ 24)
      (fun x : ℍ ↦ ∏' (i : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ^ 24) atTop := by
    sorry
  rw [Metric.tendsto_nhds] at *
  rw [Metric.tendstoLocallyUniformly_iff] at *
  have := hbound 1 (by sorry)
  have hc : Continuous (fun x : ℍ ↦ ∏' (i : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ^ 24) := by
    sorry
  have hc2 := hc.tendsto

  sorry -/

/- lemma arg_pow_of_le_one (z : ℂ) (n : ℕ) (hz : ‖z‖ < 1) : arg ((1 + z) ^ n) = n * arg (1 + z) := by
  induction' n with n hn
  simp

  sorry -/




variable {α ι: Type*}

def Modform_mul_Delta  (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
 CuspForm (CongruenceSubgroup.Gamma 1) k where
   toFun := f * Delta
   slash_action_eq' := sorry
   holo' := sorry
   zero_at_infty' := sorry

/-this is done in the modformdims repo, soon to be in mathlib.-/
lemma weigth_zero_rank_eq_one : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 0) = 1 :=
  by apply ModularForm.levelOne_weight_zero_rank_one

/-this is done in the modformdims repo, now in mathlib.-/
lemma neg_weight_rank_zero (k : ℤ) (hk : k < 0) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by
    exact ModularForm.levelOne_neg_weight_rank_zero hk


def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
      toFun f :=  CuspForm_div_Discriminant k f
      map_add' a b := CuspForm_div_Discriminant_Add k a b
      map_smul' := by
        intro m a
        ext z
        simp only [CuspForm_div_Discriminant_apply, CuspForm.smul_apply, smul_eq_mul,
          RingHom.id_apply, ModularForm.smul_apply]
        ring
      invFun f := sorry
      left_inv := sorry
      right_inv := sorry


-- lemma E4_E6_q_exp :  ((E₄ z) ^ 3 - (E₆ z) ^ 2) / 1728  =


open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

lemma IteratedDeriv_smul (a : ℂ)  (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (a • f) = a • iteratedDeriv m f  := by
  induction' m with m hm
  simp
  rw [iteratedDeriv_succ, iteratedDeriv_succ]
  rw [hm]
  ext x
  rw [@Pi.smul_def]
  exact deriv_const_smul' a (f := iteratedDeriv m f) (x := x)



lemma qExpansion_smul (a : ℂ) (f : CuspForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · rw [h]
      have h0 := CuspFormClass.cuspFunction_apply_zero n (a • f)
      have h1 := CuspFormClass.cuspFunction_apply_zero n f
      simp only [h0, Pi.smul_apply, h1, smul_eq_mul, mul_zero]
    · simp only [cuspFunction, CuspForm.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ h,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp only [PowerSeries.coeff_mk]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring





local notation "𝕢" => Periodic.qParam




theorem cuspfunc_lim_coef {k : ℤ} {F : Type u_1} [inst : FunLike F ℍ ℂ] (n : ℕ) (c : ℕ → ℂ) (f : F)
  [inst_1 : ModularFormClass F Γ(n) k] [inst_2 : NeZero n] (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 ↑n ↑τ ^ m) (f τ))
  (q : ℂ) (hq : ‖q‖ < 1) (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q) := by
  have hq2 := Function.Periodic.im_invQParam_pos_of_abs_lt_one (h := n)
    (by simp; exact Nat.pos_of_neZero n) hq hq1
  have hft := hf ⟨(Periodic.invQParam (↑n) q), hq2⟩
  have := eq_cuspFunction n f ⟨(Periodic.invQParam (↑n) q), hq2⟩
  simp only [smul_eq_mul, Complex.norm_eq_abs, ne_eq, coe_mk_subtype] at *
  rw [Function.Periodic.qParam_right_inv] at this hft
  rw [← this] at hft
  exact hft
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1


lemma tsum_zero_pow (f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0 := by
  rw [tsum_eq_zero_add]
  simp only [pow_zero, mul_one, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, tsum_zero, add_zero]
  rw [← summable_nat_add_iff 1]
  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
  apply summable_zero


lemma cuspfunc_Zero [NeZero n] [ModularFormClass F Γ(n) k] : cuspFunction n f 0 = (qExpansion n f).coeff ℂ 0 := by
  have := hasSum_qExpansion_of_abs_lt n f (q := 0) (by simp)
  simp at this
  rw [Summable.hasSum_iff] at this
  rw [tsum_zero_pow] at this
  apply this.symm

  sorry






lemma modfom_q_exp_cuspfunc  (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k]
    [NeZero n]
    (hf : ∀ τ : ℍ,  HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) : ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun m : ℕ ↦ c m • q ^ m) (cuspFunction n f q) := by
  intro q hq
  by_cases hq1 : q ≠ 0
  ·  apply cuspfunc_lim_coef n c f hf q hq hq1
  · --have h1 : Tendsto (fun z : ℍ => ∑' i, c i * (𝕢 n z) ^ n) atImInfty (𝓝 (c 0)) := by sorry
    have h2 : cuspFunction n f 0 = c 0 := by
      rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
      apply Filter.Tendsto.limUnder_eq
      have := cuspfunc_lim_coef n c f hf
      rw [cuspFunction] at this
      have htt : Tendsto (fun q => ∑' m, c m * q ^ m) (𝓝[≠] 0) (𝓝 (c 0)) := by
        have hD := tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[≠] (0 : ℂ)))
          (f := fun q : ℂ => fun m : ℕ => c m * q ^ m) (g := fun m : ℕ => c m * 0 ^ m) (bound := fun m => ‖c m‖ * (1 / 2 ) ^ m ) ?_ ?_ ?_
        convert hD
        simp only
        rw [tsum_zero_pow]
        have ht3 := (this (1/2) (by norm_num) (by apply one_div_ne_zero; exact Ne.symm (NeZero.ne' 2))).summable.norm
        simpa using ht3
        intro k
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
          simp only [smul_eq_mul, Complex.norm_eq_abs, ne_eq, Decidable.not_not, one_div,
            mem_inter_iff, mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff,
            mem_setOf_eq] at *
          refine ⟨hy.2, hy.1⟩
        · intro y hy k
          simp only [norm_mul, Complex.norm_eq_abs, norm_pow, one_div, inv_pow]
          gcongr
          have hy2 := hy.2.le
          rw [← inv_pow]
          gcongr
          simpa only [Complex.norm_eq_abs, one_div] using hy2
      apply htt.congr'
      rw [@eventuallyEq_nhdsWithin_iff, eventually_nhds_iff_ball]
      use 1
      simp only [gt_iff_lt, zero_lt_one, mem_ball, dist_zero_right, Complex.norm_eq_abs,
        mem_compl_iff, mem_singleton_iff, true_and]
      intro y hy hy0
      exact (this y hy hy0).tsum_eq
    simp only [ne_eq, Decidable.not_not] at hq1
    simp_rw [hq1]
    rw [h2]
    simp only [smul_eq_mul]
    rw [Summable.hasSum_iff]
    apply tsum_zero_pow
    rw [← summable_nat_add_iff 1]
    simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
    apply summable_zero

lemma q_exp_unique (c : ℕ → ℂ) (f : ModularForm Γ(n) k) [NeZero n]
    (hf : ∀ τ : ℍ,  HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ))  :
    c = (fun m => (qExpansion n f).coeff ℂ m) := by
  ext m
  have h := hasFPowerSeries_cuspFunction n f
  let qExpansion2 : PowerSeries ℂ := .mk fun m ↦ c m
  let qq : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun m ↦ (qExpansion2).coeff ℂ m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  have hqq2 :  ∀ m , ‖qq m‖ = ‖(qExpansion2).coeff ℂ m‖ := by
    intro m
    simp only [qq]
    rw [
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
    simp only [_root_.map_smul, smul_eq_mul, norm_mul, Complex.norm_eq_abs,
      LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  have H2 : HasFPowerSeriesOnBall (cuspFunction n f) qq 0 1 := by
    have H21 : 1 ≤ qq.radius := by
        refine le_of_forall_ge_of_dense fun r hr ↦ ?_
        lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        conv =>
          enter [1]
          intro n
          rw [hqq2]
        simp only [PowerSeries.coeff_mk, Complex.norm_eq_abs, qExpansion2, qq]
        sorry
    refine ⟨H21 , zero_lt_one, ?_⟩
    intro y hy
    rw [EMetric.mem_ball, edist_zero_right, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one,
    coe_nnnorm, Complex.norm_eq_abs] at hy
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
      smul_eq_mul, qExpansion2, qq]
    rw [@Fin.prod_ofFn]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one, qExpansion2, qq]
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
  let v :=   (PowerSeries.coeff ℂ m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ m
  have htv : (c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun =
    ( (PowerSeries.coeff ℂ m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun := by
    rw [h5]
  have h6 := congrFun htv m
  simpa only [ContinuousMultilinearMap.toMultilinearMap_smul, Pi.natCast_def,
    MultilinearMap.toFun_eq_coe, MultilinearMap.smul_apply, ContinuousMultilinearMap.coe_coe,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, and_not_self,
    or_false, qExpansion2, qq] using h6


theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) (f : ModularForm Γ(n) k) [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  simp only [comp_apply]
  have h1 := Function.Periodic.boundedAtFilter_cuspFunction (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)
    (bounded_at_infty_comp_ofComplex f)
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Function.Periodic.differentiableAt_cuspFunction_zero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) ?_ ?_ ?_).continuousAt.tendsto
    apply SlashInvariantFormClass.periodic_comp_ofComplex
    simp only [eventually_comap, eventually_atTop, ge_iff_le]
    use 1
    intro b hb a ha
    apply ModularFormClass.differentiableAt_comp_ofComplex (z := a)
    rw [ha]
    linarith
    apply ModularFormClass.bounded_at_infty_comp_ofComplex
  apply h2.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  use ball 0 1
  constructor
  apply Metric.ball_mem_nhds
  exact Real.zero_lt_one
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · simp_rw [h, cuspFunction,Periodic.cuspFunction]
      simp
      rw [Filter.limUnder_eq_iff ]
      have hl : ((a • ⇑f) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = fun x => a * (f ∘ ↑ofComplex) (Periodic.invQParam ↑n x) := by
        simp only [comp_apply, smul_eq_mul]
        ext y
        simp
      rw [hl]
      simp
      apply Filter.Tendsto.const_mul
      have := modform_tendto_ndhs_zero _ f
      simp at this
      convert this
      rw [Filter.limUnder_eq_iff ]
      apply this
      aesop
      have := modform_tendto_ndhs_zero _ (a • f)
      aesop
    · simp only [cuspFunction, CuspForm.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ h,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul]
      simp
  rw [this]
  simp only [PowerSeries.coeff_mk]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring


theorem cuspFunction_mul_zero (n : ℕ) (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b) [inst : NeZero n] :
    cuspFunction n (f.mul g) 0 = cuspFunction n f 0 * cuspFunction n g 0 := by
  rw [cuspFunction, Periodic.cuspFunction ]
  simp only [mul_coe, update_self]
  apply Filter.Tendsto.limUnder_eq
  have : (⇑f * ⇑g) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) * (⇑g ∘ ↑ofComplex) := by
    ext y
    simp only [comp_apply, Pi.mul_apply]
  rw [this]
  apply Filter.Tendsto.mul
  · apply modform_tendto_ndhs_zero
  · apply modform_tendto_ndhs_zero


lemma qExpansion_mul_coeff_zero (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : (qExpansion n (f.mul g)).coeff ℂ 0 =
      (((qExpansion n f)).coeff ℂ 0) * ((qExpansion n g)).coeff ℂ 0 := by
    simp_rw [qExpansion_coeff ]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    apply cuspFunction_mul_zero

lemma cuspFunction_mul (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : cuspFunction n (f.mul g) = cuspFunction n f * cuspFunction n g := by
    ext z
    by_cases h : z = 0
    rw [h]
    simp only [Pi.mul_apply]
    apply cuspFunction_mul_zero
    simp_rw [cuspFunction, Periodic.cuspFunction]
    simp only [mul_coe, ne_eq, h, not_false_eq_true, update_of_ne, comp_apply, Pi.mul_apply]

/- lemma IteratedDeriv_mul_eq (f g : ℂ → ℂ)  (m : ℕ) :
    iteratedDeriv m (f * g) = ∑ i ∈ Finset.antidiagonal m, ((f * iteratedDeriv i.1 g) +
      g * (iteratedDeriv i.2 f)) := by
  induction' m with m hm
  simp only [iteratedDeriv_zero, Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton,
    Prod.fst_zero, Prod.snd_zero, self_eq_add_right]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, hm]
  simp only [mul_add, add_mul, sum_range_succ, mul_assoc, mul_comm, mul_left_comm]
 -/

lemma deriv_mul_eq (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (f * g) = deriv f *  g + f * deriv g := by
  ext y
  exact deriv_mul (hf y) (hg y)

lemma deriv_mul_smul_eq (f g : ℂ → ℂ) (a : ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (a • (f * g)) = a • deriv f *  g + a• f * deriv g := by
  sorry

lemma iteratedDeriv_mul (f g : ℂ → ℂ) (m : ℕ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    iteratedDeriv m (f * g) =
    ∑ i in Finset.range m.succ, (m.choose i) * (iteratedDeriv i f) * (iteratedDeriv (m - i) g) := by
  induction' m with m hm generalizing f g
  simp only [iteratedDeriv_zero, Finset.sum_singleton, Finset.range_one, Finset.mem_singleton,
    Nat.choose_zero_right, Nat.sub_zero, Nat.choose_one_right, Nat.sub_self, mul_one]
  ring
  --rw [iteratedDeriv_succ', deriv_mul_eq f g hf hg]
  rw [iteratedDeriv_succ, hm]
  ext y
  simp
  have := deriv_sum (A := fun i => (((m.choose i) : ℂ) • (iteratedDeriv i f) * (iteratedDeriv (m - i) g ))) (u := Finset.range (m+1)) (x := y) ?_
  simp at *
  have hy : (fun y ↦ ∑ x ∈ Finset.range (m + 1), ↑(m.choose x) * iteratedDeriv x f y * iteratedDeriv (m - x) g y) =
    (∑ x ∈ Finset.range (m + 1), (fun y => ↑(m.choose x) * iteratedDeriv x f * iteratedDeriv (m - x) g) y) := by
    exact
      Eq.symm
        (Finset.sum_fn (Finset.range (m + 1)) fun c y ↦
          ↑(m.choose c) * iteratedDeriv c f y * iteratedDeriv (m - c) g y)
  rw [hy] at this
  simp at this
  --have (i : ℕ) := deriv_const_smul (m.choose i) ?_ (f:= (iteratedDeriv i f)*(iteratedDeriv (m - i) g)) (x := y)

  have ht (x : ℕ) :   deriv (((m.choose x)  : ℂ) • (iteratedDeriv x f * iteratedDeriv (m - x) g)) y =
    ↑(m.choose x) • deriv ((iteratedDeriv x f * iteratedDeriv (m - x) g)) y := by

    simp
    rw [← deriv_const_mul ]
    congr

    sorry
  conv =>
    enter [1]
    rw [this]
    conv =>
      enter [2]
      ext x
      rw [ht x]
      rw [deriv_mul_eq _ _ (sorry) (sorry)]
  --have := norm_iteratedFDeriv_mul_le


  sorry
  sorry
  sorry
  sorry





/-


lemma cuspform_iff_coeff_zero (f : ModularForm Γ(n) k) [NeZero n] (A : SL(2, ℤ)) :
    (qExpansion n f).coeff ℂ 0 = 0 ↔  f.1.1 ∈ CuspForm Γ(n) k := by
  split
  · intro h
    have h1 := Function.Periodic.cuspFunction_eq_of_nonzero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) h
    rw [cuspFunction, Periodic.cuspFunction] at h1
    simp only [update_self, mul_coe] at h1
    exact h1
  · intro h
    have h1 := Function.Periodic.cuspFunction_eq_of_nonzero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) h
    rw [cuspFunction, Periodic.cuspFunction] at h1
    simp only [update_self, mul_coe] at h1
    exact h1 -/



def ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k ) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_infty' A := (f.zero_at_infty' A).boundedAtFilter

lemma ModForm_mk_inj (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k ) (hf : f ≠ 0) :
  ModForm_mk _ _ f ≠ 0 := by
  rw [@DFunLike.ne_iff] at *
  obtain ⟨x, hx⟩ := hf
  use x
  simp [ModForm_mk] at *
  exact hx

def CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k where
  toFun f := ModForm_mk Γ k f
  map_add' := by
    intro f g
    simp only [ModForm_mk, CuspForm.coe_add]
    rfl
  map_smul' := by
    intro m f
    simp only [ModForm_mk, CuspForm.coe_smul, RingHom.id_apply]
    rfl

def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ)  : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm_to_ModularForm Γ k)

lemma mem_CuspFormSubmodule  (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ∈ CuspFormSubmodule Γ k) :
    ∃ g : CuspForm Γ k, f = CuspForm_to_ModularForm Γ k g := by
  rw [CuspFormSubmodule, LinearMap.mem_range] at hf
  aesop

instance (priority := 100) CuspFormSubmodule.funLike : FunLike (CuspFormSubmodule Γ k) ℍ ℂ where
  coe f := f.1.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspFormClass (CuspFormSubmodule Γ k) Γ k where
  slash_action_eq f := f.1.slash_action_eq'
  holo f := f.1.holo'
  zero_at_infty f := by
    have hf := f.2
    have := mem_CuspFormSubmodule Γ k f hf
    obtain ⟨g, hg⟩ := this
    convert g.zero_at_infty'
    ext y
    aesop

def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f ∈ CuspFormSubmodule Γ k

def IsCuspForm_to_CuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : CuspForm Γ k := by
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  exact hf.choose

lemma CuspForm_to_ModularForm_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toSlashInvariantForm =
    f.toSlashInvariantForm := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp_rw [CuspForm_to_ModularForm] at hg
  have hgg := congr_arg (fun x ↦ x.toSlashInvariantForm) hg
  simp [ModForm_mk] at *
  exact hgg

lemma CuspForm_to_ModularForm_Fun_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toFun =
    f.toFun := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp_rw [CuspForm_to_ModularForm] at hg
  have hgg := congr_arg (fun x ↦ x.toFun) hg
  simp [ModForm_mk] at *
  exact hgg

lemma IsCuspForm_iff_coeffZero_eq_zero  (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff ℂ 0 = 0 := by
  constructor
  · intro h
    rw [qExpansion_coeff]
    simp
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at h
    obtain ⟨g, hg⟩ := h
    have := CuspFormClass.cuspFunction_apply_zero 1 g
    simp [CuspForm_to_ModularForm, ModForm_mk] at hg
    rw [← hg]
    exact this
  · intro h
    rw [IsCuspForm]
    rw [CuspFormSubmodule, LinearMap.mem_range]
    use ⟨f.toSlashInvariantForm , f.holo', ?_⟩
    · simp only [CuspForm_to_ModularForm, ModForm_mk]
      rfl
    · intro A
      have hf := f.slash_action_eq' A (CongruenceSubgroup.mem_Gamma_one A)
      simp only [ SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, SL_slash] at *
      rw [hf]
      rw [qExpansion_coeff] at h
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
      have := modform_tendto_ndhs_zero 1 f
      rw [h] at this
      have hgg : (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (1 : ℕ) x)) = ((⇑f ∘ ↑ofComplex) ∘ (Periodic.invQParam (1 : ℕ))) := by
        rfl
      rw [hgg] at this
      have hgg2 := this.comp (Function.Periodic.qParam_tendsto (h := 1) ( Real.zero_lt_one))
      have hgg3 := hgg2.comp tendsto_coe_atImInfty
      rw [IsZeroAtImInfty, ZeroAtFilter]
      apply hgg3.congr'
      rw [Filter.eventuallyEq_iff_exists_mem]
      use ⊤
      simp only [top_eq_univ, univ_mem, Nat.cast_one, eqOn_univ, true_and]
      ext y
      simp only [comp_apply]
      have h5 := periodic_comp_ofComplex 1 f
      have := Function.Periodic.qParam_left_inv_mod_period (h := 1) (Ne.symm (zero_ne_one' ℝ)) y
      obtain ⟨m, hm⟩ := this
      have h6 := Function.Periodic.int_mul h5 m y
      simp only [Nat.cast_one, comp_apply, Periodic, ofReal_one, mul_one, ofComplex_apply] at *
      rw [← hm] at h6
      exact h6


lemma auxasdf (n : ℕ) : (PowerSeries.coeff ℂ n) ((qExpansion 1 E₄) * (qExpansion 1 E₆)) =
    ∑ p ∈ Finset.antidiagonal n, (PowerSeries.coeff ℂ p.1) ((qExpansion 1 E₄)) * (PowerSeries.coeff ℂ p.2) ((qExpansion 1 E₆)) := by
  apply PowerSeries.coeff_mul



def Delta_E4_E6_aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 := by
  let foo : ModularForm Γ(1) 12 := (E₄).mul ((E₄).mul E₄)
  let bar : ModularForm Γ(1) 12 := (E₆).mul E₆
  let F := DirectSum.of _ 4 E₄
  let G := DirectSum.of _ 6 E₆
  apply IsCuspForm_to_CuspForm _ _ ((1/ 1728 : ℂ) • (F^3 - G^2) 12 )
  rw [IsCuspForm_iff_coeffZero_eq_zero]

  sorry


lemma Delta_E4_E6_eq : ModForm_mk _ _ Delta_E4_E6_aux =
  ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12 )) := by
  rw [ModForm_mk]
  rw [Delta_E4_E6_aux]
  have := CuspForm_to_ModularForm_Fun_coe _ _  ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12 )) ?_
  simp at *
  ext z
  have hg := congr_fun this z
  simp at *
  rw [← hg]
  rfl

  sorry



lemma Delta_cuspFuntion_eq : Set.EqOn  (cuspFunction 1 Delta)
     (fun y  => (y : ℂ) * ∏' i, ((1 : ℂ) - y ^ (i + 1)) ^ 24)  (Metric.ball 0 (1/2)) := by
  rw [cuspFunction]
  intro y hy
  by_cases hyn0 : y = 0
  · rw [hyn0]
    simp
    have := CuspFormClass.cuspFunction_apply_zero 1 Delta
    rw [cuspFunction] at this
    simpa using this
  · rw [Function.Periodic.cuspFunction_eq_of_nonzero]
    simp
    have hz :=Function.Periodic.im_invQParam_pos_of_abs_lt_one (h := 1) (by exact Real.zero_lt_one) (q := y) ?_ ?_
    rw [ofComplex_apply_of_im_pos hz]
    rw [Delta_apply, Δ]
    have hq := Function.Periodic.qParam_right_inv (h := 1) ?_ (q := y) hyn0
    simp
    have : cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y) = y := by
      nth_rw 2 [← hq]
      congr 1
      simp
    rw [this]
    congr
    ext n
    congr
    have : cexp (2 * ↑π * Complex.I * (↑n + 1) * Periodic.invQParam 1 y) =
      (cexp (2 * ↑π * Complex.I * Periodic.invQParam 1 y)) ^ (n+1)  := by
      rw [← Complex.exp_nsmul]
      congr
      ring
    rw [this]
    congr
    exact Ne.symm (zero_ne_one' ℝ)
    simp at hy
    apply lt_trans hy
    linarith
    exact hyn0
    exact hyn0


lemma Delta_ne_zero : Delta ≠ 0 := by
  have := Δ_ne_zero UpperHalfPlane.I
  rw [@DFunLike.ne_iff]
  refine ⟨UpperHalfPlane.I, this⟩

lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux := by
  have := CuspForms_iso_Modforms 12
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 := by
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq this]
    simp
    exact weigth_zero_rank_eq_one
  simp at this
  apply (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp hr Delta_E4_E6_aux




lemma asdf : TendstoLocallyUniformlyOn (fun n : ℕ ↦ ∏ x ∈ Finset.range n,
    fun y : ℂ ↦ (1 - y ^ (x + 1))) (fun x ↦ ∏' i, (1 - x ^ (i + 1))) atTop (Metric.ball 0 (1/2 : ℝ)) := by
  have := prod_tendstoUniformlyOn_tprod' ( Metric.closedBall 0 (1/2)) (f:= fun x : ℕ => fun y : ℂ => -y ^ (x + 1) )
    (by exact isCompact_closedBall 0 (1 / 2)) (fun n => (1/2)^(n +1)) (sorry) ?_ ?_ ?_
  apply TendstoLocallyUniformlyOn.mono (s := Metric.closedBall 0 (1/2))
  simp at *
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
  intro n x hx
  simp at *
  rw [← inv_pow]
  apply pow_le_pow_left₀
  exact AbsoluteValue.nonneg Complex.abs x
  exact hx
  intro x n
  have hx := x.2
  simp at *

  sorry
  intro n
  fun_prop



theorem diffwithinat_prod_1 :
  DifferentiableWithinAt ℂ (fun (y : ℂ) ↦ ∏' (i : ℕ), (1 - y ^ (i + 1)) ^ 24) (ball 0 (1 / 2)) 0 := by
  conv =>
    enter [2]
    ext n
    rw [← tprod_pow _ (sorry)]
  apply DifferentiableWithinAt.pow
  have hu := asdf.differentiableOn ?_ ?_
  apply hu
  simp
  simp
  use 0
  intro b hb
  have := DifferentiableOn.finset_prod (u := Finset.range b) (f := fun x : ℕ => fun y : ℂ => 1 - y ^ (x + 1))
    (s := Metric.ball 0 (1/2)) ?_
  simp at this
  convert this
  simp
  intro i hi
  fun_prop
  exact isOpen_ball


lemma Delta_q_one_term : (qExpansion 1 Delta).coeff ℂ 1 = 1 := by
  rw [qExpansion_coeff]
  simp
  rw [← derivWithin_of_isOpen (s := Metric.ball 0 (1 / 2 : ℝ)) (isOpen_ball) (by sorry) ]
  rw [derivWithin_congr Delta_cuspFuntion_eq ]
  rw [derivWithin_mul ]
  simp
  have := derivWithin_id' ( 0 * ∏' (i : ℕ), (1 - 0 ^ (i + 1)) ^ 24 : ℂ) (Metric.ball 0 (1 / 2 : ℝ)) ?_
  simp at *
  rw [this]
  simp
  apply IsOpen.uniqueDiffWithinAt
  exact isOpen_ball
  refine mem_ball_self (by norm_num)
  exact differentiableWithinAt_id'
  apply diffwithinat_prod_1
  simp
  exact CuspFormClass.cuspFunction_apply_zero 1 Delta


/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by sorry

lemma sigma_zero (k : ℕ) : sigma k 0 = 0 := by
  exact rfl

lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff ℂ 0 = 1 := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else 240 * (sigma 3 m)
  have h := q_exp_unique 1 c E₄ ?_
  have hc := congr_fun h 0
  rw [← hc]
  simp [c]
  intro z
  have := E_k_q_expansion 4 (by norm_num) (by exact Nat.even_iff.mpr rfl) z
  rw [Summable.hasSum_iff]
  rw [ E4_apply]
  simp at this
  rw [this, tsum_eq_zero_add']
  have V := tsum_pnat_eq_tsum_succ (fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
  simp at *
  rw [← V]
  simp [c]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro b
  have Z := riemannZeta_two_mul_nat (k := 2) (by norm_num)
  simp at Z
  rw [ show 2 * 2 = (4 : ℂ) by ring] at Z
  rw [Z]
  ring
  rw [Complex.I_pow_four ]
  simp [bernoulli, Nat.factorial]
  have pin : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  field_simp
  ring
  congr
  rw [Function.Periodic.qParam]
  rw [← Complex.exp_nsmul]
  congr
  simp
  ring
  sorry
  sorry

lemma E4_q_exp_one : (qExpansion 1 E₄).coeff ℂ 1 = 240 := by sorry

lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : (qExpansion n (f.mul g)) = ((qExpansion n f)) * ((qExpansion n g)) := by
  ext m
  induction' m with m hm
  simpa using qExpansion_mul_coeff_zero n a b f g
  rw [PowerSeries.coeff_mul ] at *
  --have := PowerSeries.coeff_succ_mul_X
  simp_rw [qExpansion_coeff, cuspFunction_mul ] at *
  rw [iteratedDeriv_succ']
  rw [deriv_mul_eq]
  rw [iteratedDeriv_add]
  rw [iteratedDeriv_mul, iteratedDeriv_mul]
  simp
  have := Finset.sum_choose_succ_mul (fun i => fun j => ((iteratedDeriv i (cuspFunction n f)) * (iteratedDeriv j (cuspFunction n g))) 0) m

  sorry

  --rw [Finset.sum_antidiagonal_choose_succ_mul ]

  --have := FormalMultilinearSeries.coeff_fslope
  --have := deriv_mul (c:= cuspFunction n f) (d := cuspFunction n g)
 /-  by_cases h : m = 0
  simp_rw [h]
  simpa using qExpansion_mul_coeff_zero n a b f g
  rw [PowerSeries.coeff_mul ]
  simp_rw [qExpansion_coeff ] -/

  all_goals {sorry}

lemma antidiagonal_one : Finset.antidiagonal 1 = {(1,0), (0,1)} := by
  ext ⟨x,y⟩
  simp
  omega



lemma E4_pow_q_exp_one : (qExpansion 1 ((E₄).mul ((E₄).mul E₄))).coeff ℂ 1 = 3 * 240 := by
  rw [qExpansion_mul_coeff, qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  simp
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  have := E4_q_exp_zero
  simp at *
  simp_rw [E4_q_exp_one, this]
  ring


lemma E6_pow_q_exp_one : (qExpansion 1 ((E₆).mul E₆)).coeff ℂ 1 = -2 * 504 := by sorry

lemma Delta_E4_E6_aux_q_one_term : (qExpansion 1 Delta_E4_E6_aux).coeff ℂ 1 = 1 := by sorry

theorem Delta_E4_eqn : Delta = Delta_E4_E6_aux  := by
  ext z
  obtain ⟨c, H⟩ := delta_eq_E4E6_const
  suffices h2 : c  = 1 by
    rw [h2] at H
    simp at H
    rw [H]
  · have h1 := Delta_q_one_term
    have h2 := Delta_E4_E6_aux_q_one_term
    have := qExpansion_smul 1 c Delta
    rw [← H] at h2
    rw [← this] at h2
    simp at h2
    rw [h1] at h2
    simpa using h2

--enough to check its a cuspform, since if it is, then divining by Δ gives a modular form of weight 0.

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) : Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  have := CuspForms_iso_Modforms k
  --apply Module.finrank_eq_of_rank_eq
  rw [LinearEquiv.rank_eq this]
  apply ModularForm.levelOne_neg_weight_rank_zero
  linarith

lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2:= CuspForm_to_ModularForm_coe _ _ f hf
  ext z
  simp only [ModularForm.zero_apply] at *
  have hy := congr_arg (fun x ↦ x.1) hfc2
  have hz := congr_fun hy z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
  toSlashInvariantForm_coe] at hz
  rw [← hz]
  have := rank_zero_iff_forall_zero.mp  (cuspform_weight_lt_12_zero k hk)
    (IsCuspForm_to_CuspForm Γ(1) k f hf)
  rw [this]
  simp only [CuspForm.zero_apply]


/-This is in the mod forms repo-/
lemma E4_ne_zero : E₄ ≠ 0 := by sorry

lemma E6_ne_zero : E₆ ≠ 0 := by sorry

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 := by
  rw [rank_eq_one_iff ]
  refine ⟨E₄,E4_ne_zero, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) 4 f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff ℂ 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff ℂ 0 with hc
    have hcusp : IsCuspForm Γ(1) 4 (E₄ - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]

      sorry
    have := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) (E₄ - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop


lemma modularForm_normalise (f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) :
    (qExpansion 1 (((qExpansion 1 f).coeff ℂ 0)⁻¹ • f)).coeff ℂ 0  = 1 := by
  rw [← qExpansion_smul2]
  refine inv_mul_cancel₀ ?_
  intro h
  rw [← (IsCuspForm_iff_coeffZero_eq_zero k f)] at h
  exact hf h

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 := by
  rw [rank_eq_one_iff ]
  refine ⟨E₆,E6_ne_zero, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) 6 f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero 6 (by norm_num) f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff ℂ 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff ℂ 0 with hc
    have hcusp : IsCuspForm Γ(1) 6 (E₆ - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]

      sorry
    have := IsCuspForm_weight_lt_eq_zero 6 (by norm_num) (E₆ - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop




lemma weight_two_zero (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := by
/- cant be a cuspform from the above, so let a be its constant term, then f^2 = a^2 E₄ and
f^3 = a^3 E₆, but now this would mean that Δ = 0 or a = 0, which is a contradiction. -/
  by_cases hf : IsCuspForm (CongruenceSubgroup.Gamma 1) 2 f
  --have hfc := IsCuspForm_to_CuspForm _ _ f hf
  · have hfc2:= CuspForm_to_ModularForm_coe _ _ f hf
    ext z
    simp only [ModularForm.zero_apply] at *
    have hy := congr_arg (fun x ↦ x.1) hfc2
    have hz := congr_fun hy z
    simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
      toSlashInvariantForm_coe] at hz
    rw [← hz]
    have := rank_zero_iff_forall_zero.mp  (cuspform_weight_lt_12_zero 2 (by norm_num))
      (IsCuspForm_to_CuspForm Γ(1) 2 f hf)
    rw [this]
    simp only [CuspForm.zero_apply]
  · have hc1 : (qExpansion 1 f).coeff ℂ 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf h
    have r6 := weight_six_one_dimensional
    rw [Module.rank_eq_one_iff_finrank_eq_one] at r6
    rw [finrank_eq_one_iff_of_nonzero' E₆ E6_ne_zero] at r6
    have r6f := r6 ((f.mul f).mul f)
    obtain ⟨c6, hc6⟩ := r6f
    have hc6e : c6 =  ((qExpansion 1 f).coeff ℂ 0)^3 := by sorry
    have r4 := weight_four_one_dimensional
    rw [Module.rank_eq_one_iff_finrank_eq_one] at r4
    rw [finrank_eq_one_iff_of_nonzero' E₄ E4_ne_zero] at r4
    have r4f := r4 (f.mul f)
    obtain ⟨c4, hc4⟩ := r4f
    have hc4e : c4 =  ((qExpansion 1 f).coeff ℂ 0)^2 := by

      sorry
    exfalso
    let F :=  DirectSum.of _ 2 f
    let D := DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) 12
    have : D ≠ 0 := by
      have HD := ModForm_mk_inj _ _ _ Delta_ne_zero
      apply HD
    have HF2 : (F^2)  =  c4 • (DirectSum.of _ 4 E₄) := by
      rw [← DirectSum.of_smul, hc4]
      simp [F]
      rw [pow_two, DirectSum.of_mul_of]
      rfl
    have HF3 : (F^3)  =  c6 • (DirectSum.of _ 6 E₆) := by
      rw [← DirectSum.of_smul, hc6]
      simp [F]
      rw [pow_three,  ← mul_assoc, DirectSum.of_mul_of, DirectSum.of_mul_of]
      rfl
    have HF12 : (((F^2)^3) 12) = ((qExpansion 1 f).coeff ℂ 0)^6 • (E₄.mul (E₄.mul E₄)) := by
      rw [HF2, pow_three]
      simp
      rw [DirectSum.of_mul_of, DirectSum.of_mul_of, hc4e, smul_smul, smul_smul]
      ring
      rw [@DirectSum.smul_apply]
      simp
      rfl
    have hF2 : (((F^3)^2) 12) = ((qExpansion 1 f).coeff ℂ 0)^6 • ((E₆.mul E₆)) := by
      rw [HF3, pow_two]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Int.reduceAdd,
        PowerSeries.coeff_zero_eq_constantCoeff, F]
      rw [DirectSum.of_mul_of, hc6e, smul_smul]
      ring_nf
      rw [@DirectSum.smul_apply]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, DirectSum.of_eq_same, F]
      rfl
    have V : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) =  ((qExpansion 1 f).coeff ℂ 0)^6 • D := by
      rw [HF12, hF2]
      simp [D]
      rw [Delta_E4_eqn, Delta_E4_E6_eq, pow_two, pow_three, DirectSum.of_mul_of,
        DirectSum.of_mul_of,DirectSum.of_mul_of]
      simp only [one_div, Int.reduceAdd, DirectSum.sub_apply, DirectSum.of_eq_same, D, F]
      ext y
      simp only [ModularForm.smul_apply, sub_apply, Int.reduceAdd, smul_eq_mul, D, F]
      ring_nf
      rfl

    have ht : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = 0 := by
      ext y
      simp
      ring_nf
    rw [ht] at V
    have hr := congr_fun (congr_arg (fun x ↦ x.toFun) V) UpperHalfPlane.I
    simp at hr
    rcases hr with h | h
    · simp at *
      exact hc1 h
    · simp [D, ModForm_mk] at h
      have hDelta := Δ_ne_zero UpperHalfPlane.I
      rw [← Delta_apply] at hDelta
      exact hDelta h




lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℤ) (hk : 2 < k):
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := sorry

lemma dim_modforms_lvl_one (k : ℤ) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = if 12 ∣ k - 2 then
    Nat.floor (k / 12) else Nat.floor (k / 12) + 1 := sorry

lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry
--use the norm to turn it into a level one question.



open ArithmeticFunction

section Ramanujan_Formula

-- In this section, we state some simplifications that are used in Cor 7.5-7.7 of the blueprint

theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  sorry



end Ramanujan_Formula

#min_imports

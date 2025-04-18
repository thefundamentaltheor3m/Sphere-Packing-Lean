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
import SpherePacking.ModularForms.qExpansion_lems
import SpherePacking.ModularForms.IsCuspForm
import SpherePacking.ModularForms.Eisensteinqexpansions

-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions




-- private lemma aux4 : (3 : ℤ) ≤ 4 := by norm_num
-- private lemma aux6 : (3 : ℤ) ≤ 6 := by norm_num

/- The Eisenstein Series E₂, E₄ and E₆ -/

def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition


lemma E4_eq : E₄ = E 4 (by norm_num) := rfl

lemma E6_eq : E₆ = E 6 (by norm_num) := rfl


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

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

/- lemma IsZeroAtImInfty_iff_coeff_eq_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k] [inst : NeZero n] :
    IsZeroAtImInfty  f ↔ (qExpansion n f).coeff ℂ 0 = 0 := by
  rw [IsZeroAtImInfty, ZeroAtFilter]
  rw [qExpansion_coeff]
  simp
  rw [cuspFunction]
  rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  constructor
  intro h
  apply Filter.Tendsto.limUnder_eq
  have := modform_tendto_ndhs_zero f n
  have h2 :=   Periodic.cuspFunction_zero_of_zero_at_inf (h := n)
    (by simp; exact Nat.pos_of_neZero n) (h.comp tendsto_comap_im_ofComplex)
  rw [cuspFunction] at this
  rw [h2] at this -/





def mul_Delta_map (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) : ModularForm (CongruenceSubgroup.Gamma 1) k := by
  have := (f.mul (ModForm_mk _ 12 Delta))
  have hk : k - 12 + 12 = k := by ring
  exact ModularForm.mcast hk this

lemma mcast_apply {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) (z : ℍ) :
  (ModularForm.mcast h f) z = f z := by
  rfl

lemma mul_Delta_map_eq (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) (z : ℍ) :
  (mul_Delta_map k f) z = f z * Delta z := by
  rw [mul_Delta_map, mcast_apply ]
  rfl

lemma mul_Delta_map_eq_mul (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
  ((mul_Delta_map k f) : ℍ → ℂ) = (f.mul (ModForm_mk _ 12 Delta))  := by
  ext z
  rw [mul_Delta_map, mcast_apply ]


lemma mul_Delta_IsCuspForm (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
  IsCuspForm (CongruenceSubgroup.Gamma 1) k (mul_Delta_map k f) := by
  rw [IsCuspForm_iff_coeffZero_eq_zero]
  rw [qExpansion_ext2  _ _ (mul_Delta_map_eq_mul k f)]
  rw [qExpansion_mul_coeff_zero]
  simp only [ mul_eq_zero]
  right
  rw [← IsCuspForm_iff_coeffZero_eq_zero ]
  rw [IsCuspForm, CuspFormSubmodule, CuspForm_to_ModularForm]
  simp

/- def Modform_mul_Delta (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
 CuspForm (CongruenceSubgroup.Gamma 1) k where
  toFun := f * Delta
  slash_action_eq' A hA := by
    conv =>
      enter [1,2]
      rw [show k = k - 12 + 12 by ring]
    rw [ModularForm.mul_slash_SL2,
    SlashInvariantFormClass.slash_action_eq f A hA, SlashInvariantFormClass.slash_action_eq Delta A hA]
  holo' := f.holo'.mul Delta.holo'
  zero_at_infty' := by
    intro A
    have h1 := f.bdd_at_infty' A
    have h2 := Delta.zero_at_infty' A
    rw [IsBoundedAtImInfty, BoundedAtFilter, IsZeroAtImInfty, ZeroAtFilter] at *

    sorry -/


def Modform_mul_Delta' (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
 CuspForm (CongruenceSubgroup.Gamma 1) k := IsCuspForm_to_CuspForm _ k (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)


theorem mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z :=
  rfl

lemma Modform_mul_Delta_apply (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) (z : ℍ) :
  (Modform_mul_Delta' k f) z = f z * Delta z := by
  rw [Modform_mul_Delta']
  have := congr_fun
    (CuspForm_to_ModularForm_Fun_coe _ _ (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)) z
  simp at *
  rw [mul_Delta_map_eq] at this
  exact this

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
      invFun := Modform_mul_Delta' k
      left_inv := by
        intro f
        ext z
        simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply ]
        rw [Delta_apply]
        rw [div_mul_cancel₀ ]
        apply Δ_ne_zero
      right_inv := by
        intro f
        ext z
        simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply ]
        rw [Delta_apply]
        rw [mul_div_cancel_right₀]
        apply Δ_ne_zero




open scoped Real MatrixGroups CongruenceSubgroup


local notation "𝕢" => Periodic.qParam


theorem cuspfunc_lim_coef {k : ℤ} {F : Type u_1} [inst : FunLike F ℍ ℂ] (n : ℕ) (c : ℕ → ℂ) (f : F)
  [inst_1 : ModularFormClass F Γ(n) k] [inst_2 : NeZero n] (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 ↑n ↑τ ^ m) (f τ))
  (q : ℂ) (hq : ‖q‖ < 1) (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q) := by
  have hq2 := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := n)
    (by simp; exact Nat.pos_of_neZero n) hq hq1
  have hft := hf ⟨(Periodic.invQParam (↑n) q), hq2⟩
  have := eq_cuspFunction n f ⟨(Periodic.invQParam (↑n) q), hq2⟩
  simp only [smul_eq_mul, ne_eq, coe_mk_subtype] at *
  rw [Function.Periodic.qParam_right_inv] at this hft
  rw [← this] at hft
  exact hft
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1

theorem summable_zero_pow {G : Type*} [NormedField G] (f : ℕ → G) : Summable fun m ↦ f m * 0 ^ m := by
  rw [← summable_nat_add_iff 1]
  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
  apply summable_zero

lemma tsum_zero_pow (f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0 := by
  rw [tsum_eq_zero_add]
  simp only [pow_zero, mul_one, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, tsum_zero, add_zero]
  apply summable_zero_pow


lemma cuspfunc_Zero [NeZero n] [ModularFormClass F Γ(n) k] : cuspFunction n f 0 = (qExpansion n f).coeff ℂ 0 := by
  have := hasSum_qExpansion_of_abs_lt n f (q := 0) (by simp)
  simp at this
  rw [Summable.hasSum_iff] at this
  rw [tsum_zero_pow] at this
  apply this.symm
  rw [← summable_nat_add_iff 1]
  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
  apply summable_zero

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
    apply tsum_zero_pow
    rw [← summable_nat_add_iff 1]
    simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
    apply summable_zero


lemma qParam_surj_onto_ball (r : ℝ) (hr : 0 < r) (hr2 : r < 1) [NeZero n] : ∃ (z : ℍ), ‖𝕢 n z‖ = r := by
  use ⟨(Periodic.invQParam n r), ?_⟩
  have hq := Function.Periodic.qParam_right_inv (h := n) (q := r) ?_ ?_
  simp only [UpperHalfPlane.coe]
  rw [hq]
  simp [hr.le]
  exact Ne.symm (NeZero.ne' _)
  simp
  exact ne_of_gt hr
  rw [Function.Periodic.im_invQParam]
  simp
  rw [mul_pos_iff]
  right
  constructor
  refine div_neg_of_neg_of_pos ?_ ?_
  simp
  exact Nat.pos_of_neZero n
  exact two_pi_pos
  rw [propext (log_neg_iff hr)]
  exact hr2


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
        simp only [PowerSeries.coeff_mk,  qExpansion2, qq]
        by_cases hr0 : r = 0
        rw [hr0]
        apply summable_zero_pow
        obtain ⟨z, hz⟩ :=  qParam_surj_onto_ball n r (by simp; exact pos_iff_ne_zero.mpr hr0 )
          (by simpa using hr)
        rw [← hz]
        have hfz := summable_norm_iff.mpr (hf z).summable
        simpa using hfz
    refine ⟨H21 , zero_lt_one, ?_⟩
    intro y hy
    rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one,
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

/- lemma deriv_mul_smul_eq (f g : ℂ → ℂ) (a : ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (a • (f * g)) = a • deriv f *  g + a• f * deriv g := by
  sorry -/

/- lemma iteratedDeriv_mul (f g : ℂ → ℂ) (m : ℕ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
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


lemma iteratedDerivAt_mul (f g : ℂ → ℂ) (s : ℂ) (m : ℕ) (hf : DifferentiableAt ℂ f s)
    (hg : DifferentiableAt ℂ g s) :
    iteratedDeriv m (f * g) s =
    ∑ i in Finset.range m.succ, (m.choose i) * (iteratedDeriv i f s) * (iteratedDeriv (m - i) g s) := by
  induction' m with m hm generalizing f g
  simp only [iteratedDeriv_zero, Finset.sum_singleton, Finset.range_one, Finset.mem_singleton,
    Nat.choose_zero_right, Nat.sub_zero, Nat.choose_one_right, Nat.sub_self, mul_one]
  ring
  rfl
  --rw [iteratedDeriv_succ', deriv_mul_eq f g hf hg]
  rw [iteratedDeriv_succ]
  --rw [deriv_mul_eq]
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
  sorry
 -/

/-
lemma iteratedDeriv_mul_anti (f g : ℂ → ℂ) (m : ℕ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    iteratedDeriv m (f * g) =
    ∑ i in Finset.antidiagonal (m + 1), (m.choose i.2) * (iteratedDeriv i.1 f) * (iteratedDeriv i.2 g) := by

  sorry -/
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




lemma auxasdf (n : ℕ) : (PowerSeries.coeff ℂ n) ((qExpansion 1 E₄) * (qExpansion 1 E₆)) =
    ∑ p ∈ Finset.antidiagonal n, (PowerSeries.coeff ℂ p.1) ((qExpansion 1 E₄)) * (PowerSeries.coeff ℂ p.2) ((qExpansion 1 E₆)) := by
  apply PowerSeries.coeff_mul


lemma sigma_bound (k n : ℕ) : sigma k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  have :  ∑ d ∈ n.divisors, d ^ k ≤  ∑ d ∈ n.divisors, n ^ k := by
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

def Ek_q (k : ℕ) : ℕ → ℂ :=  fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (sigma (k-1) m)

lemma qexpsummable (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
  Summable fun m ↦ Ek_q k m • 𝕢 ↑1 ↑z ^ m := by
  rw [← summable_nat_add_iff 1]
  simp [Ek_q, Function.Periodic.qParam]
  conv =>
    enter [1]
    ext m
    rw [mul_assoc]
  apply Summable.mul_left
  rw [sigma]
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
  simp
  intro b
  simp at *
  have hr : ‖∑ x ∈ (b + 1).divisors, (x : ℂ) ^ (k - 1)‖ ≤
    ‖∑ x ∈ (b + 1).divisors, ((b + 1) : ℂ) ^ (k - 1)‖ := by
    apply le_trans (norm_sum_le (b + 1).divisors _ )
    simp only [norm_pow, Complex.norm_natCast, Finset.sum_const, nsmul_eq_mul, Complex.norm_mul]
    have h2 :  ∑ x ∈ (b + 1).divisors, (x : ℝ) ^ (k - 1) ≤
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
      Nat.cast_one, Nat.cast_pos, Finset.card_pos, Nat.nonempty_divisors, ne_eq, Nat.add_eq_zero,
      one_ne_zero, and_false, not_false_eq_true, mul_le_mul_left]
    norm_cast
  apply le_trans hr
  simp
  norm_cast
  nth_rw 2 [show k = 1 + (k - 1) by omega]
  rw [pow_add]
  gcongr
  simp
  simpa using Nat.card_divisors_le_self (b + 1)


lemma Ek_q_exp_zero (k : ℕ) (hk :  3 ≤ (k : ℤ)) (hk2 : Even k) : (qExpansion 1 (E k hk)).coeff ℂ 0 = 1 := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (sigma (k-1) m)
  have h := q_exp_unique 1 c (E k hk) ?_
  have hc := congr_fun h 0
  rw [← hc]
  simp [c]
  intro z
  have := E_k_q_expansion k hk hk2 z
  rw [Summable.hasSum_iff]
  simp at this
  rw [this, tsum_eq_zero_add']
  have V := tsum_pnat_eq_tsum_succ (fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
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
  have :=  qexpsummable k hk z
  simp [c, Ek_q] at *
  apply this
  have :=  qexpsummable k hk z
  simp [c, Ek_q] at *
  apply this


lemma Ek_q_exp (k : ℕ) (hk :  3 ≤ (k : ℤ)) (hk2 : Even k) : (fun m => (qExpansion 1 (E k hk)).coeff ℂ m) =
  fun m => if m = 0 then 1 else
    (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (sigma (k-1) m) := by
  let c : ℕ → ℂ := fun m => if m = 0 then 1 else
      (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) * (sigma (k-1) m)
  have h := q_exp_unique 1 c (E k hk) ?_
  rw [← h]
  intro z
  have := E_k_q_expansion k hk hk2 z
  rw [Summable.hasSum_iff]
  simp at this
  rw [this, tsum_eq_zero_add']
  have V := tsum_pnat_eq_tsum_succ (fun b => c (b) • 𝕢 ↑1 ↑z ^ (b))
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
  have :=  qexpsummable k hk z
  simp [c, Ek_q] at *
  apply this
  have :=  qexpsummable k hk z
  simp [c, Ek_q] at *
  apply this

lemma E4_q_exp : (fun m => (qExpansion 1 E₄).coeff ℂ m) =
    fun m => if m = 0 then 1 else (240 : ℂ) * (sigma 3 m) := by
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
    simp [inv_pow, bernoulli, bernoulli'_four, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, mul_inv_rev, inv_div, Nat.factorial,
    Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul, Nat.cast_ofNat, inv_inv]
    ring_nf
    rw [Complex.I_pow_four ]
    have pin : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
    field_simp



lemma E4_q_exp_zero : (qExpansion 1 E₄).coeff ℂ 0 = 1 := by
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

lemma E6_q_exp : (fun m => (qExpansion 1 E₆).coeff ℂ m) = fun m => if m = 0 then 1 else  -(504 : ℂ) * (sigma 5 m) := by

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
  rfl
  simp only [inv_pow, bernoulli, bernoulli'_six, one_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_inv, Rat.cast_ofNat, mul_inv_rev, inv_inv, Nat.factorial,
    Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul, Nat.cast_ofNat, mul_neg,
    neg_mul, neg_inj]
  ring_nf
  rw [Complex.I_pow_six ]
  have pin : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  field_simp


lemma E6_q_exp_zero : (qExpansion 1 E₆).coeff ℂ 0 = 1 := by
  simpa using congr_fun E6_q_exp 0

theorem E4E6_coeff_zero_eq_zero  :
  (PowerSeries.coeff ℂ 0)
      (qExpansion 1
        ((1 / 1728 : ℂ) • ((DirectSum.of (ModularForm Γ(1)) 4) E₄ ^ 3 - (DirectSum.of (ModularForm Γ(1)) 6) E₆ ^ 2) 12)) =
    0 := by
  simp only [one_div, DirectSum.sub_apply]
  rw [← qExpansion_smul2, qExpansion_sub]
  simp only [_root_.map_smul,  map_sub, smul_eq_mul,
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
  rw [qExpansion_mul_coeff, qExpansion_mul_coeff, qExpansion_mul_coeff, PowerSeries.coeff_mul, PowerSeries.coeff_mul,]
  simp only [Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton, Prod.fst_zero,
    Prod.snd_zero, map_mul]
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
    have hz := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := 1) (by exact Real.zero_lt_one) (q := y) ?_ ?_
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
    exact ModularForm.levelOne_weight_zero_rank_one
  simp at this
  apply (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp hr Delta_E4_E6_aux




lemma asdf : TendstoLocallyUniformlyOn (fun n : ℕ ↦ ∏ x ∈ Finset.range n,
    fun y : ℂ ↦ (1 - y ^ (x + 1))) (fun x ↦ ∏' i, (1 - x ^ (i + 1))) atTop (Metric.ball 0 (1/2 : ℝ)) := by
  have := prod_tendstoUniformlyOn_tprod' ( Metric.closedBall 0 (1/2)) (f:= fun x : ℕ => fun y : ℂ => -y ^ (x + 1) )
    (by exact isCompact_closedBall 0 (1 / 2)) (fun n => (1/2)^(n +1)) ?_ ?_ ?_ ?_
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
  · rw [@summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
    simp
    exact two_inv_lt_one
  intro n x hx
  simp at *
  rw [← inv_pow]
  apply pow_le_pow_left₀
  exact norm_nonneg x
  exact hx
  intro x n
  have hx := x.2
  simp at *
  apply  ball_pow_ne_1
  simp at *
  apply lt_of_le_of_lt hx
  exact two_inv_lt_one
  intro n
  fun_prop



theorem diffwithinat_prod_1 :
  DifferentiableWithinAt ℂ (fun (y : ℂ) ↦ ∏' (i : ℕ), (1 - y ^ (i + 1)) ^ 24) (ball 0 (1 / 2)) 0 := by
  suffices DifferentiableWithinAt ℂ (fun (n : ℂ) ↦ (∏' (i : ℕ), (1 - n ^ (i + 1))) ^ 24) (ball 0 (1 / 2)) 0 by
    apply this.congr
    intro x hx
    rw [← tprod_pow _ (by apply multipliable_lt_one  x (by simp at *; apply lt_trans hx; exact
      two_inv_lt_one))]
    simp
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
  rw [← derivWithin_of_isOpen (s := Metric.ball 0 (1 / 2 : ℝ)) (isOpen_ball) (by simp) ]
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



lemma sigma_zero (k : ℕ) : sigma k 0 = 0 := by
  exact rfl



variable {α β γ : Type*}


variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]

def HasProdUniformlyOn (f : ι → β → α) (g : β → α) (s : Set β) : Prop :=
  TendstoUniformlyOn (fun s : Finset ι ↦ ∏ b ∈ s, f b) g atTop s

lemma E4_q_exp_one : (qExpansion 1 E₄).coeff ℂ 1 = 240 := by
  have := E4_q_exp
  have H := congr_fun this 1
  simp at H
  rw [H]
  simp
  exact rfl

lemma E6_q_exp_one : (qExpansion 1 E₆).coeff ℂ 1 = -504 := by
  have := E6_q_exp
  have H := congr_fun this 1
  simp at H
  rw [H]
  simp
  exact rfl


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



lemma Ek_ne_zero (k : ℕ) (hk :  3 ≤ (k : ℤ)) (hk2 : Even k) : E k hk ≠ 0 := by
  have := Ek_q_exp_zero k hk hk2
  intro h
  rw [h, qExpansion_zero] at this
  simp at this


/-This is in the mod forms repo-/
lemma E4_ne_zero : E₄ ≠ 0 := by
  apply Ek_ne_zero 4 (by norm_num) (by exact Nat.even_iff.mpr rfl)

lemma E6_ne_zero : E₆ ≠ 0 := by
    apply Ek_ne_zero 6 (by norm_num) (by exact Nat.even_iff.mpr rfl)

lemma modularForm_normalise (f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) :
    (qExpansion 1 (((qExpansion 1 f).coeff ℂ 0)⁻¹ • f)).coeff ℂ 0  = 1 := by
  rw [← qExpansion_smul2]
  refine inv_mul_cancel₀ ?_
  intro h
  rw [← (IsCuspForm_iff_coeffZero_eq_zero k f)] at h
  exact hf h

lemma PowerSeries.coeff_add (f g : PowerSeries ℂ) (n : ℕ) :
    (f + g).coeff ℂ n = (f.coeff ℂ n) + (g.coeff ℂ n) := by
  exact rfl

/- lemma ModularForm_limUnder_eq (n : ℕ) (f : ModularForm Γ(n) k) [NeZero n] :
  limUnder (𝓝[≠] 0) ((⇑f ∘ ↑ofComplex) ∘ Periodic.invQParam n) = cuspFunction n f 0 := by
  apply Filter.Tendsto.limUnder_eq
  apply modform_tendto_ndhs_zero -/



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
  rw [IsCuspForm_iff_coeffZero_eq_zero]
  exact E4E6_coeff_zero_eq_zero

instance : FunLike (ℍ → ℂ) ℍ ℂ := { coe := fun ⦃a₁⦄ ↦ a₁, coe_injective' := fun ⦃_ _⦄ a ↦ a}


lemma Delta_E4_E6_aux_q_one_term : (qExpansion 1 Delta_E4_E6_aux).coeff ℂ 1 = 1 := by
  have := Delta_E4_E6_eq
  have h1 : (qExpansion 1 Delta_E4_E6_aux) = qExpansion 1 (ModForm_mk Γ(1) 12 Delta_E4_E6_aux) := by
    apply qExpansion_ext2 Delta_E4_E6_aux (ModForm_mk Γ(1) 12 Delta_E4_E6_aux) ?_
    ext z
    rw [Delta_E4_E6_aux, ModForm_mk]
    simp
    rfl
  rw [h1, Delta_E4_E6_eq]
  simp only [one_div, DirectSum.sub_apply]
  rw [← qExpansion_smul2]
  rw [qExpansion_sub]
  have h4 := qExpansion_pow E₄ 3
  have h6 := qExpansion_pow E₆ 2
  simp only [Nat.cast_ofNat, Int.reduceMul] at h4 h6
  rw [h4, h6]
  simp
  rw [pow_three, pow_two]
  simp_rw [PowerSeries.coeff_mul]
  rw [antidiagonal_one]
  simp  [Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self,
    not_false_eq_true, Finset.sum_insert, Finset.antidiagonal_zero, Prod.mk_zero_zero,
    Finset.sum_singleton, Prod.fst_zero, Prod.snd_zero]
  have he4 := E4_q_exp_zero
  have he6 := E6_q_exp_zero
  simp at *
  simp_rw [E4_q_exp_one, he4, he6]
  ring_nf
  rw [antidiagonal_one]
  simp  [Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self,
    not_false_eq_true, Finset.sum_insert, Finset.antidiagonal_zero, Prod.mk_zero_zero,
    Finset.sum_singleton, Prod.fst_zero, Prod.snd_zero]
  simp_rw [E4_q_exp_one, he4, E6_q_exp_one]
  ring

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
      rw [qExpansion_sub]
      have := modularForm_normalise f hf2
      simp only [ne_eq,  map_sub] at *
      rw [hc, this]
      rw [E6_q_exp_zero]
      exact sub_eq_zero_of_eq rfl
    have := IsCuspForm_weight_lt_eq_zero 6 (by norm_num) (E₆ - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop


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
      rw [qExpansion_sub]
      have := modularForm_normalise f hf2
      simp only [ne_eq,  map_sub] at *
      rw [hc, this]
      rw [E4_q_exp_zero]
      exact sub_eq_zero_of_eq rfl
    have := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) (E₄ - c⁻¹• f) hcusp
    have hfc := hf c
    rw [@sub_eq_zero] at this
    aesop

lemma weight_eight_one_dimensional  (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12):
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_eq_one_iff ]
  refine ⟨E k hk ,Ek_ne_zero k hk hk2, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) k f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero k (by simpa using hk3) f hf2
    aesop
  · have hc1 : (qExpansion 1 f).coeff ℂ 0 ≠ 0 := by
      intro h
      rw [← IsCuspForm_iff_coeffZero_eq_zero] at h
      exact hf2 h
    set c := (qExpansion 1 f).coeff ℂ 0 with hc
    have hcusp : IsCuspForm Γ(1) k (E k hk - c⁻¹• f) := by
      rw [IsCuspForm_iff_coeffZero_eq_zero]
      rw [qExpansion_sub]
      have := modularForm_normalise f hf2
      simp only [ne_eq,  map_sub] at *
      rw [hc, this]
      have hE := Ek_q_exp_zero k hk hk2
      simp at *
      rw [hE]
      exact sub_eq_zero_of_eq rfl
    have := IsCuspForm_weight_lt_eq_zero k (by simpa using hk3) (E k hk - c⁻¹• f) hcusp
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
    have hc6e : c6 =  ((qExpansion 1 f).coeff ℂ 0)^3 := by
      have := qExpansion_mul_coeff 1 4 2 (f.mul f) f
      have h2 := qExpansion_mul_coeff 1 2 2 f f
      rw [← hc6] at this
      rw [← qExpansion_smul2 1 c6, h2] at this
      have hh := congr_arg (fun x => x.coeff ℂ 0) this
      simp only [_root_.map_smul, smul_eq_mul,
        map_mul] at hh
      rw [E6_q_exp_zero] at hh
      rw [pow_three]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, ne_eq, Int.reduceAdd, mul_one,
        map_mul] at *
      rw [← mul_assoc]
      exact hh
    have r4 := weight_four_one_dimensional
    rw [Module.rank_eq_one_iff_finrank_eq_one] at r4
    rw [finrank_eq_one_iff_of_nonzero' E₄ E4_ne_zero] at r4
    have r4f := r4 (f.mul f)
    obtain ⟨c4, hc4⟩ := r4f
    have hc4e : c4 =  ((qExpansion 1 f).coeff ℂ 0)^2 := by
      have := qExpansion_mul_coeff 1 2 2 f f
      rw [← hc4] at this
      rw [← qExpansion_smul2 1 c4] at this
      have hh := congr_arg (fun x => x.coeff ℂ 0) this
      simp only [_root_.map_smul, smul_eq_mul,
        map_mul] at hh
      rw [E4_q_exp_zero] at hh
      rw [pow_two]
      simpa using hh
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
      ring_nf
      rw [@DirectSum.smul_apply]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, DirectSum.of_eq_same, F]
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
      simp only [one_div, Int.reduceAdd, PowerSeries.coeff_zero_eq_constantCoeff,
        DirectSum.of_eq_same, D, F]
      rw [Delta_E4_eqn, Delta_E4_E6_eq, pow_two, pow_three, DirectSum.of_mul_of,
        DirectSum.of_mul_of,DirectSum.of_mul_of]
      simp only [one_div, Int.reduceAdd, DirectSum.sub_apply, DirectSum.of_eq_same, D, F]
      ext y
      simp only [ModularForm.smul_apply, sub_apply, Int.reduceAdd, smul_eq_mul, D, F]
      ring_nf
      rfl
    have ht : (1 / 1728 : ℂ) • ((((F^2)^3) 12) - (((F^3)^2) 12)) = 0 := by
      ext y
      simp only [one_div, ModularForm.smul_apply, sub_apply, smul_eq_mul, ModularForm.zero_apply,
        mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, F, D]
      ring_nf
    rw [ht] at V
    have hr := congr_fun (congr_arg (fun x ↦ x.toFun) V) UpperHalfPlane.I
    simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, ModularForm.zero_apply,
      PowerSeries.coeff_zero_eq_constantCoeff, ModularForm.smul_apply, smul_eq_mul, zero_eq_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, F, D] at hr
    rcases hr with h | h
    · simp only [PowerSeries.coeff_zero_eq_constantCoeff, ne_eq, Int.reduceAdd, one_div,
      isUnit_iff_ne_zero, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.smul_eq_zero,
      F, D] at *
      exact hc1 h
    · simp only [ModForm_mk, DirectSum.of_eq_same, F, D] at h
      have hDelta := Δ_ne_zero UpperHalfPlane.I
      rw [← Delta_apply] at hDelta
      exact hDelta h



lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
    have h1 : Module.rank ℂ (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k)  =
      Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
      apply LinearEquiv.rank_eq
      have := CuspForm_iso_CuspFormSubmodule Γ(1) k
      exact _root_.id this.symm
    rw [← h1, ← Submodule.rank_quotient_add_rank (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k)]
    congr
    rw [rank_eq_one_iff ]
    refine ⟨ Submodule.Quotient.mk (E k (by linarith)), ?_, ?_⟩
    intro hq
    rw [Submodule.Quotient.mk_eq_zero] at hq
    have := IsCuspForm_iff_coeffZero_eq_zero k (E k (by linarith))
    rw [IsCuspForm] at this
    rw [this, Ek_q_exp_zero k hk hk2] at hq
    aesop
    intro v
    have  := Quotient.exists_rep v
    obtain ⟨f, hf⟩ := this
    use ((qExpansion 1 f).coeff ℂ 0)
    rw [← Submodule.Quotient.mk_smul, ← hf ]
    have : ⟦f⟧ = Submodule.Quotient.mk f
      (p := (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k)  ):= by rfl
    rw [this, Submodule.Quotient.eq, CuspFormSubmodule_mem_iff_coeffZero_eq_zero, qExpansion_sub,
      ← qExpansion_smul2]
    have hc := Ek_q_exp_zero k hk hk2
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_sub, PowerSeries.constantCoeff_smul,
      smul_eq_mul] at *
    rw [hc]
    ring


theorem dim_weight_two : Module.rank ℂ (ModularForm Γ(1) ↑2) = 0 := by
  rw [@rank_zero_iff_forall_zero]
  intro f
  apply weight_two_zero f

/- lemma dims_weight_lt_three_and_not_zero_Eq_zero (k : ℕ) (hk : (k : ℤ) < 3) (hk0 : k ≠ 0) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by
  by_cases hOdd : Odd k

  sorry
  simp at hOdd
  by_cases h2 : k = 2
  rw [h2]
  apply dim_weight_two
  exfalso
  simp at *
  rw [@even_iff_exists_two_mul] at hOdd
  obtain ⟨n, hn⟩ := hOdd
  rw [hn] at hk
  omega -/

lemma floor_lem1 (k a : ℚ) (ha : 0 < a) (hak : a ≤ k) :
    1 + Nat.floor ((k - a) / a) = Nat.floor (k / a) := by
  rw [div_sub_same (Ne.symm (ne_of_lt ha))]
  have := Nat.floor_sub_one (k/a)
  norm_cast at *
  rw [this]
  refine Nat.add_sub_cancel' ?_
  refine Nat.le_floor ?_
  refine (le_div_iff₀ ha).mpr ?_
  simpa using hak


lemma dim_modforms_lvl_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k)  :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction' k using Nat.strong_induction_on with k ihn
  rw [dim_modforms_eq_one_add_dim_cuspforms (k) (by omega) hk2 ,
    LinearEquiv.rank_eq (CuspForms_iso_Modforms (((k)) : ℤ))]
  by_cases HK : (3 : ℤ) ≤ (((k : ℤ) - 12))
  · have iH := ihn (k - 12) (by omega) ?_ ?_
    · have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by
        norm_cast
        refine Eq.symm (Int.subNatNat_of_le ?_)
        omega
      rw [hk12] at iH
      have : ((k - 12) : ℕ) = (k : ℚ) - 12 := by
        norm_cast
      rw [iH, this]
      by_cases h12 : 12 ∣ ((k) : ℤ) - 2
      · have h12k : 12 ∣ (k : ℤ) -12 - 2 := by
          omega
        simp only [h12k, ↓reduceIte, h12]
        have := floor_lem1 k 12 (by norm_num)
        norm_cast at *
        apply this
        omega
      · have h12k : ¬ 12 ∣ (k : ℤ) -12 - 2 := by
          omega
        simp only [h12k, ↓reduceIte, Nat.cast_add, Nat.cast_one, h12]
        have := floor_lem1 k 12 (by norm_num)
        norm_cast at *
        rw [← add_assoc, this]
        omega
    · omega
    · refine (Nat.even_sub ?_).mpr ?_
      omega
      simp only [hk2, true_iff]
      decide
  · simp only [not_le] at HK
    have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
      simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]
      omega
    have : Finset.filter Even (Finset.Icc 3 14) = ({4,6,8,10,12, 14} : Finset ℕ) := by
        decide
    rw [this] at hkop
    fin_cases hkop
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.reduceDiv, Nat.floor_zero,
      zero_add, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one]
      have h8 : -8 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.reduceDiv, Nat.floor_zero,
      zero_add, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one]
      have h8 : -6 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.reduceDiv, Nat.floor_zero,
      zero_add, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one]
      have h8 : -4 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.reduceDiv, Nat.floor_zero,
      zero_add, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one]
      have h8 : -2 < 0 := by norm_num
      rw [ModularForm.levelOne_neg_weight_rank_zero h8]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_self, Nat.floor_one, Nat.reduceAdd, Nat.cast_ite, Nat.cast_one]
      rw [ModularForm.levelOne_weight_zero_rank_one]
      norm_cast
    · simp only [Nat.cast_ofNat, Int.reduceSub, dim_weight_two, add_zero, dvd_refl, ↓reduceIte]
      norm_cast


lemma ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k)  :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (k)) = if 12 ∣ ((k) : ℤ) - 2 then
    Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  apply dim_modforms_lvl_one k hk hk2

#print axioms ModularForm.dimension_level_one


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

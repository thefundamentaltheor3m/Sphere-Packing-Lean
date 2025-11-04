import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.ModularForms.clog_arg_lems
import SpherePacking.ModularForms.eta
import Mathlib.NumberTheory.ModularForms.QExpansion
import SpherePacking.Tactic.NormNumI

import SpherePacking.ForMathlib.Cusps

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

noncomputable section Definitions

/- The discriminant form -/
def Δ (z : UpperHalfPlane) := cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

lemma DiscriminantProductFormula (z : ℍ) : Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
    simp [Δ]
    conv =>
      enter [1,1]
      ext n
      rw [show (n : ℂ) + 1 = ((n + 1) : ℕ) by simp]

    have := tprod_pnat_eq_tprod_succ (f := (fun n => (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24))
    rw [this]


lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  rw [η, Δ, mul_pow]
  congr
  · rw [← Complex.exp_nat_mul]
    congr 1
    simp [field]
  rw [tprod_pow]
  apply MultipliableEtaProductExpansion


/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Delta_eq_eta_pow]
  simpa using eta_nonzero_on_UpperHalfPlane z

/-This one is easy.-/
lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [ modular_slash_T_apply, Δ, Δ]
  simp only [coe_vadd, ofReal_one]
  have h1 : cexp (2 * ↑π * Complex.I * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * (↑z)) := by
    simpa using exp_periodo z 1
  rw [h1]
  simp only [mul_eq_mul_left_iff, Complex.exp_ne_zero, or_false]
  apply tprod_congr
  intro b
  have := exp_periodo z (b+1)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]


/-This is the hard one. -/
lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [ modular_slash_S_apply, Delta_eq_eta_pow, Delta_eq_eta_pow]
  have he := eta_equality z.2
  simp only [comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, UpperHalfPlane.coe_mk,
    Int.reduceNeg, zpow_neg] at *
  have hi : -1/(z.1 : ℂ) = (-(z : ℂ))⁻¹ := by
    rw [neg_div]
    rw [← neg_inv]
    simp [UpperHalfPlane.coe]
  rw [hi] at he
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_I]
  simp only [inv_one, one_mul, UpperHalfPlane.coe]
  rw [mul_comm]
  have hzz := csqrt_pow_24 z.1 (ne_zero z)
  rw [hzz, ← mul_assoc]
  have hz := ne_zero z
  simp only [UpperHalfPlane.coe, ne_eq] at hz
  norm_cast
  field_simp

def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' A := by
    intro hA
    exact slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant A hA


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


lemma I_in_atImInfty (A : ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty := by
  rw [atImInfty_mem]
  use A
  simp only [mem_setOf_eq, imp_self, implies_true]


instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2

theorem natPosSMul_apply (c : ℕ+) (z : ℍ) : ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := by rfl

def pnat_smul_stable (S : Set ℍ) := ∀ n : ℕ+, ∀ (s : ℍ), s ∈ S → n • s ∈ S

lemma atImInfy_pnat_mono (S : Set ℍ) (hS : S ∈ atImInfty) (B : ℝ) : ∃ A : ℝ,
    pnat_smul_stable (S ∩ {z : ℍ | max A B ≤ z.im}) ∧ S ∩ {z : ℍ | max A B ≤ z.im} ∈ atImInfty := by
  have hS2 := hS
  rw [atImInfty_mem] at hS
  obtain ⟨A, hA⟩ := hS
  use A
  constructor
  · intro n s hs
    simp only [mem_inter_iff, mem_setOf_eq] at *
    have K : max A B ≤ (n • s).im := by
      rw [UpperHalfPlane.im, natPosSMul_apply]
      simp only [mul_im, natCast_re, coe_im, natCast_im, coe_re, zero_mul, add_zero]
      have hs2 := hs.2
      simp at *
      constructor
      apply le_trans hs2.1
      have hn : (1 : ℝ) ≤ n := by
        norm_cast
        exact PNat.one_le n
      apply (le_mul_iff_one_le_left s.2).mpr hn
      apply le_trans hs2.2
      have hn : (1 : ℝ) ≤ n := by
        norm_cast
        exact PNat.one_le n
      apply (le_mul_iff_one_le_left s.2).mpr hn
    refine ⟨?_, K⟩
    simp at K
    apply hA _ K.1
  · simp only [ inter_mem_iff, hS2, true_and]
    apply I_in_atImInfty

lemma cexp_two_pi_I_im_antimono (a b : ℍ) (h : a.im ≤ b.im) (n : ℕ) :
    ‖(cexp (2 * ↑π * Complex.I * n * b))‖
    ≤ ‖(cexp (2 * ↑π * Complex.I *n * a))‖:= by
  simp_rw [Complex.norm_exp]
  simp
  gcongr

theorem tendsto_neg_cexp_atImInfty (k : ℕ) :
  Tendsto (fun x : ℍ ↦ -cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) atImInfty (𝓝 0) := by
  have := Tendsto.neg (f := (fun x : ℍ ↦ cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)))
    (l := atImInfty) (y := 0)
  simp only [neg_zero] at this
  apply this
  refine tendsto_exp_nhds_zero_iff.mpr ?_
  simp
  apply Filter.Tendsto.const_mul_atTop (by positivity)
  exact tendsto_iff_comap.mpr fun ⦃U⦄ a ↦ a

theorem log_one_neg_cexp_tendto_zero (k : ℕ) :
  Tendsto (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24))
    atImInfty (𝓝 0) := by
  have : (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24)) =
      (Complex.log) ∘ ((fun x => x ^ 24) ∘ (fun x : ℍ ↦ ((1 - cexp (2 * π * Complex.I *
      (k + 1) * x))))) := by
    ext x
    simp
  rw [this]
  apply Tendsto.comp (y := 𝓝 1)
  · nth_rw 1 [← Complex.log_one]
    refine ContinuousAt.tendsto (x := 1) (f := Complex.log) ?_
    apply continuousAt_clog
    simp
  apply Tendsto.comp (y := 𝓝 1)
  · exact (continuous_pow 24).tendsto' ( 1 : ℂ) (1 : ℂ) (by simp)
  · simp_rw [sub_eq_add_neg]
    nth_rw 3 [show (1 : ℂ) = 1 + 0 by ring]
    apply Tendsto.add
    · simp only [tendsto_const_nhds_iff]
    apply tendsto_neg_cexp_atImInfty


variable {α ι : Type*}

lemma Complex.cexp_tsum_eq_tprod_func (f : ι → α → ℂ) (hfn : ∀ x n, f n x ≠ 0)
    (hf : ∀ x : α, Summable fun n => log (f n x)) :
    (cexp ∘ (fun a : α => (∑' n : ι, log (f n a)))) = fun a : α => ∏' n : ι, f n a := by
  ext a
  apply (HasProd.tprod_eq ?_).symm
  apply ((hf a).hasSum.cexp).congr
  intro _
  congr
  exact funext fun x ↦ exp_log (hfn a x)

theorem Delta_boundedfactor :
  Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty
    (𝓝 1) := by
  have := Complex.cexp_tsum_eq_tprod_func (fun n : ℕ => fun x : ℍ => (1 - (cexp (2 * ↑π * Complex.I
    * (↑n + 1) * ↑x))) ^ 24 ) ?_ ?_
  conv =>
    enter [1]
    rw [← this]
  · apply Tendsto.comp (y := (𝓝 0))
    · exact Complex.continuous_exp.tendsto' 0 1 Complex.exp_zero
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (g := fun (x : ℕ) => (0 : ℂ))
        (f := (fun x : ℍ ↦ fun (n : ℕ) => Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑n + 1) *
          (x : ℂ))) ^ 24)))
        (bound := fun k => ‖(24 *((3/2)* cexp (2 * ↑π * Complex.I * (↑k + 1) * Complex.I)))‖)
    simp at this
    apply this
    · apply Summable.mul_left
      apply Summable.mul_left
      simpa using (summable_exp_pow UpperHalfPlane.I)
    · apply log_one_neg_cexp_tendto_zero
    · have := fun k => (tendsto_neg_cexp_atImInfty k)
      have h0 := this 0
      have h1 := clog_pow2 24 _ h0
      simp only [CharP.cast_eq_zero, zero_add, mul_one, Nat.cast_ofNat] at h1
      rw [Metric.tendsto_nhds] at h0
      have h00 := h0 (1/2) (one_half_pos)
      simp only [CharP.cast_eq_zero, zero_add, mul_one, dist_zero_right, norm_neg, one_div] at h00
      rw [Filter.eventually_iff_exists_mem ] at *
      obtain ⟨a, ha0, ha⟩ := h1
      obtain ⟨a2, ha2, ha3⟩ := h00
      have hminmem: min a a2 ∈ atImInfty := by
        simp only [inf_eq_inter, inter_mem_iff, ha0, ha2, and_self]
      have hT := atImInfy_pnat_mono (min a a2) hminmem 1
      obtain ⟨A, hA, hAmem⟩ := hT
      use (a ⊓ a2) ∩ {z | A ⊔ 1 ≤ z.im}
      refine ⟨hAmem, ?_⟩
      intro b hb k
      let K : ℕ+ := ⟨k+1, Nat.zero_lt_succ k⟩
      have haa := ha (K • b) (by have h8 := hA K b hb; simp only [inf_eq_inter, sup_le_iff,
        mem_inter_iff, mem_setOf_eq] at h8; exact h8.1.1)
      simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, K] at haa
      have := Complex.norm_log_one_add_half_le_self (z := -cexp (2 * ↑π * Complex.I * (↑k + 1) * b))
      rw [sub_eq_add_neg]
      simp_rw [← mul_assoc] at haa
      rw [haa]
      simp only [forall_exists_index, and_imp, gt_iff_lt, CharP.cast_eq_zero, zero_add, mul_one,
        dist_zero_right, norm_neg, inf_eq_inter, inter_mem_iff, sup_le_iff, mem_inter_iff,
        mem_setOf_eq, one_div, Complex.norm_mul, norm_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀,
        ge_iff_le] at *
      apply le_trans (this ?_)
      · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
        have hr := cexp_two_pi_I_im_antimono UpperHalfPlane.I b (n := k + 1) ?_
        · simpa using hr
        simp only [UpperHalfPlane.I_im, hb.2.2]
      have HH := ha3 (K • b) (by
        have h8 := hA K b hb; simp only [mem_inter_iff, mem_setOf_eq] at h8; exact h8.1.2)
      simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, ← mul_assoc, K] at HH
      exact HH.le
  · intro x n
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    apply term_ne_zero
  · intro x
    simp only
    have := log_summable_pow (fun n => -cexp (2 * ↑π * Complex.I * (↑n + 1) * x)) ?_ 24
    · apply this.congr
      intro b
      rw [sub_eq_add_neg]
    · rw [←summable_norm_iff]
      simpa using (summable_exp_pow x)

open Real

lemma Discriminant_zeroAtImInfty :
    ∀ γ ∈ 𝒮ℒ, IsZeroAtImInfty (Discriminant_SIF ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ)) := by
  intro γ ⟨γ', hγ⟩
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have := Discriminant_SIF.slash_action_eq' γ ⟨γ', CongruenceSubgroup.mem_Gamma_one γ', hγ⟩
  simp at *
  rw [this]
  simp [Discriminant_SIF]
  unfold Δ
  rw [show (0 : ℂ) = 0 * 1 by ring]
  apply Tendsto.mul
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat,
      ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im,
      mul_one, sub_self, coe_re, coe_im, zero_sub, tendsto_exp_comp_nhds_zero,
      tendsto_neg_atBot_iff]
    rw [Filter.tendsto_const_mul_atTop_iff_pos ]
    · exact two_pi_pos
    rw [atImInfty]
    exact tendsto_comap
  · apply Delta_boundedfactor

def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Discriminant_SIF
  slash_action_eq' := Discriminant_SIF.slash_action_eq'
  holo' := by
    rw [mdifferentiable_iff]
    simp only [SlashInvariantForm.coe_mk]
    have := eta_DifferentiableAt_UpperHalfPlane
    have he2 : DifferentiableOn ℂ (fun z => (η z) ^ 24) {z | 0 < z.im} := by
      apply DifferentiableOn.pow
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      exact this ⟨x, hx⟩
    rw [Discriminant_SIF]
    simp only [SlashInvariantForm.coe_mk]
    apply he2.congr
    intro z hz
    have := Delta_eq_eta_pow (⟨z, hz⟩ : ℍ)
    simp only [coe_mk_subtype, comp_apply] at *
    rw [ofComplex_apply_of_im_pos hz]
    exact this
  zero_at_cusps' hc := zero_at_cusps_of_zero_at_infty hc Discriminant_zeroAtImInfty

lemma Delta_apply (z : ℍ) : Delta z = Δ z := by rfl

lemma Delta_isTheta_rexp : Delta =Θ[atImInfty] (fun τ => Real.exp (-2 * π * τ.im)) := by
  rw [Asymptotics.IsTheta]
  refine ⟨by simpa using CuspFormClass.exp_decay_atImInfty 1 Delta, ?_⟩
  rw [Asymptotics.isBigO_iff']
  have := Delta_boundedfactor.norm
  simp only [norm_one] at this
  have h12 : (1 : ℝ) / 2 < 1 := one_half_lt_one
  have hl := Filter.Tendsto.eventually_const_le h12 this
  rw [Metric.tendsto_nhds] at *
  use 2
  refine ⟨by simp, ?_⟩
  rw [Filter.eventually_iff_exists_mem] at *
  obtain ⟨A1, hA1, hA2⟩ := hl
  use A1
  refine ⟨hA1, ?_⟩
  intro z hz
  rw [Delta_apply, Δ]
  simp only [neg_mul, Real.norm_eq_abs, Real.abs_exp, norm_mul]
  have hA3 := hA2 z hz
  conv =>
    enter [2,2,1]
    rw [Complex.norm_exp]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re,
    mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im, zero_sub]
  have hm : 0 ≤ 2 * rexp (-(2 * π * z.im)) := by
    positivity
  have h4 := mul_le_mul_of_nonneg_left hA3 hm
  conv at h4 =>
    enter [1]
    rw [mul_comm, ← mul_assoc]
    simp
  simp only [gt_iff_lt, one_div, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, ge_iff_le] at *
  rw [← mul_assoc]
  exact h4

lemma CuspForm_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
  f.toFun z = f z := by rfl

theorem div_Delta_is_SIF (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) :
    (⇑f / ⇑Delta) ∣[k - 12] γ = ⇑f / ⇑Delta := by
  simp only [Subgroup.mem_map] at hγ
  obtain ⟨γ, hA₁, hA₂⟩ := hγ
  rw [← hA₂]
  ext z
  change ((⇑f / ⇑Delta) ∣[k - 12] γ) z = (⇑f / ⇑Delta) z
  rw [ModularForm.slash_action_eq'_iff (k -12) _ γ]
  have h0 : (⇑f / ⇑Delta) z = (⇑f z / ⇑Delta z) := rfl
  have h1 : (⇑f / ⇑Delta) (γ • z) = (⇑f (γ • z) / ⇑Delta (γ • z)) := rfl
  have h2 : (f.toFun ∣[k] γ) z = f.toFun z := by
    apply congrFun
    apply f.slash_action_eq'
    exact Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hA₁
  have h3 : (Delta.toFun ∣[(12:ℤ)] γ) z = Delta.toFun z := by
    apply congrFun
    apply Delta.slash_action_eq'
    exact Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hA₁
  rw [ModularForm.slash_action_eq'_iff, CuspForm_apply, CuspForm_apply] at h2 h3
  rw [h0, h1, h2, h3, Delta_apply]
  have hD := Δ_ne_zero z
  have := pow_ne_zero 12 (denom_ne_zero γ z)
  rw [ModularGroup.denom_apply] at this
  ring_nf
  nth_rw 2 [mul_comm]
  rw [← inv_zpow, inv_zpow']
  simp_rw [← mul_assoc]
  rw [zpow_add₀ (by apply (denom_ne_zero γ z))]
  ring

def CuspForm_div_Discriminant (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) :
  ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
    toFun := f / Delta
    slash_action_eq' := by
      intro γ hγ
      exact div_Delta_is_SIF _ _ γ hγ
    holo' := by
      rw [mdifferentiable_iff]
      simp only [SlashInvariantForm.coe_mk]
      have : (⇑f / ⇑Delta) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) / (Delta ∘ ↑ofComplex) := by rfl
      rw [this]
      apply DifferentiableOn.div
      · simpa only [CuspForm.toSlashInvariantForm_coe] using
        (UpperHalfPlane.mdifferentiable_iff.mp f.holo')
      · simpa only [CuspForm.toSlashInvariantForm_coe] using
        (UpperHalfPlane.mdifferentiable_iff.mp Delta.holo')
      · intro x hx
        have := Δ_ne_zero ⟨x, hx⟩
        simp only [comp_apply, ne_eq]
        rw [ofComplex_apply_of_im_pos hx]
        apply this
    bdd_at_cusps' {c} hc := by
      apply bounded_at_cusps_of_bounded_at_infty hc
      intro A ⟨A', hA'⟩
      have h1 := CuspFormClass.exp_decay_atImInfty 1 f
      have h2 := Delta_isTheta_rexp.2
      rw [IsBoundedAtImInfty, BoundedAtFilter] at *
      rw [Asymptotics.isBigO_iff'] at h1 ⊢
      rw [Asymptotics.isBigO_iff''] at h2
      simp only [gt_iff_lt, neg_mul, Nat.cast_one, div_one, Real.norm_eq_abs,
        Real.abs_exp, Pi.one_apply, norm_one, mul_one] at *
      obtain ⟨e1, he1, hf⟩ := h1
      obtain ⟨e2, he2, hD⟩ := h2
      use e1/e2
      refine ⟨ by positivity, ?_⟩
      rw [eventually_iff_exists_mem] at *
      obtain ⟨A1, hA, hA2⟩ := hf
      obtain ⟨B2, hB2, hB3⟩ := hD
      use min A1 B2
      refine ⟨by simp [hA, hB2], ?_⟩
      intro z hz
      have : ((⇑f / ⇑Delta) ∣[k - 12] (A: GL (Fin 2) ℝ)) z = ((⇑f z / ⇑Delta z)) := by
        have := congrFun (div_Delta_is_SIF k f A'
                            (Subgroup.mem_map.mp ⟨A', CongruenceSubgroup.mem_Gamma_one A', rfl⟩)) z
        rw [← hA']
        simpa [SL_slash, Pi.div_apply] using this
      rw [this]
      simp
      have he1e2 : e1 / e2 = (e1 * rexp (-(2 * π * z.im))) / (e2 * rexp (-(2 * π * z.im))) := by
        refine Eq.symm (mul_div_mul_right e1 e2 (Real.exp_ne_zero _))
      rw [he1e2]
      apply div_le_div₀
      · positivity
      · apply hA2
        apply hz.1
      · positivity
      · apply hB3
        apply hz.2

lemma CuspForm_div_Discriminant_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k)
    (z : ℍ) : (CuspForm_div_Discriminant k f) z = f z / Δ z := rfl

theorem CuspForm_div_Discriminant_Add (k : ℤ) (x y : CuspForm (CongruenceSubgroup.Gamma 1) k) :
  (fun f ↦ CuspForm_div_Discriminant k f) (x + y) =
    (fun f ↦ CuspForm_div_Discriminant k f) x + (fun f ↦ CuspForm_div_Discriminant k f) y := by
  ext z
  simp only [CuspForm_div_Discriminant_apply, CuspForm.add_apply, ModularForm.add_apply]
  ring

lemma Delta_im_line_im_part {t : ℝ} (ht : 0 < t) : (Delta ⟨(Complex.I * t), by simp [ht]⟩ ).im =0 :=
    by
  rw [Delta_apply, Δ]
  sorry

lemma Delta_im_line {t : ℝ} (ht : 0 < t) : 0 < ‖Delta ⟨(Complex.I * t), by simp [ht]⟩‖ := by
  rw [Delta_apply, Δ, norm_mul]
  simp_rw [Complex.norm_exp]
  simp
  have (i : ℕ) : cexp (2 * ↑π * Complex.I * (↑i + 1) * (Complex.I * ↑t)) =
      cexp (-2 * ↑π * (↑i + 1) * (↑t)) := by
      congr 1
      linear_combination π * (i + 1) * 2 * t * I_sq
  conv =>
    enter [2,2,1,1]
    intro i
    rw [this i]
    rw [sub_eq_add_neg]
  apply mul_pos
  · exact exp_pos (-(2 * π * t))
  have H := Complex.cexp_tsum_eq_tprod (f := fun (i : ℕ) => (1 + -cexp (-2 * ↑π * (↑i + 1) *
    ↑t))^24) ?_ ?_
  · rw [← H]
    simp
  · intro i
    simp
    norm_cast
    have := Real.exp_lt_one_iff (x := -(2 * π * (i + 1) * t)).2 ?_
    · rw [← sub_eq_add_neg]
      rw [@sub_eq_zero]
      intro h
      norm_cast at *
      rw [← h] at this
      exact (lt_self_iff_false 1).mp this
    simp
    positivity

  · simp_rw [← sub_eq_add_neg]
    norm_cast

    sorry

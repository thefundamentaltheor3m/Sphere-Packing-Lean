module

public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.ClogArgLemmas
public import SpherePacking.ModularForms.Eta
public import SpherePacking.ModularForms.MultipliableLemmas
public import SpherePacking.ModularForms.ResToImagAxis
import Mathlib.NumberTheory.ModularForms.QExpansion
import SpherePacking.Tactic.NormNumI

public import SpherePacking.ForMathlib.Cusps

@[expose] public section

/-!
# Discriminant Product Formula

This file proves results such as `DiscriminantProductFormula`, `Delta_eq_eta_pow`,
`Discriminant_T_invariant`, `Discriminant_S_invariant`, `I_in_atImInfty`.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

noncomputable section Definitions

/- The discriminant form -/
def Δ (z : UpperHalfPlane) := cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

/-- Reindex `Δ` from a product over `ℕ` to a product over `ℕ+`. -/
lemma DiscriminantProductFormula (z : ℍ) :
    Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
  simpa [Δ, Nat.cast_add, Nat.cast_one, add_mul] using
    (tprod_pnat_eq_tprod_succ (f := fun n : ℕ =>
      (1 - cexp (2 * π * Complex.I * (n : ℂ) * z)) ^ 24)).symm

/-- The discriminant form is the 24th power of the Dedekind eta function. -/
lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  have hm : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n z) := by
    refine (MultipliableEtaProductExpansion z).congr ?_
    intro n
    simp [ModularForm.eta_q_eq_cexp]
  rw [η, ModularForm.eta, Δ, mul_pow, tprod_pow (f := fun n : ℕ => 1 - ModularForm.eta_q n z)
    hm 24]
  congr
  · rw [Periodic.qParam]
    rw [← Complex.exp_nat_mul]
    congr 1
    simp [field]
  · ext n
    simp [ModularForm.eta_q_eq_cexp]

/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Delta_eq_eta_pow]
  simpa [η] using (ModularForm.eta_ne_zero (z := (z : ℂ)) z.2)

/-- Invariance of `Δ` under the translation `T : z ↦ z + 1`. -/
public lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [ modular_slash_T_apply, Δ, Δ]
  simp only [coe_vadd, ofReal_one]
  congr 1
  · simpa using exp_periodo z 1
  · refine tprod_congr fun b => ?_
    simpa [Nat.cast_add, Nat.cast_one] using
      congrArg (fun t => (1 - t) ^ (24 : ℕ)) (exp_periodo z (b + 1))


/-- Invariance of `Δ` under the inversion `S : z ↦ -1/z`. -/
public lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [modular_slash_S_apply, Delta_eq_eta_pow, Delta_eq_eta_pow]
  have he : η ((-z : ℂ)⁻¹) = (csqrt Complex.I)⁻¹ * (csqrt (z : ℂ) * η (z : ℂ)) := by
    simpa [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, div_eq_mul_inv] using
      (eta_equality z.2)
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  rw [he]
  simp [mul_pow, inv_pow, csqrt_I, csqrt_pow_24 (z := (z : ℂ)) hz, zpow_neg]
  field_simp [hz]

/-- Δ as a SlashInvariantForm of weight 12 -/
@[expose] public def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' :=
    slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant

/-- Δ is 1-periodic: Δ(z + 1) = Δ(z) -/
public lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z :=
  by simpa using SlashInvariantForm.vAdd_width_periodic 1 12 1 Discriminant_SIF z

/-- Δ transforms under S as: Δ(-1/z) = z¹² · Δ(z) -/
public lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := congrFun Discriminant_S_invariant z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  rw [h, mul_comm]

lemma I_in_atImInfty (A : ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty := by
  rw [atImInfty_mem]
  exact ⟨A, fun _ hz ↦ hz⟩


/-- Scalar multiplication of `ℍ` by a positive natural number. -/
public instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by
    have hx : 0 < (x : ℝ) := by exact_mod_cast x.pos
    simpa [mul_im] using mul_pos hx z.2

/-- Coercion formula for the `ℕ+`-scalar action on `ℍ`. -/
public theorem natPosSMul_apply (c : ℕ+) (z : ℍ) :
    ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := rfl

/-- A set `S ⊆ ℍ` is stable under scaling by positive naturals. -/
@[expose] public def pnat_smul_stable (S : Set ℍ) :=
    ∀ n : ℕ+, ∀ (s : ℍ), s ∈ S → n • s ∈ S

/-- Inside `atImInfty`, shrink to a subset stable under positive-integer scaling. -/
public lemma atImInfy_pnat_mono (S : Set ℍ) (hS : S ∈ atImInfty) (B : ℝ) :
    ∃ A : ℝ,
      pnat_smul_stable (S ∩ {z : ℍ | max A B ≤ z.im}) ∧
        S ∩ {z : ℍ | max A B ≤ z.im} ∈ atImInfty := by
  have hS2 := hS
  rw [atImInfty_mem] at hS
  obtain ⟨A, hA⟩ := hS
  use A
  constructor
  · intro n s hs
    rcases hs with ⟨hsS, hsIm⟩
    have hsIm' : A ≤ s.im ∧ B ≤ s.im := by
      simpa [max_le_iff] using hsIm
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (PNat.one_le n)
    have hmul : s.im ≤ (n : ℝ) * s.im := (le_mul_iff_one_le_left s.2).2 hn
    have K : max A B ≤ (n • s).im := by
      rw [UpperHalfPlane.im, natPosSMul_apply]
      simp only [mul_im, natCast_re, coe_im, natCast_im, coe_re, zero_mul, add_zero]
      exact (max_le_iff.2 ⟨le_trans hsIm'.1 hmul, le_trans hsIm'.2 hmul⟩)
    exact ⟨hA _ (le_trans (le_max_left A B) K), K⟩
  · exact Filter.inter_mem hS2 (I_in_atImInfty (A := max A B))

/-!
## Helper lemmas (kept modular)

These are intentionally kept as named `private` lemmas rather than being inlined inside the main
asymptotic/imag-axis proofs. Inlining them saves little (if any) code, but it hurts readability and
reusability.
-/

private lemma cexp_two_pi_I_im_antimono (a b : ℍ) (h : a.im ≤ b.im) (n : ℕ) :
    ‖cexp (2 * ↑π * Complex.I * n * b)‖ ≤ ‖cexp (2 * ↑π * Complex.I * n * a)‖ := by
  simp only [mul_right_comm, norm_exp, mul_re, re_ofNat, Complex.I_re, mul_zero, im_ofNat,
    Complex.I_im, mul_one, sub_self, coe_re, zero_mul, mul_im, add_zero, coe_im, zero_sub,
    ofReal_re, neg_mul, zero_add, ofReal_im, sub_zero, natCast_re, natCast_im, Real.exp_le_exp,
    neg_le_neg_iff]
  gcongr

private lemma tendsto_neg_cexp_atImInfty (k : ℕ) :
    Tendsto (fun x : ℍ ↦ -cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) atImInfty (𝓝 0) := by
  simpa using
    (tendsto_exp_nhds_zero_iff.mpr
        (by
          simpa [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re,
            mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, add_re, natCast_re, one_re,
            add_im, natCast_im, one_im, coe_re, zero_add, coe_im, zero_sub, tendsto_neg_atBot_iff,
            mul_assoc, mul_left_comm, mul_comm] using
            (tendsto_im_atImInfty.const_mul_atTop
              (by positivity : 0 < (2 * π * ((k : ℝ) + 1)))))).neg

private lemma log_one_neg_cexp_tendto_zero (k : ℕ) :
    Tendsto (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24))
      atImInfty (𝓝 0) := by
  have hpow :
      Tendsto (fun x : ℍ ↦ (1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24) atImInfty
        (𝓝 (1 : ℂ)) := by
    have hsub :
        Tendsto (fun x : ℍ ↦ (1 : ℂ) - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) atImInfty
          (𝓝 (1 : ℂ)) := by
      simpa [sub_eq_add_neg] using (tendsto_const_nhds.add (tendsto_neg_cexp_atImInfty k))
    simpa using (hsub.pow 24)
  have hclog :
      Tendsto Complex.log (𝓝 (1 : ℂ)) (𝓝 0) := by
    simpa [Complex.log_one] using (continuousAt_clog (x := (1 : ℂ)) one_mem_slitPlane).tendsto
  exact hclog.comp hpow

variable {α ι : Type*}

lemma Complex.cexp_tsum_eq_tprod_func (f : ι → α → ℂ) (hfn : ∀ x n, f n x ≠ 0)
    (hf : ∀ x : α, Summable fun n => log (f n x)) :
    (cexp ∘ (fun a : α => (∑' n : ι, log (f n a)))) = fun a : α => ∏' n : ι, f n a := by
  funext a
  simpa [Function.comp] using
    (Complex.cexp_tsum_eq_tprod (f := fun n : ι => f n a) (hfn a) (hf a))

/-- The bounded factor in the discriminant product tends to `1` at `Im z → ∞`. -/
public theorem Delta_boundedfactor :
  Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty
    (𝓝 1) := by
  let f : ℕ → ℍ → ℂ :=
    fun (n : ℕ) (x : ℍ) => (1 - (cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x))) ^ 24
  have hfn : ∀ x n, f n x ≠ 0 := by
    intro x n
    simp [f, pow_eq_zero_iff]
    simpa using term_ne_zero x n
  have hf : ∀ x : ℍ, Summable fun n : ℕ => log (f n x) := by
    intro x
    simp only [f]
    have h := log_summable_pow (fun n => -cexp (2 * ↑π * Complex.I * (↑n + 1) * x)) ?_ 24
    · refine h.congr ?_
      intro b
      rw [sub_eq_add_neg]
    · rw [← summable_norm_iff]
      simpa using (summable_exp_pow x)
  have hcexp :
      (cexp ∘ fun a : ℍ => ∑' n : ℕ, log (f n a)) = fun a : ℍ => ∏' n : ℕ, f n a :=
    Complex.cexp_tsum_eq_tprod_func (f := f) hfn hf
  have ht : Tendsto (cexp ∘ fun x : ℍ => ∑' n : ℕ, log (f n x)) atImInfty (𝓝 1) := by
    apply Tendsto.comp (y := 𝓝 0)
    · exact Complex.continuous_exp.tendsto' 0 1 Complex.exp_zero
    have hsum :
        Tendsto (fun x : ℍ ↦ ∑' n : ℕ, log (f n x)) atImInfty (𝓝 (∑' _ : ℕ, (0 : ℂ))) := by
      refine
        tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (g := fun _ : ℕ => (0 : ℂ))
          (f := fun x : ℍ ↦ fun n : ℕ => log (f n x))
          (bound := fun k =>
            ‖(24 * ((3 / 2) * cexp (2 * ↑π * Complex.I * (↑k + 1) * Complex.I)))‖) ?_ ?_ ?_
      · simp_rw [norm_mul, mul_assoc]
        apply Summable.mul_left
        apply Summable.mul_left
        simpa [mul_assoc] using summable_exp_pow UpperHalfPlane.I
      · intro k
        simpa only [f] using log_one_neg_cexp_tendto_zero k
      · have hneg := tendsto_neg_cexp_atImInfty
        have h0 := hneg 0
        have h1 := clog_pow2 24 _ h0
        simp only [CharP.cast_eq_zero, zero_add, mul_one, Nat.cast_ofNat] at h1
        rw [Metric.tendsto_nhds] at h0
        have h00 := h0 (1/2) (one_half_pos)
        simp only [CharP.cast_eq_zero, zero_add, mul_one, dist_zero_right, norm_neg, one_div] at h00
        rw [Filter.eventually_iff_exists_mem] at *
        obtain ⟨a, ha0, ha⟩ := h1
        obtain ⟨a2, ha2, ha3⟩ := h00
        have hminmem : min a a2 ∈ atImInfty := by
          simp only [inf_eq_inter, inter_mem_iff, ha0, ha2, and_self]
        have hT := atImInfy_pnat_mono (min a a2) hminmem 1
        obtain ⟨A, hA, hAmem⟩ := hT
        use (a ⊓ a2) ∩ {z | A ⊔ 1 ≤ z.im}
        refine ⟨hAmem, ?_⟩
        intro b hb k
        simp only [f]
        let K : ℕ+ := ⟨k+1, Nat.zero_lt_succ k⟩
        have haa := ha (K • b) (by
          have h8 := hA K b hb
          simp only [inf_eq_inter, sup_le_iff, mem_inter_iff, mem_setOf_eq] at h8
          exact h8.1.1)
        simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, K] at haa
        have hlog :=
          Complex.norm_log_one_add_half_le_self (z := -cexp (2 * ↑π * Complex.I * (↑k + 1) * b))
        rw [sub_eq_add_neg]
        simp_rw [← mul_assoc] at haa
        rw [haa]
        simp only [gt_iff_lt, CharP.cast_eq_zero, zero_add, mul_one,
          dist_zero_right, norm_neg, inf_eq_inter, inter_mem_iff, sup_le_iff, mem_inter_iff,
          mem_setOf_eq, one_div, Complex.norm_mul, norm_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀,
          ge_iff_le] at *
        have HH := ha3 (K • b) (by
          have h8 := hA K b hb
          simp only [mem_inter_iff, mem_setOf_eq] at h8
          exact h8.1.2)
        simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, ← mul_assoc, K] at HH
        refine le_trans (hlog HH.le) ?_
        have hr := cexp_two_pi_I_im_antimono UpperHalfPlane.I b (n := k + 1) ?_
        · simpa using hr
        · simpa [UpperHalfPlane.I_im] using hb.2.2
    simpa [tsum_zero] using hsum
  exact (tendsto_congr (congrFun hcexp)).mp ht

/-- The discriminant has a zero at the cusp `∞` after any `SL(2,ℤ)` slash action. -/
public lemma Discriminant_zeroAtImInfty :
    ∀ γ ∈ 𝒮ℒ, IsZeroAtImInfty (Discriminant_SIF ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ)) := by
  intro γ ⟨γ', hγ⟩
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have hslash' : (⇑Discriminant_SIF ∣[(12 : ℤ)] γ) = ⇑Discriminant_SIF := by
    simpa [SlashInvariantForm.toFun_eq_coe] using
      Discriminant_SIF.slash_action_eq' γ ⟨γ', CongruenceSubgroup.mem_Gamma_one γ', hγ⟩
  rw [hslash']
  simp only [Discriminant_SIF, SlashInvariantForm.coe_mk]
  unfold Δ
  rw [show (0 : ℂ) = 0 * 1 by ring]
  apply Tendsto.mul
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat,
      ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im,
      mul_one, sub_self, coe_re, coe_im, zero_sub, Real.tendsto_exp_comp_nhds_zero,
      tendsto_neg_atBot_iff]
    rw [Filter.tendsto_const_mul_atTop_iff_pos ]
    · exact Real.two_pi_pos
    rw [atImInfty]
    exact tendsto_comap
  · apply Delta_boundedfactor

/-- The discriminant cusp form of weight `12` on `Γ(1)`. -/
def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Discriminant_SIF
  slash_action_eq' := Discriminant_SIF.slash_action_eq'
  holo' := by
    rw [mdifferentiable_iff]
    simp only [SlashInvariantForm.coe_mk]
    have he2 : DifferentiableOn ℂ (fun z => (η z) ^ 24) {z | 0 < z.im} := by
      apply DifferentiableOn.pow
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      simpa [η] using (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx)
    rw [Discriminant_SIF]
    simp only [SlashInvariantForm.coe_mk]
    apply he2.congr
    intro z hz
    have := Delta_eq_eta_pow (⟨z, hz⟩ : ℍ)
    simp only [comp_apply] at *
    rw [ofComplex_apply_of_im_pos hz]
    exact this
  zero_at_cusps' hc := zero_at_cusps_of_zero_at_infty hc Discriminant_zeroAtImInfty

/-- Unfolding lemma for `Delta`. -/
public lemma Delta_apply (z : ℍ) : Delta z = Δ z := rfl

/-- The discriminant cusp form is nonzero. -/
public lemma Delta_ne_zero : Delta ≠ 0 := by
  refine (DFunLike.ne_iff).2 ⟨UpperHalfPlane.I, ?_⟩
  simpa [Delta_apply] using Δ_ne_zero UpperHalfPlane.I

/-- The discriminant cusp form is `Theta`-equivalent to `exp (-2π Im z)` at `Im z → ∞`. -/
public lemma Delta_isTheta_rexp : Delta =Θ[atImInfty] (fun τ => Real.exp (-2 * π * τ.im)) := by
  rw [Asymptotics.IsTheta]
  refine ⟨by simpa using CuspFormClass.exp_decay_atImInfty (h := 1) Delta, ?_⟩
  let g : ℍ → ℂ :=
    fun z : ℍ => ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24
  have ht : Tendsto (fun z : ℍ => ‖g z‖) atImInfty (𝓝 (1 : ℝ)) := by
    simpa [g] using Delta_boundedfactor.norm
  have hl : ∀ᶠ z : ℍ in atImInfty, (1 : ℝ) / 2 ≤ ‖g z‖ := by
    have hlt : ∀ᶠ x in 𝓝 (1 : ℝ), (1 : ℝ) / 2 < x :=
      Ioi_mem_nhds (by linarith : (1 : ℝ) / 2 < 1)
    exact (ht.eventually hlt).mono fun _ hx => le_of_lt hx
  refine Asymptotics.IsBigO.of_bound (2 : ℝ) ?_
  filter_upwards [hl] with z hz
  have hExp : ‖cexp (2 * π * Complex.I * (z : ℂ))‖ = Real.exp (-2 * π * z.im) := by
    simp [Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm]
  have hnonneg : 0 ≤ Real.exp (-2 * π * z.im) := le_of_lt (Real.exp_pos _)
  have h2 : Real.exp (-2 * π * z.im) ≤ 2 * (Real.exp (-2 * π * z.im) * ‖g z‖) := by
    have h1 : (1 : ℝ) ≤ 2 * ‖g z‖ := by
      nlinarith [hz]
    have := mul_le_mul_of_nonneg_left h1 hnonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  calc
    ‖Real.exp (-2 * π * z.im)‖ = Real.exp (-2 * π * z.im) := by
      simp
    _ ≤ 2 * (Real.exp (-2 * π * z.im) * ‖g z‖) := h2
    _ = 2 * (‖cexp (2 * π * Complex.I * (z : ℂ))‖ * ‖g z‖) :=
      congrArg (fun t => 2 * (t * ‖g z‖)) hExp.symm
    _ = 2 * ‖cexp (2 * π * Complex.I * (z : ℂ)) * g z‖ := by
      simp [mul_comm]
    _ = 2 * ‖Delta z‖ := by
      simp [Delta_apply, Δ, g, mul_left_comm, mul_comm]

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

/-- Division by the discriminant, viewed as a map `CuspForm Γ(1) k → ModularForm Γ(1) (k - 12)`. -/
@[expose] public def CuspForm_div_Discriminant (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma 1) k) :
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
      have h1 := CuspFormClass.exp_decay_atImInfty (h := 1) f zero_lt_one (by simp)
      have h2 := Delta_isTheta_rexp.2
      rw [IsBoundedAtImInfty, BoundedAtFilter] at *
      rw [Asymptotics.isBigO_iff'] at h1 ⊢
      rw [Asymptotics.isBigO_iff''] at h2
      simp only [gt_iff_lt, neg_mul, div_one, Real.norm_eq_abs,
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

/-- Pointwise evaluation of `CuspForm_div_Discriminant`. -/
public lemma CuspForm_div_Discriminant_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k)
    (z : ℍ) : (CuspForm_div_Discriminant k f) z = f z / Δ z := rfl

/-- The map `CuspForm_div_Discriminant k` is additive. -/
public theorem CuspForm_div_Discriminant_Add (k : ℤ)
    (x y : CuspForm (CongruenceSubgroup.Gamma 1) k) :
    CuspForm_div_Discriminant k (x + y) =
      CuspForm_div_Discriminant k x + CuspForm_div_Discriminant k y := by
  ext z
  simp [CuspForm_div_Discriminant_apply, add_div]

lemma cexp_aux1 (t : ℝ) : cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
  calc
    _ = cexp (2 * ↑π * (Complex.I * Complex.I) * t) := by ring_nf
    _ = rexp (-2 * π * t) := by simp

lemma cexp_aux2 (t : ℝ) (n : ℕ)
    : cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) := by
  calc
    _ = cexp (2 * ↑π * (n + 1) * (Complex.I * Complex.I) * t) := by ring_nf
    _ = rexp (-(2 * π * (n + 1) * t)) := by simp

lemma cexp_aux4 (t : ℝ) (n : ℕ) : (cexp (-2 * π * (n + 1) * t)).im = 0 := by
  simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-2 * π * (n + 1) * t)

/-- If `Im z = 0` then `Im (z^m) = 0`. -/
public lemma Complex.im_pow_eq_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) (m : ℕ) :
    (z ^ m).im = 0 :=
  (Complex.im_eq_zero_iff_isSelfAdjoint _).2 <|
    IsSelfAdjoint.pow ((Complex.im_eq_zero_iff_isSelfAdjoint z).1 hz) m

private lemma Complex_im_finset_prod_eq_zero_of_im_eq_zero (s : Finset ℕ) (f : ℕ → ℂ)
    (h : ∀ i ∈ s, (f i).im = 0) : (∏ i ∈ s, f i).im = 0 := by
  refine (Complex.im_eq_zero_iff_isSelfAdjoint _).2 ?_
  revert h
  refine Finset.induction_on s (by intro; simp) ?_
  intro a s ha ih h
  simpa [Finset.prod_insert, ha] using
    IsSelfAdjoint.mul
      ((Complex.im_eq_zero_iff_isSelfAdjoint (f a)).1 (h a (by simp [ha])))
      (ih (fun i hi => h i (by simp [hi])))

private lemma Complex_im_tprod_eq_zero_of_im_eq_zero (f : ℕ → ℂ) (hf : Multipliable f)
    (him : ∀ n, (f n).im = 0) : (∏' n : ℕ, f n).im = 0 := by
  have hz : ∀ n, (∏ i ∈ Finset.range n, f i).im = 0 := fun n =>
    Complex_im_finset_prod_eq_zero_of_im_eq_zero (s := Finset.range n) (f := f)
      (by intro i _; simpa using him i)
  have h2 : Tendsto (fun n => (∏ i ∈ Finset.range n, f i).im) atTop (𝓝 (0 : ℝ)) := by simp [hz]
  exact tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hf.hasProd.tendsto_prod_nat) h2

/-- `Δ (i t)` is real for `t > 0`. -/
public lemma Delta_imag_axis_real : ResToImagAxis.Real Δ := by
  intro t ht
  have cexp_aux4 (t : ℝ) (n : ℕ) : (cexp (-2 * π * (n + 1) * t)).im = 0 := by
    simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-2 * π * (n + 1) * t)
  simp only [resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, Δ, mul_im]
  set g : ℕ → ℂ := fun n => (1 - cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t))) ^ 24
  have hArg (n : ℕ) :
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t) = -(2 * (π : ℂ) * (n + 1) * t) := by
    calc
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t)
        = 2 * (π : ℂ) * (Complex.I * Complex.I) * (n + 1) * t := by ring
      _ = -(2 * (π : ℂ) * (n + 1) * t) := by simp
  have him_g : ∀ n, (g n).im = 0 := fun n => by
    have : (cexp (-(2 * (π : ℂ) * ((n + 1) : ℂ) * t))).im = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (cexp_aux4 t n)
    have : ((1 - cexp (2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t))) : ℂ).im = 0 := by
      simpa [Complex.sub_im, hArg n] using this
    simpa [g] using Complex.im_pow_eq_zero_of_im_eq_zero this 24
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hmul : Multipliable g := by
    have hz : (z : ℂ) = Complex.I * t := rfl
    simpa [g, hz] using
      (Multipliable_pow _ (by simpa using MultipliableEtaProductExpansion z) 24)
  have htprod_im : (∏' n : ℕ, g n).im = 0 :=
    Complex_im_tprod_eq_zero_of_im_eq_zero g hmul him_g
  have him_pref : (cexp (2 * π * Complex.I * (Complex.I * t))).im = 0 := by
    have : (cexp (-(2 * π * t))).im = 0 := by
      simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-(2 * π * t))
    simpa [by simpa using hArg 0] using this
  simp [g, him_pref, htprod_im]

/-- Real-part formula for `Δ (i t)` on the imaginary axis, rewritten as a real infinite product. -/
public lemma re_ResToImagAxis_Delta_eq_real_prod (t : ℝ) (ht : 0 < t) :
  (Δ.resToImagAxis t).re =
    Real.exp (-2 * π * t) *
      ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  have cexp_aux2 (t : ℝ) (n : ℕ) :
      cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) :=
    cexp_aux2 t n
  have cexp_aux1 (t : ℝ) : cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
    simpa using (cexp_aux2 t 0)
  set fR : ℕ → ℝ := fun n => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24
  have hMap' :
      Complex.ofReal (∏' n : ℕ, fR n) = ∏' n : ℕ, ((fR n : ℝ) : ℂ) := by
    simpa using
      (Function.LeftInverse.map_tprod (f := fR)
        (g := Complex.ofRealHom.toMonoidHom)
        (hg := by simpa using Complex.continuous_ofReal)
        (hg' := Complex.continuous_re)
        (hgg' := by intro x; simp))
  simpa [ResToImagAxis, ht, Delta_apply, Δ, cexp_aux1, cexp_aux2, hMap', fR] using
    Complex.ofReal_re (Real.exp (-2 * π * t) * ∏' n : ℕ, fR n)

private lemma Delta_tprod_pos_nat_im (z : ℍ) :
    0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := by
  have hpos_pow :
      ∀ n : ℕ, 0 < (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := fun n =>
        pow_pos (sub_pos.2 ((Real.exp_lt_one_iff).2 (neg_lt_zero.2 (by positivity)))) _
  have hsum_log :
      Summable (fun n : ℕ => Real.log ((1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24)) := by
    simp only [Real.log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    apply Summable.const_smul
    apply Real.summable_log_one_add_of_summable
    apply Summable.neg
    have h0 : Summable (fun n : ℕ => Real.exp (n * (-(2 * π * z.im)))) :=
      (Real.summable_exp_nat_mul_iff.mpr
        (by
          simpa using (neg_lt_zero.mpr (by positivity : 0 < 2 * π * z.im))))
    simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
      ((summable_nat_add_iff 1).2 h0)
  rw [← Real.rexp_tsum_eq_tprod
        (f := fun n : ℕ => (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24)
        hpos_pow hsum_log]
  exact Real.exp_pos _

/-- `Δ (i t)` is positive for `t > 0`. -/
public lemma Delta_imag_axis_pos : ResToImagAxis.Pos Δ := by
  rw [ResToImagAxis.Pos]
  refine And.intro Delta_imag_axis_real ?_
  intro t ht
  have hprod :
      0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
    simpa [UpperHalfPlane.im] using
      (Delta_tprod_pos_nat_im (z := ⟨Complex.I * t, by simp [ht]⟩))
  rw [re_ResToImagAxis_Delta_eq_real_prod t ht]
  exact mul_pos (Real.exp_pos _) hprod

end Definitions

import Mathlib
import SpherePacking.ModularForms.exp_lems
import SpherePacking.ModularForms.multipliable_lems
import SpherePacking.ModularForms.logDeriv_lems
import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.csqrt
import SpherePacking.ModularForms.uniformcts

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

local notation "𝕢" => Periodic.qParam

noncomputable abbrev eta_q (n : ℕ) (z : ℂ) :=  - (𝕢 1 z) ^ (n + 1)

lemma eta_q_eq_exp (n : ℕ) (z : ℂ) : eta_q n z = -cexp (2 * π * Complex.I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : eta_q n z = -cexp (2 * π * Complex.I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

lemma one_add_eta_q_ne_zero (n : ℕ) (z : ℍ) : 1 + eta_q n z ≠ 0 := by
  rw [eta_q_eq_exp, ← sub_eq_add_neg, sub_ne_zero]
  intro h
  have := exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp only [norm_one, lt_self_iff_false] at *

noncomputable abbrev eta_prod_term (z : ℂ) := ∏' (n : ℕ), (1 + eta_q n z)

local notation "ηₚ" => eta_prod_term

/- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
noncomputable def ModularForm.eta (z : ℂ) := (𝕢 24 z) * ηₚ z

local notation "η" => ModularForm.eta

/-this is being PRd-/
lemma prod_tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → (‖(f n x)‖) ≤ u n)
    (hfn : ∀ x : K, ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
    apply tendstoUniformlyOn_tprod' hK hu h hfn hcts

theorem Summable_eta_q (z : ℍ) : Summable fun n : ℕ ↦ ‖eta_q n z‖ := by
    simp_rw  [eta_q, eta_q_eq_pow, norm_neg, norm_pow, summable_nat_add_iff 1]
    simp only [summable_geometric_iff_norm_lt_one, norm_norm]
    apply exp_upperHalfPlane_lt_one z

lemma eta_tndntunif : TendstoLocallyUniformlyOn
    (fun n a ↦ ∏ i ∈ Finset.range n, (1 + eta_q i a)) ηₚ atTop {x | 0 < x.im} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    ((isOpen_lt continuous_const Complex.continuous_im))]
  intro K hK hK2
  by_cases hN : ¬ Nonempty K
  · simpa [not_nonempty_iff_eq_empty'.mp hN] using tendstoUniformlyOn_empty
  · have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by fun_prop
    obtain ⟨z, hz, hB, HB⟩ := IsCompact.exists_sSup_image_eq_and_ge hK2 (by simpa using hN) hc
    refine prod_tendstoUniformlyOn_tprod' hK2 (Summable_eta_q ⟨z, by simpa using (hK hz)⟩)
      (f := eta_q) ?_ ?_ (by simp_rw [eta_q_eq_pow]; fun_prop)
    · intro n x hx
      simpa only [eta_q, eta_q_eq_pow n x, norm_neg, norm_pow, coe_mk_subtype,
        eta_q_eq_pow n (⟨z, hK hz⟩ : ℍ)] using
        pow_le_pow_left₀ (by simp [norm_nonneg]) (HB x hx) (n + 1)
    · refine fun x k => one_add_eta_q_ne_zero k ⟨x, hK x.2⟩

lemma tprod_ne_zero' {ι α : Type*} (x : α) (f : ι → α → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : α, Summable fun n => f n x) : (∏' i : ι, (1 + f i) x) ≠ 0 := by
  simp only [Pi.add_apply, Pi.one_apply, ne_eq]
  rw [← Complex.cexp_tsum_eq_tprod (f := fun n => 1 + f n x) (fun n => hf n x)]
  · simp only [comp_apply, exp_ne_zero, not_false_eq_true]
  · exact Complex.summable_log_one_add_of_summable (hu x)

theorem eta_prod_term_ne_zero (z : ℍ) : ηₚ z ≠ 0 := by
  simp only [eta_prod_term, eta_q, ne_eq]
  refine tprod_ne_zero' z (fun (n : ℕ) (x : ℍ) => eta_q n x) ?_ ?_
  · refine fun i x => by simpa using one_add_eta_q_ne_zero i x
  · intro x
    rw [←summable_norm_iff]
    simpa [eta_q] using Summable_eta_q x

/--Eta is non-vanishing!-/
lemma eta_nonzero_on_UpperHalfPlane (z : ℍ) : η z ≠ 0 := by
  rw [ModularForm.eta, Periodic.qParam]
  simpa using eta_prod_term_ne_zero z

/- lemma differentiable_q (n : ℝ) : Differentiable ℂ (𝕢 n) := by
    rw [show 𝕢 n = fun x => exp (2 * π * Complex.I * x / n)  by rfl]
    fun_prop

lemma differentiable_eta_q (n : ℕ) : Differentiable ℂ (eta_q n) := by
  rw [show eta_q n = fun x => -exp (2 * π * Complex.I * x) ^ (n + 1) by
      ext z; exact eta_q_eq_pow n z]
  fun_prop -/

lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  simp [logDeriv]

lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_exp]
  ring

lemma tsum_log_deriv_eta_q (z : ℂ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 + eta_q i x) z =
  ∑' n : ℕ, (2 * ↑π * Complex.I * (n + 1)) * (eta_q n z) / (1  + eta_q n z) := by
  refine tsum_congr (fun i => ?_)
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by aesop
  have h3 : deriv (fun x : ℂ ↦ (2 * π * Complex.I * (i + 1) * x)) =
        fun _ ↦ 2 * π * Complex.I * (i + 1) := by
      ext y
      simpa using deriv_const_mul (2 * π * Complex.I * (i + 1)) (d := fun (x : ℂ) => x) (x := y)
  simp_rw [eta_q_eq_exp, ← sub_eq_add_neg, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * Complex.I * (i + 1) * x)) (by fun_prop), h3]
  simp

lemma tsum_log_deriv_eqn (z : ℍ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ↑z  =
    ∑' n : ℕ, -(2 * ↑π * Complex.I * (↑n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) := by
  congr
  ext i
  have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
  have h1 := fun i : ℕ => logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
  have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
  have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_mul]
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
        deriv_add, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_id']
  rw [h2 i, h1 i, h3 i]
  simp

lemma logDeriv_q (n : ℝ) (z : ℂ) : logDeriv (𝕢 n) z = 2 * ↑π * Complex.I / n := by
  have : (𝕢 n) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / n) * z)  := by
    ext y
    simp only [Periodic.qParam, ofReal_ofNat, comp_apply]
    ring_nf
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop)]
  simp only [LogDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]

lemma logDeriv_z_term (z : ℍ) : logDeriv (𝕢 24) ↑z  =  2 * ↑π * Complex.I / 24 := by
  have : (𝕢 24) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z)  := by
    ext y
    simp only [Periodic.qParam, ofReal_ofNat, comp_apply]
    ring_nf
  rw [this, logDeriv_comp, deriv_const_mul]
  simp only [LogDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]
  · fun_prop
  · fun_prop
  · fun_prop

theorem eta_differentiableAt (z : ℍ) : DifferentiableAt ℂ ηₚ ↑z := by
  have hD := eta_tndntunif.differentiableOn ?_ (isOpen_lt continuous_const Complex.continuous_im)
  · rw [DifferentiableOn] at hD
    apply (hD z (by apply z.2)).differentiableAt
    · apply IsOpen.mem_nhds  (isOpen_lt continuous_const Complex.continuous_im)
      apply z.2
  · filter_upwards with b y
    apply (DifferentiableOn.finset_prod (u := Finset.range b)
      (f := fun i x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
      (by fun_prop)).congr
    intro x hx
    simp [sub_eq_add_neg, eta_q_eq_exp]

lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ eta z := by
  apply DifferentiableAt.mul
  · conv =>
      enter [2]
      rw [show (𝕢 24) = cexp ∘ (fun z => 2 * ↑π * Complex.I * z / 24) by rfl]
    apply DifferentiableAt.cexp
    fun_prop
  · apply eta_differentiableAt

lemma eta_logDeriv (z : ℍ) : logDeriv ModularForm.eta z = (π * Complex.I / 12) * E₂ z := by
  unfold ModularForm.eta
  unfold eta_prod_term
  rw [logDeriv_mul]
  have HG := logDeriv_tprod_eq_tsum (s := {x : ℂ | 0 < x.im}) ?_ z
    (fun (n : ℕ) => fun (x : ℂ) => 1 - cexp (2 * π * Complex.I * (n + 1) * x)) ?_ ?_ ?_ ?_ ?_
  simp only [mem_setOf_eq, UpperHalfPlane.coe] at *
  conv =>
    enter [1,2,1]
    intro z
    conv =>
    enter [1]
    intro n
    rw [eta_q_eq_exp, ← sub_eq_add_neg]
  rw [HG]
  · have := tsum_log_deriv_eqn z
    have h0 := logDeriv_z_term z
    simp only [UpperHalfPlane.coe] at *
    rw [this, E₂, h0]
    simp
    rw [G2_q_exp]
    rw [riemannZeta_two]
    conv =>
      enter [1,2,1]
      ext n
      rw [show  -(2 * ↑π * Complex.I * (↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
        (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) =
        (-2 * ↑π * Complex.I) * (((↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
        (1 - cexp (2 * ↑π * Complex.I * (n + 1) * z.1))) by ring]
    rw [tsum_mul_left (a := -2 * ↑π * Complex.I)]
    have := tsum_eq_tsum_sigma z
    simp only [UpperHalfPlane.coe] at *
    rw [this, mul_sub]
    rw [sub_eq_add_neg, mul_add]
    congr 1
    · have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      ring_nf
      field_simp
      ring
    ·
      have hr :    ↑π * Complex.I / 12 *
         -((↑π ^ 2 / (6 : ℂ))⁻¹ * 2⁻¹ * (8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) =
        (↑π * Complex.I * (1 / 12) * -(((π : ℂ) ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8)) *
        ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1)) := by
          ring_nf
          rfl
      simp only [UpperHalfPlane.coe] at *
      rw [hr]
      congr 1
      have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      field_simp
      ring
      conv =>
        enter [1,1]
        ext n
        rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
      have hl := tsum_pnat_eq_tsum_succ3
        (fun n ↦ ↑((σ 1) (n)) * cexp (↑π * Complex.I * 2 * (↑n) * ↑z))
      simp only [UpperHalfPlane.coe] at hl
      rw [ hl]
      apply tsum_congr
      intro b
      simp
      left
      congr 1
      ring
  · exact isOpen_lt continuous_const Complex.continuous_im
  · intro i
    simp only [mem_setOf_eq, ne_eq]
    rw [@sub_eq_zero]
    intro h
    have j := exp_upperHalfPlane_lt_one_nat z i
    simp only [UpperHalfPlane.coe] at *
    rw [← h] at j
    simp at j
  · intro i x hx
    fun_prop
  · simp only [mem_setOf_eq]
    have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
    have h1 := fun i : ℕ => logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
    have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
    have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_mul]
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
        deriv_add, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_id']
    conv =>
      enter [1]
      ext i
      rw [h2 i, h1 i, h3 i]
    simp only [neg_mul, one_mul]
    conv =>
      enter [1]
      ext i
      rw [mul_assoc, neg_div, ← mul_div]
    apply Summable.neg
    apply Summable.mul_left
    have hS := logDeriv_q_expo_summable (cexp (2 * ↑π * Complex.I * ↑z))
      (by simpa using exp_upperHalfPlane_lt_one z)
    rw [← summable_nat_add_iff 1] at hS
    apply hS.congr
    intro b
    congr
    simp only [Nat.cast_add, Nat.cast_one]
    · rw [← Complex.exp_nsmul]
      simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf
    · rw [← Complex.exp_nsmul]
      simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf
  · simp_rw [sub_eq_add_neg]
    have:= eta_tndntunif
    simp [eta_q_eq_exp, eta_prod_term] at this
    sorry
  · sorry
    --exact eta_tprod_ne_zero z
  · simp only [ne_eq, exp_ne_zero, not_false_eq_true]
    sorry
  · sorry
    --exact eta_tprod_ne_zero z
  · sorry
    --fun_prop
  · apply eta_differentiableAt



lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = ((z :ℂ)^(2 : ℤ))⁻¹ * (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    congr
    conv =>
      enter [1,1]
      intro z
      rw [neg_div]
      simp
    simp only [deriv.neg', deriv_inv', neg_neg, inv_inj]
    norm_cast
    · simpa only using
      eta_DifferentiableAt_UpperHalfPlane (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
    conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    simp only [differentiableAt_id']
    exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  nth_rw 2 [logDeriv_apply]
  unfold csqrt
  have := csqrt_deriv z
  rw [this]
  simp only [one_div, neg_mul, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg, show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
   (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring, ← Complex.exp_add,
   ← sub_eq_add_neg, show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring, Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
  have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
  simp only [coe_mk_subtype] at Rb
  rw [Rb]
  have E := E₂_transform z
  simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def, slash, ← ModularGroup.sl_moeb,
    modular_S_smul, ModularGroup.det_coe, ofReal_one, Int.reduceSub, zpow_one, mul_one,
    ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
  have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    simp [UpperHalfPlane.mk]
    ring_nf
  rw [h00] at E
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  simp only [UpperHalfPlane.coe] at *
  rw [E, add_mul, add_comm]
  congr 1
  have hzne := ne_zero z
  have hI : Complex.I ≠ 0 := by
    exact I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact Real.pi_ne_zero
  simp [UpperHalfPlane.coe] at hzne ⊢
  field_simp
  ring
  rw [mul_comm]
  · simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · unfold csqrt
    rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
    apply DifferentiableAt.comp
    simp
    apply DifferentiableAt.const_mul
    apply Complex.differentiableAt_log
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only [UpperHalfPlane.coe] at hz
    exact Ne.symm (ne_of_lt hz)
  · apply eta_DifferentiableAt_UpperHalfPlane z

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql ⟨z, hz⟩
  exact this

lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩
    · apply DifferentiableOn.div
      fun_prop
      fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp at *
      exact this
  · apply DifferentiableOn.mul
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · use UpperHalfPlane.I
    simp only [coe_I, mem_setOf_eq, Complex.I_im, zero_lt_one]
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply eta_nonzero_on_UpperHalfPlane ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := eta_nonzero_on_UpperHalfPlane ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
    simpa only [ne_eq, coe_mk_subtype] using this

lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const
  obtain ⟨z, hz, h⟩ := h
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    have h:=  eta_nonzero_on_UpperHalfPlane UpperHalfPlane.I
    convert h
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2

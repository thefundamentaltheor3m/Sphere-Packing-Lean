import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.csqrt
import SpherePacking.ModularForms.logDeriv_lems
import SpherePacking.ModularForms.multipliable_lems


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma


/- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
noncomputable def η (z : ℂ) := cexp (2 * π * Complex.I * z / 24) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z))


lemma tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  apply HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
  · apply Summable.hasProdUniformlyOn_nat_one_add hK hu ?_ hcts
    filter_upwards with n x hx using h n x hx

/-this is being PRd-/
lemma prod_tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} (K : Set α)
    (hK : IsCompact K) (u : ℕ → ℝ) (hu : Summable u) (h : ∀ n x, x ∈ K → (‖(f n x)‖) ≤ u n)
    (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
    apply tendstoUniformlyOn_tprod' hK hu h hcts

lemma eta_tndntunif : TendstoLocallyUniformlyOn (fun n ↦ ∏ x ∈ Finset.range n,
    fun x_1 ↦ 1 + -cexp (2 * ↑π * Complex.I *  (↑x + 1) * x_1))
    (fun x ↦ ∏' (i : ℕ), (1 + -cexp (2 * ↑π * Complex.I * (↑i + 1) * x))) atTop {x | 0 < x.im} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_im)]
  intro K hK hK2
  obtain rfl | hN := K.eq_empty_or_nonempty
  · exact tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by
    fun_prop
  have := IsCompact.exists_sSup_image_eq_and_ge hK2 (by simpa using hN) hc
  obtain ⟨z, hz, hB, HB⟩ := this
  have :=  prod_tendstoUniformlyOn_tprod'  K  hK2 (f := (fun i ↦
    fun x_1 ↦ -cexp (2 * ↑π * Complex.I *  (i + 1) * x_1)))
    (fun n=> ‖cexp (2 * ↑π * Complex.I * z)^(n + 1)‖) ?_ ?_ ?_
  · simp only at *
    convert this
    simp only [Finset.prod_apply]
  · simp_rw [norm_pow]
    rw [summable_nat_add_iff 1]
    simp only [summable_geometric_iff_norm_lt_one, norm_norm]
    apply  exp_upperHalfPlane_lt_one ⟨z, by simpa using (hK hz)⟩
  · intro n x hx
    simp only [norm_neg]
    rw [show 2 * ↑π * Complex.I * (↑n + 1) * x = (n+1)* (2 * ↑π * Complex.I  * x) by ring ]
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
    rw [Complex.exp_nat_mul]
    have HB2 := HB x hx
    simp_rw [norm_pow]
    apply pow_le_pow_left₀ _  HB2
    simp only [norm_nonneg]
  · intro n
    fun_prop

theorem eta_tprod_ne_zero (z : ℍ) :
  ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z)) ≠ 0 := by
  simp_rw [sub_eq_add_neg]
  have := tprod_ne_zero z (fun n x => -cexp (2 * ↑π * Complex.I * (n + 1) * x)) ?_ ?_
  · simp only [Pi.add_apply, Pi.one_apply, ne_eq] at *
    apply this
  · intro i x
    simpa using (term_ne_zero x i)
  intro x
  rw [←summable_norm_iff]
  simpa using summable_exp_pow x

/-- Eta is non-vanishing! -/
lemma eta_nonzero_on_UpperHalfPlane (z : ℍ) : η z ≠ 0 := by
  rw [η]
  have := eta_tprod_ne_zero z
  simp only [ne_eq, mul_eq_zero, exp_ne_zero, false_or] at *
  apply this

lemma tsum_log_deriv_eqn (z : ℍ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ↑z =
  ∑' n : ℕ, -(2 * ↑π * Complex.I * (↑n + 1)) *
             cexp (2 * π * Complex.I * (n + 1) * z) /
             (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) := by
  congr
  ext i
  have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
  have h1 := fun i : ℕ =>
    logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
  have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
  have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_fun_mul]
      · simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_fun_id]
  rw [h2 i, h1 i, h3 i]
  simp

lemma logDeriv_z_term (z : ℍ) : logDeriv (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) ↑z =
    2* ↑π * Complex.I / 24 := by
  have : (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) =
      (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z) := by
    ext y
    simp
    congr
    ring
  rw [this, logDeriv_comp, deriv_const_mul]
  · simp only [LogDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]
  · fun_prop
  · fun_prop
  · fun_prop


theorem eta_differentiableAt (z : ℍ) :
  DifferentiableAt ℂ (fun z ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z))) ↑z := by
  have hD := eta_tndntunif.differentiableOn ?_ (isOpen_lt continuous_const Complex.continuous_im)
  · simp_rw [sub_eq_add_neg]
    rw [DifferentiableOn] at hD
    have hDz := (hD z (by apply z.2)).differentiableAt
    apply hDz
    · apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im)
      apply z.2
  simp only [eventually_atTop, ge_iff_le]
  use 0
  intro b hb
  have := DifferentiableOn.finset_prod (u := Finset.range b)
    (f := fun i : ℕ => fun x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
    (s := {x : ℂ | 0 < x.im}) ?_
  · apply this.congr
    intro x hx
    simp [sub_eq_add_neg]
  · intro i hi
    fun_prop


lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ η z := by
  unfold η
  apply DifferentiableAt.mul
  · conv =>
      enter [2]
      rw [show (fun z => cexp (2 * ↑π * Complex.I * z / 24)) =
               cexp ∘ (fun z => 2 * ↑π * Complex.I * z / 24) by rfl]
    apply DifferentiableAt.cexp
    fun_prop
  · apply eta_differentiableAt

lemma eta_logDeriv (z : ℍ) : logDeriv η z = (π * Complex.I / 12) * E₂ z := by
  unfold η
  rw [logDeriv_mul]
  · have HG := logDeriv_tprod_eq_tsum (s := {x : ℂ | 0 < x.im}) ?_ z
     (fun (n : ℕ) => fun (x : ℂ) => 1 - cexp (2 * π * Complex.I * (n + 1) * x)) ?_ ?_ ?_ ?_ ?_
    · simp only [mem_setOf_eq, UpperHalfPlane.coe] at *
      rw [HG]
      · have := tsum_log_deriv_eqn z
        have h0 := logDeriv_z_term z
        simp only [UpperHalfPlane.coe] at *
        rw [this, E₂, h0]
        simp only [neg_mul, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
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
        · have hpi : (π : ℂ) ≠ 0 := by simp
          ring_nf
          field_simp
        · have hr : ↑π * Complex.I / 12 *
            -((↑π ^ 2 / (6 : ℂ))⁻¹ * 2⁻¹ *
               (8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) =
            (↑π * Complex.I * (1 / 12) * -(((π : ℂ) ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8)) *
            ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1)) := by
              ring_nf
              rfl
          simp only [UpperHalfPlane.coe] at *
          rw [hr]
          congr 1
          · have hpi : (π : ℂ) ≠ 0 := by simp
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
          simp only [Nat.cast_add, Nat.cast_one, mul_eq_mul_left_iff, Nat.cast_eq_zero,
            ArithmeticFunction.sigma_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false]
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
      have h1 := fun i : ℕ =>
        logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
      have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
        ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
        intro i
        ext y
        simp
      have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
          fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
        intro i
        ext y
        rw [deriv_fun_mul]
        · simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
        · simp only [differentiableAt_const]
        · simp only [differentiableAt_fun_id]
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
      · simp only [Nat.cast_add, Nat.cast_one]
      · rw [← Complex.exp_nsmul]
        simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring_nf
      · rw [← Complex.exp_nsmul]
        simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring_nf
    · simp_rw [sub_eq_add_neg]
      apply eta_tndntunif
    · exact eta_tprod_ne_zero z
  · simp only [ne_eq, exp_ne_zero, not_false_eq_true]
  · exact eta_tprod_ne_zero z
  · fun_prop
  · apply eta_differentiableAt


lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
            ((z :ℂ)^(2 : ℤ))⁻¹ *
              (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    · congr
      conv =>
        enter [1,1]
        intro z
        rw [neg_div]
        simp
      simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
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
    · simp only [differentiableAt_fun_id]
    · exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  · nth_rw 2 [logDeriv_apply]
    unfold csqrt
    have := csqrt_deriv z
    rw [this]
    simp only [one_div, neg_mul, smul_eq_mul]
    nth_rw 2 [div_eq_mul_inv]
    · rw [← Complex.exp_neg,
          show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
               (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring,
          ← Complex.exp_add, ← sub_eq_add_neg,
          show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
          Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
      · have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
        simp only [coe_mk_subtype] at Rb
        rw [Rb]
        have E := E₂_transform z
        simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def, modular_S_smul,
                   ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
        have h00 : UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos =
                   (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
          simp [UpperHalfPlane.mk]
          ring_nf
        rw [h00] at E
        rw [← mul_assoc, mul_comm, ← mul_assoc]
        simp only [UpperHalfPlane.coe] at *
        rw [E, add_mul, add_comm]
        congr 1
        · have hzne := ne_zero z
          have hI : Complex.I ≠ 0 := I_ne_zero
          have hpi : (π : ℂ) ≠ 0 := by
            simp only [ne_eq, ofReal_eq_zero]
            exact Real.pi_ne_zero
          simp [UpperHalfPlane.coe] at hzne ⊢
          field_simp
          ring
        rw [mul_comm]
      simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · exact csqrt_differentiableAt z
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
      · fun_prop
      · fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp only [mem_setOf_eq]
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp only [coe_mk_subtype, inv_neg, neg_im, inv_im, Left.neg_pos_iff] at *
      exact this
  · apply DifferentiableOn.mul
    · simp only [DifferentiableOn, mem_setOf_eq]
      intro x hx
      apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · apply Convex.isPreconnected
    exact convex_halfSpace_im_gt 0
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
  simp only [comp_apply, div_I, neg_mul, one_mul, neg_neg, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul] at h3
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

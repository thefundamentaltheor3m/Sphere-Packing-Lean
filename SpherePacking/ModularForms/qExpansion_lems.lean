import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Cases

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k] [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  simp only [comp_apply]
  have hi : IsCusp OnePoint.infty Γ(n) := by
    apply Γ(n).isCusp_of_mem_strictPeriods (h := n)
    · have h := inst.1
      positivity
    · simp
  have h1 := Function.Periodic.boundedAtFilter_cuspFunction (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)
    (bounded_at_infty_comp_ofComplex f hi)
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Function.Periodic.differentiableAt_cuspFunction_zero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) ?_ ?_ ?_).continuousAt.tendsto
    · apply SlashInvariantFormClass.periodic_comp_ofComplex
      simp
    · simp only [eventually_comap, eventually_atTop, ge_iff_le]
      use 1
      intro b hb a ha
      apply ModularFormClass.differentiableAt_comp_ofComplex (z := a)
      rw [ha]
      linarith
    apply ModularFormClass.bounded_at_infty_comp_ofComplex
    exact hi
  apply h2.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  use ball 0 1
  constructor
  · apply Metric.ball_mem_nhds
    exact Real.zero_lt_one
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

theorem cuspFunction_mul_zero (n : ℕ) (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
  [inst : NeZero n] :
    cuspFunction n (f.mul g) 0 = cuspFunction n f 0 * cuspFunction n g 0 := by
  rw [cuspFunction, Periodic.cuspFunction ]
  simp only [coe_mul, update_self]
  apply Filter.Tendsto.limUnder_eq
  have : (⇑f * ⇑g) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) * (⇑g ∘ ↑ofComplex) := by
    ext y
    simp only [comp_apply, Pi.mul_apply]
  rw [this]
  apply Filter.Tendsto.mul
  · apply modform_tendto_ndhs_zero
  · apply modform_tendto_ndhs_zero

lemma qExpansion_mul_coeff_zero (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : (qExpansion n (f.mul g)).coeff 0 =
      (((qExpansion n f)).coeff 0) * ((qExpansion n g)).coeff 0 := by
    simp_rw [qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    apply cuspFunction_mul_zero

lemma cuspFunction_mul (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : cuspFunction n (f.mul g) = cuspFunction n f * cuspFunction n g := by
  ext z
  by_cases h : z = 0
  · rw [h]
    simp only [Pi.mul_apply]
    apply cuspFunction_mul_zero
  simp_rw [cuspFunction, Periodic.cuspFunction]
  simp only [coe_mul, ne_eq, h, not_false_eq_true, update_of_ne, comp_apply, Pi.mul_apply]

theorem derivWithin_mul2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hd : DifferentiableOn ℂ g s) :
    s.restrict (derivWithin (fun y => f y * g y) s) =
      s.restrict (derivWithin f s * g + f * derivWithin g s) := by
  ext y
  simp only [restrict_apply, Pi.add_apply, Pi.mul_apply]
  rw [derivWithin_fun_mul (hf y y.2) (hd y y.2)]

lemma iteratedDerivWithin_mul (f g : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (m : ℕ)
    (hf : ContDiffOn ℂ ⊤ f s) (hg : ContDiffOn ℂ ⊤ g s) :
    iteratedDerivWithin m (f * g) s x =
    ∑ i ∈ Finset.range m.succ, (m.choose i) * (iteratedDerivWithin i f s x) *
    (iteratedDerivWithin (m - i) g s x) := by
  induction m generalizing f g with
  | zero => simp only [iteratedDerivWithin_zero, Pi.mul_apply, Nat.succ_eq_add_one, zero_add,
    Finset.range_one, zero_le, Nat.sub_eq_zero_of_le, Finset.sum_singleton, Nat.choose_self,
    Nat.cast_one, one_mul]
  | succ m hm =>
    have h1 :=
      derivWithin_mul2 f g s (hf.differentiableOn (by simp)) (hg.differentiableOn (by simp))
    have h2 : (fun y => f y * g y) = f * g := by ext y; simp
    rw [iteratedDerivWithin_succ']
    have hset : s.EqOn (derivWithin (f * g) s) (derivWithin f s * g + f * derivWithin g s) := by
      intro z hz
      aesop
    rw [iteratedDerivWithin_congr hset hx, iteratedDerivWithin_add hx hs.uniqueDiffOn, hm _ _ hf,
      hm _ _ _ hg]
    · simp_rw [←iteratedDerivWithin_succ']
      have := Finset.sum_choose_succ_mul (fun i => fun j =>
        ((iteratedDerivWithin i f s x) * (iteratedDerivWithin j g s x)) ) m
      simp only [Nat.succ_eq_add_one, restrict_eq_restrict_iff] at *
      rw [show m + 1 + 1 = m + 2 by ring]
      simp_rw [← mul_assoc] at *
      rw [this, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intros i hi
      congr
      simp at hi
      omega
    · exact ContDiffOn.derivWithin hf (by exact IsOpen.uniqueDiffOn hs) (m := ⊤) (by simp)
    · exact ContDiffOn.derivWithin hg (by exact IsOpen.uniqueDiffOn hs) (m := ⊤) (by simp)
    · apply ContDiffOn.mul
      · exact ContDiffOn.derivWithin hf (by exact IsOpen.uniqueDiffOn hs) (m := m) (by simp)
      · apply ContDiffOn.of_le hg (by simp)
      exact hx
    · apply ContDiffOn.mul
      · apply ContDiffOn.of_le hf (by simp)
      · apply ContDiffOn.derivWithin hg (by exact IsOpen.uniqueDiffOn hs) (m := m) (by simp)
      exact hx

lemma iteratedDeriv_eq_iteratedDerivWithin (n : ℕ) (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
  (z : ℂ) (hz : z ∈ s) : iteratedDeriv n f z = iteratedDerivWithin n f s z := by
  rw [← iteratedDerivWithin_univ]
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_congr_set]
  apply EventuallyEq.symm
  rw [eventuallyEq_univ]
  exact IsOpen.mem_nhds hs hz

lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [hn : NeZero n] : qExpansion n (f.mul g) = qExpansion n f * qExpansion n g := by
  ext m
  induction m with
  | zero => simpa using qExpansion_mul_coeff_zero n a b f g
  | succ m hm =>
    simp_rw [PowerSeries.coeff_mul ,qExpansion_coeff, cuspFunction_mul ] at *
    have :=iteratedDerivWithin_mul (f := cuspFunction n f) (g := cuspFunction n g) (Metric.ball 0 1)
      (isOpen_ball) 0 (by simp) (m+1) ?_ ?_
    · simp_rw [← iteratedDeriv_eq_iteratedDerivWithin (m+1) _ (Metric.ball 0 1) (isOpen_ball) 0
        (by simp)] at this
      conv at this =>
        enter [2,2]
        intro n
        rw [← iteratedDeriv_eq_iteratedDerivWithin n _ (Metric.ball 0 1) (isOpen_ball) 0 (by simp)]
        rw [← iteratedDeriv_eq_iteratedDerivWithin (m + 1 -n) _ (Metric.ball 0 1) (isOpen_ball) 0
          (by simp)]
      rw [this]
      simp only [Nat.succ_eq_add_one]
      have h0 : ((m+1)! : ℂ) ≠ 0 := by
        norm_cast
        exact Nat.factorial_ne_zero (m + 1)
      rw [inv_mul_eq_iff_eq_mul₀ h0, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.mul_sum]
      simp only [Nat.succ_eq_add_one]
      have ht (x : ℕ) : ↑(m + 1)! *
        ((↑x !)⁻¹ * iteratedDeriv x (cuspFunction n f) 0 *
          ((↑(m + 1 - x)!)⁻¹ * iteratedDeriv (m + 1 - x) (cuspFunction n g) 0)) =
          (↑(m + 1)! *
        ((↑x !)⁻¹ * ((↑(m + 1 - x)!)⁻¹) * iteratedDeriv x (cuspFunction n f) 0 *
          iteratedDeriv (m + 1 - x) (cuspFunction n g) 0)) := by ring
      conv =>
        enter [2,2]
        intro x
        rw [ht x]
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [← mul_assoc]
      congr
      simp only [Finset.mem_range] at hx
      rw [Nat.cast_choose ℂ (b := m + 1) (a := x)]
      · field_simp
      omega
    · refine DifferentiableOn.contDiffOn ?_ (isOpen_ball)
      intro y hy
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_cuspFunction (h := n)
      · have := hn.1; positivity
      · simp
      simpa using hy
    · refine DifferentiableOn.contDiffOn ?_ (isOpen_ball)
      intro y hy
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_cuspFunction (h := n)
      · have := hn.1; positivity
      · simp
      simpa using hy


lemma cuspFunction_sub [NeZero n] (f g : ModularForm Γ(n) k) :
    cuspFunction n (f - g) = cuspFunction n f - cuspFunction n g := by
  simp only [cuspFunction, Periodic.cuspFunction]
  ext y
  obtain rfl | hy := eq_or_ne y 0; swap
  · simp [hy]
  simp only [update_self]
  have : ((⇑f - ⇑g) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = (⇑f ∘ ↑ofComplex) ∘ Periodic.invQParam
    ↑n
      - (⇑g ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n := by
    ext y
    simp
  simp only [Pi.sub_apply, update_self] at *
  rw [this]
  rw [Filter.Tendsto.limUnder_eq]
  apply Tendsto.sub
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero f n
    simp only [comp_apply] at *
    aesop
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero g n
    simp only [comp_apply] at *
    aesop

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma qExpansion_sub (f g : ModularForm Γ(1) k) : (qExpansion (1 : ℕ) (f - g)) =
    (qExpansion 1 f) - (qExpansion 1 g) := by
  ext m
  simp_rw [qExpansion]
  simp only [PowerSeries.coeff_mk, map_sub, coe_sub]
  rw [cuspFunction_sub]
  rw [← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1)]
  · rw [iteratedDerivWithin_sub]
    · ring_nf
    · refine mem_ball_self ?_
      exact Real.zero_lt_one
    · refine IsOpen.uniqueDiffOn ?_
      exact isOpen_ball
    · refine (DifferentiableOn.contDiffOn ?_ isOpen_ball).contDiffWithinAt (by simp)
      intro x hx
      refine DifferentiableAt.differentiableWithinAt ?_
      apply differentiableAt_cuspFunction f (by positivity) (by simp)
      simpa using hx
    · refine (DifferentiableOn.contDiffOn ?_ isOpen_ball).contDiffWithinAt (by simp)
      intro x hx
      refine DifferentiableAt.differentiableWithinAt ?_
      refine differentiableAt_cuspFunction g (by positivity) (by simp) ?_
      simpa using hx
  · exact isOpen_ball.uniqueDiffOn
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero g (by positivity) (by simp)
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero f (by positivity) (by simp)
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    refine AnalyticAt.sub ?_ ?_
    · exact analyticAt_cuspFunction_zero f (by positivity) (by simp)
    exact analyticAt_cuspFunction_zero g (by positivity) (by simp)
  · refine mem_ball_self ?_
    exact Real.zero_lt_one


lemma cuspFunction_add [NeZero n] (f g : ModularForm Γ(n) k) :
    cuspFunction n (f + g) = cuspFunction n f + cuspFunction n g := by
  simp only [cuspFunction, Periodic.cuspFunction]
  ext y
  obtain rfl | hy := eq_or_ne y 0; swap
  · simp [hy]
  simp only [update_self, Pi.add_apply ]
  have : ((⇑f + ⇑g) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = (⇑f ∘ ↑ofComplex) ∘ Periodic.invQParam
    ↑n
      + (⇑g ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n := by
    ext y
    simp
  rw [this]
  rw [Filter.Tendsto.limUnder_eq]
  apply Tendsto.add
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero f n
    aesop
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero g n
    aesop

lemma qExpansion_add (f g : ModularForm Γ(1) k) : (qExpansion 1 (f + g)) =
    (qExpansion 1 f) + (qExpansion 1 g) := by
  ext m
  simp_rw [qExpansion]
  simp only [PowerSeries.coeff_mk, map_add, coe_add, ← Nat.cast_one (R := ℝ)]
  rw [cuspFunction_add]
  rw [← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1)]
  · rw [iteratedDerivWithin_add]
    · ring
    · refine mem_ball_self ?_
      exact Real.zero_lt_one
    · refine IsOpen.uniqueDiffOn ?_
      exact isOpen_ball
    · refine (DifferentiableOn.contDiffOn ?_ isOpen_ball).contDiffWithinAt (by simp)
      intro x hx
      refine DifferentiableAt.differentiableWithinAt ?_
      refine differentiableAt_cuspFunction f (by positivity) (by simp) ?_
      simpa using hx
    · refine (DifferentiableOn.contDiffOn ?_ isOpen_ball).contDiffWithinAt (by simp)
      intro x hx
      refine DifferentiableAt.differentiableWithinAt ?_
      refine differentiableAt_cuspFunction g (by positivity) (by simp) ?_
      simpa using hx
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero g (by positivity) (by simp)
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero f (by positivity) (by simp)
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    refine AnalyticAt.add ?_ ?_
    · exact analyticAt_cuspFunction_zero f (by positivity) (by simp)
    exact analyticAt_cuspFunction_zero g (by positivity) (by simp)
  · refine mem_ball_self ?_
    exact Real.zero_lt_one


lemma IteratedDeriv_smul (a : ℂ) (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (a • f) = a • iteratedDeriv m f := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hm]
    ext x
    rw [@Pi.smul_def]
    exact deriv_const_smul' a ..


lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · simp_rw [h, cuspFunction,Periodic.cuspFunction]
      simp only [update_self, Pi.smul_apply, smul_eq_mul]
      rw [Filter.limUnder_eq_iff ]
      · have hl : ((a • ⇑f) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = fun x => a * (f ∘ ↑ofComplex)
          (Periodic.invQParam ↑n x) := by
          ext y
          simp
        rw [hl]
        simp only [comp_apply]
        apply Filter.Tendsto.const_mul
        have := modform_tendto_ndhs_zero f _
        simp only [comp_apply] at this
        convert this
        rw [Filter.limUnder_eq_iff ]
        · apply this
        aesop
      have := modform_tendto_ndhs_zero (a • f) _
      aesop
    · simp only [cuspFunction, Pi.smul_apply, smul_eq_mul]
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ h,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
      simp
  simp only [PowerSeries.coeff_mk, IsGLPos.coe_smul, this]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma qExpansion_smul (a : ℂ) (f : CuspForm Γ(n) k) [hn : NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · rw [h]
      have n_pos : 0 < n := Nat.zero_lt_of_ne_zero hn.1
      have h0 := CuspFormClass.cuspFunction_apply_zero (h := n) (a • f) (by positivity) (by simp)
      have h1 := CuspFormClass.cuspFunction_apply_zero (h := n) f (by positivity) (by simp)
      simp only [CuspForm.IsGLPos.coe_smul] at h0
      simp only [h0, Pi.smul_apply, h1, smul_eq_mul, mul_zero]
    · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
  simp only [PowerSeries.coeff_mk, CuspForm.IsGLPos.coe_smul, this]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

instance : FunLike (ℍ → ℂ) ℍ ℂ := { coe := fun ⦃a₁⦄ ↦ a₁, coe_injective' := fun ⦃_ _⦄ a ↦ a}

lemma qExpansion_ext (f g : ℍ → ℂ) (h : f = g) : qExpansion 1 f =
    qExpansion 1 g := by
  rw [h]

lemma cuspFunction_congr_funLike
    {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (n : ℕ) (f : α) (g : β) (h : ⇑f = ⇑g) :
    cuspFunction n f = cuspFunction n g := by
  ext z
  by_cases hz : z = 0
  · simp [cuspFunction, Periodic.cuspFunction, h]
  · simp [cuspFunction, Periodic.cuspFunction, h, hz]

lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β) (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  have hcf : cuspFunction 1 f = cuspFunction 1 g := congrArg (cuspFunction 1) h
  ext m
  simp [qExpansion_coeff, hcf]

lemma qExpansion_of_mul (a b : ℤ) (f : ModularForm Γ(1) a) (g : ModularForm Γ(1) b) :
  qExpansion 1 (((((DirectSum.of (ModularForm Γ(1)) a ) f)) * ((DirectSum.of (ModularForm Γ(1)) b )
    g)) (a + b)) =
    (qExpansion 1 f) * (qExpansion 1 g) := by
  rw [DirectSum.of_mul_of, ← Nat.cast_one (R := ℝ), ← qExpansion_mul_coeff]
  simp only [DirectSum.of_eq_same]
  rfl

@[simp] --generalize this away from ℂ
lemma IteratedDeriv_zero_fun (n : ℕ) (z : ℂ) : iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) z = 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp [iteratedDeriv_succ', hn]

lemma iteratedDeriv_const_eq_zero (m : ℕ) (hm : 0 < m) (c : ℂ) :
    iteratedDeriv m (fun _ : ℂ => c) = fun _ : ℂ => 0 := by
  ext z
  have := iteratedDeriv_const_add hm (f := fun (x : ℂ) => (0 : ℂ)) c (x := z)
  simpa only [add_zero, IteratedDeriv_zero_fun] using this

lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
  qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k ) f) ^ n) (n * k)) = (qExpansion 1 f) ^ n := by
  induction n with
  | zero =>
    simp only [Int.cast_ofNat_Int, pow_zero]
    rw [show 0 * k = 0 by ring]
    have hq : qExpansion 1 ((1 : ModularForm Γ(1) 0)) = 1 := by
      have : cuspFunction 1 ((1 : ModularForm Γ(1) 0)) = 1 := by
        simp only [cuspFunction, Periodic.cuspFunction]
        ext z
        simp only [one_coe_eq_one, Pi.one_comp, Pi.one_apply]
        by_cases hz : z = 0
        · rw [hz]
          simp only [update_self]
          apply Filter.Tendsto.limUnder_eq
          apply tendsto_const_nhds
        simp [hz]
      rw [qExpansion]
      rw [this]
      ext m
      simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
      by_cases hm : m = 0
      · rw [hm]
        simp
      simp only [hm, ↓reduceIte, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero]
      right
      have hmp : 0 < m := by omega
      have := iteratedDeriv_const_eq_zero m hmp 1
      have ht := congr_fun this 0
      apply ht
    rw [← hq]
    rfl
  | succ n hn =>
    rw [pow_succ, pow_succ, show ↑(n + 1) * k = (n • k) + k by simp; ring]
    rw [DirectSum.ofPow] at *
    rw [qExpansion_of_mul]
    congr
    rw [← hn]
    apply qExpansion_ext2
    ext z
    rw [show n * k = n • k by rfl]
    simp

@[simp]
lemma qExpansion_zero [NeZero n] : qExpansion n (0 : ModularForm Γ(n) k) = 0 := by
  simpa using (qExpansion_smul2 (a := (0 : ℂ)) (f := (0 : ModularForm Γ(n) k))).symm

lemma qExpansion_injective [hn : NeZero n] (f : ModularForm Γ(n) k) :
    qExpansion n f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext z
    have n_pos : 0 < n := Nat.zero_lt_of_ne_zero hn.1
    simp [← (hasSum_qExpansion (h := n) f (by positivity) (by simp) z).tsum_eq, h]
  · simp [h]

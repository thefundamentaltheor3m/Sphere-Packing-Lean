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

theorem derivWithin_mul2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hd : DifferentiableOn ℂ g s) :
    s.restrict (derivWithin (fun y => f y * g y) s) =
      s.restrict (derivWithin f s * g + f * derivWithin g s) := by
  ext y
  simp only [restrict_apply, Pi.add_apply, Pi.mul_apply]
  rw [derivWithin_fun_mul (hf y y.2) (hd y y.2)]

lemma iteratedDerivWithin_mul' (f g : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (x : ℂ) (hx : x ∈ s) (m : ℕ)
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
  simpa using
    (ModularForm.qExpansion_mul (Γ := Γ(n)) (h := n)
      (hh := by exact Nat.cast_pos.mpr (Nat.pos_of_neZero n))
      (hΓ := by simp) f g)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

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
  simpa using
    (qExpansion_smul (Γ := Γ(n)) (h := n)
      (hh := by exact Nat.cast_pos.mpr (Nat.pos_of_neZero n))
      (hΓ := by simp) a f).symm

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
  simpa using
    (qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℕ))
      (hh := by positivity) (hΓ := by simp) (f := f) (n := n))

lemma qExpansion_injective [hn : NeZero n] (f : ModularForm Γ(n) k) :
    qExpansion n f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext z
    have n_pos : 0 < n := Nat.zero_lt_of_ne_zero hn.1
    simp [← (hasSum_qExpansion (h := n) f (by positivity) (by simp) z).tsum_eq, h]
  · subst h
    simpa using (qExpansion_zero (h := n))

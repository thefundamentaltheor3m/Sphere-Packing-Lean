module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Cases


/-!
# Limits at infinity

For modular forms, the value at the cusp `∞` is a genuine limit as `im τ → ∞`.

## Main statements
* `modularForm_tendsto_atImInfty`
* `qExpansion_mul_coeff`
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat MatrixGroups CongruenceSubgroup

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

/-- The cusp function at `0` is a (punctured) limit along the inverse `q`-parameter. -/
public theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k]
    [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hcont : ContinuousAt (Function.Periodic.cuspFunction (n : ℝ) (⇑f ∘ (↑ofComplex : ℂ → ℍ)))
      0 := by
    simpa [SlashInvariantFormClass.cuspFunction] using
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos
        (by simp [CongruenceSubgroup.strictPeriods_Gamma])).continuousAt
  simpa [SlashInvariantFormClass.cuspFunction, Function.comp] using
    (Function.Periodic.tendsto_nhds_zero (h := (n : ℝ)) (f := ⇑f ∘ (↑ofComplex : ℂ → ℍ)) hcont)


/-- A modular form converges to its `valueAtInfty` as `im τ → ∞` (for `Γ(n)`). -/
public theorem modularForm_tendsto_atImInfty {k : ℤ} (n : ℕ) (f : ModularForm Γ(n) k)
    [NeZero n] :
    Tendsto (fun τ : ℍ => f τ) atImInfty (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have ht :
      Tendsto (fun τ : ℍ => cuspFunction (n : ℝ) f (Periodic.qParam (n : ℝ) τ)) atImInfty
        (𝓝 (cuspFunction (n : ℝ) f 0)) := by
    simpa [cuspFunction] using
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos hmem).continuousAt.tendsto.comp
        (UpperHalfPlane.qParam_tendsto_atImInfty hn_pos)
  have hzero : cuspFunction (n : ℝ) f 0 = UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) := by
    simpa [SlashInvariantFormClass.cuspFunction, hn_ne] using
      (cuspFunction_apply_zero (f := f) (h := (n : ℝ)) hn_pos hmem)
  have ht' :
      Tendsto (fun τ : ℍ => cuspFunction (n : ℝ) f (Periodic.qParam (n : ℝ) τ)) atImInfty
        (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
    simpa [hzero] using ht
  refine ht'.congr fun τ ↦ ?_
  exact eq_cuspFunction f τ hmem hn_ne

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

/-- The `qExpansion` of a product is the product of the `qExpansion`s (coeffwise). -/
public lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [hn : NeZero n] : qExpansion n (f.mul g) = qExpansion n f * qExpansion n g := by
  exact ModularForm.qExpansion_mul (Γ := Γ(n)) (h := (n : ℝ)) (Nat.cast_pos.mpr (NeZero.pos n))
    (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f g

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
    exact deriv_const_smul_field a ..

public lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] :
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
  simp only [PowerSeries.coeff_mk, this]
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
    {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (h : ℝ) (f : α) (g : β) (hf : ⇑f = ⇑g) :
    cuspFunction h f = cuspFunction h g := by
  ext z
  by_cases hz : z = 0 <;> simp [cuspFunction, Periodic.cuspFunction, hf, hz]

/-- If two `FunLike` objects have the same underlying function, then their `qExpansion`s agree. -/
public lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β)
    (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  ext m
  simp [qExpansion_coeff, cuspFunction_congr_funLike (h := (1 : ℝ)) (f := f) (g := g) h]

/-- On `Γ(1)`, `qExpansion` commutes with subtraction. -/
public lemma qExpansion_sub1 {a b : ℤ} (f : ModularForm Γ(1) a) (g : ModularForm Γ(1) b) :
    qExpansion 1 (f - g) = qExpansion 1 f - qExpansion 1 g := by
  simpa using
    (qExpansion_sub (Γ := Γ(1)) (h := (1 : ℝ)) (by norm_num)
      (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f g)

@[simp] --generalize this away from ℂ
lemma IteratedDeriv_zero_fun (n : ℕ) (z : ℂ) : iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) z = 0 := by
  norm_num

lemma iteratedDeriv_const_eq_zero (m : ℕ) (hm : 0 < m) (c : ℂ) :
    iteratedDeriv m (fun _ : ℂ => c) = fun _ : ℂ => 0 := by
  ext z
  have := iteratedDeriv_const_add hm (f := fun (x : ℂ) => (0 : ℂ)) c (x := z)
  simpa only [add_zero, IteratedDeriv_zero_fun] using this

/-- The `qExpansion` of a power agrees with the power of the `qExpansion`. -/
public lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
    qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k) f) ^ n) (n * k)) =
      (qExpansion 1 f) ^ n := by
  simpa using
    (qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℝ)) (k := k) (by norm_num)
      (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f n)

/-
lemma qExpansion_injective [hn : NeZero n] (f : ModularForm Γ(n) k) :
    qExpansion n f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext z
    have n_pos : 0 < n := Nat.zero_lt_of_ne_zero hn.1
    simp [← (hasSum_qExpansion (h := n) f (by positivity) (by simp) z).tsum_eq, h]
  · simp [h]
-/

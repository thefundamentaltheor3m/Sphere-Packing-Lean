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
    simpa [cuspFunction] using
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos
        (by simp [CongruenceSubgroup.strictPeriods_Gamma])).continuousAt
  simpa [cuspFunction, Function.comp] using
    (Function.Periodic.tendsto_nhds_zero (h := (n : ℝ)) (f := ⇑f ∘ (↑ofComplex : ℂ → ℍ)) hcont)

/-- A modular form converges to its `valueAtInfty` as `im τ → ∞` (for `Γ(n)`). -/
public theorem modularForm_tendsto_atImInfty {k : ℤ} (n : ℕ) (f : ModularForm Γ(n) k)
    [NeZero n] :
    Tendsto (fun τ : ℍ => f τ) atImInfty (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma]
  have hzero : cuspFunction (n : ℝ) f 0 = UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) :=
    cuspFunction_apply_zero (f := (f : ℍ → ℂ)) hn_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos hmem)
      (SlashInvariantFormClass.periodic_comp_ofComplex (f := f) hmem)
  have ht : Tendsto (fun τ : ℍ => cuspFunction (n : ℝ) f (Periodic.qParam (n : ℝ) τ)) atImInfty
      (𝓝 (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
    rw [← hzero]
    simpa [cuspFunction] using
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos hmem).continuousAt.tendsto.comp
        (UpperHalfPlane.qParam_tendsto_atImInfty hn_pos)
  exact ht.congr fun τ ↦ SlashInvariantFormClass.eq_cuspFunction (f := f) τ hmem
    (by exact_mod_cast NeZero.ne n)

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
      · have hl : ((a • ⇑f) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n =
            fun x => a * (f ∘ ↑ofComplex) (Periodic.invQParam ↑n x) := by ext y; simp
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
    rw [iteratedDeriv_const_smul_field]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

instance : FunLike (ℍ → ℂ) ℍ ℂ := { coe := fun ⦃a₁⦄ ↦ a₁, coe_injective' := fun ⦃_ _⦄ a ↦ a}

/-- If two `FunLike` objects have the same underlying function, then their `qExpansion`s agree. -/
public lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β)
    (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  have hcf : cuspFunction (1 : ℝ) f = cuspFunction (1 : ℝ) g := by
    ext z; by_cases hz : z = 0 <;> simp [cuspFunction, Periodic.cuspFunction, h, hz]
  ext m; simp [qExpansion_coeff, hcf]

/-- On `Γ(1)`, `qExpansion` commutes with subtraction. -/
public lemma qExpansion_sub1 {a b : ℤ} (f : ModularForm Γ(1) a) (g : ModularForm Γ(1) b) :
    qExpansion 1 (f - g) = qExpansion 1 f - qExpansion 1 g :=
  ModularForm.qExpansion_sub (h := (1 : ℝ)) (by norm_num)
    (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f g

/-- The `qExpansion` of a power agrees with the power of the `qExpansion`. -/
public lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
    qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k) f) ^ n) (n * k)) =
      (qExpansion 1 f) ^ n := by
  simpa using
    (qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℝ)) (k := k) (by norm_num)
      (by simp [CongruenceSubgroup.strictPeriods_Gamma]) f n)


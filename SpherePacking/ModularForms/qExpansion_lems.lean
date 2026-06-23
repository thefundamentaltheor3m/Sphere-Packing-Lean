module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Cases

@[expose] public section

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
  have hn : (0 : ℝ) < (n : ℝ) := by simpa using Nat.pos_of_neZero n
  -- The cusp function is analytic (hence continuous) at `0` — now provided directly by mathlib's
  -- `ModularFormClass.analyticAt_cuspFunction_zero`, so the bespoke derivation is no longer needed.
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (ModularFormClass.analyticAt_cuspFunction_zero f hn (by simp)).continuousAt.tendsto
  apply h2.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  use ball 0 1
  constructor
  · apply Metric.ball_mem_nhds
    exact Real.zero_lt_one
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

instance : FunLike (ℍ → ℂ) ℍ ℂ where
  coe := fun ⦃a₁⦄ ↦ a₁
  coe_injective := fun ⦃_ _⦄ a ↦ a

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

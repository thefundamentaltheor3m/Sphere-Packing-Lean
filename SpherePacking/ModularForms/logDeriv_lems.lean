module
public import SpherePacking.ModularForms.tendstolems
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Lemmas about `logDeriv`

This file collects auxiliary lemmas about the logarithmic derivative `logDeriv`, including
formulas for `logDeriv` of exponential expressions and a basic summability statement.

## Main statements
* `logDeriv_one_sub_exp_comp`
* `logDeriv_q_expo_summable`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

/-
theorem logDeriv_tprod_eq_tsum2 {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : MultipliableLocallyUniformlyOn f s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have := logDeriv_tendsto (f := fun (n : ℕ) ↦ ∏ i ∈ Finset.range n, (f i)) (g := g) (s := s) hs
      (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall, g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    · apply HT.congr
      intro m
      congr
      ext i
      simp only [Finset.prod_apply]
    · have := htend.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      convert this
      simp
    · use 0
    · intro _ _
      exact DifferentiableOn.finset_prod fun i a ↦ hd i
    · exact hnez


theorem logDeriv_tprod_eq_tsum {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have :=
      logDeriv_tendsto (f := fun n ↦ ∏ i ∈ Finset.range n, (f i)) (g:=g) (s := s) hs (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall, g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    · apply HT.congr
      intro m
      congr
      ext i
      simp only [Finset.prod_apply]
    · exact htend
    · use 0
    · intro _ _
      exact DifferentiableOn.finset_prod fun i a ↦ hd i
    · exact hnez
-/

lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  simp [logDeriv]

/-- A chain rule computation for `logDeriv` of `(fun z => 1 - r * cexp z) ∘ g`. -/
public lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw [logDeriv_comp _ (hg y), logDeriv_one_sub_exp]
  · ring
  · fun_prop

/-- If `‖r‖ < 1`, then the series `∑ n, n * r^n / (1 - r^n)` is summable. -/
public lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  simpa [pow_one] using (summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 (r := r) hr)

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd : d x ≠ 0) :
     (a / b) x = (c /d) x ↔ (a * d) x = (b * c) x := by
  simpa [Pi.div_apply, Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
    (div_eq_div_iff hb hd : a x / b x = c x / d x ↔ a x * d x = c x * b x)

lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) ( deriv g) := by
  intro x hx
  simpa [derivWithin_of_isOpen hs hx] using
    (derivWithin_congr hfg (hfg hx))

lemma logDeriv_eqOn_iff' (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s → g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) :
    EqOn (logDeriv f) (logDeriv g) s ↔ ∃ z : ℂ, z ≠ 0 ∧ EqOn f (z • g) s := by
  simpa using logDeriv_eqOn_iff hf hg hs2 hsc.isPreconnected hgn hfn

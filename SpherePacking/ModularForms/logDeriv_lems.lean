import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import SpherePacking.ModularForms.tendstolems


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction



theorem logDeriv_tprod_eq_tsum  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
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
    have := logDeriv_tendsto (fun n ↦ ∏ i ∈ Finset.range n, (f i)) g (s := s) hs (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall, g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply HT.congr
    intro m
    congr
    ext i
    simp only [Finset.prod_apply]
    exact htend
    use 0
    intro b hb
    rw [DifferentiableOn]
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hp : ∀ (i : ℕ), i ∈ Finset.range b →  DifferentiableAt ℂ (f i) z := by
      intro i hi
      have := (hd i z hz).differentiableAt
      apply this
      exact IsOpen.mem_nhds hs hz
    have := DifferentiableAt.finset_prod hp
    convert this
    simp only [Finset.prod_apply]
    · exact hnez


lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  rw [logDeriv]
  simp only [Pi.div_apply, differentiableAt_const, differentiableAt_exp, DifferentiableAt.mul,
    deriv_sub, deriv_const', deriv_mul, zero_mul, Complex.deriv_exp, zero_add, zero_sub, neg_mul]

lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw  [logDeriv_comp, logDeriv_one_sub_exp]
  simp only [neg_mul]
  ring
  simp only [differentiableAt_const, differentiableAt_exp, DifferentiableAt.mul,
    DifferentiableAt.sub]
  exact hg y

lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  have := aux47 r hr
  have h1 : Tendsto (fun n : ℕ => (1 : ℂ)) atTop (𝓝 1) := by simp
  have h2 := Filter.Tendsto.div h1 this (by simp)
  rw [Metric.tendsto_atTop] at h2
  simp only [gt_iff_lt, ge_iff_le, Pi.div_apply, one_div, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, dist_eq_norm] at h2
  have h3 := h2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (g := fun n => 2 * ‖n * r^n‖)
  apply Summable.mul_left
  simp
  · have := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)
    simp at this
    apply this
  · simp
    obtain ⟨N, hN⟩ := h3
    use N
    intro n hn
    have h4 := hN n hn
    have := norm_lt_of_mem_ball h4 (E := ℂ)
    simp at *
    rw [div_eq_mul_inv]
    rw [mul_comm]
    gcongr
    apply le_trans this.le
    norm_cast

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd :  d x ≠ 0) :
     (a / b) x = (c /d) x ↔ (a * d) x = (b * c) x := by
  constructor
  intro h
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  simp only [Pi.mul_apply]
  simp only [Pi.div_apply] at h
  rw [div_eq_div_iff] at h
  nth_rw 2 [mul_comm]
  exact h
  exact hb
  exact hd
  intro h
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  simp only [Pi.mul_apply] at h
  nth_rw 2 [mul_comm]
  exact h
  apply hb
  apply hd

lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) ( deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]
  rw [← derivWithin_of_isOpen hs hx]
  apply derivWithin_congr hfg
  apply hfg hx

lemma logDeriv_eqOn_iff (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hs : s.Nonempty) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s →  g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) : EqOn (logDeriv f) (logDeriv g) s ↔
    ∃( z : ℂ),  z ≠ 0 ∧  EqOn (f) (z • g) s := by
  constructor
  simp_rw [logDeriv]
  intro h
  rw [@nonempty_def] at hs
  obtain ⟨t, ht⟩ := hs
  use (f t) * (g t)⁻¹
  refine ⟨by apply mul_ne_zero (hfn t ht) (by simpa using (hgn t ht)) , ?_⟩
  intro y hy
  have h2 := h hy
  rw [func_div] at h2
  have hderiv : EqOn (deriv (f * g⁻¹))  (deriv f * g⁻¹ - f * deriv g / g ^ 2) s := by
    have hfg : f * g⁻¹ = fun x => f x * (g⁻¹ x) := by rfl
    rw [hfg]
    intro z hz
    rw [deriv_mul]
    have hgi : g⁻¹ = (fun x => x⁻¹) ∘ g := by
      ext y
      simp only [Pi.inv_apply, comp_apply]
    rw [hgi, deriv_comp, deriv_inv]
    simp only [comp_apply, neg_mul, mul_neg, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring
    · refine differentiableAt_inv ?_
      exact hgn z hz
    · apply hg.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
    · exact hf.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
    · apply DifferentiableAt.inv
      exact hg.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
      exact hgn z hz
  have H3 := Convex.is_const_of_fderivWithin_eq_zero (f := f * g⁻¹) (𝕜 := ℂ) (s := s) ?_ ?_ ?_ hy ht
  simp only [Pi.mul_apply, Pi.inv_apply] at H3
  rw [← H3]
  field_simp [hgn y hy]
  · exact hsc
  · apply DifferentiableOn.mul
    exact hf
    apply DifferentiableOn.inv
    exact hg
    exact hgn
  have he : s.EqOn  (deriv f * g⁻¹ - f * deriv g / g ^ 2)  0 := by
    intro z hz
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply, Pi.zero_apply]
    have hgg : g z ≠ 0 := by apply hgn z hz
    field_simp
    rw [pow_two, mul_comm, mul_assoc, ← mul_sub]
    simp only [mul_eq_zero]
    right
    have H := h hz
    rw [func_div] at H
    simp only [Pi.mul_apply] at H
    rw [← H]
    ring
    exact hfn z hz
    exact hgn z hz
  intro v hv
  have H := h hv
  rw [func_div] at H
  have ha := hderiv hv
  have hb := he hv
  rw [hb] at ha
  simp only [Pi.zero_apply] at ha
  rw [fderivWithin_of_isOpen hs2 hv]
  exact Eq.symm (ContinuousLinearMap.ext_ring (_root_.id (Eq.symm ha)))
  exact  hfn v hv
  exact  hgn v hv
  exact  hfn y hy
  exact hgn y hy
  · intro h
    obtain ⟨z, hz0, hz⟩ := h
    intro x hx
    have h := hz hx
    simp_rw [logDeriv_apply]
    have HJ := deriv_EqOn_congr s hz hs2 hx
    rw [HJ, h]
    nth_rw 1 [show z • g = fun x => z • g x by rfl]
    rw [deriv_const_smul]
    simp
    rw [mul_div_mul_left (deriv g x) (g x) hz0]
    exact hg.differentiableAt (x := x) (IsOpen.mem_nhds hs2 hx)

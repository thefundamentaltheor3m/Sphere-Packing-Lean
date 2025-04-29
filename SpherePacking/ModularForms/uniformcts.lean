/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Data.Complex.Exponential

/-!
# Products of one plus a complex number

We gather some results about the uniform convergence of the product of `1 + f n x` for a
sequence `f n x` or complex numbers.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Classical Complex

variable {α β ι : Type*}

/--There is likely a way more general proof of this, what should it be? -/
lemma le_of_TendstoUniformlyOn_le_right (f : ι → α → ℝ) {p : Filter ι}
    {g : α → ℝ} {K : Set α} {T : ℝ} (hf : TendstoUniformlyOn f g p K) (hg : ∀ x : K, g x ≤ T) :
    ∀ᶠ (n : ι) in p, ∀ x : K, f n x ≤ (T + 1) := by
  rw [Metric.tendstoUniformlyOn_iff] at hf
  have hf2 := hf 1 (Real.zero_lt_one)
  simp_rw [Filter.eventually_iff_exists_mem, dist_comm ] at *
  obtain ⟨N, hN, hN2⟩ := hf2
  refine ⟨N, hN, fun n hn x => ?_⟩
  apply le_trans (tsub_le_iff_right.mp (le_trans (Real.le_norm_self _) (hN2 n hn x x.2).le))
  linarith [hg x]

variable [PseudoMetricSpace α]

lemma Metric.tendstouniformlyOn_iff_restrict [Preorder ι] {f : ι → β → α} {g : β → α} (K : Set β) :
    TendstoUniformlyOn f g atTop K ↔
    TendstoUniformly (fun n : ι => K.restrict (f n)) (K.restrict g) atTop := by
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, ←
    tendstoUniformlyOn_univ, Set.mem_univ, Set.restrict_apply, true_implies, Subtype.forall] at *

variable {α β ι : Type*}

lemma tendstoUniformlyOn_comp_cexp [Preorder ι] {f : ι → α → ℂ} {g : α → ℂ} {K : Set α}
    (hf : TendstoUniformlyOn f g atTop K) (hg : ∃ T : ℝ, ∀ x : K, (g x).re ≤ T) :
    TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) atTop K := by
  obtain ⟨T, hT⟩ := hg
  have h2 := le_of_TendstoUniformlyOn_le_right (fun n x => (f n x).re) hf.re hT
  have w2 := tendstoUniformlyOn_univ.mpr <| UniformContinuousOn.comp_tendstoUniformly_eventually
    {x : ℂ | x.re ≤ T + 1} (fun a => K.restrict (f (a))) (fun b => g b) (by simpa using h2) ?_
      (UniformContinuousOn.cexp (T + 1)) ((Metric.tendstouniformlyOn_iff_restrict K).mp hf)
  · rw [Metric.tendstouniformlyOn_iff_restrict, ← tendstoUniformlyOn_univ]
    exact w2
  · simp only [Set.mem_setOf_eq, Subtype.forall]
    apply fun a ha => le_trans (hT ⟨a,ha⟩) (by aesop)

lemma tendstoUniformlyOn_tprod {f : ℕ → α → ℂ} {K : Set α}
    (h : ∀ x : K, Summable fun n => log (f n x))
    (hf : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i ∈ Finset.range n, log (f i a))
    (fun a : α => ∑' n : ℕ, log (f n a)) atTop K) (hfn : ∀ x : K, ∀ n : ℕ, f n x ≠ 0)
    (hg : ∃ T : ℝ, ∀ x : K, (∑' n : ℕ, log (f n x)).re ≤ T) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (f i a))
    (fun a => ∏' i, (f i a)) atTop K := by
  suffices HU : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (f i a))
       (cexp ∘ fun a ↦ ∑' (n : ℕ), log (f n a)) atTop K by
        apply TendstoUniformlyOn.congr_right HU
        intro x hx
        simpa using (Complex.cexp_tsum_eq_tprod (hfn ⟨x, hx⟩) (h ⟨x, hx⟩))
  apply TendstoUniformlyOn.congr (tendstoUniformlyOn_comp_cexp hf hg)
  simp only [eventually_atTop, ge_iff_le]
  refine ⟨0, fun b _ x hx => ?_⟩
  simp only [Complex.exp_sum]
  congr
  ext y
  apply Complex.exp_log (hfn ⟨x, hx⟩ y)

/--This is the version for infinite products of with terms of the from `1 + f n x`. -/
lemma tendstoUniformlyOn_tprod' [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hfn : ∀ x : K, ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  apply tendstoUniformlyOn_tprod _ (tendstoUniformlyOn_tsum_nat_log_one_add K hu
    (Filter.Eventually.of_forall h)) hfn
  · have H : ContinuousOn (fun x ↦ (∑' (n : ℕ), Complex.log (1 + f n x)).re) K := by
      have := (tendstoUniformlyOn_tsum_nat_log_one_add K hu
        (Filter.Eventually.of_forall h)).re.continuousOn
      simp only [re_sum, eventually_atTop, ge_iff_le, forall_exists_index] at this
      apply this 0
      intro _ _
      apply continuousOn_finset_sum
      intro c _
      simp_rw [log_re]
      apply ContinuousOn.log
      · apply ContinuousOn.comp _ _ (Set.mapsTo_image (fun x ↦ 1 + f c x) K)
        · apply Continuous.continuousOn continuous_norm
        · apply (ContinuousOn.add continuousOn_const (hcts c))
      · intro z hz
        simp [ne_eq, map_eq_zero]
        apply hfn ⟨z, hz⟩ c
    have := IsCompact.bddAbove_image hK H
    simp only [ ne_eq, Subtype.forall, bddAbove_def, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
    obtain ⟨T, hT⟩ := this
    refine ⟨T, fun x hx => by aesop⟩
  · intro x
    apply Complex.summable_log_one_add_of_summable
    rw [← summable_norm_iff]
    apply Summable.of_nonneg_of_le (fun b ↦ norm_nonneg (f b ↑x)) (fun _ => h _ _ x.2) hu

/- variable {𝕜 𝕜': Type*} [NormedAddCommGroup 𝕜'] [CompleteSpace 𝕜'] [TopologicalSpace 𝕜]
  [LocallyCompactSpace 𝕜]

lemma SummableLocallyUniformlyOn.of_locally_bounded (f : ι → 𝕜 → 𝕜') {s : Set 𝕜} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : ι → ℝ, Summable u ∧ ∀ n (k : K), ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := (fun x => ∑' i, f i x))
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  apply tendstoUniformlyOn_tsum hu1 fun n x hx ↦ hu2 n ⟨x, hx⟩

/-This is just a test of the defns -/
theorem derivWithin_tsum {ι F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [LocallyCompactSpace E] [NormedField F] [NormedSpace E F] (f : ι → E → F) {s : Set E}
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n , f n z) s x = ∑' n, derivWithin (fun z ↦ f n z) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (IsOpen.uniqueDiffWithinAt hs hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ Summable.hasSum (hf y hy)) hx
  · use fun n : Finset ι ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun ⦃b⦄ hb ↦ Eq.symm (HasSumLocallyUniformlyOn.tsum_eqOn hg hb)
  · filter_upwards with t r hr
    apply HasDerivAt.sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · exact DifferentiableWithinAt.hasDerivWithinAt (hf2 q r hr).differentiableWithinAt
    · exact IsOpen.mem_nhds hs hr
 -/

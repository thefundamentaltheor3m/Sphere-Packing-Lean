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
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn
import Mathlib.Data.Complex.Exponential


/-!
# Products of one plus a complex number

We gather some results about the uniform convergence of the product of `1 + f n x` for a
sequence `f n x` or complex numbers.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Classical Complex

variable {α β ι : Type*}



/--This is the version for infinite products of with terms of the from `1 + f n x`. -/
lemma tendstoUniformlyOn_tprod' [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  apply HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
  apply Summable.hasProdUniformlyOn_nat_one_add hK hu ?_ hcts
  filter_upwards with n x hx using h n x hx
  simp


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

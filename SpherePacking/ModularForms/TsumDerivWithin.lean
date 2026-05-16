module
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

/-- A `HasDerivAt`-of-`tsum` lemma under a locally uniform summability bound. -/
public theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu : ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy => (hf y hy).hasSum) hx
    (f' := fun t : Finset α => fun a => ∑ i ∈ t, derivWithin (fun z => f i z) s a)
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    refine tendstoUniformlyOn_tsum hu1 ?_
    intro n x hx
    exact hu2 n ⟨x, hx⟩
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq =>
        ((hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt.hasDerivAt) (hs.mem_nhds hr))

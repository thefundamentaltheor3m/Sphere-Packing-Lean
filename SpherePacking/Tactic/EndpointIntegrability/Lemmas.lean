/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Integrability on an interval from integrability at its ends

A function is integrable on an interval if and only if it is locally integrable on the interval
and integrable at each end which is open or infinite, along `atBot`, `atTop`, `𝓝[>] a` or
`𝓝[<] b`. Mathlib states this for the intervals `Ici`, `Ioi`, `Iic`, `Iio` and for the whole
space. This file adds the bounded intervals `Ioo`, `Ioc` and `Ico`, and states all nine cases as
implications of the same shape: the local integrability first, then the condition at the lower
end, then the condition at the upper end, each only when the end is open or infinite.

It also adds the lemmas closing an end of an interval for a measure which is finite on compact
sets: a function integrable on `Ioc a b` is integrable on `Icc a b`, and so on.

Finally, for the measure `volume` on `ℝ`, it reduces the integrability and the strong
measurability at the ends `atBot`, `𝓝[>] a` and `𝓝[<] b` to those at `atTop` and `𝓝[>] 0`, by the
changes of variables `t ↦ -t`, `t ↦ a + t` and `t ↦ b - t`.

The same changes of variables reduce the boundedness `f =O[l] g` at these ends, for the
integrable factors of the tactic. A function bounded in norm by `b` on a set of a filter `l` is
`O(b)` along `l` (`Asymptotics.IsBigO.of_forall_mem_norm_le`): a pointwise bound near an end is an
asymptotic bound at that end.

For the majorant of an integrand with bounded terms, it adds
`MeasureTheory.integrableOn_of_forall_norm_le`, the integrability on a set of a function bounded
there by an integrable function, and bounds on the norms of negations, natural powers, quotients
and absolute values.

For the integrable factors of the tactic, it adds `MeasureTheory.IntegrableAtFilter.of_norm_le_mul`
and `MeasureTheory.LocallyIntegrableOn.of_norm_le_mul`: a function whose norm is bounded by the
product of a bounded, respectively continuous, function `H` and the norm of an integrable function
`G` is integrable at a filter, respectively locally integrable, if it is measurable; and the bounds
`‖f x‖ ≤ H x * ‖G x‖` along products, scalar multiplications, quotients, norms, absolute values
and casts, such as `norm_mul_le_mul_of_le_left`.

Finally, it states the definitions of the pointwise operations on functions of a real variable,
such as `f * g = fun x ↦ f x * g x`, with which the tactic unfolds them in the goal and in the
hypotheses.

These are the lemmas used by the `endpoint_integrability` tactic.

## Main statements

* `MeasureTheory.LocallyIntegrableOn.integrableOn_Icc` and its eight siblings: integrability on
  an interval from local integrability and integrability at the open or infinite ends, for the
  nine kinds of intervals.
* `MeasureTheory.integrableOn_Icc_of_integrableOn_Ioc` and its four siblings: closing the open
  ends of an interval.
* `MeasureTheory.integrableAtFilter_atBot_iff_comp_neg`,
  `MeasureTheory.integrableAtFilter_nhdsGT_iff_comp_add_left` and
  `MeasureTheory.integrableAtFilter_nhdsLT_iff_comp_sub_left`: the reduction of the integrability
  at an end to `atTop` or `𝓝[>] 0`.
* `StronglyMeasurableAtFilter.comp_neg`, `StronglyMeasurableAtFilter.comp_add_left` and
  `StronglyMeasurableAtFilter.comp_sub_left`: the same for the strong measurability, from
  `MeasurableEmbedding.stronglyMeasurableAtFilter_map_iff`.
* `Real.tendsto_add_left_nhdsGT_zero` and `Real.tendsto_sub_left_nhdsGT_zero`: the changes of
  variables tend to the ends, along which the hypotheses `f =O[l] g` are transported by
  `Asymptotics.IsBigO.comp_tendsto` (with Mathlib's `tendsto_neg_atTop_atBot` at `atBot`).
* `Asymptotics.isBigO_atBot_iff_comp_neg`, `Asymptotics.isBigO_nhdsGT_iff_comp_add_left` and
  `Asymptotics.isBigO_nhdsLT_iff_comp_sub_left`: the reduction of `f =O[l] g` to `atTop` or
  `𝓝[>] 0`.
* `MeasureTheory.IntegrableAtFilter.of_norm_le_mul` and
  `MeasureTheory.LocallyIntegrableOn.of_norm_le_mul`: integrability from an integrable factor.
-/

@[expose] public section

open Set Filter Topology

namespace MeasureTheory

section Decomposition

variable {X ε : Type*} [MeasurableSpace X] [TopologicalSpace X] [LinearOrder X]
  [CompactIccSpace X] [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace.PseudoMetrizableSpace ε] {f : X → ε} {μ : Measure X} {a b : X}

/-- A function locally integrable on `Icc a b` is integrable on `Icc a b`. -/
theorem LocallyIntegrableOn.integrableOn_Icc (hf : LocallyIntegrableOn f (Icc a b) μ) :
    IntegrableOn f (Icc a b) μ :=
  hf.integrableOn_isCompact isCompact_Icc

/-- A function locally integrable on `Ici a` and integrable at `atTop` is integrable on
`Ici a`. -/
theorem LocallyIntegrableOn.integrableOn_Ici (hf : LocallyIntegrableOn f (Ici a) μ)
    (hb : IntegrableAtFilter f atTop μ) : IntegrableOn f (Ici a) μ :=
  integrableOn_Ici_iff_integrableAtFilter_atTop.2 ⟨hb, hf⟩

/-- A function locally integrable on `Iic b` and integrable at `atBot` is integrable on
`Iic b`. -/
theorem LocallyIntegrableOn.integrableOn_Iic (hf : LocallyIntegrableOn f (Iic b) μ)
    (ha : IntegrableAtFilter f atBot μ) : IntegrableOn f (Iic b) μ :=
  integrableOn_Iic_iff_integrableAtFilter_atBot.2 ⟨ha, hf⟩

/-- A function locally integrable on `univ` and integrable at `atBot` and at `atTop` is
integrable on `univ`. -/
theorem LocallyIntegrableOn.integrableOn_univ {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] [TopologicalSpace.PseudoMetrizableSpace ε] {f : X → ε}
    (hf : LocallyIntegrableOn f univ μ) (ha : IntegrableAtFilter f atBot μ)
    (hb : IntegrableAtFilter f atTop μ) : IntegrableOn f univ μ :=
  MeasureTheory.integrableOn_univ.2 <| integrable_iff_integrableAtFilter_atBot_atTop.2
    ⟨⟨ha, hb⟩, locallyIntegrableOn_univ.1 hf⟩

variable [OrderTopology X]

/-- A function locally integrable on `Ioo a b` and integrable at `𝓝[>] a` and at `𝓝[<] b` is
integrable on `Ioo a b`. -/
theorem LocallyIntegrableOn.integrableOn_Ioo (hf : LocallyIntegrableOn f (Ioo a b) μ)
    (ha : IntegrableAtFilter f (𝓝[>] a) μ) (hb : IntegrableAtFilter f (𝓝[<] b) μ) :
    IntegrableOn f (Ioo a b) μ := by
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨s, hs, hfs⟩ := ha
    obtain ⟨t, ht, hft⟩ := hb
    obtain ⟨u, hu, hus⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hab).1 hs
    obtain ⟨l, hl, hlt⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hab).1 ht
    have hc : IntegrableOn f (Icc u l) μ := hf.integrableOn_compact_subset
      (fun x hx ↦ ⟨lt_of_lt_of_le hu hx.1, lt_of_le_of_lt hx.2 hl⟩) isCompact_Icc
    refine ((hfs.mono_set hus).union (hc.union (hft.mono_set hlt))).mono_set fun x hx ↦ ?_
    rcases lt_or_ge x u with hxu | hxu
    · exact Or.inl ⟨hx.1, hxu⟩
    rcases lt_or_ge l x with hxl | hxl
    · exact Or.inr (Or.inr ⟨hxl, hx.2⟩)
    · exact Or.inr (Or.inl ⟨hxu, hxl⟩)
  · rw [Ioo_eq_empty hab.not_gt]
    exact integrableOn_empty

/-- A function locally integrable on `Ioc a b` and integrable at `𝓝[>] a` is integrable on
`Ioc a b`. -/
theorem LocallyIntegrableOn.integrableOn_Ioc (hf : LocallyIntegrableOn f (Ioc a b) μ)
    (ha : IntegrableAtFilter f (𝓝[>] a) μ) : IntegrableOn f (Ioc a b) μ := by
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨s, hs, hfs⟩ := ha
    obtain ⟨u, hu, hus⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hab).1 hs
    have hc : IntegrableOn f (Icc u b) μ := hf.integrableOn_compact_subset
      (fun x hx ↦ ⟨lt_of_lt_of_le hu hx.1, hx.2⟩) isCompact_Icc
    refine ((hfs.mono_set hus).union hc).mono_set fun x hx ↦ ?_
    rcases lt_or_ge x u with hxu | hxu
    · exact Or.inl ⟨hx.1, hxu⟩
    · exact Or.inr ⟨hxu, hx.2⟩
  · rw [Ioc_eq_empty hab.not_gt]
    exact integrableOn_empty

/-- A function locally integrable on `Ico a b` and integrable at `𝓝[<] b` is integrable on
`Ico a b`. -/
theorem LocallyIntegrableOn.integrableOn_Ico (hf : LocallyIntegrableOn f (Ico a b) μ)
    (hb : IntegrableAtFilter f (𝓝[<] b) μ) : IntegrableOn f (Ico a b) μ := by
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨t, ht, hft⟩ := hb
    obtain ⟨l, hl, hlt⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hab).1 ht
    have hc : IntegrableOn f (Icc a l) μ := hf.integrableOn_compact_subset
      (fun x hx ↦ ⟨hx.1, lt_of_le_of_lt hx.2 hl⟩) isCompact_Icc
    refine (hc.union (hft.mono_set hlt)).mono_set fun x hx ↦ ?_
    rcases lt_or_ge l x with hxl | hxl
    · exact Or.inr ⟨hxl, hx.2⟩
    · exact Or.inl ⟨hx.1, hxl⟩
  · rw [Ico_eq_empty hab.not_gt]
    exact integrableOn_empty

/-- A function locally integrable on `Ioi a` and integrable at `𝓝[>] a` and at `atTop` is
integrable on `Ioi a`. -/
theorem LocallyIntegrableOn.integrableOn_Ioi [NoMaxOrder X]
    (hf : LocallyIntegrableOn f (Ioi a) μ) (ha : IntegrableAtFilter f (𝓝[>] a) μ)
    (hb : IntegrableAtFilter f atTop μ) : IntegrableOn f (Ioi a) μ :=
  integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.2 ⟨hb, ha, hf⟩

/-- A function locally integrable on `Iio b` and integrable at `atBot` and at `𝓝[<] b` is
integrable on `Iio b`. -/
theorem LocallyIntegrableOn.integrableOn_Iio [NoMinOrder X]
    (hf : LocallyIntegrableOn f (Iio b) μ) (ha : IntegrableAtFilter f atBot μ)
    (hb : IntegrableAtFilter f (𝓝[<] b) μ) : IntegrableOn f (Iio b) μ :=
  integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin.2 ⟨ha, hb, hf⟩

end Decomposition

section ClosingEnds

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [PartialOrder X]
  [MeasurableSingletonClass X] [NormedAddCommGroup E] {f : X → E} {μ : Measure X}
  [IsFiniteMeasureOnCompacts μ] {a b : X}

/-- A function integrable on `Ioc a b` is integrable on `Icc a b`, for a measure which is finite
on compact sets. -/
theorem integrableOn_Icc_of_integrableOn_Ioc (h : IntegrableOn f (Ioc a b) μ) :
    IntegrableOn f (Icc a b) μ :=
  (integrableOn_Icc_iff_integrableOn_Ioc' isCompact_singleton.measure_lt_top.ne
    eNorm_ne_top).2 h

/-- A function integrable on `Ico a b` is integrable on `Icc a b`, for a measure which is finite
on compact sets. -/
theorem integrableOn_Icc_of_integrableOn_Ico (h : IntegrableOn f (Ico a b) μ) :
    IntegrableOn f (Icc a b) μ :=
  (integrableOn_Icc_iff_integrableOn_Ico' isCompact_singleton.measure_lt_top.ne
    eNorm_ne_top).2 h

/-- A function integrable on `Ioo a b` is integrable on `Icc a b`, for a measure which is finite
on compact sets. -/
theorem integrableOn_Icc_of_integrableOn_Ioo (h : IntegrableOn f (Ioo a b) μ) :
    IntegrableOn f (Icc a b) μ :=
  (integrableOn_Icc_iff_integrableOn_Ioo' isCompact_singleton.measure_lt_top.ne eNorm_ne_top
    isCompact_singleton.measure_lt_top.ne eNorm_ne_top).2 h

/-- A function integrable on `Ioi a` is integrable on `Ici a`, for a measure which is finite on
compact sets. -/
theorem integrableOn_Ici_of_integrableOn_Ioi (h : IntegrableOn f (Ioi a) μ) :
    IntegrableOn f (Ici a) μ :=
  (integrableOn_Ici_iff_integrableOn_Ioi' isCompact_singleton.measure_lt_top.ne
    eNorm_ne_top).2 h

/-- A function integrable on `Iio b` is integrable on `Iic b`, for a measure which is finite on
compact sets. -/
theorem integrableOn_Iic_of_integrableOn_Iio (h : IntegrableOn f (Iio b) μ) :
    IntegrableOn f (Iic b) μ :=
  (integrableOn_Iic_iff_integrableOn_Iio' isCompact_singleton.measure_lt_top.ne
    eNorm_ne_top).2 h

end ClosingEnds

end MeasureTheory

section Reduction

/-! ### Reduction to the ends `atTop` and `𝓝[>] 0` -/

namespace Real

/-- The translation `t ↦ a + t` maps `𝓝[>] 0` to `𝓝[>] a`. -/
theorem map_add_left_nhdsGT_zero (a : ℝ) : map (a + ·) (𝓝[>] 0) = 𝓝[>] a := by
  have h := (Homeomorph.addLeft a).isEmbedding.map_nhdsWithin_eq (Ioi 0) 0
  simpa only [Homeomorph.coe_addLeft, image_const_add_Ioi, add_zero] using h

/-- The reflection `t ↦ b - t` maps `𝓝[>] 0` to `𝓝[<] b`. -/
theorem map_sub_left_nhdsGT_zero (b : ℝ) : map (b - ·) (𝓝[>] 0) = 𝓝[<] b := by
  have h := (Homeomorph.subLeft b).isEmbedding.map_nhdsWithin_eq (Ioi 0) 0
  simpa only [Homeomorph.coe_subLeft, image_const_sub_Ioi, sub_zero] using h

/-- The translation `t ↦ a + t` tends to `𝓝[>] a` along `𝓝[>] 0`. -/
theorem tendsto_add_left_nhdsGT_zero (a : ℝ) : Tendsto (fun t ↦ a + t) (𝓝[>] 0) (𝓝[>] a) :=
  (map_add_left_nhdsGT_zero a).le

/-- The reflection `t ↦ b - t` tends to `𝓝[<] b` along `𝓝[>] 0`. -/
theorem tendsto_sub_left_nhdsGT_zero (b : ℝ) : Tendsto (fun t ↦ b - t) (𝓝[>] 0) (𝓝[<] b) :=
  (map_sub_left_nhdsGT_zero b).le

end Real

open Real

/-- A function is strongly measurable at the image of a filter by a measurable embedding `e`, for
the image measure, if and only if its composition with `e` is strongly measurable at the
filter. -/
theorem MeasurableEmbedding.stronglyMeasurableAtFilter_map_iff {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace γ] {e : α → β}
    (he : MeasurableEmbedding e) {g : β → γ} {l : Filter α} {μ : MeasureTheory.Measure α} :
    StronglyMeasurableAtFilter g (l.map e) (μ.map e) ↔
      StronglyMeasurableAtFilter (g ∘ e) l μ := by
  simp_rw [StronglyMeasurableAtFilter, he.restrict_map,
    he.aestronglyMeasurable_map_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨e '' s, by rwa [mem_map, he.injective.preimage_image]⟩

namespace MeasureTheory

variable {ε : Type*} [TopologicalSpace ε] {f : ℝ → ε} {a b : ℝ}

/-- A function is integrable at `atBot` if and only if its composition with `t ↦ -t` is integrable
at `atTop`. -/
theorem integrableAtFilter_atBot_iff_comp_neg [ContinuousENorm ε] :
    IntegrableAtFilter f atBot ↔ IntegrableAtFilter (fun t ↦ f (-t)) atTop := by
  have h := measurableEmbedding_neg.integrableAtFilter_map_iff (f := f) (l := atTop)
    (μ := (volume : Measure ℝ))
  rwa [map_neg_atTop, Measure.map_neg_eq_self] at h

/-- A function is integrable at `𝓝[>] a` if and only if its composition with `t ↦ a + t` is
integrable at `𝓝[>] 0`. -/
theorem integrableAtFilter_nhdsGT_iff_comp_add_left [ContinuousENorm ε] :
    IntegrableAtFilter f (𝓝[>] a) ↔ IntegrableAtFilter (fun t ↦ f (a + t)) (𝓝[>] 0) := by
  have h := (measurableEmbedding_addLeft a).integrableAtFilter_map_iff (f := f) (l := 𝓝[>] 0)
    (μ := (volume : Measure ℝ))
  rwa [map_add_left_nhdsGT_zero, (measurePreserving_add_left volume a).map_eq] at h

/-- A function is integrable at `𝓝[<] b` if and only if its composition with `t ↦ b - t` is
integrable at `𝓝[>] 0`. -/
theorem integrableAtFilter_nhdsLT_iff_comp_sub_left [ContinuousENorm ε] :
    IntegrableAtFilter f (𝓝[<] b) ↔ IntegrableAtFilter (fun t ↦ f (b - t)) (𝓝[>] 0) := by
  have h := (Homeomorph.subLeft b).measurableEmbedding.integrableAtFilter_map_iff (f := f)
    (l := 𝓝[>] 0) (μ := (volume : Measure ℝ))
  rwa [Homeomorph.coe_subLeft, map_sub_left_nhdsGT_zero,
    (Measure.measurePreserving_sub_left volume b).map_eq] at h

/-- If `f` is strongly measurable at `atBot`, then `fun t ↦ f (-t)` is strongly measurable at
`atTop`. -/
theorem _root_.StronglyMeasurableAtFilter.comp_neg (hf : StronglyMeasurableAtFilter f atBot) :
    StronglyMeasurableAtFilter (fun t ↦ f (-t)) atTop := by
  rw [← map_neg_atTop, ← Measure.map_neg_eq_self volume] at hf
  exact measurableEmbedding_neg.stronglyMeasurableAtFilter_map_iff.1 hf

/-- If `f` is strongly measurable at `𝓝[>] a`, then `fun t ↦ f (a + t)` is strongly measurable at
`𝓝[>] 0`. -/
theorem _root_.StronglyMeasurableAtFilter.comp_add_left
    (hf : StronglyMeasurableAtFilter f (𝓝[>] a)) :
    StronglyMeasurableAtFilter (fun t ↦ f (a + t)) (𝓝[>] 0) := by
  rw [← map_add_left_nhdsGT_zero, ← (measurePreserving_add_left volume a).map_eq] at hf
  exact (measurableEmbedding_addLeft a).stronglyMeasurableAtFilter_map_iff.1 hf

/-- If `f` is strongly measurable at `𝓝[<] b`, then `fun t ↦ f (b - t)` is strongly measurable at
`𝓝[>] 0`. -/
theorem _root_.StronglyMeasurableAtFilter.comp_sub_left
    (hf : StronglyMeasurableAtFilter f (𝓝[<] b)) :
    StronglyMeasurableAtFilter (fun t ↦ f (b - t)) (𝓝[>] 0) := by
  rw [← map_sub_left_nhdsGT_zero, ← (Measure.measurePreserving_sub_left volume b).map_eq] at hf
  exact (Homeomorph.subLeft b).measurableEmbedding.stronglyMeasurableAtFilter_map_iff.1 hf

end MeasureTheory

namespace Asymptotics

variable {E F : Type*} [Norm E] [Norm F] {f : ℝ → E} {g : ℝ → F} {a b : ℝ}

/-- `f =O[atBot] g` if and only if `fun t ↦ f (-t)` is `O(fun t ↦ g (-t))` at `atTop`. -/
theorem isBigO_atBot_iff_comp_neg :
    f =O[atBot] g ↔ (fun t ↦ f (-t)) =O[atTop] fun t ↦ g (-t) := by
  rw [← map_neg_atTop, isBigO_map]
  rfl

/-- `f =O[𝓝[>] a] g` if and only if `fun t ↦ f (a + t)` is `O(fun t ↦ g (a + t))` at
`𝓝[>] 0`. -/
theorem isBigO_nhdsGT_iff_comp_add_left :
    f =O[𝓝[>] a] g ↔ (fun t ↦ f (a + t)) =O[𝓝[>] 0] fun t ↦ g (a + t) := by
  rw [← map_add_left_nhdsGT_zero, isBigO_map]
  rfl

/-- `f =O[𝓝[<] b] g` if and only if `fun t ↦ f (b - t)` is `O(fun t ↦ g (b - t))` at
`𝓝[>] 0`. -/
theorem isBigO_nhdsLT_iff_comp_sub_left :
    f =O[𝓝[<] b] g ↔ (fun t ↦ f (b - t)) =O[𝓝[>] 0] fun t ↦ g (b - t) := by
  rw [← map_sub_left_nhdsGT_zero, isBigO_map]
  rfl

/-- A function whose norm is bounded by `b` on a set of the filter `l` is `O(b)` along `l`. -/
theorem IsBigO.of_forall_mem_norm_le {l : Filter ℝ} {s : Set ℝ} {b : ℝ → ℝ} (hs : s ∈ l)
    (h : ∀ x ∈ s, ‖f x‖ ≤ b x) : f =O[l] b :=
  .of_bound 1 <| Filter.mem_of_superset hs fun x hx ↦ by
    rw [Set.mem_ofPred_eq, one_mul, Real.norm_eq_abs]
    exact (h x hx).trans (le_abs_self _)

/-- A function whose norm is bounded by `b` is `O(b)` along every filter. -/
theorem IsBigO.of_forall_norm_le {l : Filter ℝ} {b : ℝ → ℝ} (h : ∀ x, ‖f x‖ ≤ b x) :
    f =O[l] b :=
  .of_forall_mem_norm_le Filter.univ_mem fun x _ ↦ h x

/-- A real function whose absolute value is bounded by `b` on a set of the filter `l` is `O(b)`
along `l`. -/
theorem IsBigO.of_forall_mem_abs_le {l : Filter ℝ} {s : Set ℝ} {f b : ℝ → ℝ} (hs : s ∈ l)
    (h : ∀ x ∈ s, |f x| ≤ b x) : f =O[l] b :=
  .of_forall_mem_norm_le hs h

/-- A real function whose absolute value is bounded by `b` is `O(b)` along every filter. -/
theorem IsBigO.of_forall_abs_le {l : Filter ℝ} {f b : ℝ → ℝ} (h : ∀ x, |f x| ≤ b x) :
    f =O[l] b :=
  .of_forall_norm_le h

end Asymptotics

end Reduction

section Domination

/-! ### Domination by an integrable majorant -/

namespace MeasureTheory

/-- A function which is almost everywhere strongly measurable on a measurable set `s`, and whose
norm is bounded on `s` by a function integrable on `s`, is integrable on `s`. -/
theorem integrableOn_of_forall_norm_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {f : α → E} {M : α → ℝ} {s : Set α} {μ : Measure α} (hs : MeasurableSet s)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hM : IntegrableOn M s μ)
    (h : ∀ x ∈ s, ‖f x‖ ≤ M x) : IntegrableOn f s μ :=
  hM.mono' hf ((ae_restrict_iff' hs).2 (ae_of_all _ h))

end MeasureTheory

/-- A bound on the norm of `a` bounds the norm of `-a`. -/
theorem norm_neg_le_of_le {E : Type*} [SeminormedAddGroup E] {a : E} {r : ℝ} (h : ‖a‖ ≤ r) :
    ‖-a‖ ≤ r :=
  (norm_neg a).trans_le h

/-- A bound on the norm of `a` bounds the norm of `a ^ n`, in a normed ring whose unit has
norm `1`. -/
theorem norm_pow_le_pow_of_le {α : Type*} [SeminormedRing α] [NormOneClass α] {a : α} {r : ℝ}
    (h : ‖a‖ ≤ r) (n : ℕ) : ‖a ^ n‖ ≤ r ^ n :=
  (norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) h n)

/-- A bound on the norm of `a` bounds the norm of `a / b` by its product with `‖b⁻¹‖`. -/
theorem norm_div_le_mul_norm_inv_of_le {α : Type*} [NormedDivisionRing α] {a : α} {r : ℝ}
    (h : ‖a‖ ≤ r) (b : α) : ‖a / b‖ ≤ r * ‖b⁻¹‖ := by
  rw [div_eq_mul_inv]
  exact norm_mul_le_of_le h le_rfl

/-- A bound on the absolute value of a real number bounds its norm. -/
theorem Real.norm_le_of_abs_le {a r : ℝ} (h : |a| ≤ r) : ‖a‖ ≤ r :=
  (Real.norm_eq_abs a).trans_le h

end Domination

section Factor

/-! ### Integrable factors -/

namespace MeasureTheory

open Asymptotics

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : α → E} {G : α → F} {H : α → ℝ} {μ : Measure α} {l : Filter α}

/-- A function integrable on a set `s` of the filter `l` is integrable at `l`. -/
theorem IntegrableOn.integrableAtFilter {s : Set α} (h : IntegrableOn G s μ) (hs : s ∈ l) :
    IntegrableAtFilter G l μ :=
  ⟨s, hs, h⟩

/-- A function `f`, strongly measurable at `l`, whose norm is eventually bounded by the product of
a function `H` bounded at `l` and the norm of a function `G` integrable at `l`, is integrable at
`l`. -/
theorem IntegrableAtFilter.of_norm_le_mul [l.IsMeasurablyGenerated]
    (hG : IntegrableAtFilter G l μ) (hH : H =O[l] fun _ ↦ (1 : ℝ))
    (hf : StronglyMeasurableAtFilter f l μ) (hle : ∀ᶠ x in l, ‖f x‖ ≤ H x * ‖G x‖) :
    IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hH.bound
  refine (IsBigO.of_bound C ?_).integrableAtFilter hf hG
  filter_upwards [hC, hle] with x hC hle
  simp only [norm_one, mul_one] at hC
  exact hle.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hC) (norm_nonneg _))

/-- A function `f`, almost everywhere strongly measurable on a measurable set `s`, whose norm is
bounded on `s` by the product of a function `H` continuous on `s` and the norm of a function `G`
locally integrable on `s`, is locally integrable on `s`. -/
theorem LocallyIntegrableOn.of_norm_le_mul [TopologicalSpace α] [OpensMeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) (hG : LocallyIntegrableOn G s μ) (hH : ContinuousOn H s)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hle : ∀ x ∈ s, ‖f x‖ ≤ H x * ‖G x‖) :
    LocallyIntegrableOn f s μ := fun x hx ↦
  have := hs.nhdsWithin_isMeasurablyGenerated x
  (hG x hx).of_norm_le_mul ((hH x hx).tendsto.isBigO_one ℝ) ⟨s, self_mem_nhdsWithin, hf⟩
    (eventually_mem_nhdsWithin.mono hle)

end MeasureTheory

variable {R : Type*} [SeminormedRing R] {a b : R} {H r : ℝ}

/-- A bound `‖a‖ ≤ H * r` gives `‖a * b‖ ≤ H * ‖b‖ * r`. -/
theorem norm_mul_le_mul_of_le_left (h : ‖a‖ ≤ H * r) (b : R) : ‖a * b‖ ≤ H * ‖b‖ * r :=
  (norm_mul_le a b).trans <| by nlinarith [norm_nonneg b]

/-- A bound `‖a‖ ≤ r` gives `‖a * b‖ ≤ ‖b‖ * r`. -/
theorem norm_mul_le_of_le_left (h : ‖a‖ ≤ r) (b : R) : ‖a * b‖ ≤ ‖b‖ * r :=
  (norm_mul_le a b).trans <| by nlinarith [norm_nonneg b]

/-- A bound `‖b‖ ≤ H * r` gives `‖a * b‖ ≤ ‖a‖ * H * r`. -/
theorem norm_mul_le_mul_of_le_right (a : R) (h : ‖b‖ ≤ H * r) : ‖a * b‖ ≤ ‖a‖ * H * r :=
  (norm_mul_le a b).trans <| by nlinarith [norm_nonneg a]

/-- A bound `‖b‖ ≤ r` gives `‖a * b‖ ≤ ‖a‖ * r`. -/
theorem norm_mul_le_of_le_right (a : R) (h : ‖b‖ ≤ r) : ‖a * b‖ ≤ ‖a‖ * r :=
  (norm_mul_le a b).trans <| by nlinarith [norm_nonneg a]

section SMul

variable {𝕜 E : Type*} [SeminormedRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] {v : E}

/-- A bound `‖v‖ ≤ H * r` gives `‖c • v‖ ≤ ‖c‖ * H * r`. -/
theorem norm_smul_le_mul_of_le (c : 𝕜) (h : ‖v‖ ≤ H * r) : ‖c • v‖ ≤ ‖c‖ * H * r :=
  (norm_smul_le c v).trans <| by nlinarith [norm_nonneg c]

/-- A bound `‖v‖ ≤ r` gives `‖c • v‖ ≤ ‖c‖ * r`. -/
theorem norm_smul_le_of_le (c : 𝕜) (h : ‖v‖ ≤ r) : ‖c • v‖ ≤ ‖c‖ * r :=
  (norm_smul_le c v).trans <| by nlinarith [norm_nonneg c]

end SMul

section Div

variable {K : Type*} [NormedDivisionRing K] {a : K}

/-- A bound `‖a‖ ≤ H * r` gives `‖a / d‖ ≤ H * ‖d⁻¹‖ * r`. -/
theorem norm_div_le_mul_of_le (h : ‖a‖ ≤ H * r) (d : K) : ‖a / d‖ ≤ H * ‖d⁻¹‖ * r := by
  rw [div_eq_mul_inv]
  exact norm_mul_le_mul_of_le_left h _

/-- A bound `‖a‖ ≤ r` gives `‖a / d‖ ≤ ‖d⁻¹‖ * r`. -/
theorem norm_div_le_inv_mul_of_le (h : ‖a‖ ≤ r) (d : K) : ‖a / d‖ ≤ ‖d⁻¹‖ * r := by
  rw [div_eq_mul_inv]
  exact norm_mul_le_of_le_left h _

end Div

/-- A bound on the norm of `a` bounds the norm of `‖a‖`. -/
theorem norm_norm_le_of_le {E : Type*} [SeminormedAddCommGroup E] {a : E} (h : ‖a‖ ≤ r) :
    ‖‖a‖‖ ≤ r :=
  (norm_norm a).trans_le h

/-- A bound on the norm of a real number `a` bounds the norm of `|a|`. -/
theorem Real.norm_abs_le_of_le {a : ℝ} (h : ‖a‖ ≤ r) : ‖|a|‖ ≤ r := by
  rwa [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs]

/-- A bound on the norm of a real number `a` bounds the norm of its cast `(a : ℂ)`. -/
theorem Complex.norm_ofReal_le_of_le {a : ℝ} (h : ‖a‖ ≤ r) : ‖(a : ℂ)‖ ≤ r := by
  rwa [Complex.norm_real]

end Factor

section Pointwise

/-! ### Pointwise operations on functions of a real variable -/

namespace Mathlib.Tactic.EndpointIntegrability

variable {E F β : Type*}

/-! The operations on functions of a real variable are the pointwise ones. These are the
definitions of `Pi`, such as `Pi.mul_def`, for functions on `ℝ` and with the bound variable `x`,
which the tactic shows in its goals and messages: `endpoint_integrability` rewrites the goal and
the hypotheses with them (see `unfoldPointwise`). -/

theorem pointwise_mul [Mul E] (f g : ℝ → E) : f * g = fun x ↦ f x * g x := rfl

theorem pointwise_add [Add E] (f g : ℝ → E) : f + g = fun x ↦ f x + g x := rfl

theorem pointwise_sub [Sub E] (f g : ℝ → E) : f - g = fun x ↦ f x - g x := rfl

theorem pointwise_div [Div E] (f g : ℝ → E) : f / g = fun x ↦ f x / g x := rfl

theorem pointwise_neg [Neg E] (f : ℝ → E) : -f = fun x ↦ -f x := rfl

theorem pointwise_inv [Inv E] (f : ℝ → E) : f⁻¹ = fun x ↦ (f x)⁻¹ := rfl

theorem pointwise_pow [Pow E β] (f : ℝ → E) (n : β) : f ^ n = fun x ↦ f x ^ n := rfl

theorem pointwise_const_smul [SMul β E] (c : β) (f : ℝ → E) : c • f = fun x ↦ c • f x := rfl

theorem pointwise_smul [SMul E F] (f : ℝ → E) (g : ℝ → F) : f • g = fun x ↦ f x • g x := rfl

theorem pointwise_comp (f : β → E) (g : ℝ → β) : f ∘ g = fun x ↦ f (g x) := rfl

theorem pointwise_one [One E] : (1 : ℝ → E) = fun _ ↦ 1 := rfl

theorem pointwise_zero [Zero E] : (0 : ℝ → E) = fun _ ↦ 0 := rfl

end Mathlib.Tactic.EndpointIntegrability

end Pointwise

/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib

/-!
# Density of sets in metric space with a measure

We define a general notion of density of a set in a metric space with a measure.
This unifies the definitions of density used in packing problems
and natural density in combinatorics.

## Main definitions

* `MeasureTheory.lowerDensityAt μ s`, the lower density of a set w.r.t. measure `s`.
* `MeasureTheory.upperDensityAt μ s`, the upper density of a set w.r.t. measure `s`.

-/

@[expose] public section

universe u

open ENNReal Filter Set NNReal

namespace MeasureTheory

variable {X : Type u} [MeasurableSpace X] [PseudoEMetricSpace X]

noncomputable def densityQuotientAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) (r : ℝ≥0) :
    ℝ≥0∞ :=
  -- Critically, this depends on the `default` parameter infered by `Inhabited X`, so in theory
  -- different basepoints could lead to different densities.
  -- However, for all interesting cases upper/lower densities will not be affected by the basepoint,
  -- so we abuse the default parameter instead of defining a noisy `densityQuotientAt`.
  letI B := Metric.eball x r
  μ (s ∩ B) / μ (B)

noncomputable def lowerDensityAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) : ℝ≥0∞ :=
  liminf (densityQuotientAt μ s x) atTop

noncomputable def upperDensityAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) : ℝ≥0∞ :=
  limsup (densityQuotientAt μ s x) atTop

@[simp]
theorem densityQuotientAt_radius_zero (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    densityQuotientAt μ s x 0 = 0 := by
  simp [densityQuotientAt]

theorem lowerDensityAt_le_upperDensityAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    lowerDensityAt μ s x ≤ upperDensityAt μ s x :=
  liminf_le_limsup

theorem densityQuotientAt_le_one (μ : Measure X := by volume_tac) (s : Set X) (x : X) (r : ℝ≥0) :
    densityQuotientAt μ s x r ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · unfold densityQuotientAt
    apply ENNReal.div_le_of_le_mul'
    grw [mul_one, measure_mono inter_subset_right]

theorem upperDensityAt_le_one (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    upperDensityAt μ s x ≤ 1 := by
  unfold upperDensityAt
  apply le_trans Filter.limsup_le_iSup
  simp [densityQuotientAt_le_one]

theorem lowerDensityAt_le_one (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    lowerDensityAt μ s x ≤ 1 :=
  le_trans (lowerDensityAt_le_upperDensityAt μ s x) (upperDensityAt_le_one μ s x)

section

variable {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X]

--TODO: `ProperSpace` should work with `PseudoEMetricSpace`
theorem densityQuotientAt_univ [ProperSpace X] (μ : Measure X := by volume_tac) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (x : X) {r : ℝ≥0} (hr : 0 < r) :
    densityQuotientAt μ univ x r = 1 := by
  rw [densityQuotientAt, inf_of_le_right (subset_univ _)]
  apply ENNReal.div_self (Metric.measure_eball_pos μ x (by norm_cast; grind)).ne.symm
  rw [Metric.eball_coe]
  exact measure_ball_ne_top

@[simp]
theorem lowerDensityAt_univ [ProperSpace X] (μ : Measure X := by volume_tac) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (x : X) :
    lowerDensityAt μ univ x = 1 := by
  unfold lowerDensityAt
  apply Tendsto.liminf_eq <| tendsto_nhds_of_eventually_eq ?_
  exact eventually_atTop.mpr ⟨1, fun r hr ↦ densityQuotientAt_univ μ x (by linarith)⟩

@[simp]
theorem upperDensityAt_univ [ProperSpace X] (μ : Measure X := by volume_tac) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (x : X) :
    upperDensityAt μ univ x = 1 := by
  apply le_antisymm
  · exact upperDensityAt_le_one μ univ x
  · grw [← lowerDensityAt_univ μ x, lowerDensityAt_le_upperDensityAt μ univ x]

end

theorem densityQuotientAt_of_measure_zero (μ : Measure X := by volume_tac) {s : Set X} (x : X)
    (r : ℝ≥0) (hs : μ s = 0) :
    densityQuotientAt μ s x r = 0 := by
  simp [densityQuotientAt, measure_inter_null_of_null_left (Metric.eball x ↑r) hs]

theorem upperDensityAt_of_measure_zero (μ : Measure X := by volume_tac) {s : Set X} (x : X)
    (hs : μ s = 0) :
    upperDensityAt μ s x = 0 := by
  simp [upperDensityAt, limsup, limsSup, densityQuotientAt_of_measure_zero μ x (hs := hs)]

theorem lowerDensityAt_of_measure_zero (μ : Measure X := by volume_tac) {s : Set X} (x : X)
    (hs : μ s = 0) :
    lowerDensityAt μ s x = 0 :=
  le_antisymm (le_trans (lowerDensityAt_le_upperDensityAt μ s x)
    (upperDensityAt_of_measure_zero μ x hs).le) zero_le

@[simp]
lemma densityQuotientAt_empty (μ : Measure X := by volume_tac) (x : X) (r : ℝ≥0) :
    densityQuotientAt μ ∅ x r = 0 :=
  densityQuotientAt_of_measure_zero μ x r measure_empty

@[simp]
lemma upperDensityAt_empty (μ : Measure X := by volume_tac) (x : X) :
    upperDensityAt μ ∅ x = 0 :=
  upperDensityAt_of_measure_zero μ x measure_empty

@[simp]
lemma lowerDensityAt_empty (μ : Measure X := by volume_tac) (x : X) :
    lowerDensityAt μ ∅ x = 0 :=
  lowerDensityAt_of_measure_zero μ x measure_empty

@[gcongr]
theorem densityQuotientAt.mono (μ : Measure X := by volume_tac) (x : X) (r : ℝ≥0) {s t : Set X}
    (st : s ⊆ t) : densityQuotientAt μ s x r ≤ densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  gcongr

@[gcongr]
theorem lowerDensityAt.mono (μ : Measure X := by volume_tac) (x : X) {s t : Set X}
    (st : s ⊆ t) : lowerDensityAt μ s x ≤ lowerDensityAt μ t x := by
  unfold lowerDensityAt
  refine liminf_le_liminf ?_ ?_ ?_
  · filter_upwards with
    gcongr
  · exact BddBelow.isBoundedUnder_of_range (by simp)
  · exact IsBoundedUnder.isCoboundedUnder_ge isBounded_le_of_top

theorem densityQuotient_union [OpensMeasurableSpace X] (μ : Measure X := by volume_tac) (x : X)
    {s t : Set X} (r : ℝ≥0) (ht : MeasurableSet t) (st : Disjoint s t) :
    densityQuotientAt μ (s ∪ t) x r = densityQuotientAt μ s x r + densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  rw [union_inter_distrib_right, measure_union (by grind) (ht.inter measurableSet_eball),
    ENNReal.add_div]

section AI

theorem densityQuotientAt_union_le (μ : Measure X := by volume_tac) (x : X) (s t : Set X)
    (r : ℝ≥0) :
    densityQuotientAt μ (s ∪ t) x r ≤ densityQuotientAt μ s x r + densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  rw [union_inter_distrib_right, ← ENNReal.add_div]
  gcongr
  exact measure_union_le _ _

theorem _root_.ENNReal.le_liminf_add {ι : Type*} {f : Filter ι} (u v : ι → ℝ≥0∞) :
    liminf u f + liminf v f ≤ liminf (u + v) f := by
  rw [f.basis_sets.liminf_eq_iSup_iInf, f.basis_sets.liminf_eq_iSup_iInf]
  refine ENNReal.biSup_add_biSup_le' ⟨univ, univ_mem⟩ ⟨univ, univ_mem⟩ fun s hs t ht ↦ ?_
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hs, ht] with a has hat
  exact add_le_add (biInf_le u has) (biInf_le v hat)

/-- Version of `ENNReal.limsup_add_le` without the `CountableInterFilter` assumption. -/
theorem _root_.ENNReal.limsup_add_le' {ι : Type*} {f : Filter ι} (u v : ι → ℝ≥0∞) :
    limsup (u + v) f ≤ limsup u f + limsup v f := by
  rw [limsup_eq_iInf_iSup (u := u), limsup_eq_iInf_iSup (u := v)]
  simp only [iInf_subtype', ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun s ↦ le_iInf fun t ↦ ?_
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [s.property, t.property] with a has hat
  exact add_le_add (le_biSup u hat) (le_biSup v has)

/-- The lower density is superadditive on disjoint sets. -/
theorem lowerDensityAt_add_le_union [OpensMeasurableSpace X] (μ : Measure X := by volume_tac)
    (x : X) {s t : Set X} (ht : MeasurableSet t) (st : Disjoint s t) :
    lowerDensityAt μ s x + lowerDensityAt μ t x ≤ lowerDensityAt μ (s ∪ t) x := by
  unfold lowerDensityAt
  have h : densityQuotientAt μ (s ∪ t) x = densityQuotientAt μ s x + densityQuotientAt μ t x :=
    funext fun r ↦ densityQuotient_union μ x r ht st
  rw [h]
  exact ENNReal.le_liminf_add _ _

/-- The upper density is subadditive. -/
theorem upperDensityAt_union_le (μ : Measure X := by volume_tac) (x : X) (s t : Set X) :
    upperDensityAt μ (s ∪ t) x ≤ upperDensityAt μ s x + upperDensityAt μ t x := by
  unfold upperDensityAt
  refine le_trans (limsup_le_limsup ?_) (ENNReal.limsup_add_le' _ _)
  filter_upwards with r
  exact densityQuotientAt_union_le μ x s t r

end AI

/- Unfininshed
namespace IsFiniteMeasure

open Topology

variable (μ : Measure X := by volume_tac) [IsFiniteMeasure μ] (s : Set X)

lemma Tendsto.densityQuotientAt (μ : Measure X := by volume_tac) [IsFiniteMeasure μ]
    (s : Set X) (x : X) :
    Tendsto (densityQuotientAt μ s x) atTop (𝓝 (μ s / μ univ)) := by
  change Tendsto (fun (r : ℝ≥0) ↦
    (μ (s ∩ Metric.eball x r) / μ (Metric.eball x r))) atTop (𝓝 (μ s / μ univ))
  rcases eq_or_ne (μ s) 0 with hs | hs
  · apply tendsto_nhds_of_eventually_eq
    filter_upwards with r
    simp [hs, measure_inter_null_of_null_left (Metric.eball x r) hs]
  rcases eq_or_ne (μ univ) 0 with hu | hu
  ·
  apply ENNReal.Tendsto.div


  apply Filter.Tendsto.div (f := fun r ↦ μ (s ∩ Metric.ball x r))
  sorry

theorem lowerDensityAt_eq (μ : Measure X := by volume_tac) [IsFiniteMeasure μ] (s : Set X) (x : X) :
    lowerDensityAt μ s x = μ s / μ Set.univ :=
  (Tendsto.densityQuotientAt μ s x).liminf_eq

theorem upperDensityAt_eq (μ : Measure X := by volume_tac) [IsFiniteMeasure μ] (s : Set X) (x : X) :
    upperDensityAt μ s x = μ s / μ Set.univ :=
  (Tendsto.densityQuotientAt μ s x).limsup_eq

theorem lowerDensityAt_eq_upperDensityAt (μ : Measure X := by volume_tac) [IsFiniteMeasure μ]
    (s : Set X) {x y : X} :
    lowerDensityAt μ s x = upperDensityAt μ s y := by
  rw [lowerDensityAt_eq μ, upperDensityAt_eq μ]

end IsFiniteMeasure

-/

end MeasureTheory

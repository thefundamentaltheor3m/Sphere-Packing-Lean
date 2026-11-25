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

* `MeasureTheory.lowerDensity μ s`, the lower density of a set w.r.t. measure `s`.
* `MeasureTheory.upperDensity μ s`, the upper density of a set w.r.t. measure `s`.

-/

@[expose] public section

universe u

open ENNReal Filter

namespace MeasureTheory

variable {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] [Inhabited X]

noncomputable def densityQuotient (μ : Measure X := by volume_tac) (s : Set X) (r : ℝ) : ℝ≥0∞ :=
  -- Critically, this depends on the `default` parameter infered by `Inhabited X`, so in theory
  -- different basepoints could lead to different densities.
  -- However, for all interesting cases upper/lower densities will not be affected by the basepoint,
  -- so we abuse the default parameter instead of defining a noisy `densityQuotientAt`.
  letI B := Metric.ball default r
  μ (s ∩ B) / μ (B)

noncomputable def lowerDensity (μ : Measure X := by volume_tac) (s : Set X) : ℝ≥0∞ :=
  liminf (densityQuotient μ s) atTop

noncomputable def upperDensity (μ : Measure X := by volume_tac) (s : Set X) : ℝ≥0∞ :=
  limsup (densityQuotient μ s) atTop

theorem lowerDensity_le_upperDensity (μ : Measure X := by volume_tac) (s : Set X) :
    lowerDensity μ s ≤ upperDensity μ s :=
  liminf_le_limsup



end MeasureTheory

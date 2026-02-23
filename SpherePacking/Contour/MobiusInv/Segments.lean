module

public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Algebra.GroupWithZero

public import SpherePacking.Contour.MobiusInv.Basic
import SpherePacking.Contour.Segments

/-!
# Mobius inversion on segments

This file proves continuity of `SpherePacking.mobiusInv` along the two line segments
`-1 → -1 + I` and `-1 + I → I`.

These lemmas are used to form `Path.map'` images under `mobiusInv` in the permutation/contour-change
arguments.
-/

namespace SpherePacking

noncomputable section

open Complex

private lemma continuousOn_mobiusInv_segment_of_ne_zero (a b : ℂ)
    (segment_ne_zero : ∀ t : Set.Icc (0 : ℝ) 1, Path.segment a b t ≠ 0) :
    ContinuousOn mobiusInv (Set.range (Path.segment a b)) := by
  rintro _ ⟨t, rfl⟩
  simpa [mobiusInv] using (continuousAt_inv₀ (segment_ne_zero t)).neg.continuousWithinAt

/-- `mobiusInv` is continuous on the segment `-1 → -1 + I`. -/
public lemma continuousOn_mobiusInv_segment_z₁ :
    ContinuousOn mobiusInv
      (Set.range (Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I))) := by
  simpa using continuousOn_mobiusInv_segment_of_ne_zero (-1) (-1 + I) segment_z₁_ne_zero

/-- `mobiusInv` is continuous on the segment `-1 + I → I`. -/
public lemma continuousOn_mobiusInv_segment_z₂ :
    ContinuousOn mobiusInv
      (Set.range (Path.segment ((-1 : ℂ) + Complex.I) Complex.I)) := by
  simpa using continuousOn_mobiusInv_segment_of_ne_zero (-1 + I) I segment_z₂_ne_zero

/-! ### Canonical mapped paths -/

/-- The segment `-1 → -1 + I` mapped by `mobiusInv`, bundled as a path. -/
public abbrev mobiusInv_segment_z₁ :
    Path (mobiusInv (-1 : ℂ)) (mobiusInv ((-1 : ℂ) + Complex.I)) :=
  (Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I)).map'
    (f := mobiusInv)
    (by
      simpa using continuousOn_mobiusInv_segment_z₁)

/-- The segment `-1 + I → I` mapped by `mobiusInv`, bundled as a path. -/
public abbrev mobiusInv_segment_z₂ :
    Path (mobiusInv ((-1 : ℂ) + Complex.I)) (mobiusInv Complex.I) :=
  (Path.segment ((-1 : ℂ) + Complex.I) Complex.I).map'
    (f := mobiusInv)
    (by
      simpa using continuousOn_mobiusInv_segment_z₂)

end

end SpherePacking

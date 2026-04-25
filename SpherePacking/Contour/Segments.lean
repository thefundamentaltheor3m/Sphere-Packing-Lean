module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Basic
public import SpherePacking.MagicFunction.IntegralParametrisations

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Shared segment parametrisations for the `J₁/J₂` permutation developments

The dimension-specific `b`-eigenfunction developments use the same four vertical/horizontal
segments in the upper half-plane:

* `z₁line` : `-1 → -1 + I`
* `z₂line` : `-1 + I → I`
* `z₃line` : `1 → 1 + I`
* `z₄line` : `1 + I → I`

We centralize their definitions and basic continuity/imaginary-part facts here to avoid
duplicating boilerplate across developments.
-/

open Set
open scoped Interval Topology

namespace SpherePacking.Contour

noncomputable section

open MagicFunction.Parametrisations

/-- Parametrization of the segment `-1 → -1 + I` (for `t ∈ [0,1]`). -/
@[expose] public def z₁line (t : ℝ) : ℂ := (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)

/-- Parametrization of the segment `-1 + I → I` (for `t ∈ [0,1]`). -/
@[expose] public def z₂line (t : ℝ) : ℂ := (-1 : ℂ) + (t : ℂ) + Complex.I

/-- Parametrization of the segment `1 → 1 + I` (for `t ∈ [0,1]`). -/
@[expose] public def z₃line (t : ℝ) : ℂ := (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)

/-- Parametrization of the segment `1 + I → I` (for `t ∈ [0,1]`). -/
@[expose] public def z₄line (t : ℝ) : ℂ := (1 : ℂ) - (t : ℂ) + Complex.I

@[simp] public lemma z₁line_def (t : ℝ) :
    z₁line t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := rfl

@[simp] public lemma z₂line_def (t : ℝ) : z₂line t = (-1 : ℂ) + (t : ℂ) + Complex.I := rfl

@[simp] public lemma z₃line_def (t : ℝ) :
    z₃line t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := rfl

@[simp] public lemma z₄line_def (t : ℝ) : z₄line t = (1 : ℂ) - (t : ℂ) + Complex.I := rfl

public lemma continuous_z₁line : Continuous z₁line := by
  simpa [z₁line] using (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))

public lemma continuous_z₂line : Continuous z₂line := by
  simpa [z₂line] using (continuous_const.add Complex.continuous_ofReal).add continuous_const

public lemma z₁line_im (t : ℝ) : (z₁line t).im = t := by simp [z₁line]

@[simp] public lemma z₂line_im (t : ℝ) : (z₂line t).im = 1 := by simp [z₂line, add_assoc]

@[simp] public lemma z₄line_im (t : ℝ) : (z₄line t).im = 1 := by
  simp [z₄line, sub_eq_add_neg, add_assoc]

public lemma z₁line_im_pos_Ioc {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < (z₁line t).im := by
  simpa [z₁line_im t] using ht.1

/-! ### `AffineMap.lineMap` descriptions of the `zⱼline` segments -/

public lemma lineMap_z₁line (t : ℝ) :
    AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t = z₁line t := by
  simp [AffineMap.lineMap_apply_module', Algebra.smul_def, z₁line, add_comm, mul_comm]

public lemma lineMap_z₂line (t : ℝ) :
    AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t = z₂line t := by
  simp [AffineMap.lineMap_apply_module', Algebra.smul_def, z₂line, add_left_comm, add_comm]

public lemma lineMap_z₃line (t : ℝ) :
    AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) t = z₃line t := by
  simp [AffineMap.lineMap_apply_module', Algebra.smul_def, z₃line, add_comm, mul_comm]

public lemma lineMap_z₄line (t : ℝ) :
    AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I t = z₄line t := by
  simp [AffineMap.lineMap_apply_module', Algebra.smul_def, z₄line, sub_eq_add_neg, add_left_comm,
    add_comm]

public lemma dir_z₁line :
    ((-1 : ℂ) + Complex.I) - (-1 : ℂ) = (Complex.I : ℂ) := by ring

public lemma dir_z₂line : Complex.I - ((-1 : ℂ) + Complex.I) = (1 : ℂ) := by ring

/-! ### Matching `MagicFunction.Parametrisations.zⱼ'` with `zⱼline` on `[0,1]` -/

public lemma z₁'_eq_z₁line (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z₁' t = z₁line t := by
  simpa [z₁line, mul_assoc, mul_left_comm, mul_comm] using (z₁'_eq_of_mem (t := t) ht)

public lemma z₂'_eq_z₂line (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z₂' t = z₂line t := by
  simpa [z₂line, add_assoc] using (z₂'_eq_of_mem (t := t) ht)

/-! ### `AffineMap.lineMap` equals `zⱼ'` on `[0,1]` -/

public lemma lineMap_z₁_eq_z₁' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t = z₁' t :=
  (lineMap_z₁line t).trans (z₁'_eq_z₁line t ht).symm

public lemma lineMap_z₂_eq_z₂' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t = z₂' t :=
  (lineMap_z₂line t).trans (z₂'_eq_z₂line t ht).symm

public lemma lineMap_z₃_eq_z₃' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) t = z₃' t := by
  simpa [z₃line, lineMap_z₃line (t := t), mul_assoc, mul_left_comm, mul_comm]
    using (z₃'_eq_of_mem (t := t) ht).symm

public lemma lineMap_z₄_eq_z₄' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I t = z₄' t := by
  simpa [z₄line, lineMap_z₄line (t := t), sub_eq_add_neg, add_assoc]
    using (z₄'_eq_of_mem (t := t) ht).symm

/-! ### Convenience lemmas for the left-side segments -/

@[simp] public lemma z₁line_add_one (t : ℝ) : z₁line t + 1 = (Complex.I : ℂ) * (t : ℂ) := by
  simp [z₁line, add_left_comm, add_comm]

@[simp] public lemma z₂line_add_one (t : ℝ) : z₂line t + 1 = (t : ℂ) + Complex.I := by
  simp [z₂line, add_left_comm, add_comm]

end

end SpherePacking.Contour

/-!
### Non-vanishing facts for the left-side segments

Several contour-change arguments require that the two left-side segments avoid `0` so that
`mobiusInv z = -z⁻¹` is well-defined.
These lemmas used to live in `SpherePacking/Contour/Segments.lean`; we keep them here to reduce
file count.
-/

namespace SpherePacking

open Complex Real Set
open scoped Interval

noncomputable section

public lemma segment_z₁_ne_zero (t : Set.Icc (0 : ℝ) 1) :
    (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) (t : ℝ)) ≠ 0 := fun hz =>
  by simpa [Contour.lineMap_z₁line, Contour.z₁line] using congrArg Complex.re hz

public lemma segment_z₂_ne_zero (t : Set.Icc (0 : ℝ) 1) :
    (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I (t : ℝ)) ≠ 0 := fun hz =>
  by simpa [Contour.lineMap_z₂line, Contour.z₂line] using congrArg Complex.im hz

end

end SpherePacking

/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.MagicFunction.a.Phi

import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.Tactic.ComplexGrind

/-!
# Cusp-Approaching Path Continuity

Helpers for cusp-approaching paths, specifically continuity of φ₀ along paths approaching i∞.

## Main results

- `continuousOn_φ₀''_cusp_path`: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞)
-/

@[expose] public section

open MeasureTheory Complex Real Set MagicFunction.a.ComplexIntegrands
open scoped ComplexGrind

noncomputable section

/-- ContinuousOn for the cusp-approaching path: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞).
Since -1/(I*t) = I/t and Im(I/t) = 1/t > 0 for t > 0, this factors through φ₀_continuous. -/
lemma continuousOn_φ₀''_cusp_path :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / (I * t))) (Set.Ioi 0) :=
  φ₀''_holo.continuousOn.comp (by fun_prop (disch := grind))
    (fun t ht => by simpa [div_mul_eq_div_div] using mem_Ioi.mp ht)

end

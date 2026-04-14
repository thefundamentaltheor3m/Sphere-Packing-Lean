/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

@[expose] public section

/-!
# Cusp-Approaching Path Continuity

Helpers for cusp-approaching paths, specifically continuity of φ₀ along paths approaching i∞.

## Main results

- `continuousOn_φ₀''_cusp_path`: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞)
-/

open MeasureTheory Complex Real Set MagicFunction.a.ComplexIntegrands

noncomputable section

/-- ContinuousOn for the cusp-approaching path: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞).
Since -1/(I*t) = I/t and Im(I/t) = 1/t > 0 for t > 0, this factors through φ₀_continuous. -/
lemma continuousOn_φ₀''_cusp_path :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / (I * t))) (Set.Ioi 0) := by
  have h_im_pos : ∀ t : ℝ, 0 < t → 0 < ((-1 : ℂ) / (I * t)).im := fun t ht => by
    rw [div_mul_eq_div_div, show (-1 : ℂ) / I = I from by norm_num1]
    simp only [div_ofReal_im, I_im, one_div]; positivity
  exact φ₀''_holo.continuousOn.comp
    (continuousOn_const.div (continuousOn_const.mul continuous_ofReal.continuousOn)
      (fun t ht => mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht))))
    (fun t ht => h_im_pos t ht)

end

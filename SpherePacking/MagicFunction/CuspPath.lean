/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

/-!
# Cusp-Approaching Path Continuity

Helpers for cusp-approaching paths, specifically continuity of φ₀ along paths approaching i∞.

## Main results

- `neg_one_div_I_mul`: Identity -1/(I*t) = I/t for t ≠ 0
- `continuousOn_φ₀''_cusp_path`: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞)
-/

open MeasureTheory Complex Real Set MagicFunction.a.ComplexIntegrands

noncomputable section

/-- Key identity: -1/(I*t) = I/t for t ≠ 0 -/
lemma neg_one_div_I_mul (t : ℝ) (ht : t ≠ 0) : (-1 : ℂ) / (I * t) = I / t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  field_simp [mul_ne_zero Complex.I_ne_zero ht', ht']
  simp

/-- ContinuousOn for the cusp-approaching path: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞).
Since -1/(I*t) = I/t and Im(I/t) = 1/t > 0 for t > 0, this factors through φ₀_continuous. -/
lemma continuousOn_φ₀''_cusp_path :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / (I * t))) (Set.Ioi 0) := by
  have h_im_pos : ∀ t : ℝ, 0 < t → 0 < ((-1 : ℂ) / (I * t)).im := fun t ht => by
    rw [neg_one_div_I_mul t (ne_of_gt ht)]
    simp only [div_ofReal_im, I_im, one_div]; positivity
  -- The path t ↦ ⟨-1/(I*t), _⟩ factorizes through UpperHalfPlane
  let path : {s : ℝ // 0 < s} → UpperHalfPlane := fun s => ⟨-1 / (I * s), h_im_pos s s.2⟩
  have h_path_cont : Continuous path := by
    refine Continuous.subtype_mk ?_ _
    apply Continuous.div continuous_const
    · exact continuous_const.mul (continuous_ofReal.comp continuous_subtype_val)
    · intro ⟨s, hs⟩
      simp only [ne_eq, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
      exact ne_of_gt hs
  have h_comp_cont : Continuous (φ₀ ∘ path) := φ₀_continuous.comp h_path_cont
  intro t ht
  rw [Set.mem_Ioi] at ht
  have h_eq : φ₀'' (-1 / (I * t)) = φ₀ (path ⟨t, ht⟩) := by
    rw [φ₀''_def (h_im_pos t ht)]
  rw [ContinuousWithinAt, h_eq]
  have h_at : ContinuousAt (φ₀ ∘ path) ⟨t, ht⟩ := h_comp_cont.continuousAt
  have h_map_eq : Filter.map (Subtype.val : {s : ℝ // 0 < s} → ℝ) (nhds ⟨t, ht⟩) =
      nhdsWithin t (Set.Ioi 0) := by convert map_nhds_subtype_val ⟨t, ht⟩
  rw [← h_map_eq, Filter.tendsto_map'_iff]
  convert h_at.tendsto using 1
  funext x
  simp [φ₀''_def (h_im_pos x.val x.prop), path]

end

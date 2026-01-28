/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.ModularForms.Derivative

/-!
# Cusp-Approaching Path Continuity

This file provides minimal helpers for cusp-approaching paths, specifically the
continuity of φ₀ along paths approaching the cusp at i∞.

These lemmas are extracted from `Segments.lean` for use by `ContourEndpoints.lean`
to prove vertical ray integrability without importing the full segment machinery.

## Main results

- `φ₀''_eq`: Unfolds φ₀'' to φ₀ when imaginary part is positive
- `neg_one_div_I_mul`: Key identity -1/(I*t) = I/t for t ≠ 0
- `φ₀_continuous`: φ₀ : ℍ → ℂ is continuous
- `continuousOn_φ₀''_cusp_path`: t ↦ φ₀''(-1/(I*t)) is continuous on (0, ∞)
-/

open MeasureTheory Complex Real Set

noncomputable section

/-- Unfold φ₀'' to φ₀ when the imaginary part is positive. -/
lemma φ₀''_eq (z : ℂ) (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩ := by
  simp only [φ₀'', hz, dite_true]

/-- Key identity: -1/(I*t) = I/t for t ≠ 0 -/
lemma neg_one_div_I_mul (t : ℝ) (ht : t ≠ 0) : (-1 : ℂ) / (I * t) = I / t := by
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  have hIt : (I : ℂ) * t ≠ 0 := mul_ne_zero hI ht'
  field_simp [hIt, ht']
  ring_nf
  simp only [Complex.I_sq]

/-- φ₀ : ℍ → ℂ is continuous.
Follows from continuity of E₂, E₄, E₆, Δ (via their MDifferentiability) and Δ ≠ 0. -/
lemma φ₀_continuous : Continuous φ₀ := by
  unfold φ₀
  have hE₂ : Continuous E₂ := MDifferentiable.continuous E₂_holo'
  have hE₄ : Continuous (fun z : UpperHalfPlane => E₄ z) := MDifferentiable.continuous E₄.holo'
  have hE₆ : Continuous (fun z : UpperHalfPlane => E₆ z) := MDifferentiable.continuous E₆.holo'
  have hΔ : Continuous (fun z : UpperHalfPlane => Δ z) := MDifferentiable.continuous Delta.holo'
  have h24 : Continuous (fun z : UpperHalfPlane => E₂ z * E₄ z) := hE₂.mul hE₄
  have h246 : Continuous (fun z : UpperHalfPlane => E₂ z * E₄ z - E₆ z) := h24.sub hE₆
  have h_sq : Continuous (fun z : UpperHalfPlane => (E₂ z * E₄ z - E₆ z)^2) := h246.pow 2
  exact Continuous.div h_sq hΔ (fun z => Δ_ne_zero z)

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
  -- Transfer to ContinuousOn via the homeomorphism
  intro t ht
  rw [Set.mem_Ioi] at ht
  have h_eq : φ₀'' (-1 / (I * t)) = φ₀ (path ⟨t, ht⟩) := by
    rw [φ₀''_eq _ (h_im_pos t ht)]
  rw [ContinuousWithinAt, h_eq]
  have h_at : ContinuousAt (φ₀ ∘ path) ⟨t, ht⟩ := h_comp_cont.continuousAt
  have h_map_eq : Filter.map (Subtype.val : {s : ℝ // 0 < s} → ℝ) (nhds ⟨t, ht⟩) =
      nhdsWithin t (Set.Ioi 0) := by convert map_nhds_subtype_val ⟨t, ht⟩
  rw [← h_map_eq, Filter.tendsto_map'_iff]
  convert h_at.tendsto using 1
  funext x
  simp only [Function.comp_apply, φ₀''_eq _ (h_im_pos x.val x.prop), path]

end

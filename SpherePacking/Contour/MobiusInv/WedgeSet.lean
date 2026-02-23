module

public import SpherePacking.Basic.Domains.WedgeSet
import SpherePacking.Contour.Segments
public import SpherePacking.Contour.MobiusInv.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mobius inversion preserves `wedgeSet` on two segments

This file proves membership of `mobiusInv` along the two line segments
`-1 → -1 + I` and `-1 + I → I` in the wedge domain `wedgeSet`.

These lemmas are used in the contour deformation developments (I12/J12 variants) to keep affine
homotopies inside `wedgeSet`.
-/

namespace SpherePacking

noncomputable section

private lemma mobiusInv_re_im (x y : ℝ) :
    (-( ((x : ℂ) + Complex.I * (y : ℂ)) )⁻¹ : ℂ).re = (-x) / (x ^ 2 + y ^ 2) ∧
      (-( ((x : ℂ) + Complex.I * (y : ℂ)) )⁻¹ : ℂ).im = y / (x ^ 2 + y ^ 2) := by
  constructor <;>
    simp [Complex.inv_re, Complex.inv_im, Complex.normSq, pow_two, neg_div]

/-- Along `-1 → -1 + I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₁_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t) ∈ wedgeSet := by
  simpa [SpherePacking.Contour.lineMap_z₁line (t := t)] using
    (show mobiusInv (SpherePacking.Contour.z₁line t) ∈ wedgeSet from by
      have hdenom : 0 < (1 + t ^ 2 : ℝ) := by nlinarith [sq_nonneg t]
      have hre : (mobiusInv (SpherePacking.Contour.z₁line t)).re = 1 / (1 + t ^ 2) := by
        simpa [SpherePacking.Contour.z₁line, mobiusInv, pow_two, add_assoc, add_comm,
          add_left_comm] using (mobiusInv_re_im (-1) t).1
      have him : (mobiusInv (SpherePacking.Contour.z₁line t)).im = t / (1 + t ^ 2) := by
        simpa [SpherePacking.Contour.z₁line, mobiusInv, pow_two, add_assoc, add_comm,
          add_left_comm] using (mobiusInv_re_im (-1) t).2
      refine (wedgeSet_iff (z := mobiusInv (SpherePacking.Contour.z₁line t))).2 ?_
      refine ⟨?_, ?_, ?_⟩
      · rw [him]
        exact div_pos ht0 hdenom
      · rw [hre, him]
        field_simp [hdenom.ne']
        nlinarith [ht0]
      · rw [hre, him]
        field_simp [hdenom.ne']
        nlinarith [ht0, ht1])

/-- Along `-1 + I → I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₂_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t) ∈ wedgeSet := by
  simpa [SpherePacking.Contour.lineMap_z₂line (t := t)] using
    (show mobiusInv (SpherePacking.Contour.z₂line t) ∈ wedgeSet from by
      set x : ℝ := t - 1
      have hdenom : 0 < (x ^ 2 + 1 : ℝ) := by nlinarith [sq_nonneg x]
      have hre : (mobiusInv (SpherePacking.Contour.z₂line t)).re = (1 - t) / (x ^ 2 + 1) := by
        have : (mobiusInv ((x : ℂ) + Complex.I * (1 : ℂ))).re = (-x) / (x ^ 2 + 1) := by
          simpa [mobiusInv, pow_two] using (mobiusInv_re_im x 1).1
        simpa [SpherePacking.Contour.z₂line, x, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm] using this
      have him : (mobiusInv (SpherePacking.Contour.z₂line t)).im = 1 / (x ^ 2 + 1) := by
        have : (mobiusInv ((x : ℂ) + Complex.I * (1 : ℂ))).im = 1 / (x ^ 2 + 1) := by
          simpa [mobiusInv, pow_two] using (mobiusInv_re_im x 1).2
        simpa [SpherePacking.Contour.z₂line, x, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm] using this
      refine (wedgeSet_iff (z := mobiusInv (SpherePacking.Contour.z₂line t))).2 ?_
      refine ⟨?_, ?_, ?_⟩
      · rw [him]
        exact (one_div_pos.2 hdenom)
      · rw [hre, him]
        field_simp [hdenom.ne']
        nlinarith [x]
      · rw [hre, him]
        field_simp [hdenom.ne']
        nlinarith [ht0, ht1, x])

end

end SpherePacking

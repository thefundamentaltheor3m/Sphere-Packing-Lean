module

public import SpherePacking.Basic.Domains.WedgeSet
import SpherePacking.Contour.Segments
public import SpherePacking.Contour.MobiusInv.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mobius inversion preserves `wedgeSet` on two segments

These lemmas show that `mobiusInv` maps the segments `-1 → -1 + I` and `-1 + I → I` into `wedgeSet`,
used in the contour deformation developments (I12/J12 variants).
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
  rw [Contour.lineMap_z₁line]
  obtain ⟨hre, him⟩ := mobiusInv_re_im (-1) t
  rw [show mobiusInv (Contour.z₁line t) = -(↑(-1 : ℝ) + Complex.I * ↑t)⁻¹ from by
    simp [mobiusInv]] at *
  refine wedgeSet_iff.mpr ⟨by rw [him]; positivity, ?_⟩
  rw [hre, him]; simp only [fieldLt]
  constructor <;> nlinarith only [ht0, ht1]

/-- Along `-1 + I → I`, the Mobius inversion map lands in `wedgeSet`. -/
public lemma mobiusInv_lineMap_z₂_mem_wedgeSet
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mobiusInv (AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t) ∈ wedgeSet := by
  rw [Contour.lineMap_z₂line]
  obtain ⟨hre, him⟩ := mobiusInv_re_im (t - 1) 1
  rw [show mobiusInv (Contour.z₂line t) = -(↑(t - 1) + Complex.I * ↑(1 : ℝ))⁻¹ from by
    simp [sub_eq_add_neg, add_comm, mobiusInv], one_pow] at *
  refine wedgeSet_iff.mpr ⟨by rw [him]; positivity, ?_⟩
  rw [hre, him]; simp only [fieldLt]
  constructor <;> nlinarith only [ht0, ht1]

end

end SpherePacking

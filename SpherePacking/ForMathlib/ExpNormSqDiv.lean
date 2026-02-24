module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Continuity of a Gaussian kernel term

This file proves continuity of the map
`(x, t) ↦ cexp ((-π) * (‖x‖ ^ 2) / t)` on `univ ×ˢ Ici 1`.
-/

namespace SpherePacking.ForMathlib

open Complex Real Set

/-- Continuity on `univ ×ˢ Ici 1` of the Gaussian kernel term `(x, t) ↦ exp (-π * ‖x‖^2 / t)`. -/
public lemma continuousOn_exp_norm_sq_div
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousOn
      (fun p : E × ℝ ↦ cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ)))
      (univ ×ˢ Ici (1 : ℝ)) := by
  intro p hp
  have hp1 : (1 : ℝ) ≤ p.2 := by simpa [Set.mem_prod, Set.mem_univ, true_and] using hp
  have hp2 : (p.2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hp1))
  exact
    (ContinuousAt.div
        (continuousAt_const.mul
          ((Complex.continuous_ofReal.comp continuous_fst.norm).pow 2).continuousAt)
        ((Complex.continuous_ofReal).continuousAt.comp continuous_snd.continuousAt) hp2).cexp
      |>.continuousWithinAt

end SpherePacking.ForMathlib

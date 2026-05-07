module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Continuity of `(x, t) ↦ cexp ((-π) * ‖x‖^2 / t)` on `univ ×ˢ Ici 1`.
-/

namespace SpherePacking.ForMathlib

open Complex Real Set

/-- Continuity on `univ ×ˢ Ici 1` of the Gaussian kernel term `(x, t) ↦ exp (-π * ‖x‖^2 / t)`. -/
public lemma continuousOn_exp_norm_sq_div
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousOn
      (fun p : E × ℝ ↦ cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ)))
      (univ ×ˢ Ici (1 : ℝ)) := fun p hp ↦ by
  have hp2 : (p.2 : ℂ) ≠ 0 := mod_cast (zero_lt_one.trans_le (by simpa using hp)).ne'
  fun_prop (disch := exact hp2)

end SpherePacking.ForMathlib

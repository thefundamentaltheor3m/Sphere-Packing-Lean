module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IneqCommon
import SpherePacking.ModularForms.FG.Inequalities


/-!
# Inequality `B`

This file proves the sign condition `B(t) > 0` for all `t > 0`, corresponding to
Proposition `prop:ineqB` in `blueprint/src/subsections/modform-ineq.tex`.

## Main statements
* `MagicFunction.g.CohnElkies.B_pos`: positivity of `B` on `(0, ∞)`.
-/

namespace MagicFunction.g.CohnElkies

open Real Complex
open scoped UpperHalfPlane

/-- Positivity of the auxiliary function `B` on `(0, ∞)`. -/
public theorem B_pos {t : ℝ} (ht : 0 < t) : 0 < B t := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hΔpos : 0 < (Δ.resToImagAxis s).re := (Delta_imag_axis_pos).2 s hs
  have hB :
      B t = (-(t ^ (2 : ℕ))) * ((FReal s - c * GReal s) / (Δ.resToImagAxis s).re) := by
    simpa [s] using (B_eq_neg_mul_FG_div_Delta (t := t) ht)
  have hFG : FReal s - c * GReal s < 0 := by
    simpa [c] using (FG_inequality_2 (t := s) hs)
  have ht2 : 0 < t ^ (2 : ℕ) := pow_pos ht _
  have : 0 < (-(t ^ (2 : ℕ))) * ((FReal s - c * GReal s) / (Δ.resToImagAxis s).re) :=
    mul_pos_of_neg_of_neg (neg_lt_zero.2 ht2) (div_neg_of_neg_of_pos hFG hΔpos)
  simpa [hB] using this

end MagicFunction.g.CohnElkies

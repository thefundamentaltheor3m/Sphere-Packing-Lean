module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IneqCommon
import SpherePacking.ModularForms.FG.Inequalities

/-!
# Inequality `A(t) < 0`

Blueprint proposition `prop:ineqA` (see `blueprint/src/subsections/modform-ineq.tex`):
`A t < 0` for all `t > 0`.
-/

namespace MagicFunction.g.CohnElkies

open Real Complex

/-- For all `t > 0`, the auxiliary function `A t` is negative. -/
public theorem A_neg {t : ℝ} (ht : 0 < t) : A t < 0 := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hA : A t = (-(t ^ (2 : ℕ))) *
      ((FReal s + c * GReal s) / (Δ.resToImagAxis s).re) := by
    simpa [s] using A_eq_neg_mul_FG_div_Delta (t := t) ht
  simpa [hA] using mul_neg_of_neg_of_pos (neg_lt_zero.2 (pow_pos ht 2))
    (div_pos (by simpa [c] using FG_inequality_1 (t := s) hs) (Delta_imag_axis_pos.2 s hs))

end MagicFunction.g.CohnElkies

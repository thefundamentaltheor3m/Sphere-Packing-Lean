/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.a.Schwartz

/-!
# Integral representations and special values of `a`

This file records the integral representation of `a` for `‖x‖ > √2`, which exhibits its double
zeros at the `E₈`-lattice vectors of norm `> √2` (Blueprint `prop:a-double-zeros`), the
representation valid for all `x ≠ 0` obtained by analytic continuation
(Blueprint `prop:a-another-integral`), and the resulting special value `a 0`
(Blueprint `prop:a0`).
-/

@[expose] public section

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions Set

namespace MagicFunction.a.SpecialValues

section IntegralRepresentations

/-- For `‖x‖ > √2`, `a x = 4i sin²(π‖x‖²/2) ∫₀^∞ t² φ₀(i/t) e^{-π‖x‖²t} dt`. This is Blueprint
`prop:a-double-zeros` (`a(r) = -4 sin²(πr²/2) ∫₀^{i∞} φ₀(-1/z) z² e^{πir²z} dz`) with the contour
parametrised as `z = it`. The integral converges for `‖x‖² > 2` by `φ₀''_isBigO_nhdsGT_zero` and
`φ₀''_isBigO_atTop`. -/
theorem a_eq_integral {x : ℝ⁸} (hx : √2 < ‖x‖) :
    a x = 4 * I * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2
      * ∫ t in Ioi (0 : ℝ), t ^ 2 * φ₀'' (I / t) * rexp (-π * ‖x‖ ^ 2 * t) := by
  sorry

/-- Integral representation of `a` valid for all `x ≠ 0` (Blueprint `prop:a-another-integral`):
subtracting the three leading terms `36/π² e^{2πt} - 8640/π t + 18144/π²` of the asymptotic
expansion of `t² φ₀(i/t)` as `t → ∞` makes the integral converge for every `x`, and the
subtracted terms are integrated explicitly. Both sides are analytic in `‖x‖²` near `[0, ∞)`, so
the identity extends from `‖x‖ > √2` (`a_eq_integral`) to all `x ≠ 0`. -/
theorem a_eq_integral' {x : ℝ⁸} (hx : 0 < ‖x‖) :
    a x = 4 * I * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2
      * (36 / (π ^ 3 * (‖x‖ ^ 2 - 2)) - 8640 / (π ^ 3 * ‖x‖ ^ 4) + 18144 / (π ^ 3 * ‖x‖ ^ 2)
        + ∫ t in Ioi (0 : ℝ), (t ^ 2 * φ₀'' (I / t) - 36 / π ^ 2 * rexp (2 * π * t)
            + 8640 / π * t - 18144 / π ^ 2) * rexp (-π * ‖x‖ ^ 2 * t)) := by
  sorry

end IntegralRepresentations

section Zero

/-- `a 0 = -8640 i / π`: the limit `x → 0` of `a_eq_integral'`, where only the term
`-8640 / (π³ ‖x‖⁴)` survives against `sin²(π‖x‖²/2) ~ π² ‖x‖⁴ / 4`. Blueprint `prop:a0`. -/
theorem a_zero : a 0 = -8640 * I / π := by sorry

end Zero
end MagicFunction.a.SpecialValues

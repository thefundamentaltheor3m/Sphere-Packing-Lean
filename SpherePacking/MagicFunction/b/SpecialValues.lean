/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.b.Schwartz

/-!
# Integral representations and special values of `b`

This file records the integral representation of `b` for `‖x‖ > √2`, which exhibits its double
zeros at the `E₈`-lattice vectors of norm `> √2` (Blueprint `prop:b-double-zeros`), the
representation valid for all `x` obtained by analytic continuation
(Blueprint `prop:b-another-integral`), and the resulting special value `b 0`
(Blueprint `prop:b0`).

## Sign conventions

`b` is defined with `J₆ = -2 ∫_i^{i∞} ψS(z) e^{πi‖x‖²z} dz` (Blueprint `def:b-definition`,
Viazovska's eq. (52)); this is the sign for which `𝓕 J₅ = -J₆` and hence `𝓕 b = -b`. Parametrising
the contour of `prop:b-double-zeros` as `z = it` then gives the prefactor `-4i` below (Viazovska's
eq. (58) prints `+4i`, which is inconsistent with her eq. (52)–(53); the magic function is
accordingly `g = (πi/8640) a - (i/(240π)) b`, see `SpherePacking.MagicFunction.g.Basic`).
-/

@[expose] public section

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions Set

namespace MagicFunction.b.SpecialValues

section IntegralRepresentations

/-- For `‖x‖ > √2`, `b x = -4i sin²(π‖x‖²/2) ∫₀^∞ ψI(it) e^{-π‖x‖²t} dt`. This is Blueprint
`prop:b-double-zeros` (`b(r) = -4 sin²(πr²/2) ∫₀^{i∞} ψI(z) e^{πir²z} dz`) with the contour
parametrised as `z = it`. The integral converges for `‖x‖² > 2` by `ψI'_isBigO_nhdsGT_zero` and
`ψI'_isBigO_atTop`. -/
theorem b_eq_integral {x : ℝ⁸} (hx : √2 < ‖x‖) :
    b x = -4 * I * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2
      * ∫ t in Ioi (0 : ℝ), ψI' (I * t) * rexp (-π * ‖x‖ ^ 2 * t) := by
  sorry

/-- Integral representation of `b` valid for all `x` (Blueprint `prop:b-another-integral`):
subtracting the leading terms `e^{2πt} + 144` of `ψI(it)` as `t → ∞` makes the integral converge
for every `x`, and the subtracted terms are integrated explicitly. Both sides are analytic in
`‖x‖²` near `[0, ∞)`, so the identity extends from `‖x‖ > √2` (`b_eq_integral`) to all `x`. -/
theorem b_eq_integral' (x : ℝ⁸) :
    b x = -4 * I * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2
      * (144 / (π * ‖x‖ ^ 2) + 1 / (π * (‖x‖ ^ 2 - 2))
        + ∫ t in Ioi (0 : ℝ),
            (ψI' (I * t) - 144 - rexp (2 * π * t)) * rexp (-π * ‖x‖ ^ 2 * t)) := by
  sorry

end IntegralRepresentations

section Zero

/-- `b 0 = 0`: immediate from `b_eq_integral'` at `x = 0`. Blueprint `prop:b0`. -/
theorem b_zero : b 0 = 0 := by sorry

end Zero

end SpecialValues

end b

end MagicFunction

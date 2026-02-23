module
public import SpherePacking.MagicFunction.g.Basic


/-!
# Cohn-Elkies auxiliary definitions for `g`

Blueprint reference: `blueprint/src/subsections/modform-ineq.tex`.

This file introduces the auxiliary real-valued functions `A` and `B` and a radial profile
`gRadial` satisfying `g x = gRadial (‖x‖ ^ 2)`.

## Main definitions
* `gRadial`
* `A`
* `B`

## Main statement
* `g_apply_eq_gRadial_norm_sq`
-/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap

open Real Complex SchwartzMap
open MagicFunction.FourierEigenfunctions

noncomputable section

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- Radial profile of `g` in the variable `‖x‖^2`. -/
@[expose] public def gRadial : 𝓢(ℝ, ℂ) :=
  ((π * I) / 8640) • a' - (I / (240 * π)) • b'

/-- The function `g` is radial, with profile `gRadial` in the variable `‖x‖ ^ 2`. -/
public theorem g_apply_eq_gRadial_norm_sq (x : ℝ⁸) : g x = gRadial (‖x‖ ^ 2) := by
  simp [g, gRadial, a, b, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]

/--
Auxiliary function `A(t)` from the blueprint, defined as the real part of
`-t^2 * φ₀(i/t) - (36/π^2) * ψI(i t)`.

We only use `A(t)` for `t > 0`, but define it on all `ℝ`.
-/
@[expose] public def A (t : ℝ) : ℝ :=
  (-(t ^ 2)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
    (36 / (π ^ (2 : ℕ)) : ℝ) * (ψI' ((Complex.I : ℂ) * (t : ℂ))).re

/--
Auxiliary function `B(t)` from the blueprint, defined as the real part of
`-t^2 * φ₀(i/t) + (36/π^2) * ψI(i t)`.

We only use `B(t)` for `t > 0`, but define it on all `ℝ`.
-/
@[expose] public def B (t : ℝ) : ℝ :=
  (-(t ^ 2)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re +
    (36 / (π ^ (2 : ℕ)) : ℝ) * (ψI' ((Complex.I : ℂ) * (t : ℂ))).re

end

end MagicFunction.g.CohnElkies

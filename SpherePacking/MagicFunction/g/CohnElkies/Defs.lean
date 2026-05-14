module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Schwartz.Basic
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.Tactic.NormNumI


/-!
# Viazovska's magic function `g` and Cohn-Elkies auxiliary definitions

Blueprint reference: `blueprint/src/subsections/modform-ineq.tex`.

This file defines Viazovska's magic function `g`, its normalization at `0`, the auxiliary
real-valued functions `A` and `B`, and a radial profile `gRadial` satisfying
`g x = gRadial (‖x‖ ^ 2)`.

## Main definitions
* `g`
* `gRadial`
* `A`
* `B`

## Main statements
* `g_zero`
* `fourier_g_zero`
* `g_apply_eq_gRadial_norm_sq`
-/

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.SpecialValues
  MagicFunction.b.SpecialValues

noncomputable section

/-- The Magic Function, `g`. -/
@[expose] public def g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a - (I / (240 * π)) • b

/-- Normalization of `g` at the origin. -/
public theorem g_zero : g 0 = 1 := by
  simp [g, a_zero, b_zero, sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1

/-- Normalization of the Fourier transform of `g` at the origin. -/
public theorem fourier_g_zero : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g 0 = 1 := by
  simp only [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
    sub_apply, smul_apply, smul_eq_mul]
  simp [a_zero, b_zero, sub_eq_add_neg, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1

end

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap

open Real Complex SchwartzMap
open MagicFunction.FourierEigenfunctions

noncomputable section

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

/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import SpherePacking.Tactic.ComplexGrind

/-!
# Tests for the `ComplexGrind` set of `grind` annotations
-/

public section

open Complex Set
open scoped UpperHalfPlane

/-! ### The set is opt-in -/

example (t : ℝ) : (I * t) ^ 2 = -(t : ℂ) ^ 2 := by
  fail_if_success grind
  grind [I_sq]

open scoped ComplexGrind

/-! ### Ring identities modulo `I ^ 2 = -1` -/

example (t : ℝ) : (I * t) ^ 2 = -(t : ℂ) ^ 2 := by grind
example (t : ℂ) : (t + I) * (t - I) = t ^ 2 + 1 := by grind
example (t : ℂ) : I ^ 3 * t = -I * t := by grind
example (t : ℝ) : -1 / (I * t) = I / t := by grind
example (a r t : ℝ) : -a * r * (I + t) = -a * I * r + -a * r * t := by grind

-- The ring solver propagates equalities, so this works under other functions too.
example (a r t : ℂ) :
    cexp (a * I * r * (-1 + t + I)) = cexp (-a * I * r + a * I * r * t + -a * r) := by
  grind

/-! ### Signs of real and imaginary parts -/

example (t : ℝ) (ht : 0 < t) : 0 < (I * t).im := by grind
example (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < (-1 + I * t).im := by grind
example (t : ℝ) : 0 < (-1 + t + I).im := by grind
example (t : ℝ) (ht : t ∈ Ici (1 : ℝ)) : 1 / 2 < (I * t).im := by grind
example (t : ℝ) : (2 * I * t).re = 0 := by grind
example (z c : ℂ) (hz : 0 < z.im) (hc : c.im = 0) : 0 < (z + c).im := by grind

/-! ### Non-vanishing -/

example (t : ℝ) (ht : t ≠ 0) : I * (t : ℂ) ≠ 0 := by grind
example (z c : ℂ) (hz : 0 < z.im) (hc : c.im = 0) : z + c ≠ 0 := by grind
example (t : ℝ) : (t : ℂ) + I ≠ 0 := by grind
example (t : ℝ) : (t : ℂ) - I ≠ 0 := by grind

/-! ### The upper half-plane -/

example (z : ℍ) : 0 < (z : ℂ).im := by grind
example (z : ℍ) : (z : ℂ) ≠ 0 := by grind
example (z : ℍ) : (z : ℂ) + 1 ≠ 0 := by grind

/-! ### As a discharger -/

example : ContinuousOn (fun t : ℝ ↦ (-1 : ℂ) / (I * t)) (Ioi 0) := by
  fun_prop (disch := grind)

example (c : ℂ) (hc : c.im = 0) :
    DifferentiableOn ℂ (fun z : ℂ ↦ -1 / (z + c)) {z | 0 < z.im} := by
  fun_prop (disch := grind)

/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.PushReIm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the `push_re_im` and `norm_exp_simp` tactics
-/

@[expose] public section

open Complex Real ComplexConjugate
open UpperHalfPlane hiding I
open scoped Real

section push_re_im

-- The canonical goal shape from the asymptotics files
example (n : ℕ+) (z : ℍ) : (2 * ↑π * I * ↑↑n * ↑z).re = -(2 * π * ↑↑n * z.im) := by
  push_re_im

example (z : ℍ) : (2 * ↑π * I * ↑z).re = -(2 * π * z.im) := by push_re_im

example (z : ℍ) : (2 * ↑π * I * ↑z).im = 2 * π * z.re := by push_re_im

-- Coercions of ℝ, ℕ, ℤ, and `I`
example (x : ℝ) : ((x : ℂ) * I).re = 0 := by push_re_im
example (n : ℕ) : ((n : ℂ) * I).im = n := by push_re_im
example (k : ℤ) : ((k : ℂ) * I).re = 0 := by push_re_im
example : ((3 : ℂ) * I).im = 3 := by push_re_im

-- Symbolic atoms fall back to `.re`/`.im`
example (w : ℂ) (z : ℍ) : (w * ↑z).re = w.re * z.re - w.im * z.im := by push_re_im

-- Powers, subtraction, negation, conjugation
example (z : ℍ) : (((z : ℂ) - I) ^ 2).im = 2 * z.re * (z.im - 1) := by push_re_im
example (z : ℍ) : (-(↑z : ℂ)).im = -z.im := by push_re_im
example (z : ℍ) : (conj (↑z : ℂ)).im = -z.im := by push_re_im

-- `cexp` of a real coercion
example (x : ℝ) : (cexp (x : ℂ) * 3).re = 3 * rexp x := by push_re_im

-- Extra lemmas: hypotheses about vanishing imaginary parts
example (F : ℍ → ℂ) (z : ℍ) (hF : (F z).im = 0) (c : ℝ) :
    ((c : ℂ) * F z).re = c * (F z).re := by
  push_re_im [hF]

-- At a hypothesis
example (z : ℍ) (h : (I * ↑z).re = 5) : -z.im = 5 := by
  push_re_im at h
  exact h

-- Fails (rather than silently succeeding) when there is nothing to push
example (w : ℂ) (h : w.re = 1) : w.re = 1 := by
  fail_if_success push_re_im
  exact h

end push_re_im

section norm_exp_simp

-- The workhorse: norms of `q`-expansion exponentials
example (z : ℍ) : ‖cexp (2 * ↑π * I * ↑z)‖ = rexp (-(2 * π * z.im)) := by norm_exp_simp

example (n : ℕ) (z : ℍ) :
    ‖cexp (2 * ↑π * I * ↑n * ↑z)‖ = rexp (-(2 * π * ↑n * z.im)) := by
  norm_exp_simp

-- Products distribute
example (w : ℂ) (z : ℍ) :
    ‖w * cexp (2 * ↑π * I * ↑z)‖ = ‖w‖ * rexp (-(2 * π * z.im)) := by
  norm_exp_simp

-- `cexp (x * I)` for real `x` has norm one
example (x : ℝ) : ‖cexp ((x : ℂ) * I)‖ = 1 := by norm_exp_simp

end norm_exp_simp

/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import SpherePacking.ForMathlib.ComplexFunProp

/-!
# Tests for `fun_prop` through the coercion `ℝ → ℂ`
-/

public section

open Complex Set

example : ContDiff ℝ ⊤ (fun t : ℝ ↦ (-1 : ℂ) + I * t) := by fun_prop
example {n : WithTop ℕ∞} : ContDiff ℝ n (fun t : ℝ ↦ (1 : ℂ) - t + I) := by fun_prop
example : ContDiffOn ℝ ⊤ (fun t : ℝ ↦ (-1 : ℂ) + I * t) (Ioc 0 1) := by fun_prop
example (x : ℝ) : ContDiffAt ℝ ⊤ (fun t : ℝ ↦ I * t) x := by fun_prop
example (x : ℝ) : ContDiffWithinAt ℝ ⊤ (fun t : ℝ ↦ (1 : ℂ) - t + I) (Icc 0 1) x := by fun_prop
example (a : ℂ) : ContDiff ℝ ⊤ (fun x : ℝ ↦ cexp (a * x)) := by fun_prop
example (a : ℂ) (f : ℝ → ℂ) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ cexp (a * x) * f x + x ^ 2) := by fun_prop

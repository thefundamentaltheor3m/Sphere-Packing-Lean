/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic

/-!
# `fun_prop` and the coercion `ℝ → ℂ`

`fun_prop` proves `Continuous`, `Measurable` and `Differentiable ℝ` for functions that pass through
the coercion `((↑) : ℝ → ℂ)`, but not `ContDiff ℝ n`. That gap is hit by every smoothness statement
about a path `ℝ → ℂ` (`fun t ↦ -1 + I * t`), and hence by every contour integral, and it is the
only reason such statements are proved by hand with `Complex.ofRealCLM.contDiff`.

Registering the one missing lemma is enough: `fun_prop` then proves `ContDiff`, `ContDiffOn`,
`ContDiffAt` and `ContDiffWithinAt` for anything built from the coercion by arithmetic,
`Complex.exp`, and the other operations it already knows.

This is a candidate for upstreaming to Mathlib.
-/

public section

/-- The coercion `ℝ → ℂ` is smooth. Registered with `fun_prop`. -/
@[fun_prop]
theorem Complex.contDiff_ofReal {n : WithTop ℕ∞} : ContDiff ℝ n ((↑) : ℝ → ℂ) :=
  Complex.ofRealCLM.contDiff

/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.Pointwise
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Tests for the `pointwise` tactic

The `#guard_msgs` tests in this file are sensitive to any other diagnostics emitted at the
guarded commands, so this file must keep a style-conformant header (otherwise
`linter.style.header` warnings can leak into the `#guard_msgs` output and fail CI).
-/

@[expose] public section

open UpperHalfPlane

section basic

variable {f g h : ℍ → ℂ}

-- Commutativity / distributivity through `Pi` operations
example : f * g = g * f := by pointwise
example : (f + g) * h = f * h + g * h := by pointwise
example : (f + g) ^ 2 = f ^ 2 + 2 * f * g + g ^ 2 := by pointwise
example : f - g = -(g - f) := by pointwise
example : -f * -g = f * g := by pointwise
example : f / g = f * g⁻¹ := by pointwise
example : f * 1 + 0 = f := by pointwise

-- Lambda on the right-hand side (`ext` + beta reduction)
example : f + g = fun z => g z + f z := by pointwise

-- Scalar multiplication, over ℂ, ℝ (with coercion), and ℕ
example : (2 : ℂ) • f = f + f := by pointwise
example : (2 : ℝ) • f = f + f := by pointwise
example : (2 : ℕ) • f = f + f := by pointwise
example (c : ℂ) : c • (f + g) = c • f + c • g := by pointwise
example (c : ℝ) : c • (f * g) = (c • f) * g := by pointwise

-- Constant functions (`OfNat` in function space)
example : (2 : ℍ → ℂ) * 3 = 6 := by pointwise
example : (12⁻¹ : ℍ → ℂ) * 12 = 1 := by pointwise

-- Function composition
example (F : ℂ → ℂ) : (F ∘ g) * 1 = fun z => F (g z) := by pointwise

end basic

section extras

variable {f g : ℍ → ℂ}

def sqFun (f : ℍ → ℂ) : ℍ → ℂ := f ^ 2

-- Extra simp lemmas: unfold a local definition
example : sqFun f = f * f := by pointwise [sqFun]

-- Extra simp lemmas: use a pointwise hypothesis
example (hfg : ∀ z, f z = g z) : f * f = g * g := by pointwise [hfg]

end extras

section closers

variable {f g : ℍ → ℂ}

-- Replace the default `try ring` closer
example : (f + g) ^ 2 = f ^ 2 + 2 * f * g + g ^ 2 := by pointwise using ring
example : (2 : ℍ → ℂ) * 3 = 6 := by pointwise using norm_num
example : f * g - g * f = 0 := by pointwise using ring_nf
example (c : ℝ) : ((c ^ 2 : ℝ) : ℂ) • f = (c : ℂ) ^ 2 • f := by
  pointwise using (push_cast; ring)

end closers

section hypotheses

variable {f g : ℍ → ℂ}

-- Rewriting hypotheses with the simp set directly
example (hfg : f * g = 1) (z : ℍ) : f z * g z = 1 := by
  have h := congrFun hfg z
  simp only [pointwise_simps] at h
  exact h

end hypotheses

section generic

-- The tactic is not specific to `ℍ → ℂ`
example (f g : ℝ → ℝ) : f * g = g * f := by pointwise
example (f g : ℂ → ℂ) : (f - g) ^ 2 = (g - f) ^ 2 := by pointwise

end generic

section failure

-- `pointwise` fails (rather than silently succeeding) on goals that are not
-- function extensionality goals
example : (1 : ℕ) = 1 := by
  fail_if_success pointwise
  rfl

end failure

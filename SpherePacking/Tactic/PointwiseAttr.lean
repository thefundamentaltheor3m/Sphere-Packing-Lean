/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp

/-!
# The `pointwise_simps` simp set

The simp set backing the `pointwise` tactic (defined in `SpherePacking.Tactic.Pointwise`).
It collects the lemmas that evaluate function-space algebra at a point: `Pi.mul_apply`,
`Pi.add_apply`, `Pi.smul_apply`, constant functions, and the `smul`-to-`mul` normalization
lemmas that let `ring` finish afterwards.

The attribute lives in its own file because an attribute cannot be used in the same file
where it is declared; the lemmas are tagged in `SpherePacking.Tactic.Pointwise`.
-/

public meta section

/-- Simp set of the `pointwise` tactic: lemmas that push applications of function-space
algebra (`(f * g) z`, `(f + g) z`, `(c • f) z`, constant functions, ...) down to pointwise
operations on values (`f z * g z`, ...), normalizing `•` to `*` along the way. -/
register_simp_attr pointwise_simps

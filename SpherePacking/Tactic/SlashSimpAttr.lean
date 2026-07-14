/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp

/-!
# The `slash_simps` simp set

The simp set backing the `slash_simp` tactic (defined in `SpherePacking.Tactic.SlashSimp`):
lemmas unfolding slash-action applications `(f ∣[k] γ) z` to `f (γ • z) * denom γ z ^ (-k)`
and evaluating `denom` on the explicit generators `S`, `T`.

The attribute lives in its own file because an attribute cannot be used in the same file
where it is declared; the lemmas are tagged in `SpherePacking.Tactic.SlashSimp`.
-/

public meta section

/-- Simp set of the `slash_simp` tactic: unfold slash-action applications and evaluate
`denom` on explicit matrices. The `≠ 0` side conditions left for `field_simp` are
discharged by `slash_ne_zero`. -/
register_simp_attr slash_simps

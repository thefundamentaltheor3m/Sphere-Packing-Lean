import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

open UpperHalfPlane

theorem isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp_rw [bounded_mem, Pi.neg_apply, map_neg_eq_map]

alias ⟨_, IsBoundedAtImInfty.neg⟩ := isBoundedAtImInfty_neg_iff


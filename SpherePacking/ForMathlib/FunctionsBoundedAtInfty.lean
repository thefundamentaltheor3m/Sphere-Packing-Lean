module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

@[expose] public section

open UpperHalfPlane

theorem isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, Pi.neg_apply, norm_neg]

-- The forward direction `IsBoundedAtImInfty.neg` is mathlib's `BoundedAtFilter.neg`; only the
-- `iff` above (used for `simp_rw`) has no mathlib counterpart, so it is kept.

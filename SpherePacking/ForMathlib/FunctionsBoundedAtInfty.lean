module
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty


/-!
# Functions bounded at infinity

This file proves results such as `isBoundedAtImInfty_neg_iff`.
-/

/-- Negating a function preserves boundedness at `i∞` on the upper half-plane. -/
public theorem isBoundedAtImInfty_neg_iff {α : Type*} [SeminormedAddGroup α]
    (f : UpperHalfPlane → α) :
    UpperHalfPlane.IsBoundedAtImInfty (-f) ↔ UpperHalfPlane.IsBoundedAtImInfty f := by
  simp [UpperHalfPlane.isBoundedAtImInfty_iff]

-- The forward direction `IsBoundedAtImInfty.neg` is mathlib's `BoundedAtFilter.neg`; only the
-- `iff` above (used for `simp_rw`) has no mathlib counterpart, so it is kept.

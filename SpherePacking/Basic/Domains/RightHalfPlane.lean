module
public import Mathlib.Analysis.Complex.Basic

/-!
# The open right half-plane

This file defines `rightHalfPlane : Set ℂ`, the open right half-plane `{u : ℂ | 0 < u.re}`,
and records basic topological facts.
-/

namespace SpherePacking

/-! ## Definitions -/

/-- The open right half-plane `{u : ℂ | 0 < u.re}`. -/
@[expose] public def rightHalfPlane : Set ℂ := {u : ℂ | 0 < u.re}

/-- The right half-plane is an open subset of `ℂ`. -/
public lemma rightHalfPlane_isOpen : IsOpen rightHalfPlane := by
  simpa [rightHalfPlane] using (isOpen_Ioi.preimage Complex.continuous_re)

end SpherePacking

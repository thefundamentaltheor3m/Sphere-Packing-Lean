module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# `atImInfty` filter helpers

Unfolding lemmas for `UpperHalfPlane.atImInfty` (the filter of points with large imaginary part).
Candidates for upstreaming to
`Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`.
-/

@[expose] public section

/-- Unfold `∀ᶠ z in UpperHalfPlane.atImInfty, p z` into an explicit bound on the imaginary part. -/
public lemma Filter.eventually_atImInfty {p : UpperHalfPlane → Prop} :
    (∀ᶠ x in UpperHalfPlane.atImInfty, p x) ↔
      ∃ A : ℝ, ∀ z : UpperHalfPlane, A ≤ z.im → p z :=
  UpperHalfPlane.atImInfty_mem (setOf p)

/-- The imaginary-part map `z ↦ z.im` tends to `∞` along the filter `UpperHalfPlane.atImInfty`. -/
public lemma Filter.tendsto_im_atImInfty :
    Tendsto (fun x : UpperHalfPlane ↦ x.im) UpperHalfPlane.atImInfty atTop := by
  simp [UpperHalfPlane.atImInfty, Filter.tendsto_iff_comap]


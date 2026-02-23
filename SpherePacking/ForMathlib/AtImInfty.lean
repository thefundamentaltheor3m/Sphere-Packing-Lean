module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

@[expose] public section

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

/-- Unfold `∀ᶠ z in UpperHalfPlane.atImInfty, p z` into an explicit bound on the imaginary part. -/
public lemma Filter.eventually_atImInfty {p : UpperHalfPlane → Prop} :
    (∀ᶠ x in UpperHalfPlane.atImInfty, p x) ↔
      ∃ A : ℝ, ∀ z : UpperHalfPlane, A ≤ z.im → p z :=
  UpperHalfPlane.atImInfty_mem (setOf p)

/-- The imaginary-part map `z ↦ z.im` tends to `∞` along the filter `UpperHalfPlane.atImInfty`. -/
public lemma Filter.tendsto_im_atImInfty :
    Tendsto (fun x : UpperHalfPlane ↦ x.im) UpperHalfPlane.atImInfty atTop := by
  simp [UpperHalfPlane.atImInfty, Filter.tendsto_iff_comap]

open UpperHalfPlane Filter

/-- If f tends to c ≠ 0 at infinity, then f ≠ 0 as a function.

This packages the common argument: if f = 0, then f → 0, but also f → c by hypothesis.
By uniqueness of limits, 0 = c, contradicting c ≠ 0. -/
lemma ne_zero_of_tendsto_ne_zero {f : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto f atImInfty (nhds c)) : f ≠ 0 := fun h =>
  hc (tendsto_nhds_unique tendsto_const_nhds (h ▸ hf)).symm

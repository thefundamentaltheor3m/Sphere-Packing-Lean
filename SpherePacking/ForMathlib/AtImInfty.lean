module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Behaviour as the Imaginary Part Tends to Infinity

Auxiliary lemmas about the `atImInfty` filter on the upper half-plane.
-/

@[expose] public section

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane Filter Topology

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (Set.ofPred p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a

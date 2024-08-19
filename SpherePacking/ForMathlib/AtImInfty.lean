import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop := by
  simp only [atImInfty_basis.tendsto_iff atTop_basis, Set.mem_preimage, Set.mem_Ici, true_and,
    true_implies]
  exact fun b ↦ ⟨b, by simp⟩

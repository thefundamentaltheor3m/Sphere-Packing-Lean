import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane

instance : atImInfty.NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have h₁ : atImInfty.sets = Set.univ := congrArg (fun F ↦ F.sets) h
  have h₂ : {I} ∉ atImInfty.sets := by
    rw [Filter.mem_sets, atImInfty_mem]
    push_neg
    intro A
    use ⟨1 + (max 2 A) * Complex.I, ?_⟩, ?_, ?_
    · simp
    · change A ≤ (1 + (max 2 A) * Complex.I).im
      simp
    · rw [Set.mem_singleton_iff]
      apply ne_of_apply_ne (fun x : ℍ ↦ Complex.im x)
      change (1 + (max 2 A) * Complex.I).im ≠ 1
      have : max 2 A ≠ 1 := by
        intro h
        have : 2 ≤ (1 : ℝ) := by simp [← h]
        norm_num at this
      simp [this]
  simp [h₁] at h₂

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a

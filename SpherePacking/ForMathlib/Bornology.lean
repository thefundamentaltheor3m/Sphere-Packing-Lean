import Mathlib.Tactic

open scoped Pointwise

lemma Bornology.isBounded_vadd_set
    {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : Set (EuclideanSpace ℝ (Fin d))) (hs : IsBounded s) :
    IsBounded (a +ᵥ s) := by
  rw [isBounded_iff_forall_norm_le] at hs ⊢
  obtain ⟨C, hC⟩ := hs
  use C + ‖a‖
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
  rw [vadd_eq_add]
  trans ‖a‖ + ‖y‖
  · exact norm_add_le _ _
  · rw [add_comm]
    gcongr
    exact hC y hy


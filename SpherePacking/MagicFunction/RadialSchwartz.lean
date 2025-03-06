import Mathlib

open SchwartzMap Function

section Aux

lemma hasTemperateGrowth_norm_sq {d : ℕ} :
    HasTemperateGrowth (fun (x : EuclideanSpace ℝ (Fin d)) ↦ ‖x‖ ^ 2) := by
  refine @Function.HasTemperateGrowth.of_fderiv (EuclideanSpace ℝ (Fin d)) ℝ _ _ _ _
    (fun x ↦ ‖x‖ ^ 2) ?_ (Differentiable.norm_sq ℝ differentiable_id) 2 1 ?_
  · sorry
  · intro x
    simp only [norm_pow, norm_norm, pow_one, one_mul, pow_two, norm_mul]
    suffices : ‖x‖ ≤ 1 + ‖x‖
    ·
      sorry
    sorry

lemma le_one_add_sq_of_nonneg {x : ℝ} : x ≤ 1 + x ^ 2 := by nlinarith

end Aux

-- @[simps!]
-- noncomputable def schwartzMap_multidimensional_of_schwartzMap_real (d : ℕ) (f : 𝓢(ℝ, ℂ)) :
--     𝓢((EuclideanSpace ℝ (Fin d)), ℂ) := f.compCLM ℝ _ _


noncomputable def schwartzMap_multidimensional_of_schwartzMap_real' (d : ℕ) (f : 𝓢(ℝ, ℂ)) :
    𝓢((EuclideanSpace ℝ (Fin d)), ℂ) where
  toFun := fun x ↦ f (‖x‖ ^ 2) -- f ∘ norm
  smooth' := f.smooth'.comp (contDiff_id.norm_sq ℝ)
  decay' := by
    intro k n
    if hk : Even k then
    · obtain ⟨m, hm⟩ := hk
      obtain ⟨C, hC⟩ := f.decay' m n
      induction' n with n hn
      · -- Base Case
        use C
        intro x
        specialize hC (‖x‖ ^ 2)
        simp only [norm_pow, norm_norm, norm_iteratedFDeriv_zero, Complex.norm_eq_abs] at hC ⊢
        suffices : ‖x‖ ^ k * Complex.abs (f (‖x‖ ^ 2)) =
          (‖x‖ ^ 2) ^ m * Complex.abs (f.toFun (‖x‖ ^ 2))
        · rw [this]
          exact hC
        simp only [← pow_mul, two_mul, ← hm, mul_eq_mul_left_iff, pow_eq_zero_iff', norm_eq_zero,
          ne_eq]
        left
        rfl
      · -- Inductive Case
        use C
        intro x
        sorry
    else
    · rw [Nat.not_even_iff_odd] at hk
      obtain ⟨m, hm⟩ := hk

      sorry
    stop
    obtain ⟨C, hC⟩ := f.decay' k n
    use C
    intro x
    specialize hC (‖x‖ ^ 2)
    -- I believe this is true...
    sorry

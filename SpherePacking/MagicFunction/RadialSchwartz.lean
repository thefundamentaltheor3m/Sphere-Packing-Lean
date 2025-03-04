import Mathlib

open SchwartzMap

section Aux

theorem norm_iteratedDeriv_multidimensional_le_const_mul_abs_nthDeriv_real {d : ℕ} (f : 𝓢(ℝ, ℂ))
    (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) {k' : ℕ} {C : ℝ}
    (hC : ∀ (x : ℝ), ‖x‖ ^ (k') * ‖iteratedFDeriv ℝ n f.toFun x‖ ≤ C) :
    ∃ (D : ℝ), ‖iteratedFDeriv ℝ 0 (fun x ↦ f (‖x‖ ^ 2)) x‖
    ≤ D * Complex.abs (iteratedDeriv n f (‖x‖ ^ 2)) := by
  induction' n with n hn
  · sorry
  · sorry

end Aux

noncomputable def schwartzMap_multidimensional_of_schwartzMap_real (d : ℕ) (f : 𝓢(ℝ, ℂ)) :
    𝓢((EuclideanSpace ℝ (Fin d)), ℂ) where
  toFun := fun x ↦ f (‖x‖ ^ 2) -- f ∘ norm
  smooth' := f.smooth'.comp (contDiff_id.norm_sq ℝ)
  decay' := by
    intro k n
    if hk : Even k then
    · obtain ⟨m, hm⟩ := hk
      obtain ⟨C, hC⟩ := f.decay' m n
      induction' n with n hn
      · use C
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
      · use C
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

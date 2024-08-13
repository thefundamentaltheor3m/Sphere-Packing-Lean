import SpherePacking.CohnElkies.Prereqs

open scoped FourierTransform

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

variable {f : ℝᵈ → ℂ}  -- Need real-valuedness (else f(0) / (𝓕f)(0) makes no sense as a bound)...

theorem LinearProgrammingBound (hPSF : PSF_Conditions f) -- (hReal : ∀ x : ℝᵈ, ∃ y : ℝ, f x = y) ?
  (hCohnElkies₁ : ∀ x : ℝᵈ, ‖x‖ ≥ 1 → ∃ y : ℝ, y ≤ 0 ∧ f x = ↑y)
  (hCohnElkies₂ : ∀ x : ℝᵈ, ∃ y : ℝ, y ≥ 0 ∧ 𝓕 f x = ↑y) : True := by
  sorry

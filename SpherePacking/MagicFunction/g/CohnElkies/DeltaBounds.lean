module
public import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.Delta

/-!
# Bounds for `Δ⁻¹` near `i∞`

Exponential growth bound for the inverse modular discriminant `Δ⁻¹` in terms of `exp (2π * im z)`
for `im z` sufficiently large.
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped UpperHalfPlane Real
open UpperHalfPlane Filter

/-- Exponential growth bound for `Δ⁻¹` for `im z` sufficiently large. -/
public lemma exists_inv_Delta_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖(Δ z)⁻¹‖ ≤ C * Real.exp (2 * π * z.im) := by
  obtain ⟨c, hcpos, hEvent⟩ := (Asymptotics.isBigO_iff'').1
    (by simpa using Delta_isTheta_rexp.2 :
      (fun τ : ℍ => Real.exp (-2 * π * τ.im)) =O[atImInfty] Delta)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 (by simpa using hEvent)
  refine ⟨c⁻¹, A, inv_pos.2 hcpos, fun z hz => ?_⟩
  have hLower : c * Real.exp (-2 * π * z.im) ≤ ‖Δ z‖ := by
    simpa [Delta_apply] using hA z hz
  calc
    ‖(Δ z)⁻¹‖ = ‖Δ z‖⁻¹ := by simp [norm_inv]
    _ ≤ (c * Real.exp (-2 * π * z.im))⁻¹ :=
          (inv_le_inv₀ (by simpa [norm_pos_iff] using Δ_ne_zero z)
            (mul_pos hcpos (Real.exp_pos _))).2 hLower
    _ = c⁻¹ * Real.exp (2 * π * z.im) := by
          simp [mul_inv_rev, Real.exp_neg, mul_assoc, mul_comm]

end MagicFunction.g.CohnElkies.IntegralReps

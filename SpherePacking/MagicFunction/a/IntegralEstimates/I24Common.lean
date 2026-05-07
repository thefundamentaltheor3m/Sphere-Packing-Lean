module

public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.MagicFunction.a.IntegralEstimates.BoundingAux
public import SpherePacking.MagicFunction.a.IntegralEstimates.PowExpBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
import SpherePacking.ForMathlib.DerivHelpers

/-!
# Common skeleton for `I₂'`/`I₄'` integral estimates

Shared infrastructure for exponential bounds and Schwartz decay of iterated derivatives of `I₂'`
and `I₄'`. Specialisations in `I2.lean` and `I4.lean` instantiate the concrete integrand.
-/

namespace MagicFunction.a.IntegralEstimates.I24Common

noncomputable section

open scoped Function UpperHalfPlane Topology Real Complex
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open MagicFunction.PolyFourierCoeffBound MagicFunction.a.ComplexIntegrands

/-- The common coefficient pattern `coeff t = (-π) + (π * I) * shift t`. -/
@[expose] public def coeff (shift : ℝ → ℂ) : ℝ → ℂ :=
  fun t : ℝ ↦ (-π : ℂ) + (π * I) * shift t

public lemma continuous_coeff {shift : ℝ → ℂ} (hshift : Continuous shift) :
    Continuous (coeff shift) :=
  continuous_const.add (continuous_const.mul hshift)

/-- Uniform bound `‖coeff t‖ ≤ 2π` on `Ioo (0, 1)` given `‖shift t‖ ≤ 1` there. -/
public lemma coeff_norm_le {shift : ℝ → ℂ} (hshift : ∀ t ∈ Ioo (0 : ℝ) 1, ‖shift t‖ ≤ 1) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : ‖coeff shift t‖ ≤ 2 * π := by
  have hnorm : ‖(π * I : ℂ)‖ = π := by simp [abs_of_nonneg Real.pi_pos.le]
  calc
    ‖coeff shift t‖
        ≤ ‖(-π : ℂ)‖ + ‖(π * I : ℂ) * shift t‖ := norm_add_le _ _
    _ = π + π * ‖shift t‖ := by rw [norm_mul, hnorm]; simp [abs_of_nonneg Real.pi_pos.le]
    _ ≤ π + π * 1 := by gcongr; exact hshift t ht
    _ = 2 * π := by ring

/-- Uniform `‖g r t‖ ≤ C₀ * exp(-π) * 2 * exp(-π * r)` bound on `Ioo (0, 1)`. -/
public lemma g_norm_bound_uniform_of {g : ℝ → ℝ → ℂ} {mob : ℝ → ℂ}
    (haux : ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ‖g r t‖ ≤ ‖φ₀'' (mob t)‖ * 2 * rexp (-π * r))
    (hmob_im : ∀ t ∈ Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (mob t).im) :
    ∃ C₀ > 0, ∀ r : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖g r t‖ ≤ C₀ * rexp (-π) * 2 * rexp (-π * r) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun r t ht ↦ (haux r t ht).trans ?_⟩
  gcongr
  have hpos : 0 < (mob t).im := one_half_pos.trans (hmob_im t ht)
  simpa [φ₀'', hpos] using
    norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im (C₀ := C₀) (hC₀_pos := hC₀_pos) (hC₀ := hC₀)
      (z := ⟨mob t, hpos⟩) (by simpa using hmob_im t ht)

end

end MagicFunction.a.IntegralEstimates.I24Common

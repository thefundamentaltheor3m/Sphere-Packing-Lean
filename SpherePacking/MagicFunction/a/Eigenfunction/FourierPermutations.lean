module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12ContourMain
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierMain
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude

/-!
# Fourier Permutations

We show that the Fourier transform permutes the integral pieces defining `a`, and deduce that `a`
is a Fourier eigenfunction.

## Main statements
* `eig_a`
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Integral_Permutations

open MeasureTheory Set Complex Real

theorem perm_I₁_I₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) =
      (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) := by
  ext w
  simp only
    [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, add_apply, I₃_apply, I₄_apply,
      fourier_coe]
  rw [fourier_I₁_eq_curveIntegral (w := w), fourier_I₂_eq_curveIntegral (w := w),
    I₃'_add_I₄'_eq_curveIntegral_segments (r := ‖w‖ ^ 2)]
  simpa using (perm_I12_contour (r := ‖w‖ ^ 2))

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.

theorem perm_₃_I₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) =
      (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) := by
  rw [← perm_I₁_I₂]
  simpa using radial_inversion (I₁ + I₂) (fun _ => by simp [I₁, I₂])

-- should use fourier_involution and the radial symmetry of I₅
theorem perm_I₆ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₆ = I₅ := by
  simpa [← perm_I₅] using radial_inversion I₅ (fun _ => by
    simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])

end Integral_Permutations

section Eigenfunction

/-- The magic function `a` is invariant under the Fourier transform. -/
public theorem eig_a : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals,
    show I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ by ac_rfl,
    map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end
end MagicFunction.a.Fourier

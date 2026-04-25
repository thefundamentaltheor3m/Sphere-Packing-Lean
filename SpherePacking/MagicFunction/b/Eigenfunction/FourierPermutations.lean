module
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12ContourDeformation
public import SpherePacking.MagicFunction.b.Schwartz.Basic
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12CurveIntegrals
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ1
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12FourierJ2
import SpherePacking.MagicFunction.b.Eigenfunction.PermJ5
import SpherePacking.Contour.PermJ12Fourier
import SpherePacking.ForMathlib.GaussianFourierCommon


/-!
# Fourier permutations for `b`

This file combines contour permutation identities for the integrals defining `b` to show that `b`
is a `(-1)`-eigenfunction of the Fourier transform on `EuclideanSpace ℝ (Fin 8)`.

## Main statement
* `eig_b`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

theorem perm_J₁_J₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) ((J₁ : SchwartzMap ℝ⁸ ℂ) + J₂) =
      -((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) :=
  SpherePacking.Contour.perm_J₁_J₂_of
    (J₁ := (J₁ : SchwartzMap ℝ⁸ ℂ)) (J₂ := J₂)
    (J₃ := (J₃ : SchwartzMap ℝ⁸ ℂ)) (J₄ := J₄)
    (Ψ₁_fourier := Ψ₁_fourier) (Ψ₁' := Ψ₁')
    (h := ⟨perm_J12_contour,
      fun w => by simpa [SchwartzMap.fourier_coe] using fourier_J₁_eq_curveIntegral (w := w),
      fun w => by simpa [SchwartzMap.fourier_coe] using fourier_J₂_eq_curveIntegral (w := w),
      fun w => by
        simpa [J₃_apply, J₄_apply, add_assoc, add_left_comm, add_comm] using
          (J₃'_add_J₄'_eq_curveIntegral_segments (r := ‖w‖ ^ (2 : ℕ))).symm⟩)

theorem perm_₃_J₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) =
      -((J₁ : SchwartzMap ℝ⁸ ℂ) + J₂) := by
  let FT := FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)
  have hsymm : FT.symm ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) = FT ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) := by
    ext x
    simp only [FT, FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, fourierInv_eq_fourier_comp_neg]
    suffices (fun y : ℝ⁸ ↦ (J₃ + J₄) (-y)) = fun y ↦ (J₃ + J₄) y by
      simpa using congrArg (fun f : ℝ⁸ → ℂ => (𝓕 f) x) this
    funext y
    simp [J₃, J₄, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  simpa [FT] using
    SpherePacking.Contour.perm_J₃_J₄_of
      (J₁ := (J₁ : SchwartzMap ℝ⁸ ℂ)) (J₂ := J₂)
      (J₃ := (J₃ : SchwartzMap ℝ⁸ ℂ)) (J₄ := J₄)
      (hsymm := hsymm) (perm_J₁_J₂ := perm_J₁_J₂)

end Integral_Permutations

section Eigenfunction

/--
The Schwartz function `b` is a `(-1)`-eigenfunction of the Fourier transform on `ℝ⁸`.
-/
public theorem eig_b : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end

end MagicFunction.b.Fourier

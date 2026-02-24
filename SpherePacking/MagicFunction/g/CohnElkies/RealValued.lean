module
public import SpherePacking.MagicFunction.g.Basic
import SpherePacking.MagicFunction.g.CohnElkies.PureImaginary
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations


/-!
# Real-valuedness of `g`

This file proves that `g` and its Fourier transform are real-valued. These lemmas are part of
blueprint Theorem `thm:g1` / `thm:g`.

## Main statements
* `MagicFunction.g.CohnElkies.g_real`
* `MagicFunction.g.CohnElkies.g_real_fourier`
-/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap
open Real Complex

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.FourierEigenfunctions

local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

private theorem ofReal_re_eq (z : ℂ) (hz : z.im = 0) : (↑z.re : ℂ) = z := by
  exact Complex.ext (by simp) (by simp [hz])

/-- The magic function `g` is real-valued. -/
public theorem g_real : ∀ x : ℝ⁸, (↑(g x).re : ℂ) = g x := by
  intro x
  refine ofReal_re_eq (g x) ?_
  simp [g, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.sub_im, Complex.mul_im, a_pureImag (x := x), b_pureImag (x := x),
    div_eq_mul_inv, Complex.mul_re]

/-- The Fourier transform `𝓕 g` is real-valued. -/
public theorem g_real_fourier : ∀ x : ℝ⁸, (↑((𝓕 g x).re : ℂ)) = (𝓕 g x) := by
  intro x
  refine ofReal_re_eq (𝓕 g x) ?_
  have hFg : FT g = ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  have hF : (𝓕 g) = FT g := by simp
  change ((𝓕 g) x).im = 0
  rw [hF, hFg]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
    a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

end MagicFunction.g.CohnElkies

module
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.b.psi
import SpherePacking.ModularForms.Delta


/-!
# Real-valuedness on the positive imaginary axis

These lemmas show that the modular input functions used in the Cohn-Elkies inequalities are
real-valued along the positive imaginary axis. They allow rewriting expressions involving `φ₀''`
and `ψI'` as `Complex.ofReal` terms, matching the auxiliary functions `A` and `B`.

## Main statements
* `φ₀''_imag_axis_im`
* `φ₀''_imag_axis_div_im`
* `ψI'_imag_axis_im`
-/

namespace MagicFunction.g.CohnElkies

open scoped UpperHalfPlane

open Complex Real UpperHalfPlane

private lemma imagAxis_im_eq_zero (F : ℍ → ℂ) (t : ℝ) (ht : 0 < t) (hF : ResToImagAxis.Real F) :
    (F ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF t ht

lemma φ₀_imag_axis_im (t : ℝ) (ht : 0 < t) : (φ₀ ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hE2 : (E₂ z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero E₂ t ht E₂_imag_axis_real
  have hE4 : (E₄ z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero E₄ t ht E₄_imag_axis_real
  have hE6 : (E₆ z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero E₆ t ht E₆_imag_axis_real
  have hΔ : (Δ z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero Δ t ht Delta_imag_axis_pos.1
  have hA : ((E₂ z) * (E₄ z) - (E₆ z)).im = 0 := by
    simp [-E4_apply, -E6_apply, Complex.sub_im, Complex.mul_im, hE2, hE4, hE6]
  -- `φ₀` is a quotient of real quantities on the imaginary axis.
  simp [-E4_apply, -E6_apply, φ₀, z, Complex.div_im, hΔ,
    Complex.im_pow_eq_zero_of_im_eq_zero hA 2]

/-- The value `φ₀'' (it)` is real for `t > 0`. -/
public lemma φ₀''_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) * (t : ℂ))).im = 0 := by
  -- On the imaginary axis, `((I:ℂ) * (t:ℂ)).im = t`.
  simpa [φ₀'', ht] using φ₀_imag_axis_im t ht

/-- The value `φ₀'' (i / t)` is real for `t > 0`. -/
public lemma φ₀''_imag_axis_div_im (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).im = 0 := by
  simpa [div_eq_mul_inv] using (φ₀''_imag_axis_im (t := (1 / t)) (by positivity))

lemma H₃_imag_axis_real : ResToImagAxis.Real H₃ := by
  simpa [jacobi_identity] using H₂_imag_axis_real.add H₄_imag_axis_real

lemma ψI_imag_axis_real : ResToImagAxis.Real ψI := by
  intro t ht
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hH2 : (H₂_MF z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero H₂ t ht H₂_imag_axis_real
  have hH3 : (H₃_MF z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero H₃ t ht H₃_imag_axis_real
  have hH4 : (H₄_MF z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero H₄ t ht H₄_imag_axis_real
  have : (ψI z).im = 0 := by
    rw [ψI_eq]
    simp [z, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im, hH2, hH3, hH4,
      Complex.im_pow_eq_zero_of_im_eq_zero hH2 2, Complex.im_pow_eq_zero_of_im_eq_zero hH3 2]
  simpa [Function.resToImagAxis, ResToImagAxis, ht, z] using this

/-- The value `ψI' (it)` is real for `t > 0`. -/
public lemma ψI'_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).im = 0 := by
  simpa [ψI', Function.resToImagAxis, ResToImagAxis, ht] using ψI_imag_axis_real t ht

end MagicFunction.g.CohnElkies

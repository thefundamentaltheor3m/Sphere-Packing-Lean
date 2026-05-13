module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IntegralA
import SpherePacking.MagicFunction.g.CohnElkies.IntegralB
import SpherePacking.MagicFunction.g.CohnElkies.IneqCommon
import SpherePacking.ModularForms.FG.Inequalities
import SpherePacking.MagicFunction.g.CohnElkies.IneqB


/-!
# Cohn-Elkies sign conditions for `g`

Sign conditions for `g` and `𝓕 g` needed for the Cohn-Elkies LP bound in dimension 8,
corresponding to (g1) and (g2) in `thm:g1`.

## Main statements
* `MagicFunction.g.CohnElkies.g_nonpos_of_norm_sq_ge_two`
* `MagicFunction.g.CohnElkies.fourier_g_nonneg`
-/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap
open MeasureTheory Real Complex

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

private lemma integral_Ioi_ofReal_mul_exp (u : ℝ) (f : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Real.exp (-π * u * t)) =
      ((∫ t in Set.Ioi (0 : ℝ), f t * Real.exp (-π * u * t) : ℝ) : ℂ) := by
  simpa [Complex.ofReal_mul, mul_left_comm, mul_comm, mul_assoc] using
    (integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ)
      (f := fun t : ℝ => f t * Real.exp (-π * u * t)))

/-- If `‖x‖ ^ 2 ≥ 2`, then the real part of `g x` is nonpositive. -/
public theorem g_nonpos_of_norm_sq_ge_two (x : ℝ⁸) (hx : 2 ≤ ‖x‖ ^ 2) : (g x).re ≤ 0 := by
  rw [g_apply_eq_gRadial_norm_sq]
  refine (isClosed_Iic.preimage
      (Complex.continuous_re.comp (SchwartzMap.continuous gRadial))).closure_subset_iff.2
    (fun u' hu' => ?_) (by simpa [closure_Ioi] using hx : ‖x‖ ^ 2 ∈ closure (Set.Ioi (2 : ℝ)))
  have hEqReal : gRadial u' = (((π / 2160 : ℝ) * (Real.sin (π * u' / 2)) ^ (2 : ℕ) *
      ∫ t in Set.Ioi (0 : ℝ), A t * Real.exp (-π * u' * t) : ℝ) : ℂ) := by
    rw [gRadial_eq_integral_A (u := u') hu', integral_Ioi_ofReal_mul_exp u' A]; push_cast; ring
  have hA_neg : ∀ {t : ℝ}, 0 < t → A t < 0 := fun {t} ht => by
    set s : ℝ := 1 / t
    have hs : 0 < s := one_div_pos.2 ht
    have hA : A t = (-(t ^ (2 : ℕ))) *
        ((FReal s + c * GReal s) / (Δ.resToImagAxis s).re) := by
      simpa [s] using A_eq_neg_mul_FG_div_Delta (t := t) ht
    simpa [hA] using mul_neg_of_neg_of_pos (neg_lt_zero.2 (pow_pos ht 2))
      (div_pos (by simpa [c] using FG_inequality_1 (t := s) hs) (Delta_imag_axis_pos.2 s hs))
  exact (congrArg Complex.re hEqReal).le.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (MeasureTheory.setIntegral_nonpos (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi fun t ht =>
        mul_nonpos_of_nonpos_of_nonneg (hA_neg ht).le (Real.exp_pos _).le))

/-- The real part of the Fourier transform `𝓕 g` is nonnegative. -/
public theorem fourier_g_nonneg : ∀ x : ℝ⁸, (𝓕 g x).re ≥ 0 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : (𝓕 g (0 : ℝ⁸)) = (1 : ℂ) := by
      simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using
        (fourier_g_zero : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g 0 = 1)
    simp [h0]
  · have hx' : 0 < ‖x‖ ^ 2 := by positivity
    set u : ℝ := ‖x‖ ^ 2 with hu
    set IB : ℝ := ∫ t in Set.Ioi (0 : ℝ), B t * Real.exp (-π * u * t)
    set s : ℝ := (π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ)
    have hEqReal : (𝓕 g x) = ((s * IB : ℝ) : ℂ) := by
      rw [show 𝓕 g x = _ from fourier_g_eq_integral_B (x := x) hx', ← hu,
        integral_Ioi_ofReal_mul_exp u B]
      push_cast [s]; ring
    have hIntegral : 0 ≤ IB :=
      MeasureTheory.setIntegral_nonneg (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t ht =>
          mul_nonneg (B_pos (t := t) ht).le (Real.exp_pos _).le
    rw [ge_iff_le, congrArg Complex.re hEqReal]
    exact mul_nonneg (by change 0 ≤ (π / 2160 : ℝ) * _; positivity) hIntegral

end MagicFunction.g.CohnElkies

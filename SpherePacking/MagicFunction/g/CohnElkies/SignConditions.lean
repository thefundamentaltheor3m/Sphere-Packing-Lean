module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IntegralA
import SpherePacking.MagicFunction.g.CohnElkies.IntegralB
import SpherePacking.MagicFunction.g.CohnElkies.IneqA
import SpherePacking.MagicFunction.g.CohnElkies.IneqB


/-!
# Cohn-Elkies sign conditions for `g`

This file proves the sign conditions for `g` and its Fourier transform needed for the
Cohn-Elkies LP bound in dimension 8. These correspond to the conditions (g1) and (g2) in the
blueprint theorem `thm:g1`.

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
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  change (∫ t : ℝ, (f t : ℂ) * Real.exp (-π * u * t) ∂ μ) =
    ((∫ t : ℝ, f t * Real.exp (-π * u * t) ∂ μ : ℝ) : ℂ)
  simpa [Complex.ofReal_mul, mul_left_comm, mul_comm, mul_assoc] using
    (integral_ofReal (μ := μ) (𝕜 := ℂ) (f := fun t : ℝ => f t * Real.exp (-π * u * t)))

lemma gRadial_re_nonpos_of_two_lt {u : ℝ} (hu : 2 < u) : (gRadial u).re ≤ 0 := by
  set IA : ℝ := ∫ t in Set.Ioi (0 : ℝ), A t * Real.exp (-π * u * t)
  have hEqReal : gRadial u =
      (((π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA : ℝ) : ℂ) := by
    rw [gRadial_eq_integral_A (u := u) hu, integral_Ioi_ofReal_mul_exp u A]
    push_cast; ring
  have hIntegral : IA ≤ 0 :=
    MeasureTheory.setIntegral_nonpos (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi fun t ht =>
        mul_nonpos_of_nonpos_of_nonneg (A_neg (t := t) ht).le (Real.exp_pos _).le
  exact (congrArg Complex.re hEqReal).le.trans
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hIntegral)

lemma gRadial_re_nonpos_of_two_le {u : ℝ} (hu : 2 ≤ u) : (gRadial u).re ≤ 0 := by
  have hclosed : IsClosed {u : ℝ | (gRadial u).re ≤ 0} :=
    isClosed_Iic.preimage (Complex.continuous_re.comp (SchwartzMap.continuous gRadial))
  have hmem : u ∈ closure (Set.Ioi (2 : ℝ)) := by simpa [closure_Ioi] using hu
  exact hclosed.closure_subset_iff.2 (fun u hu' => gRadial_re_nonpos_of_two_lt hu') hmem

/-- If `‖x‖ ^ 2 ≥ 2`, then the real part of `g x` is nonpositive. -/
public theorem g_nonpos_of_norm_sq_ge_two (x : ℝ⁸) (hx : 2 ≤ ‖x‖ ^ 2) : (g x).re ≤ 0 := by
  simpa [g_apply_eq_gRadial_norm_sq] using gRadial_re_nonpos_of_two_le (u := ‖x‖ ^ 2) hx

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

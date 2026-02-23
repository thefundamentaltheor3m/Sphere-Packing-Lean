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
  have hEq := gRadial_eq_integral_A (u := u) hu
  set IA : ℝ := ∫ t in Set.Ioi (0 : ℝ), A t * Real.exp (-π * u * t) with hIA
  have hIntA :
      (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) = (IA : ℂ) :=
    integral_Ioi_ofReal_mul_exp u A
  have hEq' : gRadial u =
      (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * (IA : ℂ) := by
    exact Eq.symm (CancelDenoms.derive_trans (id (Eq.symm hIntA)) (id (Eq.symm hEq)))
  have hEqReal : gRadial u =
      (((π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA : ℝ) : ℂ) := by
    have hcoef : (π / 2160 : ℂ) = ((π / 2160 : ℝ) : ℂ) := by
      simp
    have hEq'' := hEq'
    rw [hcoef] at hEq''
    rw [(Complex.ofReal_pow (Real.sin (π * u / 2)) (2 : ℕ)).symm] at hEq''
    rw [(Complex.ofReal_mul (π / 2160 : ℝ) ((Real.sin (π * u / 2)) ^ (2 : ℕ))).symm] at hEq''
    rw [(Complex.ofReal_mul ((π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ)) IA).symm] at hEq''
    exact hEq''
  have hRe :
      (gRadial u).re =
        (π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA := by
    have hRe0 := congrArg Complex.re hEqReal
    assumption
  have hIntegral :
      IA ≤ 0 := by
    refine MeasureTheory.setIntegral_nonpos (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi ?_
    intro t ht
    have hA : A t ≤ 0 := le_of_lt (A_neg (t := t) ht)
    have hExp : 0 ≤ Real.exp (-π * u * t) := le_of_lt (Real.exp_pos _)
    exact mul_nonpos_of_nonpos_of_nonneg hA hExp
  -- Multiply by the nonnegative prefactor.
  have hPref :
      0 ≤ (π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by
    positivity
  have hProd : (π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hPref hIntegral
  exact le_of_eq_of_le hRe hProd

lemma gRadial_re_nonpos_of_two_le {u : ℝ} (hu : 2 ≤ u) : (gRadial u).re ≤ 0 := by
  have hclosed : IsClosed {u : ℝ | (gRadial u).re ≤ 0} :=
    isClosed_Iic.preimage (Complex.continuous_re.comp (SchwartzMap.continuous gRadial))
  have hsubset : Set.Ioi (2 : ℝ) ⊆ {u : ℝ | (gRadial u).re ≤ 0} :=
    fun u hu' => gRadial_re_nonpos_of_two_lt (u := u) hu'
  have : u ∈ closure (Set.Ioi (2 : ℝ)) := by simpa [closure_Ioi] using hu
  exact (hclosed.closure_subset_iff.2 hsubset) this

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
    have hEq := fourier_g_eq_integral_B (x := x) hx'
    set IB : ℝ := ∫ t in Set.Ioi (0 : ℝ), B t * Real.exp (-π * u * t) with hIB
    have hIntB :
        (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) = (IB : ℂ) :=
      integral_Ioi_ofReal_mul_exp u B
    set s : ℝ := (π / 2160 : ℝ) * (Real.sin (π * u / 2)) ^ (2 : ℕ)
    have hEqReal : (𝓕 g x) = ((s * IB : ℝ) : ℂ) := by
      have hEq' := hEq
      rw [← hu] at hEq'
      rw [hIntB] at hEq'
      have hcoef : (π / 2160 : ℂ) = ((π / 2160 : ℝ) : ℂ) := by simp
      have hEq'' := hEq'
      rw [hcoef] at hEq''
      rw [(Complex.ofReal_pow (Real.sin (π * u / 2)) (2 : ℕ)).symm] at hEq''
      rw [(Complex.ofReal_mul (π / 2160 : ℝ) ((Real.sin (π * u / 2)) ^ (2 : ℕ))).symm] at hEq''
      simpa
    have hRe : (𝓕 g x).re = s * IB := by
      have hRe0 := congrArg Complex.re hEqReal
      assumption
    have hIntegral :
        0 ≤ IB := by
      refine MeasureTheory.setIntegral_nonneg (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi ?_
      intro t ht
      have hB : 0 ≤ B t := le_of_lt (B_pos (t := t) ht)
      have hExp : 0 ≤ Real.exp (-π * u * t) := le_of_lt (Real.exp_pos _)
      exact mul_nonneg hB hExp
    have hs : 0 ≤ s := by
      dsimp [s]
      positivity
    have hProd : 0 ≤ s * IB := mul_nonneg hs hIntegral
    exact le_of_le_of_eq hProd (id (Eq.symm hRe))

end MagicFunction.g.CohnElkies

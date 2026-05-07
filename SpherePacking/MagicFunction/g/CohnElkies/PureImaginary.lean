module
public import SpherePacking.MagicFunction.g.Basic
import SpherePacking.MagicFunction.g.CohnElkies.ImagAxisReal
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Representation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.AnotherIntegral
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.SpecialValues

/-! # Viazovska's eigenfunctions `a` and `b` are purely imaginary-valued. -/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open Complex Real MeasureTheory
open MagicFunction.FourierEigenfunctions

namespace PureImaginary

private lemma setIntegral_im_ofReal (f : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), ((f t : ℝ) : ℂ)).im = 0 := by
  simpa using congrArg Complex.im
    (integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ) (f := f))

lemma a'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (a' u).re = 0 := by
  have hEq := IntegralReps.aRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
            Real.exp (-π * u * t))
  set E : ℂ := (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
    (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u) + Iterm
  have hEq' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.aAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t => (t ^ (2 : ℕ)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
      (36 / (π ^ (2 : ℕ)) : ℝ) * Real.exp (2 * π * t) +
      (8640 / π : ℝ) * t - (18144 / (π ^ (2 : ℕ)) : ℝ)
    rw [show Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t (ht : 0 < t) => by
          rw [show φ₀'' ((Complex.I : ℂ) / (t : ℂ)) =
            ((φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re : ℂ) from by
              apply Complex.ext <;> simp [φ₀''_imag_axis_div_im t ht]]
          push_cast [innerR]; ring]
    exact setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t))
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, Complex.sub_im, hIterm, Complex.div_im, Complex.mul_im,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((π : ℂ)).im = 0 by simp) 3,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((u : ℂ)).im = 0 by simp) 2]
  rw [hEq', show ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
      (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by simp [Complex.ofReal_pow]]
  have : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  simp_all

lemma b'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (b' u).re = 0 := by
  have hEq := IntegralReps.bRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - Real.exp (2 * π * t)) *
          Real.exp (-π * u * t)
  set E : ℂ := (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + Iterm
  have hEq' : b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.bAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t =>
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) - Real.exp (2 * π * t)
    rw [show Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t (ht : 0 < t) => by
          rw [show ψI' ((Complex.I : ℂ) * (t : ℂ)) =
            ((ψI' ((Complex.I : ℂ) * (t : ℂ))).re : ℂ) from by
              apply Complex.ext <;> simp [ψI'_imag_axis_im t ht]]
          push_cast [innerR]; ring]
    exact setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t))
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, hIterm, Complex.div_im, Complex.mul_im]
  rw [hEq', show ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
      (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by simp [Complex.ofReal_pow],
    show (-4 * (Complex.I : ℂ)) * (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E =
      -4 * I * ((((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E) from by ring, Complex.mul_re,
    show ((((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * E).im = 0 from by
      rw [Complex.mul_im, hEim, Complex.ofReal_im]; simp]
  simp

/-- Extend `re = 0` from `(0,∞) \ {2}` to all of `(0,∞)` using continuity. -/
private lemma re_eq_zero_of_pos_from_ne_two (f : ℝ → ℂ) (hcont : Continuous f)
    (h : ∀ {u : ℝ}, 0 < u → u ≠ 2 → (f u).re = 0) {u : ℝ} (hu : 0 < u) : (f u).re = 0 := by
  by_cases hu2 : u = 2
  · subst hu2
    refine (IsClosed.closure_subset_iff
        (isClosed_eq (Complex.continuous_re.comp hcont) continuous_const)).2
      (fun r (hr : r ∈ Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) =>
        h hr.1 fun h' => hr.2 (by simp [h']))
      (Metric.mem_closure_iff.2 fun ε hε => ⟨2 + ε / 2,
        ⟨show (0 : ℝ) < 2 + ε / 2 by positivity,
          fun h => by linarith [show (2 + ε / 2 : ℝ) = 2 by simpa using h]⟩, ?_⟩)
    rw [Real.dist_eq, show (2 : ℝ) - (2 + ε / 2) = -(ε/2) by ring, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
  · exact h hu hu2

lemma a'_re_eq_zero_of_pos {u : ℝ} (hu : 0 < u) : (a' u).re = 0 :=
  re_eq_zero_of_pos_from_ne_two a' (SchwartzMap.continuous a') a'_re_eq_zero_of_pos_ne_two hu

lemma b'_re_eq_zero_of_pos {u : ℝ} (hu : 0 < u) : (b' u).re = 0 :=
  re_eq_zero_of_pos_from_ne_two b' (SchwartzMap.continuous b') b'_re_eq_zero_of_pos_ne_two hu

end PureImaginary

/-- The eigenfunction `a` is purely imaginary-valued (its real part vanishes). -/
public theorem a_pureImag (x : ℝ⁸) : (a x).re = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [MagicFunction.a.SpecialValues.a_zero]
  · simpa [MagicFunction.FourierEigenfunctions.a, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using PureImaginary.a'_re_eq_zero_of_pos (u := ‖x‖ ^ 2)
        (by simpa using pow_pos (norm_pos_iff.2 hx) 2)

/-- The eigenfunction `b` is purely imaginary-valued (its real part vanishes). -/
public theorem b_pureImag (x : ℝ⁸) : (b x).re = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [MagicFunction.b.SpecialValues.b_zero]
  · simpa [MagicFunction.FourierEigenfunctions.b, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using PureImaginary.b'_re_eq_zero_of_pos (u := ‖x‖ ^ 2)
        (by simpa using pow_pos (norm_pos_iff.2 hx) 2)

end MagicFunction.g.CohnElkies

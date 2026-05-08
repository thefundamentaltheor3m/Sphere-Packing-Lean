module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.ImagAxisReal
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.LaplaceRepresentation

/-!
# Integral representation for `gRadial`

This file expresses the radial profile `gRadial` as a Laplace-type integral with kernel `A(t)`.

The proof combines the Laplace representations of `a'` and `b'` with the double-zero property.
This produces the factor `sin(π u / 2)^2` where `u` is the squared norm parameter.

## Main statements
* `MagicFunction.g.CohnElkies.gRadial_eq_integral_A`
-/

namespace MagicFunction.g.CohnElkies

open MeasureTheory Real Complex
open MagicFunction.FourierEigenfunctions

/-- Laplace-type integral formula for `gRadial` in terms of the kernel `A(t)` (for `u > 2`). -/
public theorem gRadial_eq_integral_A {u : ℝ} (hu : 2 < u) : gRadial u =
    (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
    (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) := by
  set IA : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)
  set IB : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)
  have ha' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA := by
    simpa [IA, mul_assoc] using
      MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_laplace_phi0_main (u := u) hu
  have hb' : b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB := by
    simpa [IB, mul_assoc] using
      MagicFunction.g.CohnElkies.IntegralReps.bRadial_eq_laplace_psiI_main (u := u) hu
  have hg : gRadial u =
      ((↑π * Complex.I) / 8640 : ℂ) * a' u - (Complex.I / (240 * (↑π)) : ℂ) * b' u := by
    simp [gRadial, sub_eq_add_neg, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
  have hcoefA :
      ((↑π * Complex.I) / 8640 : ℂ) * (4 * (Complex.I : ℂ)) = -(π / 2160 : ℂ) := by
    ring_nf; simp; ring
  have hcoefB :
      (-(Complex.I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ)) = -(1 / (60 * π) : ℂ) := by
    field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]; ring_nf; simp
  have hA_integral : (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) =
      -IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB := by
    have hset : (∫ t in Set.Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-π * u * t)) =
        ∫ t in Set.Ioi (0 : ℝ), (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
          (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ))) *
          Real.exp (-π * u * t)) :=
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi (fun t ht => by
          simp [show (A t : ℂ) = (-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
              (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ)) by
            apply Complex.ext <;> simp [A, sub_eq_add_neg, φ₀''_imag_axis_div_im t ht,
              ψI'_imag_axis_im t ht]])
    rw [hset]
    have hIntA : IntegrableOn (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ) *
        φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegrand, mul_assoc] using
        (MagicFunction.g.CohnElkies.IntegralReps.aLaplaceIntegral_convergent (u := u) hu)
    have hIntB : IntegrableOn (fun t : ℝ => ψI' ((Complex.I : ℂ) * (t : ℂ)) *
        Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegrand] using
        (MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegral_convergent (u := u) hu)
    set c : ℂ := (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
    have hsplit : (fun t : ℝ => (((-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
        c * ψI' ((Complex.I : ℂ) * (t : ℂ))) * Real.exp (-π * u * t))) =
        fun t : ℝ => -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
          Real.exp (-π * u * t)) +
          c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) := by
      funext t; grind only [Complex.ofReal_pow]
    rw [hsplit]
    have hIntA'' : Integrable (fun t : ℝ =>
        -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := hIntA.neg
    have hIntB'' : Integrable (fun t : ℝ =>
        c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := hIntB.const_mul c
    change (∫ t : ℝ, -(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
        Real.exp (-π * u * t)) + c * (ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)) ∂
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) = -IA + c * IB
    rw [MeasureTheory.integral_add hIntA'' hIntB'']
    simp [IA, IB, c, mul_assoc, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  have hmain : ((↑π * Complex.I) / 8640 : ℂ) *
        ((4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IA) +
        (-(Complex.I / (240 * (↑π)) : ℂ)) *
        ((-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * IB) =
        (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (-IA + (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB) := by
    have h36 : (π / 2160 : ℂ) * (-(36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) = (-(1 / (60 * π)) : ℂ) := by
      exact_mod_cast show (π / 2160 : ℝ) * (-(36 / (π ^ (2 : ℕ)) : ℝ)) = -(1 / (60 * π)) by
        field_simp [Real.pi_ne_zero]; norm_num
    grind only
  simp_all

end MagicFunction.g.CohnElkies

module
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.TailDeformation

/-!
# Laplace representation for `a'`

This file proves the main Laplace representation for the radial profile `a'`, used in the
blueprint proposition `prop:a-double-zeros`.

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_laplace_phi0_main`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands

/-- Main lemma for blueprint proposition `prop:a-double-zeros`. -/
public theorem aRadial_eq_laplace_phi0_main {u : ℝ} (hu : 2 < u) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
            ((t ^ (2 : ℕ) : ℝ) : ℂ) *
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  have hu0 : 0 ≤ u := (lt_trans (by norm_num : (0 : ℝ) < 2) hu).le
  have ha : a' u = MagicFunction.a.RealIntegrals.a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) hu0)
  rw [ha]
  dsimp [MagicFunction.a.RealIntegrals.a']
  have hsplit :
      MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₂' u +
            MagicFunction.a.RealIntegrals.I₃' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₅' u + MagicFunction.a.RealIntegrals.I₆' u =
          (MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
              MagicFunction.a.RealIntegrals.I₅' u) +
            (MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₆' u) := by ring
  rw [hsplit, I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u),
    I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail (u := u) hu]
  have hseg : (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
      ∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I) := by
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [hseg]
  have hIoi :
      (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I)) +
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := by
    have h5Ioi0 : IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume :=
      by simpa [IntegrableOn, Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand] using
        (aLaplaceIntegral_convergent hu).neg'
    have h5Ioc := h5Ioi0.mono_set (fun t (ht : t ∈ Set.Ioc (0 : ℝ) 1) => ht.1)
    rw [show (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) by
      simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]]
    simpa [add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.setIntegral_union (μ := volume)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I))
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ))
        (hst := Set.Ioc_disjoint_Ioi_same)
        (ht := measurableSet_Ioi) h5Ioc (integrableOn_Φ₅'_imag_axis (u := u) hu)).symm
  set coeff : ℂ :=
    (Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))
  have hcomb :
      (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I))) +
          (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) =
        (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
    rw [← hIoi]; ring
  rw [hcomb]
  have hcoeff : coeff = -((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hrew : coeff = -((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) := by simp [coeff]; ring
    have htrig := MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u
    have hhalf := MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq u
    grind only
  have hΦ5 : (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
      - (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (g := fun t => -aLaplaceIntegrand u t)
      (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)))]
    simp [integral_neg]
  rw [hcoeff, hΦ5]
  simp [aLaplaceIntegrand, mul_assoc, mul_left_comm, mul_comm]

end MagicFunction.g.CohnElkies.IntegralReps

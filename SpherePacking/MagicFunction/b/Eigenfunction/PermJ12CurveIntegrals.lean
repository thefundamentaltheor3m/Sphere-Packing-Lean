module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.Eigenfunction.PermJ12Defs
public import SpherePacking.Contour.Segments
import SpherePacking.Contour.PermJ12CurveIntegral
import SpherePacking.Integration.EndpointIntegrability
import SpherePacking.MagicFunction.PsiTPrimeZ1
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ1
public import SpherePacking.Integration.Measure
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.Contour.GaussianIntegral


/-!
# Perm J12 Curve Integrals

This file records curve-integral representations of the primed real integrals
`J₁', J₂', J₃', J₄'`, together with auxiliary regularity and integrability lemmas.

## Main statements
* `J₃'_add_J₄'_eq_curveIntegral_segments`
* `J₁'_eq_Ioc`, `J₂'_eq_Ioc`
* `integral_rexp_neg_pi_mul_sq_norm`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral
open SpherePacking.ForMathlib
open SpherePacking.Contour


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval

lemma J₃'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₃' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁' r) z) := by
  simpa [MagicFunction.b.RealIntegrals.J₃', Ψ₁', mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₃ (f := Ψ₁' r)).symm

lemma J₄'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₄' r =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁' r) z) := by
  simpa [MagicFunction.b.RealIntegrals.J₄', Ψ₁', mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₄ (f := Ψ₁' r)).symm

/-- Combine the segment formulas for `J₃'` and `J₄'` into a single identity. -/
public lemma J₃'_add_J₄'_eq_curveIntegral_segments (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₃' r + MagicFunction.b.RealIntegrals.J₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁' r) z := by
  simp [J₃'_eq_curveIntegral_segment (r := r), J₄'_eq_curveIntegral_segment (r := r)]

/-! #### Fourier transform of the `J₁,J₂` kernels -/

/-! ##### Auxiliary integrability lemmas (`t ↦ 1/t` substitution) -/

/-- Gaussian integral in dimension `8`: `∫ exp (-π * t * ‖x‖^2) = (1 / t)^4`. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ (4 : ℕ) := by
  simpa using (SpherePacking.Contour.integral_rexp_neg_pi_mul_sq_norm_even (k := 4) (t := t) ht)

/-- Rewrite `J₁'` as a set integral over `Ioc (0, 1)`. -/
public lemma J₁'_eq_Ioc (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₁' r =
      ∫ t in Ioc (0 : ℝ) 1,
        (Complex.I : ℂ) * ψT' (z₁' t) * cexp ((π : ℂ) * I * (r : ℂ) * (z₁' t)) := by
  -- Rewrite the interval integral `∫ t in (0)..1` as a set integral over `Ioc 0 1`.
  simp [MagicFunction.b.RealIntegrals.J₁', intervalIntegral_eq_integral_uIoc, zero_le_one,
    uIoc_of_le, mul_assoc, mul_left_comm, mul_comm]

open scoped ModularForm

/-- Modular rewrite for `ψT'` on the line `z₁line`, in terms of `ψS` on the imaginary axis. -/
public lemma ψT'_z₁line_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁line t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have hz : z₁' t = z₁line t := SpherePacking.Contour.z₁'_eq_z₁line (t := t) htIcc
  simpa [hz] using MagicFunction.b.Schwartz.J1Smooth.ψT'_z₁'_eq (t := t) ht

/-- Continuity of `t ↦ ψT' (z₁line t)` on `Ioc (0, 1)`. -/
public lemma continuousOn_ψT'_z₁line :
    ContinuousOn (fun t : ℝ => ψT' (z₁line t)) (Ioc (0 : ℝ) 1) := by
  refine MagicFunction.continuousOn_ψT'_Ioc_of
      (k := 2) (ψS := ψS) (ψT' := ψT') (z := z₁line)
      (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
        MagicFunction.b.PsiBounds.continuous_ψS)
      ?_
  intro t ht
  simpa using (ψT'_z₁line_eq (t := t) ht)

/-- Rewrite `J₂'` as a set integral over `Ioc (0, 1)`. -/
public lemma J₂'_eq_Ioc (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₂' r =
      ∫ t in Ioc (0 : ℝ) 1,
        ψT' (z₂' t) * cexp ((π : ℂ) * I * (r : ℂ) * (z₂' t)) := by
  -- Rewrite the interval integral `∫ t in (0)..1` as a set integral over `Ioc 0 1`.
  simp [MagicFunction.b.RealIntegrals.J₂', intervalIntegral_eq_integral_uIoc, zero_le_one,
    uIoc_of_le, mul_assoc, mul_left_comm, mul_comm]

/-- Continuity of `t ↦ ψT' (z₂line t)` on `ℝ`. -/
public lemma continuous_ψT'_z₂line : Continuous fun t : ℝ => ψT' (z₂line t) := by
  simpa using
    SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (ψT := ψT) (ψT' := ψT') (MagicFunction.b.PsiBounds.continuous_ψT)
      (z := z₂line) continuous_z₂line (fun t => by simp [z₂line]) (fun t => by simp [ψT', z₂line])

/-- Uniform boundedness of `‖ψT' (z₂' t)‖` on `Ioc (0, 1)`. -/
public lemma exists_bound_norm_ψT'_z₂' :
    ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, ‖ψT' (z₂' t)‖ ≤ M := by
  have hcont : Continuous fun t : ℝ => ψT' (z₂line t) := continuous_ψT'_z₂line
  rcases
    SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
      (f := fun t : ℝ => ψT' (z₂line t)) hcont with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht
  have hz : z₂' t = z₂line t := SpherePacking.Contour.z₂'_eq_z₂line (t := t) (mem_Icc_of_Ioc ht)
  simpa [hz] using hM t (by simpa [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)


end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier

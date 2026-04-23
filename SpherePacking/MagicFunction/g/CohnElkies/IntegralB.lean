module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.ImagAxisReal
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Representation
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.AnotherIntegral
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.ImagAxis
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.LargeImagApprox
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Integral representation for `𝓕 g`

This file proves a Laplace-type integral representation of the Fourier transform `𝓕 g`
in terms of the kernel `B(t)`.

This corresponds to the equation "g B" in `blueprint/src/subsections/modform-ineq.tex`.

## Main statements
* `MagicFunction.g.CohnElkies.fourier_g_eq_integral_B`
-/

namespace MagicFunction.g.CohnElkies

open scoped BigOperators FourierTransform SchwartzMap Topology
open MeasureTheory Real Complex

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.FourierEigenfunctions

-- Help typeclass inference for the notation `𝓕` on Schwartz maps.
noncomputable local instance : FourierTransform (𝓢(ℝ⁸, ℂ)) (𝓢(ℝ⁸, ℂ)) :=
  ⟨FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)⟩

namespace IntegralB

lemma B_as_complex {t : ℝ} (ht : 0 < t) :
    (B t : ℂ) =
      (-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
  apply Complex.ext <;>
    simp [B, φ₀''_imag_axis_div_im (t := t) ht, ψI'_imag_axis_im (t := t) ht]

lemma B_mul_exp_eq_decomp {u t : ℝ} (ht : 0 < t) :
    (B t : ℂ) * Real.exp (-π * u * t) =
      -(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t +
          ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
            ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ) := by
  rw [IntegralB.B_as_complex (t := t) ht]
  simp [MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand,
    MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand, mul_assoc, mul_left_comm, mul_comm]
  ring_nf

private lemma integrable_aAnother {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
  MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand_integrable_of_pos (u := u) hu

private lemma integrable_bAnother {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn,
    MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand,
    MagicFunction.g.CohnElkies.IntegralReps.bAnotherBase, mul_assoc] using
    MagicFunction.g.CohnElkies.IntegralReps.bAnotherBase_integrable_exp (u := u) hu

private lemma integrable_exp_complex {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
  MagicFunction.g.CohnElkies.IntegralReps.integrableOn_exp_neg_pi_mul_Ioi_complex (u := u) hu

private lemma integrable_t_mul_exp_complex {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-π * u * t) : ℂ))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
  MagicFunction.g.CohnElkies.IntegralReps.integrableOn_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu

lemma integrableOn_B_mul_exp_neg_pi_mul {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let rhs : ℝ → ℂ := fun t =>
    ((-(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) +
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t) +
        ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))) -
      ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
  have hAe : (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) =ᵐ[μ] rhs :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      simpa [rhs, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (IntegralB.B_mul_exp_eq_decomp (u := u) (t := t) ht)
  have hRHS : Integrable rhs μ := by
    simpa [rhs] using
      ((((integrable_aAnother (u := u) hu).neg.add
          ((integrable_bAnother (u := u) hu).const_mul
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ))).add
        ((integrable_t_mul_exp_complex (u := u) hu).const_mul
          ((8640 / π : ℝ) : ℂ))).sub
      ((integrable_exp_complex (u := u) hu).const_mul
        ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ)))
  simpa [MeasureTheory.IntegrableOn, μ] using hRHS.congr hAe.symm

lemma integral_B_mul_exp_decomp {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
      -(∫ t in Set.Ioi (0 : ℝ),
          MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ),
              MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t) +
        ((8640 / π : ℝ) : ℂ) *
            (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
          ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  change (∫ t : ℝ, (B t : ℂ) * Real.exp (-π * u * t) ∂μ) =
      -(∫ t : ℝ, MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t ∂μ) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
          (∫ t : ℝ, MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t ∂μ) +
        ((8640 / π : ℝ) : ℂ) *
            (∫ t : ℝ, (t : ℂ) * (Real.exp (-π * u * t) : ℂ) ∂μ) -
          ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μ)
  let f1 : ℝ → ℂ := fun t =>
    -(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t)
  let f2 : ℝ → ℂ := fun t =>
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
      MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t
  let f3 : ℝ → ℂ := fun t =>
    ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))
  let f4 : ℝ → ℂ := fun t =>
    -((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
  have hf1 : Integrable f1 μ := (integrable_aAnother (u := u) hu).neg
  have hf2 : Integrable f2 μ := (integrable_bAnother (u := u) hu).const_mul _
  have hf3 : Integrable f3 μ := (integrable_t_mul_exp_complex (u := u) hu).const_mul _
  have hf4 : Integrable f4 μ := by
    simpa [f4, mul_assoc] using (integrable_exp_complex (u := u) hu).const_mul
      (-((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
  have hf23 : Integrable (fun t => f2 t + f3 t) μ := hf2.add hf3
  have hf234 : Integrable (fun t => (f2 t + f3 t) + f4 t) μ := hf23.add hf4
  rw [show (∫ t : ℝ, (B t : ℂ) * Real.exp (-π * u * t) ∂μ) =
        ∫ t : ℝ, (f1 t + ((f2 t + f3 t) + f4 t)) ∂μ from
      MeasureTheory.integral_congr_ae <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          simpa [f1, f2, f3, f4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc] using IntegralB.B_mul_exp_eq_decomp (u := u) (t := t) ht]
  rw [MeasureTheory.integral_add hf1 hf234, MeasureTheory.integral_add hf23 hf4,
    MeasureTheory.integral_add hf2 hf3]
  simp [f1, f2, f3, f4, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, μ,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

end IntegralB

lemma factor_sin_sq (u : ℝ) (IA IB I : ℂ)
    (hBracket :
      (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
          (1 / (60 * π) : ℂ) * ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
        (π / 2160 : ℂ) * I) :
    (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (1 / (60 * π) : ℂ) *
            ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
      (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * I := by
  grind only

lemma bracket_arith (u : ℝ) (IA IB : ℂ)
    (hπ : (π : ℂ) ≠ 0) (huC : (u : ℂ) ≠ 0) (hu2C : (u - 2 : ℂ) ≠ 0) :
    (-(π / 2160 : ℂ)) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
        (1 / (60 * π) : ℂ) * ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
      (-(π / 2160 : ℂ)) * IA +
        (1 / (60 * π) : ℂ) * IB +
        (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) -
          (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
  push_cast
  field_simp
  ring

theorem fourier_g_eq_integral_B_of_ne_two {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2)
    (hx2 : ‖x‖ ^ 2 ≠ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) *
        (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  set u : ℝ := ‖x‖ ^ 2
  have hu : 0 < u := by simpa [u] using hx
  have hu2 : u ≠ 2 := by simpa [u] using hx2
  have hFg :
      FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g =
        ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  have ha : a x = a' u := by
    simp [u, MagicFunction.FourierEigenfunctions.a,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
  have hb : b x = b' u := by
    simp [u, MagicFunction.FourierEigenfunctions.b,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
  have hFourier :
      ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        ((↑π * I) / 8640 : ℂ) * a' u + (I / (240 * (↑π)) : ℂ) * b' u := by
    show _ = _
    rw [show (𝓕 g) = FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g from rfl, hFg]
    simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, ha, hb]
  have haEq :=
    MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_another_integral_main (u := u) hu hu2
  have hbEq :=
    MagicFunction.g.CohnElkies.IntegralReps.bRadial_eq_another_integral_main (u := u) hu hu2
  set IA : ℂ :=
    ∫ t in Set.Ioi (0 : ℝ),
      ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
          Real.exp (-π * u * t))
  set IB : ℂ :=
    ∫ t in Set.Ioi (0 : ℝ),
      (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t)) : ℂ)) *
        Real.exp (-π * u * t)
  have haEq' : a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) := by simpa [IA] using haEq
  have hbEq' : b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by simpa [IB] using hbEq
  have hcoefA :
      (((↑π * I) / 8640 : ℂ) * (4 * (Complex.I : ℂ))) = -(π / 2160 : ℂ) := by
    ring_nf; simp; ring
  have hcoefB :
      (((I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ))) = (1 / (60 * π) : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hπ]; ring_nf; simp
  have hIexp :
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ) :=
    MagicFunction.g.CohnElkies.IntegralReps.integral_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hItExp :
      (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) :=
      IntegralReps.integral_mul_exp_neg_pi_mul_Ioi_complex hx
  have hAterm :
      ((↑π * I) / 8640 : ℂ) * a' u =
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) := by
    rw [haEq']
    linear_combination
      ((Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA)) * hcoefA
  have hBterm :
      (I / (240 * (↑π)) : ℂ) * b' u =
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (1 / (60 * π) : ℂ) *
            ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by
    rw [hbEq']
    linear_combination
      ((Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB)) * hcoefB
  have hFourier' :
      ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (1 / (60 * π) : ℂ) *
              ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by
    rw [hFourier, hAterm, hBterm]
  have hIA :
      (∫ t in Set.Ioi (0 : ℝ),
          MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) = IA := by
    simp [IA, MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand]
  have hIB :
      (∫ t in Set.Ioi (0 : ℝ),
          MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t) = IB := by
    simp [IB, MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand]
  have hBdecomp :
      (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        -IA + ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB +
          ((8640 / π : ℝ) : ℂ) *
              (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
            ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
              (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) := by
    simpa [hIA, hIB] using IntegralB.integral_B_mul_exp_decomp (u := u) hu
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hu2C : (u - 2 : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hu2
  have hBscaled :
      (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        (-(π / 2160 : ℂ)) * IA +
          (1 / (60 * π) : ℂ) * IB +
          (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) -
            (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
    rw [hBdecomp, hItExp, hIexp]
    push_cast
    field_simp
    ring
  have hBracket :
      (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
          (1 / (60 * π) : ℂ) *
              ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
        (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) :=
    (bracket_arith (u := u) (IA := IA) (IB := IB) hπ huC hu2C).trans hBscaled.symm
  simpa [u, mul_assoc] using
    (show ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        (π / 2160 : ℂ) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) from by
      rw [hFourier']
      exact factor_sin_sq u IA IB
        (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) hBracket)

/-- Integral representation of `𝓕 g` in terms of `B(t)` (for `0 < ‖x‖ ^ 2`). -/
public theorem fourier_g_eq_integral_B {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) *
        (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  by_cases hx2 : ‖x‖ ^ 2 = 2
  · have hsin : Real.sin (π * (‖x‖ ^ 2) / 2) = 0 := by rw [hx2]; simp
    have hRHS :
        (π / 2160 : ℂ) *
            (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
              (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) = 0 := by
      simp [hsin]
    let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
    let xseq : ℕ → ℝ⁸ := fun n => (c n) • x
    have hc : Filter.Tendsto c Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa [c] using tendsto_const_nhds.add
        (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) :
          Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0))
    have hxseq : Filter.Tendsto xseq Filter.atTop (𝓝 x) := by
      simpa [xseq] using hc.smul_const x
    have hFseq :
        Filter.Tendsto (fun n : ℕ => (𝓕 g : 𝓢(ℝ⁸, ℂ)) (xseq n)) Filter.atTop
          (𝓝 ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x)) :=
      ((SchwartzMap.continuous (𝓕 g : 𝓢(ℝ⁸, ℂ))).tendsto x).comp hxseq
    let useq : ℕ → ℝ := fun n => ‖xseq n‖ ^ 2
    have huseq_gt2 : ∀ n : ℕ, 2 < useq n := fun n => by
      have hcn_pos : 0 < c n := by positivity
      have hcn_one : 1 < c n := by
        have h1 : 0 < (1 / ((n : ℝ) + 1)) := by positivity
        linarith
      rw [show useq n = (c n) ^ (2 : ℕ) * (‖x‖ ^ 2) from by
        simp [useq, xseq, norm_smul, abs_of_pos hcn_pos, pow_two, mul_assoc, mul_left_comm,
          mul_comm], hx2]
      nlinarith [sq_nonneg (c n - 1)]
    have hEqseq :
        ∀ n : ℕ,
          ((𝓕 g : 𝓢(ℝ⁸, ℂ)) (xseq n)) =
            (π / 2160 : ℂ) *
              (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
                (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)) := fun n => by
      simpa [useq] using fourier_g_eq_integral_B_of_ne_two (x := xseq n)
        (by simpa [useq] using lt_trans (by norm_num) (huseq_gt2 n))
        (by simpa [useq] using ne_of_gt (huseq_gt2 n))
    -- Show the RHS tends to `0` by bounding the `B`-integral uniformly and using `sin^2 → 0`.
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    let M : ℝ :=
      ∫ t : ℝ, ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ ∂μ
    have hM_int :
        Integrable (fun t : ℝ => ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖) μ := by
      simpa using (IntegralB.integrableOn_B_mul_exp_neg_pi_mul (u := 2) (by positivity)).norm
    have hInt_bound :
        ∀ n : ℕ,
          ‖∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ ≤ M := fun n =>
      norm_integral_le_of_norm_le hM_int <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          have ht0 : 0 ≤ t := le_of_lt ht
          have hexp : Real.exp (-π * useq n * t) ≤ Real.exp (-π * (2 : ℝ) * t) :=
            Real.exp_le_exp.2 (by
              have := mul_le_mul_of_nonneg_right (le_of_lt (huseq_gt2 n)) ht0
              nlinarith [Real.pi_pos])
          rw [show ‖(B t : ℂ) * Real.exp (-π * useq n * t)‖ =
                ‖(B t : ℂ)‖ * Real.exp (-π * useq n * t) by
              rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le],
            show ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ =
                ‖(B t : ℂ)‖ * Real.exp (-π * (2 : ℝ) * t) by
              rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]]
          exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    have hsin_tendsto :
        Filter.Tendsto (fun n : ℕ => (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop
          (𝓝 (0 : ℝ)) := by
      have hu_tendsto : Filter.Tendsto useq Filter.atTop (𝓝 (2 : ℝ)) := by
        simpa [useq, hx2] using ((by continuity : Continuous (fun y : ℝ⁸ => ‖y‖ ^ 2)).tendsto
          x).comp hxseq
      simpa using
        (show ContinuousAt (fun u : ℝ => (Real.sin (π * u / 2)) ^ (2 : ℕ)) (2 : ℝ) by
          fun_prop).tendsto.comp hu_tendsto
    have hRHSseq0 :
        Filter.Tendsto
            (fun n : ℕ =>
              (π / 2160 : ℂ) *
                (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
                  (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)))
            Filter.atTop (𝓝 (0 : ℂ)) := by
      refine (tendsto_zero_iff_norm_tendsto_zero).2 <|
        squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
          ((tendsto_const_nhds.mul hsin_tendsto).trans (by simp) :
            Filter.Tendsto (fun n : ℕ =>
              (‖(π / 2160 : ℂ)‖ * M) * (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ))
              Filter.atTop (𝓝 (0 : ℝ)))
      rw [norm_mul, norm_mul,
        show ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ =
            (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) from by
          simpa [pow_two] using
            Complex.norm_of_nonneg (sq_nonneg (Real.sin (π * (useq n) / 2))),
        mul_right_comm]
      gcongr
      exact hInt_bound n
    rw [tendsto_nhds_unique hFseq ((Filter.tendsto_congr hEqseq).mpr hRHSseq0)]
    exact hRHS.symm
  · exact fourier_g_eq_integral_B_of_ne_two (x := x) hx hx2

end MagicFunction.g.CohnElkies

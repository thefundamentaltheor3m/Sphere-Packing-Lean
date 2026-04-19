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
  have hφim : (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).im = 0 :=
    φ₀''_imag_axis_div_im (t := t) ht
  have hψim : (ψI' ((Complex.I : ℂ) * (t : ℂ))).im = 0 :=
    ψI'_imag_axis_im (t := t) ht
  apply Complex.ext <;> simp [B, hφim, hψim]

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
    Integrable
      (fun t : ℝ => MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn] using
    (MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand_integrable_of_pos
      (u := u) hu)

private lemma integrable_bAnother {u : ℝ} (hu : 0 < u) :
    Integrable
      (fun t : ℝ => MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  have hBase :
      Integrable
        (fun t : ℝ =>
          MagicFunction.g.CohnElkies.IntegralReps.bAnotherBase t *
            (Real.exp (-π * u * t) : ℂ))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn] using
      (MagicFunction.g.CohnElkies.IntegralReps.bAnotherBase_integrable_exp (u := u) hu)
  simpa [MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand,
    MagicFunction.g.CohnElkies.IntegralReps.bAnotherBase, mul_assoc] using hBase

private lemma integrable_exp_complex {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn] using
    (MagicFunction.g.CohnElkies.IntegralReps.integrableOn_exp_neg_pi_mul_Ioi_complex
      (u := u) hu)

private lemma integrable_t_mul_exp_complex {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-π * u * t) : ℂ))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn] using
    (MagicFunction.g.CohnElkies.IntegralReps.integrableOn_mul_exp_neg_pi_mul_Ioi_complex
      (u := u) hu)

lemma integrableOn_B_mul_exp_neg_pi_mul {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let rhs : ℝ → ℂ := fun t =>
    ((-(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) +
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t) +
        ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))) -
      ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
  have hAe :
      (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) =ᵐ[μ] rhs := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    simpa [rhs, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IntegralB.B_mul_exp_eq_decomp (u := u) (t := t) ht)
  have hA := integrable_aAnother (u := u) hu
  have hB := integrable_bAnother (u := u) hu
  have hExp := integrable_exp_complex (u := u) hu
  have hTExp := integrable_t_mul_exp_complex (u := u) hu
  have hcoefB := hB.const_mul ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
  have hcoefT := hTExp.const_mul ((8640 / π : ℝ) : ℂ)
  have hcoefE := hExp.const_mul ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
  have hRHS : Integrable rhs μ := by
    simpa [rhs] using ((hA.neg.add hcoefB).add hcoefT).sub hcoefE
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
  have hcongr :
      (∫ t : ℝ, (B t : ℂ) * Real.exp (-π * u * t) ∂μ) =
        ∫ t : ℝ,
          (-(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) +
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                  MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t +
                ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
                  ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                    (Real.exp (-π * u * t) : ℂ)) ∂μ := by
    refine MeasureTheory.integral_congr_ae <|
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      IntegralB.B_mul_exp_eq_decomp (u := u) (t := t) ht
  have hA := integrable_aAnother (u := u) hu
  have hB := integrable_bAnother (u := u) hu
  have hExp := integrable_exp_complex (u := u) hu
  have hTExp := integrable_t_mul_exp_complex (u := u) hu
  let f1 : ℝ → ℂ := fun t =>
    -(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t)
  let f2 : ℝ → ℂ := fun t =>
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
      MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t
  let f3 : ℝ → ℂ := fun t =>
    ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))
  let f4 : ℝ → ℂ := fun t =>
    -((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
  have hf1 : Integrable f1 μ := hA.neg
  have hf2 : Integrable f2 μ := by simpa [f2] using hB.const_mul _
  have hf3 : Integrable f3 μ := by simpa [f3] using hTExp.const_mul _
  have hf4 : Integrable f4 μ := by
    simpa [f4, mul_assoc] using hExp.const_mul (-((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
  have hf23 : Integrable (fun t => f2 t + f3 t) μ := hf2.add hf3
  have hf234 : Integrable (fun t => (f2 t + f3 t) + f4 t) μ := hf23.add hf4
  have hsplit :
      (∫ t : ℝ, (f1 t + ((f2 t + f3 t) + f4 t)) ∂μ) =
        (∫ t : ℝ, f1 t ∂μ) +
          (∫ t : ℝ, f2 t ∂μ) + (∫ t : ℝ, f3 t ∂μ) + (∫ t : ℝ, f4 t ∂μ) := by
    rw [MeasureTheory.integral_add hf1 hf234, MeasureTheory.integral_add hf23 hf4,
      MeasureTheory.integral_add hf2 hf3]
    ring_nf
  rw [hcongr]
  have hrew :
      (fun t : ℝ =>
          (-(MagicFunction.g.CohnElkies.IntegralReps.aAnotherIntegrand u t) +
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                  MagicFunction.g.CohnElkies.IntegralReps.bAnotherIntegrand u t +
                ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
                  ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ))) =
    fun t : ℝ => f1 t + ((f2 t + f3 t) + f4 t) := by
    funext t
    simp [f1, f2, f3, f4, sub_eq_add_neg, add_left_comm, add_comm, mul_assoc]
  rw [hrew, hsplit]
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
  have hcast_u : ((1 / (π * u) : ℝ) : ℂ) = (1 : ℂ) / ((π : ℂ) * (u : ℂ)) := by
    simp [Complex.ofReal_mul]
  have hcast_u2 :
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) = (1 : ℂ) / (((π : ℂ) * (u : ℂ)) ^ (2 : ℕ)) := by
    simp [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hcast_u2, hcast_u]
  field_simp [hπ, huC, hu2C]
  ring_nf

theorem fourier_g_eq_integral_B_of_ne_two {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2)
    (hx2 : ‖x‖ ^ 2 ≠ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) *
        (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  -- Abbreviate `u = ‖x‖^2`.
  set u : ℝ := ‖x‖ ^ 2
  have hu : 0 < u := by simpa [u] using hx
  have hu2 : u ≠ 2 := by simpa [u] using hx2
  -- Rewrite `𝓕 g` using the Fourier eigenfunction identities for `a` and `b`.
  have hF : (𝓕 g) = FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g := by
    rfl
  have hFg :
      FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g =
        ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  -- Reduce to the 1D radial profiles `a'` and `b'`.
  have ha : a x = a' u := by
    simp [u, MagicFunction.FourierEigenfunctions.a,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
  have hb : b x = b' u := by
    simp [u, MagicFunction.FourierEigenfunctions.b,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
  have hFourier :
      ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        ((↑π * I) / 8640 : ℂ) * a' u + (I / (240 * (↑π)) : ℂ) * b' u := by
    rw [hF, hFg]
    simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, ha, hb]
  -- Apply the "another integral" formulas for `a'` and `b'`.
  have haEq :=
    MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_another_integral_main
      (u := u) hu hu2
  have hbEq :=
    MagicFunction.g.CohnElkies.IntegralReps.bRadial_eq_another_integral_main
      (u := u) hu hu2
  -- Abbreviate the integrals appearing in the "another integral" representations.
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
  have haEq' :
      a' u =
        (4 * (Complex.I : ℂ)) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) := by
    simpa [IA] using haEq
  have hbEq' :
      b' u =
        (-4 * (Complex.I : ℂ)) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by
    simpa [IB] using hbEq
  have hcoefA :
      (((↑π * I) / 8640 : ℂ) * (4 * (Complex.I : ℂ))) = -(π / 2160 : ℂ) := by
    ring_nf
    simp
    ring
  have hcoefB :
      (((I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ))) = (1 / (60 * π) : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hπ]
    ring_nf
    simp
  have hIexp :
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ) :=
    MagicFunction.g.CohnElkies.IntegralReps.integral_exp_neg_pi_mul_Ioi_complex
      (u := u) hu
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
    -- Combine the `a'` and `b'` contributions, avoiding a large `simp` search.
    rw [hFourier]
    rw [hAterm, hBterm]
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
    have h := IntegralB.integral_B_mul_exp_decomp (u := u) hu
    simpa [hIA, hIB] using h
  -- Turn the bracketed combination into the decomposed `B`-integral and simplify coefficients.
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  have hu2C : (u - 2 : ℂ) ≠ 0 := by
    have : (u - 2 : ℝ) ≠ 0 := sub_ne_zero.2 hu2
    exact_mod_cast this
  have hBscaled :
      (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        (-(π / 2160 : ℂ)) * IA +
          (1 / (60 * π) : ℂ) * IB +
          (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) -
            (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
    -- Expand the decomposition.
    rw [hBdecomp]
    -- Evaluate the two elementary Laplace integrals.
    rw [hItExp, hIexp]
    -- Coefficient simplifications (only involve π).
    have hcoef36 :
        (π / 2160 : ℂ) * ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) = (1 / (60 * π) : ℂ) := by
      -- Move all casts/divisions into `ℂ` before clearing denominators.
      simp [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [hπ]
      norm_num
    have hcoef8640 : (π / 2160 : ℂ) * ((8640 / π : ℝ) : ℂ) = (4 : ℂ) := by
      simp [Complex.ofReal_div]
      field_simp [hπ]
      norm_num
    have hcoef12960 :
        (π / 2160 : ℂ) * ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) = (6 / π : ℂ) := by
      simp [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [hπ]
      norm_num
    -- Distribute the scalar multiplication over the decomposition and rewrite the coefficients.
    rw [mul_sub]
    -- Expand the three-term sum `(-IA + c36*IB + c8640*J1)`:
    rw [mul_add]
    rw [mul_add]
    -- Rewrite each coefficient product.
    have hIB :
        (π / 2160 : ℂ) * (((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB) =
          (1 / (60 * π) : ℂ) * IB := by
      calc
        (π / 2160 : ℂ) * (((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB) =
            ((π / 2160 : ℂ) * ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) * IB := by
              rw [← mul_assoc]
        _ = (1 / (60 * π) : ℂ) * IB :=
              congrArg (fun z : ℂ => z * IB) hcoef36
    have hJ1coef :
        (π / 2160 : ℂ) *
              (((8640 / π : ℝ) : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)) =
            (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
      calc
        (π / 2160 : ℂ) *
              (((8640 / π : ℝ) : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)) =
            ((π / 2160 : ℂ) * ((8640 / π : ℝ) : ℂ)) *
              ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
              rw [← mul_assoc]
        _ = (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
              exact
                congrArg (fun z : ℂ => z * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)) hcoef8640
    have hJ0coef :
        (π / 2160 : ℂ) *
              (((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ((1 / (π * u) : ℝ) : ℂ)) =
            (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
      calc
        (π / 2160 : ℂ) *
              (((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ((1 / (π * u) : ℝ) : ℂ)) =
            ((π / 2160 : ℂ) * ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
              ((1 / (π * u) : ℝ) : ℂ) := by
              rw [← mul_assoc]
        _ = (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
              exact congrArg (fun z : ℂ => z * ((1 / (π * u) : ℝ) : ℂ)) hcoef12960
    -- Apply the coefficient rewrites.
    rw [hIB, hJ1coef, hJ0coef]
    -- Only the `(-IA)` factor remains; rewrite it and reassociate.
    ring
  have hBracket :
      (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
          (1 / (60 * π) : ℂ) *
              ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
        (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) := by
    -- Compare with the scaled decomposition: the `(u-2)` terms cancel, the rest matches `hBscaled`.
    have hBracket' := bracket_arith (u := u) (IA := IA) (IB := IB) hπ huC hu2C
    exact hBracket'.trans hBscaled.symm
  -- Finish by factoring out `sin^2`.
  have hFactor :
      ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        (π / 2160 : ℂ) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) := by
    rw [hFourier']
    exact
      factor_sin_sq u IA IB
        (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) hBracket
  simpa [u, mul_assoc] using hFactor

/-- Integral representation of `𝓕 g` in terms of `B(t)` (for `0 < ‖x‖ ^ 2`). -/
public theorem fourier_g_eq_integral_B {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) *
        (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  by_cases hx2 : ‖x‖ ^ 2 = 2
  · -- `sin (π*2/2)=0`, so the RHS is `0`. Show the LHS vanishes by a continuity argument.
    have hsin : Real.sin (π * (‖x‖ ^ 2) / 2) = 0 := by
      rw [hx2]
      simp
    have hRHS :
        (π / 2160 : ℂ) *
            (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
              (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) =
          0 := by
      simp [hsin]
    -- Define a sequence of scalings `xₙ = cₙ • x` with `‖xₙ‖^2 > 2` and `xₙ → x`.
    let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
    let xseq : ℕ → ℝ⁸ := fun n => (c n) • x
    have hc : Filter.Tendsto c Filter.atTop (𝓝 (1 : ℝ)) := by
      have hdiv :
          Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop
            (𝓝 (0 : ℝ)) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [c] using (tendsto_const_nhds.add hdiv)
    have hxseq : Filter.Tendsto xseq Filter.atTop (𝓝 x) := by
      simpa [xseq] using hc.smul_const x
    have hFseq :
        Filter.Tendsto (fun n : ℕ => (𝓕 g : 𝓢(ℝ⁸, ℂ)) (xseq n)) Filter.atTop
          (𝓝 ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x)) :=
      ((SchwartzMap.continuous (𝓕 g : 𝓢(ℝ⁸, ℂ))).tendsto x).comp hxseq
    let useq : ℕ → ℝ := fun n => ‖xseq n‖ ^ 2
    have huseq_gt2 : ∀ n : ℕ, 2 < useq n := by
      intro n
      have hcn_pos : 0 < c n := by positivity
      have hcn_one : 1 < c n := by
        have : 0 < (1 / ((n : ℝ) + 1)) := by positivity
        linarith [this]
      have hcn_sq : 1 < (c n) ^ (2 : ℕ) := by
        have hmul : c n < c n * c n := by
          simpa [mul_assoc] using (mul_lt_mul_of_pos_right hcn_one hcn_pos)
        have : 1 < c n * c n := lt_trans hcn_one hmul
        simpa [pow_two] using this
      have hnormsq :
          useq n = (c n) ^ (2 : ℕ) * (‖x‖ ^ 2) := by
        simp [useq, xseq, norm_smul, abs_of_pos hcn_pos, pow_two,
          mul_assoc, mul_left_comm, mul_comm]
      rw [hnormsq, hx2]
      nlinarith [hcn_sq]
    have hEqseq :
        ∀ n : ℕ,
          ((𝓕 g : 𝓢(ℝ⁸, ℂ)) (xseq n)) =
            (π / 2160 : ℂ) *
              (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
                (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)) := by
      intro n
      have hxpos : 0 < ‖xseq n‖ ^ 2 := by
        have : 0 < useq n := lt_trans (by norm_num) (huseq_gt2 n)
        simpa [useq] using this
      have hxne : ‖xseq n‖ ^ 2 ≠ 2 := by
        have : useq n ≠ 2 := ne_of_gt (huseq_gt2 n)
        simpa [useq] using this
      simpa [useq] using fourier_g_eq_integral_B_of_ne_two (x := xseq n) hxpos hxne
    -- Show the RHS tends to `0` by bounding the `B`-integral uniformly and using `sin^2 → 0`.
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    let M : ℝ :=
      ∫ t : ℝ, ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ ∂μ
    have hM_int :
        Integrable (fun t : ℝ => ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖) μ := by
      have hI2 :
          Integrable (fun t : ℝ => (B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)) μ := by
        have hI2' :
            IntegrableOn
                (fun t : ℝ => (B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)) (Set.Ioi (0 : ℝ)) :=
          IntegralB.integrableOn_B_mul_exp_neg_pi_mul (u := 2) (by positivity)
        simpa [MeasureTheory.IntegrableOn, μ] using hI2'
      simpa using hI2.norm
    have hInt_bound :
        ∀ n : ℕ,
          ‖∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ ≤ M := by
      intro n
      have hle :
          ∀ᵐ t ∂μ,
            ‖(B t : ℂ) * Real.exp (-π * (useq n) * t)‖ ≤
              ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ := by
        refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_)
        intro t ht
        have ht0 : 0 < t := ht
        have ht0' : 0 ≤ t := le_of_lt ht0
        have hnegπ : (-π : ℝ) ≤ 0 := by
          have : (0 : ℝ) ≤ π := le_of_lt Real.pi_pos
          exact neg_nonpos.mpr this
        have hmul : (2 : ℝ) * t ≤ (useq n) * t :=
          mul_le_mul_of_nonneg_right (le_of_lt (huseq_gt2 n)) ht0'
        have hexparg :
            (-π : ℝ) * ((useq n) * t) ≤ (-π : ℝ) * ((2 : ℝ) * t) :=
          mul_le_mul_of_nonpos_left hmul hnegπ
        have hexp :
            Real.exp ((-π : ℝ) * ((useq n) * t)) ≤ Real.exp ((-π : ℝ) * ((2 : ℝ) * t)) :=
          Real.exp_le_exp.2 hexparg
        -- Convert the exponential bound into a norm inequality.
        have hBN : 0 ≤ ‖(B t : ℂ)‖ := norm_nonneg _
        have hexp_nonneg : 0 ≤ Real.exp (-π * (useq n) * t) := le_of_lt (Real.exp_pos _)
        have hexp2_nonneg : 0 ≤ Real.exp (-π * (2 : ℝ) * t) := le_of_lt (Real.exp_pos _)
        have hnorm2 :
            ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ =
              ‖(B t : ℂ)‖ * Real.exp (-π * (2 : ℝ) * t) := by
          -- `‖z * r‖ = ‖z‖ * r` for `r ≥ 0`.
            calc
              ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ =
                  ‖(B t : ℂ)‖ * ‖((Real.exp (-π * (2 : ℝ) * t)) : ℂ)‖ := by
                    simp
            _ = ‖(B t : ℂ)‖ * Real.exp (-π * (2 : ℝ) * t) := by
                  rw [Complex.norm_of_nonneg hexp2_nonneg]
        calc
          ‖(B t : ℂ) * Real.exp (-π * (useq n) * t)‖
              = ‖(B t : ℂ)‖ * Real.exp (-π * (useq n) * t) := by
                  calc
                      ‖(B t : ℂ) * Real.exp (-π * (useq n) * t)‖ =
                          ‖(B t : ℂ)‖ * ‖((Real.exp (-π * (useq n) * t)) : ℂ)‖ := by
                            simp
                    _ = ‖(B t : ℂ)‖ * Real.exp (-π * (useq n) * t) := by
                          rw [Complex.norm_of_nonneg hexp_nonneg]
          _ = ‖(B t : ℂ)‖ * Real.exp ((-π : ℝ) * ((useq n) * t)) := by
                  simp [mul_assoc]
          _ ≤ ‖(B t : ℂ)‖ * Real.exp ((-π : ℝ) * ((2 : ℝ) * t)) :=
                  mul_le_mul_of_nonneg_left hexp hBN
          _ = ‖(B t : ℂ)‖ * Real.exp (-π * (2 : ℝ) * t) := by
                  simp [mul_assoc]
          _ = ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖ :=
                  hnorm2.symm
      -- Apply `norm_integral_le_of_norm_le` on the restricted measure.
      exact norm_integral_le_of_norm_le hM_int hle
    have hsin_tendsto :
        Filter.Tendsto (fun n : ℕ => (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop
          (𝓝 (0 : ℝ)) := by
      have hu_tendsto : Filter.Tendsto useq Filter.atTop (𝓝 (2 : ℝ)) := by
        have hcontU : Continuous (fun y : ℝ⁸ => ‖y‖ ^ 2) := by
          continuity
        simpa [useq, hx2] using (hcontU.tendsto x).comp hxseq
      have hcontS :
          ContinuousAt (fun u : ℝ => (Real.sin (π * u / 2)) ^ (2 : ℕ)) (2 : ℝ) := by
        have hlin : Continuous (fun u : ℝ => π * u / 2) := by
          fun_prop
        have hsin : Continuous (fun u : ℝ => Real.sin (π * u / 2)) :=
          Real.continuous_sin.comp hlin
        exact (hsin.pow 2).continuousAt
      simpa using (hcontS.tendsto.comp hu_tendsto)
    have hRHSseq0 :
        Filter.Tendsto
            (fun n : ℕ =>
              (π / 2160 : ℂ) *
                (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
                  (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)))
            Filter.atTop (𝓝 (0 : ℂ)) := by
      refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
      have hle' :
          ∀ n : ℕ,
            ‖(π / 2160 : ℂ) *
                  (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
                    (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t))‖
              ≤ (‖(π / 2160 : ℂ)‖ * M) * (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) := by
        intro n
        have hsin_nonneg : 0 ≤ (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) := by positivity
        calc
          ‖(π / 2160 : ℂ) *
                (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
                  (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t))‖
                  = ‖(π / 2160 : ℂ)‖ *
                    ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ *
                      ‖∫ t in Set.Ioi (0 : ℝ),
                          (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ := by
                  have h₁ :
                      ‖(π / 2160 : ℂ) *
                            ((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ =
                        ‖(π / 2160 : ℂ)‖ *
                          ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ := by
                    simp
                  have h₂ :
                      ‖(π / 2160 : ℂ) *
                            ((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ) *
                          (∫ t in Set.Ioi (0 : ℝ),
                                (B t : ℂ) * Real.exp (-π * (useq n) * t))‖ =
                        ‖(π / 2160 : ℂ) *
                              ((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ *
                            ‖∫ t in Set.Ioi (0 : ℝ),
                                  (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ := by
                    simp [mul_assoc]
                  calc
                    ‖(π / 2160 : ℂ) *
                          ((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ) *
                        (∫ t in Set.Ioi (0 : ℝ),
                              (B t : ℂ) * Real.exp (-π * (useq n) * t))‖
                        =
                        ‖(π / 2160 : ℂ) *
                              ((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ *
                            ‖∫ t in Set.Ioi (0 : ℝ),
                                  (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ := h₂
                    _ =
                        (‖(π / 2160 : ℂ)‖ *
                            ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖) *
                          ‖∫ t in Set.Ioi (0 : ℝ),
                                (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ := by
                      simp
                    _ = ‖(π / 2160 : ℂ)‖ *
                          ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ *
                        ‖∫ t in Set.Ioi (0 : ℝ),
                              (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ := by
                      simp [mul_assoc]
          _ ≤ ‖(π / 2160 : ℂ)‖ *
                ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ * M := by
                gcongr
                exact hInt_bound n
          _ = (‖(π / 2160 : ℂ)‖ * M) * (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) := by
                have hnorm_sin :
                    ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ =
                      (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) := by
                  simpa [pow_two] using
                    (Complex.norm_of_nonneg (sq_nonneg (Real.sin (π * (useq n) / 2))))
                calc
                  ‖(π / 2160 : ℂ)‖ *
                        ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ * M =
                      ‖(π / 2160 : ℂ)‖ * M *
                        ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ := by
                    ac_rfl
                  _ = ‖(π / 2160 : ℂ)‖ * M * (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) := by
                    rw [hnorm_sin]
      have hbound_tendsto :
          Filter.Tendsto
              (fun n : ℕ =>
                (‖(π / 2160 : ℂ)‖ * M) * (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ))
              Filter.atTop (𝓝 (0 : ℝ)) :=
        (tendsto_const_nhds.mul hsin_tendsto).trans (by simp)
      exact squeeze_zero (fun _ => norm_nonneg _) hle' hbound_tendsto
    have hSeq0 :
        Filter.Tendsto (fun n : ℕ => (𝓕 g : 𝓢(ℝ⁸, ℂ)) (xseq n)) Filter.atTop
          (𝓝 (0 : ℂ)) :=
      (Filter.tendsto_congr hEqseq).mpr hRHSseq0
    have hLHS : ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) = 0 := tendsto_nhds_unique hFseq hSeq0
    -- Avoid `simp` rewriting `Real.sin` into `Complex.sin`.
    rw [hLHS]
    exact hRHS.symm
  · exact fourier_g_eq_integral_B_of_ne_two (x := x) hx hx2

end MagicFunction.g.CohnElkies

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
open MagicFunction.g.CohnElkies.IntegralReps

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
  apply Complex.ext <;> simp [B, φ₀''_imag_axis_div_im (t := t) ht, ψI'_imag_axis_im (t := t) ht]

lemma B_mul_exp_eq_decomp {u t : ℝ} (ht : 0 < t) :
    (B t : ℂ) * Real.exp (-π * u * t) =
      -(aAnotherIntegrand u t) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * bAnotherIntegrand u t +
          ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
            ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ) := by
  simp [IntegralB.B_as_complex (t := t) ht, aAnotherIntegrand, bAnotherIntegrand,
    mul_assoc, mul_left_comm, mul_comm]; ring_nf

private lemma integrable_bAnother {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => bAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn, bAnotherIntegrand, bAnotherBase, mul_assoc] using
    bAnotherBase_integrable_exp hu

lemma integrableOn_B_mul_exp_neg_pi_mul {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) :=
  ((((aAnotherIntegrand_integrable_of_pos hu).neg.add
    ((integrable_bAnother hu).const_mul ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ))).add
      ((integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu).const_mul ((8640 / π : ℝ) : ℂ))).sub
    ((integrableOn_exp_neg_pi_mul_Ioi_complex hu).const_mul
      ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ))).congr <|
  MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IntegralB.B_mul_exp_eq_decomp (t := t) ht).symm

lemma integral_B_mul_exp_decomp {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
      -(∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) +
        ((8640 / π : ℝ) : ℂ) *
            (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
          ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let f1 : ℝ → ℂ := fun t => -(aAnotherIntegrand u t)
  let f2 : ℝ → ℂ := fun t => ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * bAnotherIntegrand u t
  let f3 : ℝ → ℂ := fun t => ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))
  let f4 : ℝ → ℂ := fun t =>
    -((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
  have hf1 : Integrable f1 μ := (aAnotherIntegrand_integrable_of_pos hu).neg
  have hf2 : Integrable f2 μ := (integrable_bAnother hu).const_mul _
  have hf3 : Integrable f3 μ := (integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu).const_mul _
  have hf4 : Integrable f4 μ := by simpa [f4, mul_assoc] using
    (integrableOn_exp_neg_pi_mul_Ioi_complex hu).const_mul (-((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
  have hf23 : Integrable (fun t => f2 t + f3 t) μ := hf2.add hf3
  have hf234 : Integrable (fun t => (f2 t + f3 t) + f4 t) μ := hf23.add hf4
  rw [show (∫ t : ℝ, (B t : ℂ) * Real.exp (-π * u * t) ∂μ) =
        ∫ t : ℝ, (f1 t + ((f2 t + f3 t) + f4 t)) ∂μ from
      MeasureTheory.integral_congr_ae <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          simpa [f1, f2, f3, f4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc] using IntegralB.B_mul_exp_eq_decomp (t := t) ht,
    MeasureTheory.integral_add hf1 hf234, MeasureTheory.integral_add hf23 hf4,
    MeasureTheory.integral_add hf2 hf3]
  simp [f1, f2, f3, f4, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, μ,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

end IntegralB

theorem fourier_g_eq_integral_B_of_ne_two {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2)
    (hx2 : ‖x‖ ^ 2 ≠ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) *
        (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  set u : ℝ := ‖x‖ ^ 2
  have hFourier :
      ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        ((↑π * I) / 8640 : ℂ) * a' u + (I / (240 * (↑π)) : ℂ) * b' u := by
    change (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g) x = _
    rw [show FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g =
        ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b from by
      simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
        -FourierTransform.fourierCLE_apply]]
    simp [u, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul,
      MagicFunction.FourierEigenfunctions.a, MagicFunction.FourierEigenfunctions.b,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
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
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) := by
    simpa [IA] using aRadial_eq_another_integral_main hx hx2
  have hbEq' : b' u =
      (-4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by
    simpa [IB] using bRadial_eq_another_integral_main hx hx2
  have hcoefA : (((↑π * I) / 8640 : ℂ) * (4 * (Complex.I : ℂ))) = -(π / 2160 : ℂ) := by
    field_simp; rw [Complex.I_sq]; ring
  have hcoefB : (((I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ))) = (1 / (60 * π) : ℂ) := by
    field_simp; rw [Complex.I_sq]; ring
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
  have hBscaled :
      (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        (-(π / 2160 : ℂ)) * IA +
          (1 / (60 * π) : ℂ) * IB +
          (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) -
            (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        -IA + ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB +
          ((8640 / π : ℝ) : ℂ) *
              (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
            ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
              (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) from by
        simpa [IA, IB, aAnotherIntegrand, bAnotherIntegrand]
          using IntegralB.integral_B_mul_exp_decomp hx,
      integral_mul_exp_neg_pi_mul_Ioi_complex hx, integral_exp_neg_pi_mul_Ioi_complex hx]
    push_cast; field_simp; ring
  have hBracket :
      (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
          (1 / (60 * π) : ℂ) * ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
        (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) := by
    rw [show (-(π / 2160 : ℂ)) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
          (1 / (60 * π) : ℂ) * ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
        (-(π / 2160 : ℂ)) * IA + (1 / (60 * π) : ℂ) * IB +
          (4 : ℂ) * ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) -
          (6 / π : ℂ) * ((1 / (π * u) : ℝ) : ℂ) by push_cast; field_simp; ring]
    exact hBscaled.symm
  simpa [u, mul_assoc] using
    (show ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
        (π / 2160 : ℂ) *
          (Real.sin (π * u / 2)) ^ (2 : ℕ) *
            (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) from by
      rw [hFourier, hAterm, hBterm]; grind only)

/-- Integral representation of `𝓕 g` in terms of `B(t)` (for `0 < ‖x‖ ^ 2`). -/
public theorem fourier_g_eq_integral_B {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) *
        (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  by_cases hx2 : ‖x‖ ^ 2 = 2
  · let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
    let xseq : ℕ → ℝ⁸ := fun n => (c n) • x
    have hxseq : Filter.Tendsto xseq Filter.atTop (𝓝 x) := by
      simpa [xseq] using (show Filter.Tendsto c Filter.atTop (𝓝 (1 : ℝ)) by
        simpa [c] using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).smul_const x
    let useq : ℕ → ℝ := fun n => ‖xseq n‖ ^ 2
    have huseq_gt2 (n : ℕ) : 2 < useq n := by
      rw [show useq n = (c n) ^ (2 : ℕ) * (‖x‖ ^ 2) by
        simp [useq, xseq, norm_smul, abs_of_pos (by positivity : (0 : ℝ) < c n), pow_two,
          mul_assoc, mul_left_comm, mul_comm], hx2]
      nlinarith [sq_nonneg (c n - 1), (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    have hEqseq (n : ℕ) : ((𝓕 g : 𝓢(ℝ⁸, ℂ)) (xseq n)) =
        (π / 2160 : ℂ) * (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)) :=
      fourier_g_eq_integral_B_of_ne_two (x := xseq n)
        ((by norm_num : (0:ℝ) < 2).trans (huseq_gt2 n)) (huseq_gt2 n).ne'
    let M : ℝ := ∫ t in Set.Ioi (0 : ℝ), ‖(B t : ℂ) * Real.exp (-π * (2 : ℝ) * t)‖
    have hInt_bound (n : ℕ) :
        ‖∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)‖ ≤ M :=
      norm_integral_le_of_norm_le
        (by simpa using (IntegralB.integrableOn_B_mul_exp_neg_pi_mul (u := 2) (by positivity)).norm)
        <| MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
            Complex.norm_of_nonneg (Real.exp_pos _).le]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
          nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right (le_of_lt (huseq_gt2 n)) ht.le]
    have hsin_tendsto : Filter.Tendsto (fun n : ℕ =>
        (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using (show ContinuousAt (fun u : ℝ => (Real.sin (π * u / 2)) ^ (2 : ℕ)) (2 : ℝ) by
        fun_prop).tendsto.comp (show Filter.Tendsto useq Filter.atTop (𝓝 (2 : ℝ)) by
          simpa [useq, hx2] using
            ((by continuity : Continuous (fun y : ℝ⁸ => ‖y‖ ^ 2)).tendsto x).comp hxseq)
    have hRHSseq0 : Filter.Tendsto (fun n : ℕ => (π / 2160 : ℂ) *
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
            (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) by
          simpa [pow_two] using Complex.norm_of_nonneg (sq_nonneg (Real.sin (π * (useq n) / 2))),
        mul_right_comm]
      gcongr; exact hInt_bound n
    rw [tendsto_nhds_unique (((SchwartzMap.continuous (𝓕 g : 𝓢(ℝ⁸, ℂ))).tendsto x).comp hxseq)
      ((Filter.tendsto_congr hEqseq).mpr hRHSseq0)]
    simp [show Real.sin (π * (‖x‖ ^ 2) / 2) = 0 by simp [hx2]]
  · exact fourier_g_eq_integral_B_of_ne_two (x := x) hx hx2

end MagicFunction.g.CohnElkies

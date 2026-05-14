module
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceB.LaplaceRepresentation
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.IntegralLemmas
public import SpherePacking.ModularForms.FG.Basic
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.b.Psi
import SpherePacking.Integration.Measure
import SpherePacking.ModularForms.Delta
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.AnotherIntegral
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.Integrability
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.Cancellation
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.ModularForms.FG.Inequalities
import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Integral representation for `𝓕 g` and Cohn-Elkies sign conditions

* "Another integral" representation `aRadial_eq_another_integral_main` for `a'` (blueprint
  `prop:a-another-integral`).
* Integral representation `fourier_g_eq_integral_B` for `𝓕 g` in terms of `B(t)`
  (blueprint equation "g B" in `subsections/modform-ineq.tex`), merged from `IntegralB`.
* Sign conditions for `g` and `𝓕 g` needed for the Cohn-Elkies LP bound in dimension 8,
  corresponding to (g1) and (g2) in `thm:g1`.

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_another_integral_main`
* `MagicFunction.g.CohnElkies.fourier_g_eq_integral_B`
* `MagicFunction.g.CohnElkies.gRadial_eq_integral_A`
* `MagicFunction.g.CohnElkies.g_nonpos_of_norm_sq_ge_two`
* `MagicFunction.g.CohnElkies.fourier_g_nonneg`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

section AnotherIntegralA

open MeasureTheory Real Complex
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

lemma corrIntegral_eval {u : ℝ} (hu0 : 0 < u) (hu : 2 < u)
    {c36 c8640 c18144 : ℂ}
    (hc36 : c36 = ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
    (hc8640 : c8640 = ((8640 / π : ℝ) : ℂ))
    (hc18144 : c18144 = ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))
    {corr : ℝ → ℂ}
    (hcorr : corr =
      fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t))
    (hIexp :
        (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ))
    (hItexp : (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ))
    (hI2exp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ))
    (hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (hTExpInt : IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)))
    (h2ExpInt : IntegrableOn
        (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) := by
  rw [hcorr]
  let f0 : ℝ → ℂ := fun t : ℝ => (Real.exp (-π * u * t) : ℂ)
  let f1 : ℝ → ℂ := fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)
  let f2 : ℝ → ℂ := fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)
  rw [show (∫ t in Set.Ioi (0 : ℝ),
      (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)) =
      ∫ t in Set.Ioi (0 : ℝ), ((c36 * f2 t + (-c8640) * f1 t) + c18144 * f0 t) from
    congrArg (integral (volume.restrict (Set.Ioi 0))) <| by funext t; dsimp [f0, f1, f2]; ring]
  change (∫ t, ((c36 * f2 t + (-c8640) * f1 t) + c18144 * f0 t) ∂ μIoi0) =
    (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u)
  have hI (f : ℝ → ℂ) (hf : IntegrableOn f (Set.Ioi (0 : ℝ))) : Integrable f μIoi0 := by
    simpa [MeasureTheory.IntegrableOn, μIoi0] using hf
  rw [integral_add_add (μ := μIoi0) ((hI f2 h2ExpInt).const_mul c36)
      ((hI f1 hTExpInt).const_mul (-c8640)) ((hI f0 hExpInt).const_mul c18144),
    integral_const_mul (μ := μIoi0) c36 f2, integral_const_mul (μ := μIoi0) (-c8640) f1,
    integral_const_mul (μ := μIoi0) c18144 f0,
    show (∫ t, f2 t ∂μIoi0) = ((1 / (π * (u - 2)) : ℝ) : ℂ) by simpa [f2, μIoi0] using hI2exp,
    show (∫ t, f1 t ∂μIoi0) = ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) by simpa [f1, μIoi0] using hItexp,
    show (∫ t, f0 t ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ) by simpa [f0, μIoi0] using hIexp,
    hc36, hc8640, hc18144]
  have hu2ne : (u - 2 : ℝ) ≠ 0 := (sub_pos.mpr hu).ne'
  have hune : (u : ℝ) ≠ 0 := hu0.ne'
  push_cast [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp
  ring

lemma aRadial_eq_another_integral_of_gt2 {u : ℝ} (hu : 2 < u) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              aAnotherIntegral u) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hLap' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
      (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    simpa [aLaplaceIntegrand, mul_assoc] using aRadial_eq_laplace_phi0_main hu
  set c36 : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc36
  set c8640 : ℂ := ((8640 / π : ℝ) : ℂ) with hc8640
  set c18144 : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ) with hc18144
  let corr : ℝ → ℂ :=
    fun t : ℝ => (c36 * Real.exp (2 * π * t) - c8640 * t + c18144) * Real.exp (-π * u * t)
  have hIexp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) = ((1 / (π * u) : ℝ) : ℂ) :=
    integral_exp_neg_pi_mul_Ioi_complex hu0
  have hItexp : (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := integral_mul_exp_neg_pi_mul_Ioi_complex hu0
  have hI2exp : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex hu
  have hExpInt : IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_pi_mul_Ioi_complex hu0
  have hTExpInt : IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu0
  have h2ExpInt : IntegrableOn
      (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex hu
  have hCorrInt : IntegrableOn corr (Set.Ioi (0 : ℝ)) := by
    refine ((((h2ExpInt.const_mul c36).sub (hTExpInt.const_mul c8640)).add
      (hExpInt.const_mul c18144)).congr <|
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_)
    dsimp [corr]; ring
  have hLapInt_decomp : (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
      (∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) + (∫ t in Set.Ioi (0 : ℝ), corr t) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) =
        ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t + corr t from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
        simp [-Complex.ofReal_exp, aLaplaceIntegrand, aAnotherIntegrand, c36, c8640, c18144,
          sub_eq_add_neg, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, corr]
        ring]
    exact integral_add (by simpa [MeasureTheory.IntegrableOn] using
      aAnotherIntegrand_integrable_of_pos hu0)
      (by simpa [MeasureTheory.IntegrableOn] using hCorrInt)
  simpa [aAnotherIntegral, hLapInt_decomp, show (∫ t in Set.Ioi (0 : ℝ), corr t) =
      (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
        (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u) from
    corrIntegral_eval hu0 hu hc36 hc8640 hc18144 rfl hIexp hItexp hI2exp hExpInt hTExpInt h2ExpInt,
    add_assoc, add_left_comm, add_comm] using hLap'

/-- Main lemma for blueprint proposition `prop:a-another-integral`. -/
public theorem aRadial_eq_another_integral_main {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
            (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
              ∫ t in Set.Ioi (0 : ℝ),
                ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                        ((8640 / π : ℝ) : ℂ) * t -
                        ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
                    Real.exp (-π * u * t))) := by
  simpa [aAnotherIntegrand] using
    aRadial_eq_another_integral_analytic_continuation_of_gt2 (u := u) (hu := hu) (hu2 := hu2)
      fun r hr => by simpa [aAnotherIntegral] using aRadial_eq_another_integral_of_gt2 (u := r) hr

end AnotherIntegralA

end MagicFunction.g.CohnElkies.IntegralReps

namespace MagicFunction.g.CohnElkies

open scoped BigOperators FourierTransform SchwartzMap Topology UpperHalfPlane
open MeasureTheory Real Complex
open MagicFunction.FourierEigenfunctions MagicFunction.g.CohnElkies.IntegralReps

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

noncomputable local instance : FourierTransform (𝓢(ℝ⁸, ℂ)) (𝓢(ℝ⁸, ℂ)) :=
  ⟨FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)⟩

/-! ## Real-valuedness on the positive imaginary axis (merged from `ImagAxisReal`) -/

private lemma imagAxis_im_eq_zero (F : ℍ → ℂ) (t : ℝ) (ht : 0 < t) (hF : ResToImagAxis.Real F) :
    (F ⟨Complex.I * t, by simp [ht]⟩).im = 0 := by
  simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF t ht

/-- The value `φ₀'' (it)` is real for `t > 0`. -/
public lemma φ₀''_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) * (t : ℂ))).im = 0 := by
  simpa [φ₀'', ht] using show (φ₀ ⟨Complex.I * t, by simp [ht]⟩).im = 0 by
    set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    have hE2 : (E₂ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero E₂ t ht E₂_imag_axis_real
    have hE4 : (E₄ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero E₄ t ht E₄_imag_axis_real
    have hE6 : (E₆ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero E₆ t ht E₆_imag_axis_real
    have hΔ : (Δ z).im = 0 := by simpa [z] using imagAxis_im_eq_zero Δ t ht Delta_imag_axis_pos.1
    simp [-E4_apply, -E6_apply, φ₀, z, Complex.div_im, hΔ,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((E₂ z) * (E₄ z) - (E₆ z)).im = 0 by
        simp [-E4_apply, -E6_apply, Complex.sub_im, Complex.mul_im, hE2, hE4, hE6]) 2]

/-- The value `φ₀'' (i / t)` is real for `t > 0`. -/
public lemma φ₀''_imag_axis_div_im (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).im = 0 := by
  simpa [div_eq_mul_inv] using (φ₀''_imag_axis_im (t := (1 / t)) (by positivity))

/-- The value `ψI' (it)` is real for `t > 0`. -/
public lemma ψI'_imag_axis_im (t : ℝ) (ht : 0 < t) :
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).im = 0 := by
  set z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hH2 : (H₂_MF z).im = 0 := by simpa [z] using imagAxis_im_eq_zero H₂ t ht H₂_imag_axis_real
  have hH3 : (H₃_MF z).im = 0 := by
    simpa [z] using imagAxis_im_eq_zero H₃ t ht (by
      simpa [jacobi_identity] using H₂_imag_axis_real.add H₄_imag_axis_real)
  have hH4 : (H₄_MF z).im = 0 := by simpa [z] using imagAxis_im_eq_zero H₄ t ht H₄_imag_axis_real
  simpa [ψI', Function.resToImagAxis, ResToImagAxis, ht, z] using show (ψI z).im = 0 by
    rw [ψI_eq]
    simp [z, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im, hH2, hH3, hH4,
      Complex.im_pow_eq_zero_of_im_eq_zero hH2 2, Complex.im_pow_eq_zero_of_im_eq_zero hH3 2]

/-! ## Integral representation for `𝓕 g` (merged from `IntegralB`) -/

namespace IntegralB

lemma B_mul_exp_eq_decomp {u t : ℝ} (ht : 0 < t) : (B t : ℂ) * Real.exp (-π * u * t) =
    -(aAnotherIntegrand u t) + ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * bAnotherIntegrand u t +
      ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
        ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ) := by
  have hB : (B t : ℂ) = (-(t ^ (2 : ℕ)) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) +
      ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
    apply Complex.ext <;> simp [B, φ₀''_imag_axis_div_im (t := t) ht, ψI'_imag_axis_im (t := t) ht]
  simp [hB, aAnotherIntegrand, bAnotherIntegrand, mul_assoc, mul_left_comm, mul_comm]; ring_nf

private lemma integrable_bAnother {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => bAnotherIntegrand u t)
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  simpa [MeasureTheory.IntegrableOn, bAnotherIntegrand, bAnotherBase, mul_assoc] using
    bAnotherBase_integrable_exp hu

lemma integrableOn_B_mul_exp_neg_pi_mul {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (B t : ℂ) * Real.exp (-π * u * t)) (Set.Ioi (0 : ℝ)) :=
  ((((aAnotherIntegrand_integrable_of_pos hu).neg.add ((integrable_bAnother hu).const_mul _)).add
    ((integrableOn_mul_exp_neg_pi_mul_Ioi_complex hu).const_mul _)).sub
    ((integrableOn_exp_neg_pi_mul_Ioi_complex hu).const_mul _)).congr <|
  MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (IntegralB.B_mul_exp_eq_decomp (t := t) ht).symm

lemma integral_B_mul_exp_decomp {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
      -(∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) +
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (∫ t in Set.Ioi (0 : ℝ), bAnotherIntegrand u t) +
        ((8640 / π : ℝ) : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
        ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let f1 : ℝ → ℂ := fun t => -(aAnotherIntegrand u t)
  let f2 : ℝ → ℂ := fun t => ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * bAnotherIntegrand u t
  let f3 : ℝ → ℂ := fun t => ((8640 / π : ℝ) : ℂ) * ((t : ℂ) * (Real.exp (-π * u * t) : ℂ))
  let f4 : ℝ → ℂ := fun t => -((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * (Real.exp (-π * u * t) : ℂ)
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

theorem fourier_g_eq_integral_B_of_ne_two {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) (hx2 : ‖x‖ ^ 2 ≠ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) = (π / 2160 : ℂ) * (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
      (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (‖x‖ ^ 2) * t)) := by
  set u : ℝ := ‖x‖ ^ 2
  have hFourier : ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      ((↑π * I) / 8640 : ℂ) * a' u + (I / (240 * (↑π)) : ℂ) * b' u := by
    change (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g) x = _
    simp [u, show FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g =
        ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b from by
      simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
        -FourierTransform.fourierCLE_apply], SchwartzMap.add_apply, SchwartzMap.smul_apply,
      smul_eq_mul, MagicFunction.FourierEigenfunctions.a, MagicFunction.FourierEigenfunctions.b,
      schwartzMap_multidimensional_of_schwartzMap_real, SchwartzMap.compCLM_apply]
  set IA : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
        ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) * Real.exp (-π * u * t))
  set IB : ℂ := ∫ t in Set.Ioi (0 : ℝ),
    (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - ((Real.exp (2 * π * t)) : ℂ)) *
      Real.exp (-π * u * t)
  have hAterm : ((↑π * I) / 8640 : ℂ) * a' u =
      (Real.sin (π * u / 2)) ^ (2 : ℕ) * (-(π / 2160 : ℂ)) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) := by
    rw [show a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) from by
      simpa [IA] using aRadial_eq_another_integral_main hx hx2]
    linear_combination ((Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
        (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA)) * (by field_simp; rw [Complex.I_sq]; ring :
        (((↑π * I) / 8640 : ℂ) * (4 * (Complex.I : ℂ))) = -(π / 2160 : ℂ))
  have hBterm : (I / (240 * (↑π)) : ℂ) * b' u =
      (Real.sin (π * u / 2)) ^ (2 : ℕ) * (1 / (60 * π) : ℂ) *
        ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) := by
    rw [show b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) from by
      simpa [IB] using bRadial_eq_another_integral_main hx hx2]
    linear_combination ((Real.sin (π * u / 2)) ^ (2 : ℕ) *
      ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB)) *
      (by field_simp; rw [Complex.I_sq]; ring :
        (((I / (240 * (↑π)) : ℂ)) * (-4 * (Complex.I : ℂ))) = (1 / (60 * π) : ℂ))
  have hBracket : (-(π / 2160 : ℂ)) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) - (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) + IA) +
      (1 / (60 * π) : ℂ) * ((144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + IB) =
      (π / 2160 : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) := by
    rw [show (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) =
        -IA + ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * IB +
          ((8640 / π : ℝ) : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-π * u * t) : ℂ)) -
          ((12960 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) from by
        simpa [IA, IB, aAnotherIntegrand, bAnotherIntegrand]
          using IntegralB.integral_B_mul_exp_decomp hx,
      integral_mul_exp_neg_pi_mul_Ioi_complex hx, integral_exp_neg_pi_mul_Ioi_complex hx]
    push_cast; field_simp; ring
  simpa [u, mul_assoc] using show ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) =
      (π / 2160 : ℂ) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * u * t)) by
    rw [hFourier, hAterm, hBterm]; grind only

/-- Integral representation of `𝓕 g` in terms of `B(t)` (for `0 < ‖x‖ ^ 2`). -/
public theorem fourier_g_eq_integral_B {x : ℝ⁸} (hx : 0 < ‖x‖ ^ 2) :
    ((𝓕 g : 𝓢(ℝ⁸, ℂ)) x) = (π / 2160 : ℂ) * (Real.sin (π * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) *
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
    have hRHSseq0 : Filter.Tendsto (fun n : ℕ => (π / 2160 : ℂ) *
        (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ), (B t : ℂ) * Real.exp (-π * (useq n) * t)))
        Filter.atTop (𝓝 (0 : ℂ)) := by
      refine (tendsto_zero_iff_norm_tendsto_zero).2 <|
        squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
          ((tendsto_const_nhds.mul (show Filter.Tendsto (fun n : ℕ =>
              (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop (𝓝 (0 : ℝ)) by
            simpa using (show ContinuousAt (fun u : ℝ => (Real.sin (π * u / 2)) ^ (2 : ℕ)) (2 : ℝ)
              by fun_prop).tendsto.comp (show Filter.Tendsto useq Filter.atTop (𝓝 (2 : ℝ)) by
                simpa [useq, hx2] using
                  ((by continuity : Continuous (fun y : ℝ⁸ => ‖y‖ ^ 2)).tendsto x).comp
                    hxseq))).trans (by simp) :
            Filter.Tendsto (fun n : ℕ => (‖(π / 2160 : ℂ)‖ * M) *
              (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ)) Filter.atTop (𝓝 (0 : ℝ)))
      rw [norm_mul, norm_mul,
        show ‖((Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) : ℂ)‖ =
            (Real.sin (π * (useq n) / 2)) ^ (2 : ℕ) by
          simpa [pow_two] using Complex.norm_of_nonneg (sq_nonneg (Real.sin (π * (useq n) / 2))),
        mul_right_comm]
      gcongr; exact hInt_bound n
    rw [tendsto_nhds_unique (((SchwartzMap.continuous (𝓕 g : 𝓢(ℝ⁸, ℂ))).tendsto x).comp hxseq)
      ((Filter.tendsto_congr fun n => fourier_g_eq_integral_B_of_ne_two (x := xseq n)
        ((by norm_num : (0:ℝ) < 2).trans (huseq_gt2 n)) (huseq_gt2 n).ne').mpr hRHSseq0)]
    simp [hx2]
  · exact fourier_g_eq_integral_B_of_ne_two (x := x) hx hx2

/-! ## Cohn-Elkies sign conditions -/

noncomputable section

private lemma complex_eq_ofReal_of_im_eq_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext rfl (by simp [hz])

/-- The constant `c = 18 / π^2` appearing in the definitions of `A` and `B`. -/
public abbrev c : ℝ := 18 * (π ^ (-2 : ℤ))

/-- Real part of `φ₀'' (I / t)` in terms of `FReal` and the imaginary-axis restriction of `Δ`. -/
public lemma phi0''_re_I_div (t : ℝ) (ht : 0 < t) :
    (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re =
      (FReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  let z : ℍ := ⟨Complex.I * s, by simp [hs]⟩
  have hz : (z : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by simp [z, s, div_eq_mul_inv]
  calc (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re
      = (φ₀ z).re := by simpa [hz] using congrArg Complex.re (φ₀''_coe_upperHalfPlane z)
    _ = ((F z) / (Δ z)).re := by simp [φ₀, F]
    _ = ((FReal s : ℂ) / (Δ.resToImagAxis s)).re := by
        simp [show F z = (FReal s : ℂ) by
          simpa [Function.resToImagAxis, ResToImagAxis, hs, z] using F_eq_FReal (t := s) hs,
          show Δ z = Δ.resToImagAxis s by simp [Function.resToImagAxis, ResToImagAxis, hs, z]]
    _ = ((FReal s : ℂ) / ((Δ.resToImagAxis s).re : ℂ)).re := by
        rw [complex_eq_ofReal_of_im_eq_zero _ (Delta_imag_axis_pos.1 s hs)]; rfl
    _ = (FReal s) / (Δ.resToImagAxis s).re := by rw [← Complex.ofReal_div]; simp
    _ = (FReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by simp [s]

/-- Real part of `ψS` on the imaginary axis, written using `GReal` and `Δ`. -/
public lemma ψS_resToImagAxis_re (s : ℝ) (hs : 0 < s) :
    (ψS.resToImagAxis s).re = -(2⁻¹ * GReal s) / (Δ.resToImagAxis s).re := by
  let z : ℍ := ⟨Complex.I * s, by simp [hs]⟩
  calc (ψS.resToImagAxis s).re
      = ((-(1 / 2 : ℂ)) * (G.resToImagAxis s) / (Δ.resToImagAxis s)).re := by
        simpa using congrArg Complex.re (show ψS.resToImagAxis s =
            (-(1 / 2 : ℂ)) * (G.resToImagAxis s) / (Δ.resToImagAxis s) by
          simpa [Function.resToImagAxis, ResToImagAxis, hs, z] using show
              ψS z = (-(1 / 2 : ℂ)) * (G z) / (Δ z) by
            rw [MagicFunction.b.PsiBounds.ψS_apply_eq_factor z]
            simp [G, show Δ z = (H₂ z * H₃ z * H₄ z) ^ 2 / (256 : ℂ) by
              simpa [Delta_apply, mul_assoc] using Delta_eq_H₂_H₃_H₄ z]
            field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z]; ring_nf)
    _ = ((-(1 / 2 : ℂ)) * (GReal s : ℂ) / (Δ.resToImagAxis s)).re := by
        simp [show ResToImagAxis G s = (GReal s : ℂ) by
          simpa [Function.resToImagAxis_apply, GReal] using G_eq_GReal (t := s) hs]
    _ = ((-(1 / 2 : ℂ)) * (GReal s : ℂ) / ((Δ.resToImagAxis s).re : ℂ)).re := by
        rw [complex_eq_ofReal_of_im_eq_zero _ (Delta_imag_axis_pos.1 s hs)]; rfl
    _ = (-(1 / 2 : ℝ)) * (GReal s) / (Δ.resToImagAxis s).re := by simp
    _ = -(2⁻¹ * GReal s) / (Δ.resToImagAxis s).re := by simp [div_eq_mul_inv, mul_assoc]

/-- Relate `ψI' (I * t)` to `ψS` at `1 / t` via the slash-action symmetry. -/
public lemma ψI'_re_mul_I (t : ℝ) (ht : 0 < t) :
    (ψI' ((Complex.I : ℂ) * (t : ℂ))).re =
      -(t ^ (2 : ℕ)) * (ψS.resToImagAxis (1 / t)).re := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hψS' : ψS.resToImagAxis s = ((-(s ^ (2 : ℕ)) : ℝ) : ℂ) * ψI.resToImagAxis t := by
    simpa [show (1 / s) = t by simp [s], zpow_ofNat, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using
      ResToImagAxis.SlashActionS (F := ψI) (k := (-2 : ℤ)) (t := s) hs
  have hts : (t ^ (2 : ℕ)) * (s ^ (2 : ℕ)) = (1 : ℝ) := by
    simp [s, ht.ne', pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
  have hψIaxis : ψI.resToImagAxis t = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s :=
    calc ψI.resToImagAxis t
        = ((t ^ (2 : ℕ) * s ^ (2 : ℕ) : ℝ) : ℂ) * ψI.resToImagAxis t := by simp [hts]
      _ = ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * ψS.resToImagAxis s := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (congrArg (fun w : ℂ => ((-(t ^ (2 : ℕ)) : ℝ) : ℂ) * w) hψS').symm
  calc (ψI' ((Complex.I : ℂ) * (t : ℂ))).re
      = (ψI.resToImagAxis t).re := by simp [ψI', ResToImagAxis, ht]
    _ = (-(t ^ (2 : ℕ)) : ℝ) * (ψS.resToImagAxis s).re := by
      rw [hψIaxis]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = -(t ^ (2 : ℕ)) * (ψS.resToImagAxis (1 / t)).re := by simp [s]

/-- Rewrite `A t` as a quotient involving `FReal`, `GReal`, and `Δ` on the imaginary axis. -/
public lemma A_eq_neg_mul_FG_div_Delta (t : ℝ) (ht : 0 < t) :
    A t = (-(t ^ (2 : ℕ))) *
      ((FReal (1 / t) + c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hΔr : (Δ.resToImagAxis s).re ≠ 0 := ne_of_gt (Delta_imag_axis_pos.2 s hs)
  rw [show A t = (-(t ^ (2 : ℕ))) * (FReal s / (Δ.resToImagAxis s).re) -
        (36 / (π ^ (2 : ℕ)) : ℝ) * (-(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re) by
      simp [A, show (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = FReal s / (Δ.resToImagAxis s).re by
        simpa [s] using phi0''_re_I_div (t := t) ht,
        show (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ResToImagAxis ψS s).re by
          simpa [s, Function.resToImagAxis_apply] using ψI'_re_mul_I (t := t) ht],
    ψS_resToImagAxis_re (s := s) hs]
  field_simp [hΔr]; ring

/-- Rewrite `B t` as a quotient involving `FReal`, `GReal`, and `Δ` on the imaginary axis. -/
public lemma B_eq_neg_mul_FG_div_Delta (t : ℝ) (ht : 0 < t) :
    B t = (-(t ^ (2 : ℕ))) *
      ((FReal (1 / t) - c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re) := by
  set s : ℝ := 1 / t
  have hs : 0 < s := one_div_pos.2 ht
  have hΔr : (Δ.resToImagAxis s).re ≠ 0 := ne_of_gt (Delta_imag_axis_pos.2 s hs)
  rw [show B t = (-(t ^ (2 : ℕ))) * (FReal s / (Δ.resToImagAxis s).re) +
        (36 / (π ^ (2 : ℕ)) : ℝ) * (-(t ^ (2 : ℕ)) * (ψS.resToImagAxis s).re) by
      simp [B, show (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re = FReal s / (Δ.resToImagAxis s).re by
        simpa [s] using phi0''_re_I_div (t := t) ht,
        show (ψI' ((Complex.I : ℂ) * (t : ℂ))).re = -(t ^ (2 : ℕ)) * (ResToImagAxis ψS s).re by
          simpa [s, Function.resToImagAxis_apply] using ψI'_re_mul_I (t := t) ht],
    ψS_resToImagAxis_re (s := s) hs]
  field_simp [hΔr]; ring

end

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
    have hB_pos : ∀ {t : ℝ}, 0 < t → 0 < B t := fun {t} ht => by
      set sB : ℝ := 1 / t
      have hsB : 0 < sB := one_div_pos.2 ht
      have hΔpos : 0 < (Δ.resToImagAxis sB).re := (Delta_imag_axis_pos).2 sB hsB
      have hB :
          B t = (-(t ^ (2 : ℕ))) * ((FReal sB - c * GReal sB) / (Δ.resToImagAxis sB).re) := by
        simpa [sB] using (B_eq_neg_mul_FG_div_Delta (t := t) ht)
      simpa [hB] using mul_pos_of_neg_of_neg (neg_lt_zero.2 (pow_pos ht _))
        (div_neg_of_neg_of_pos (by simpa [c] using (FG_inequality_2 (t := sB) hsB)) hΔpos)
    have hIntegral : 0 ≤ IB :=
      MeasureTheory.setIntegral_nonneg (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t ht =>
          mul_nonneg (hB_pos ht).le (Real.exp_pos _).le
    rw [ge_iff_le, congrArg Complex.re hEqReal]
    exact mul_nonneg (by change 0 ≤ (π / 2160 : ℝ) * _; positivity) hIntegral

end MagicFunction.g.CohnElkies

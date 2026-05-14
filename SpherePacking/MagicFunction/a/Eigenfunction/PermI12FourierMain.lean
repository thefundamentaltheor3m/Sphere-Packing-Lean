module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Fourier
import SpherePacking.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierIntegrableI1
import SpherePacking.Contour.Segments
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import Mathlib.Tactic.Ring.RingNF
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier transforms of `I₁` and `I₂` as curve integrals

We rewrite the Fourier transforms of `I₁` and `I₂` as curve integrals of `Φ₁_fourier` along two
straight segments. This is the analytic input for the contour permutation identity.
-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MeasureTheory Set Complex Real SpherePacking.Integration SpherePacking.Contour
open MagicFunction.a.RealIntegrals MagicFunction.a.ComplexIntegrands
open scoped Interval RealInnerProductSpace

/-- The `x`-integral of `permI1Kernel` is `Φ₁_fourier` evaluated at `z₁line t`. -/
public lemma integral_permI1Kernel_x (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, permI1Kernel w (x, t)) =
      (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := z₁line_im_pos_Ioc ht
  let c : ℂ := (I : ℂ) * (φ₀'' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ 2)
  have hfactor : (fun x : ℝ⁸ => permI1Kernel w (x, t)) = fun x : ℝ⁸ =>
      c * (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
        cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) := by
    funext x; dsimp [permI1Kernel, MagicFunction.a.ComplexIntegrands.Φ₁', c]; ac_rfl
  calc
    (∫ x : ℝ⁸, permI1Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₁line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₁line t))) := by
      simpa [hfactor] using
        integral_const_mul_phase_gaussian_pi_mul_I_mul_even
          (k := 4) (w := w) (z := z₁line t) hz (c := c)
    _ = (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
      simp only [c, Φ₁_fourier]; ring

/-- The `x`-integral of `permI2Kernel` is `Φ₁_fourier` evaluated at `z₂line t`. -/
public lemma integral_permI2Kernel_x (w : ℝ⁸) (t : ℝ) :
    (∫ x : ℝ⁸, permI2Kernel w (x, t)) =
      Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := φ₀'' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ 2
  have hfactor : (fun x : ℝ⁸ => permI2Kernel w (x, t)) = fun x : ℝ⁸ =>
      c * (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
        cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) := by
    funext x; dsimp [permI2Kernel, MagicFunction.a.ComplexIntegrands.Φ₁', c]; ac_rfl
  calc
    (∫ x : ℝ⁸, permI2Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₂line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₂line t))) := by
      simpa [hfactor] using
        integral_const_mul_phase_gaussian_pi_mul_I_mul_even
          (k := 4) (w := w) (z := z₂line t) hz (c := c)
    _ = Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
      simp only [c, Φ₁_fourier]; ring

open SpherePacking.ForMathlib

lemma integral_norm_permI2Kernel_bound (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) ≤ (2 : ℝ) * ‖φ₀'' (-1 / (z₂line t + 1))‖ := by
  have ht0 : 0 < t := ht.1
  have hpow : ‖(z₂line t + 1) ^ 2‖ ≤ (2 : ℝ) := by
    have ht_sq : t ^ 2 ≤ 1 := by nlinarith [ht0.le, ht.2]
    calc
      ‖(z₂line t + 1) ^ 2‖ = ‖(z₂line t + 1)‖ ^ 2 := by simp [norm_pow]
      _ = Complex.normSq (z₂line t + 1) := by simp [Complex.sq_norm]
      _ = Complex.normSq ((t : ℂ) + I) := by
        simpa using congrArg Complex.normSq (z₂line_add_one (t := t))
      _ = t ^ 2 + 1 := by simpa [mul_comm] using (Complex.normSq_add_mul_I t (1 : ℝ))
      _ ≤ 2 := by linarith
  have hexp (x : ℝ⁸) :
      ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₂line t : ℂ))‖ = rexp (-(Real.pi * (‖x‖ ^ 2))) := by
    set r : ℝ := ‖x‖ ^ 2
    have hmain : ‖cexp ((Real.pi : ℂ) * I * (r : ℂ) * z₂line t)‖ = rexp (-Real.pi * r) := by
      simp [Complex.norm_exp]
    simpa [r, mul_assoc, mul_left_comm, mul_comm, neg_mul] using hmain
  have hnorm (x : ℝ⁸) :
      ‖permI2Kernel w (x, t)‖ =
        ‖φ₀'' (-1 / (z₂line t + 1))‖ * (‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2)))) := by
    have hphase' : ‖cexp (-(2 * (↑π * ↑⟪x, w⟫) * I))‖ = (1 : ℝ) := by
      simpa [show (↑(-2 * (π * ⟪x, w⟫)) : ℂ) * I = -(2 * (↑π * ↑⟪x, w⟫) * I) by push_cast; ring]
        using SpherePacking.ForMathlib.norm_phase_eq_one (w := w) (x := x)
    calc ‖permI2Kernel w (x, t)‖
        = ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ *
            ‖MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t)‖ := by
          simp [permI2Kernel, mul_assoc]
      _ = ‖MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t)‖ := by simp [hphase']
      _ = ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 *
            ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₂line t : ℂ))‖ := by
          simp [MagicFunction.a.ComplexIntegrands.Φ₁', norm_pow, mul_assoc]
      _ = ‖φ₀'' (-1 / (z₂line t + 1))‖ *
            (‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2)))) := by rw [hexp x, mul_assoc]
  have hgauss_one : (∫ x : ℝ⁸, rexp (-(Real.pi * (‖x‖ ^ 2)))) = (1 : ℝ) := by
    simpa [one_mul] using
      (integral_rexp_neg_pi_mul_sq_norm (t := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1)).trans (by simp)
  have hEq :
      (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) =
        ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 := by
    simp only [funext hnorm, integral_const_mul]; rw [hgauss_one]; ring
  simpa [hEq, mul_comm, ← norm_pow] using
    mul_le_mul_of_nonneg_left hpow (norm_nonneg (φ₀'' (-1 / (z₂line t + 1))))

lemma integrable_integral_norm_permI2Kernel (w : ℝ⁸) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) μIoc01 := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine Integrable.mono' (g := fun _ => (2 : ℝ) * (C₀ : ℝ))
    (by simpa using MeasureTheory.integrable_const (μ := μIoc01) ((2 : ℝ) * (C₀ : ℝ)))
    (by simpa using ((permI2Kernel_measurable (w := w)).norm.prod_swap.integral_prod_right'
      (μ := μIoc01) (ν := (volume : Measure ℝ⁸)))) ?_
  filter_upwards [show ∀ᵐ t : ℝ ∂μIoc01, t ∈ Ioc (0 : ℝ) 1 by
      simpa [μIoc01] using (ae_restrict_mem measurableSet_Ioc : ∀ᵐ t ∂μIoc01, t ∈ Ioc (0 : ℝ) 1),
    show ∀ᵐ t : ℝ ∂μIoc01, t ≠ 1 by
      simpa [Set.mem_singleton_iff] using
        measure_eq_zero_iff_ae_notMem.1 (by simp [μIoc01] : μIoc01 ({(1 : ℝ)} : Set ℝ) = 0)]
    with t ht htne1
  have ht_lt1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  have him_pos : 0 < ((-1 : ℂ) / ((t : ℂ) + I)).im := by
    simpa using neg_one_div_im_pos ((t : ℂ) + I) (by simp : 0 < (((t : ℂ) + I)).im)
  let z : UpperHalfPlane := ⟨(-1 : ℂ) / ((t : ℂ) + I), him_pos⟩
  have hz_half : (1 / 2 : ℝ) < z.im := by
    have him : ((-1 : ℂ) / ((t : ℂ) + I)).im = 1 / (t ^ 2 + 1) := by
      simpa using SpherePacking.Integration.im_neg_one_div_ofReal_add_I (t := t)
    simpa [z, UpperHalfPlane.im, him] using
      SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 ⟨ht.1, ht_lt1⟩
  have hφ₀'' : ‖φ₀'' ((-1 : ℂ) / ((t : ℂ) + I))‖ ≤ (C₀ : ℝ) := calc
    ‖φ₀'' ((-1 : ℂ) / ((t : ℂ) + I))‖
        = ‖φ₀ z‖ := by
          simpa [z] using congrArg norm (φ₀''_def (z := (-1 : ℂ) / ((t : ℂ) + I)) him_pos)
      _ ≤ (C₀ : ℝ) * rexp (-2 * π * z.im) := hC₀ z hz_half
      _ ≤ (C₀ : ℝ) := mul_le_of_le_one_right hC₀_pos.le
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, z.2.le]))
  have hφ₀''_seg : ‖φ₀'' (-1 / (z₂line t + 1))‖ ≤ (C₀ : ℝ) := by
    rw [z₂line_add_one (t := t)]; simpa using hφ₀''
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)]
  linarith [integral_norm_permI2Kernel_bound (w := w) (t := t) ht]

/-- Integrability of `permI2Kernel` on the product measure `volume × μIoc01`. -/
public lemma integrable_perm_I₂_kernel (w : ℝ⁸) :
    Integrable (permI2Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
  (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01)
    (permI2Kernel_measurable (w := w))).2
    ⟨ae_integrable_permI2Kernel_slice (w := w), integrable_integral_norm_permI2Kernel (w := w)⟩

section PermI12Fourier_Main

/-- Swap order of integration over `volume × μIoc01` and rewrite the inner integral using `g`. -/
private lemma integral_integral_swap_muIoc01
    {V : Type*} [MeasureSpace V] [MeasureTheory.SFinite (volume : Measure V)]
    {f : V → ℝ → ℂ} {g : ℝ → ℂ}
    (hint : Integrable (Function.uncurry f) ((volume : Measure V).prod μIoc01))
    (hfg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (∫ x : V, f x t) = g t) :
    (∫ x : V, ∫ t : ℝ, f x t ∂μIoc01) = ∫ t : ℝ, g t ∂μIoc01 := by
  rw [show (∫ x : V, ∫ t : ℝ, f x t ∂μIoc01) =
      ∫ t : ℝ, ∫ x : V, f x t ∂(volume : Measure V) ∂μIoc01 from by
    simpa using (MeasureTheory.integral_integral_swap (μ := volume) (ν := μIoc01) hint)]
  refine MeasureTheory.integral_congr_ae <|
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ioc).2 <|
      Filter.Eventually.of_forall fun t ht => by simp [hfg t ht]

/-- Fourier transform of `I₁`, rewritten as a curve integral of `Φ₁_fourier` along the first
vertical segment. -/
public lemma fourier_I₁_eq_curveIntegral (w : ℝ⁸) :
    (𝓕 (I₁ : ℝ⁸ → ℂ)) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
  rw [fourier_eq' (I₁ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₁_apply, mul_assoc]
  have hI₁' (x : ℝ⁸) : RealIntegrals.I₁' (‖x‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t) := by
    rw [I₁'_eq_curveIntegral_segment,
      curveIntegral_segment (ω := scalarOneForm (Φ₁' (‖x‖ ^ 2))) (-1 : ℂ) ((-1 : ℂ) + I),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp [lineMap_z₁line]
  let f : ℝ⁸ → ℝ → ℂ := fun x t => permI1Kernel w (x, t)
  let g : ℝ → ℂ := fun t => (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t)
  have hswapEq : (∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t) = ∫ t in Ioc (0 : ℝ) 1, g t := by
    simpa [μIoc01] using
      integral_integral_swap_muIoc01 (V := ℝ⁸) (f := f) (g := g)
        (integrable_perm_I₁_kernel (w := w)) fun t ht => by
          simpa [f] using integral_permI1Kernel_x (w := w) (t := t) ht
  calc
    (∫ x : ℝ⁸, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * RealIntegrals.I₁' (‖x‖ ^ 2)) =
        ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ((I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)) := by
        simp_rw [hI₁', integral_const_mul]
    _ = ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t := by simp [f, permI1Kernel]
    _ = ∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := hswapEq
    _ = (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
      rw [curveIntegral_segment (ω := scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)))
        (-1 : ℂ) ((-1 : ℂ) + I)]
      simp [g, intervalIntegral.integral_of_le, lineMap_z₁line]

/-- Fourier transform of `I₂`, rewritten as a curve integral of `Φ₁_fourier` along the second
segment. -/
public lemma fourier_I₂_eq_curveIntegral (w : ℝ⁸) :
    (𝓕 (I₂ : ℝ⁸ → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
  rw [fourier_eq' (I₂ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₂_apply, mul_assoc]
  have hI₂' (x : ℝ⁸) : RealIntegrals.I₂' (‖x‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) 1, Φ₁' (‖x‖ ^ 2) (z₂line t) := by
    rw [I₂'_eq_curveIntegral_segment,
      curveIntegral_segment (ω := scalarOneForm (Φ₁' (‖x‖ ^ 2))) ((-1 : ℂ) + I) I,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp [lineMap_z₂line]
  let f : ℝ⁸ → ℝ → ℂ := fun x t => permI2Kernel w (x, t)
  let g : ℝ → ℂ := fun t => Φ₁_fourier (‖w‖ ^ 2) (z₂line t)
  have hswapEq : (∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t) = ∫ t in Ioc (0 : ℝ) 1, g t := by
    simpa [μIoc01] using
      integral_integral_swap_muIoc01 (V := ℝ⁸) (f := f) (g := g)
        (integrable_perm_I₂_kernel (w := w)) fun t _ => by
          simpa [f] using integral_permI2Kernel_x (w := w) (t := t)
  calc
    (∫ x : ℝ⁸, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * RealIntegrals.I₂' (‖x‖ ^ 2)) =
        ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * Φ₁' (‖x‖ ^ 2) (z₂line t) := by
        simp_rw [hI₂', integral_const_mul]
    _ = ∫ x : ℝ⁸, ∫ t in Ioc (0 : ℝ) 1, f x t := by simp [f, permI2Kernel]
    _ = ∫ t in Ioc (0 : ℝ) 1, Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := hswapEq
    _ = (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := by
      rw [curveIntegral_segment (ω := scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)))
        ((-1 : ℂ) + I) I]
      simp [g, intervalIntegral.integral_of_le, lineMap_z₂line]

end Integral_Permutations.PermI12Fourier_Main
end
end MagicFunction.a.Fourier

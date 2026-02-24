module
public import SpherePacking.MagicFunction.a.Eigenfunction.PermI12Fourier
import SpherePacking.MagicFunction.a.Eigenfunction.PermI12FourierIntegrableI1
import SpherePacking.Contour.Segments
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.ForMathlib.IntegralProd
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.PolyFourierCoeffBound


/-!
# Integrability of the `I₂` Fourier kernel

We bound `t ↦ ∫ ‖permI2Kernel w (x, t)‖` on `Ioc 0 1` and deduce integrability of `permI2Kernel w`
on the product measure `volume × μIoc01`.

## Main statements
* `integrable_perm_I₂_kernel`

-/

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Integrable

open MeasureTheory Set Complex Real
open SpherePacking.ForMathlib
open SpherePacking.Contour
open SpherePacking.Integration
open scoped Interval

lemma integral_norm_permI2Kernel_bound (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) ≤ (2 : ℝ) * ‖φ₀'' (-1 / (z₂line t + 1))‖ := by
  have ht0 : 0 < t := ht.1
  have hpow : ‖(z₂line t + 1) ^ 2‖ ≤ (2 : ℝ) := by
    have ht0le : 0 ≤ t := ht0.le
    have ht1 : t ≤ 1 := ht.2
    have ht_sq : t ^ 2 ≤ 1 := by
      have habs : |t| ≤ 1 := by simpa [abs_of_nonneg ht0le] using ht1
      simpa [pow_two] using (pow_le_one₀ (abs_nonneg t) habs (n := 2))
    -- `‖(t + I)^2‖ = ‖t + I‖^2 = t^2 + 1`
    calc
      ‖(z₂line t + 1) ^ 2‖ = ‖(z₂line t + 1)‖ ^ 2 := by simp [norm_pow]
      _ = Complex.normSq (z₂line t + 1) := by simp [Complex.sq_norm]
      _ = Complex.normSq ((t : ℂ) + I) := by
        simpa using congrArg Complex.normSq (z₂line_add_one (t := t))
      _ = t ^ 2 + 1 := by
        -- `normSq (t + I) = t^2 + 1^2`
        simpa [mul_comm] using (Complex.normSq_add_mul_I t (1 : ℝ))
      _ ≤ 1 + 1 := by gcongr
      _ = (2 : ℝ) := by ring
  have hexp (x : ℝ⁸) :
      ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₂line t : ℂ))‖ = rexp (-(Real.pi * (‖x‖ ^ 2))) := by
    set r : ℝ := ‖x‖ ^ 2
    have hre : (((Real.pi : ℂ) * I * (r : ℂ) * z₂line t)).re = -Real.pi * r := by
      -- `z₂line t = (-1 + t) + I`
      have hz' : z₂line t = ((t - 1 : ℝ) : ℂ) + I := by
        -- `(-1 : ℂ) + (t : ℂ) = ((t - 1 : ℝ) : ℂ)`
        have : (-1 : ℂ) + (t : ℂ) = ((t - 1 : ℝ) : ℂ) := by
          push_cast
          ring
        simp [z₂line, this, add_comm]
      -- Expand and take real parts; only the `I * I` term contributes.
      calc
        (((Real.pi : ℂ) * I * (r : ℂ) * z₂line t)).re =
            (((Real.pi : ℂ) * I * (r : ℂ) * (((t - 1 : ℝ) : ℂ) + I))).re := by
              simp
        _ =
            (((Real.pi : ℂ) * I * (r : ℂ) * ((t - 1 : ℝ) : ℂ) +
                  (Real.pi : ℂ) * I * (r : ℂ) * I)).re := by
              simp [mul_add]
        _ =
            (((Real.pi : ℂ) * I * (r : ℂ) * ((t - 1 : ℝ) : ℂ)).re +
                  ((Real.pi : ℂ) * I * (r : ℂ) * I).re) := by
              simp
        _ = 0 + (-Real.pi * r) := by
              simp
        _ = -Real.pi * r := by simp
    have hmain :
        ‖cexp ((Real.pi : ℂ) * I * (r : ℂ) * z₂line t)‖ = rexp (-Real.pi * r) := by
      simp [Complex.norm_exp]
    have : rexp (-Real.pi * r) = rexp (-(Real.pi * r)) := by
      congr 1; ring
    simpa [r, mul_assoc, mul_left_comm, mul_comm, this] using hmain
  have hnorm (x : ℝ⁸) :
      ‖permI2Kernel w (x, t)‖ =
        ‖φ₀'' (-1 / (z₂line t + 1))‖ * (‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2)))) := by
    have hphase : ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ = (1 : ℝ) :=
      SpherePacking.ForMathlib.norm_phase_eq_one (w := w) (x := x)
    have hphase' : ‖cexp (-(2 * (↑π * ↑⟪x, w⟫) * I))‖ = (1 : ℝ) := by
      have harg :
          (↑(-2 * (π * ⟪x, w⟫)) : ℂ) * I = -(2 * (↑π * ↑⟪x, w⟫) * I) := by
        push_cast
        ring
      simpa [harg] using hphase
    calc
      ‖permI2Kernel w (x, t)‖ =
          ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ *
            ‖MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t)‖ := by
          simp [permI2Kernel, mul_assoc]
      _ = ‖MagicFunction.a.ComplexIntegrands.Φ₁' (‖x‖ ^ 2) (z₂line t)‖ := by
          simp [hphase']
      _ =
          ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 *
            ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₂line t : ℂ))‖ := by
          simp [MagicFunction.a.ComplexIntegrands.Φ₁', norm_pow, mul_assoc]
      _ = ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2))) := by
          rw [hexp x]
      _ = ‖φ₀'' (-1 / (z₂line t + 1))‖ * (‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2)))) := by
          simp [mul_assoc]
  have hEq :
      (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) =
        ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 := by
    have hgauss_one : (∫ x : ℝ⁸, rexp (-(Real.pi * (‖x‖ ^ 2)))) = (1 : ℝ) := by
      have h :=
        (integral_rexp_neg_pi_mul_sq_norm (t := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1))
      simpa [one_mul] using (h.trans (by simp))
    calc
      (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖)
          = ∫ x : ℝ⁸,
              ‖φ₀'' (-1 / (z₂line t + 1))‖ *
                (‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2)))) := by
            refine congrArg (fun f : (ℝ⁸ → ℝ) => ∫ x : ℝ⁸, f x) ?_
            ext x
            exact hnorm x
      _ =
          ‖φ₀'' (-1 / (z₂line t + 1))‖ *
            ∫ x : ℝ⁸, ‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2))) := integral_const_mul _ _
      _ =
          ‖φ₀'' (-1 / (z₂line t + 1))‖ *
            (‖z₂line t + 1‖ ^ 2 * ∫ x : ℝ⁸, rexp (-(Real.pi * (‖x‖ ^ 2)))) := by
            have h :
                (∫ x : ℝ⁸, ‖z₂line t + 1‖ ^ 2 * rexp (-(Real.pi * (‖x‖ ^ 2)))) =
                  ‖z₂line t + 1‖ ^ 2 * ∫ x : ℝ⁸, rexp (-(Real.pi * (‖x‖ ^ 2))) := by
              simpa [mul_assoc] using
                (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ⁸))
                  (r := ‖z₂line t + 1‖ ^ 2)
                  (f := fun x : ℝ⁸ ↦ rexp (-(Real.pi * (‖x‖ ^ 2)))))
            rw [h]
      _ = ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 := by
            simp [hgauss_one]
  -- bound `‖z₂line t + 1‖ ^ 2` by `2`
  have :
      (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) ≤
        (2 : ℝ) * ‖φ₀'' (-1 / (z₂line t + 1))‖ := by
    -- rewrite using the exact integral, then apply the estimate `hpow`
    have hnonneg : 0 ≤ ‖φ₀'' (-1 / (z₂line t + 1))‖ := norm_nonneg _
    have hpow' : ‖z₂line t + 1‖ ^ 2 ≤ (2 : ℝ) := by
      simpa [norm_pow] using hpow
    have hmul :
        ‖φ₀'' (-1 / (z₂line t + 1))‖ * ‖z₂line t + 1‖ ^ 2 ≤
          ‖φ₀'' (-1 / (z₂line t + 1))‖ * (2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hpow' hnonneg
    simpa [hEq, mul_assoc, mul_left_comm, mul_comm] using hmul
  simpa [mul_comm] using this

lemma integrable_integral_norm_permI2Kernel (w : ℝ⁸) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) μIoc01 := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  -- A constant majorant is integrable on `Ioc (0,1)`.
  have hmajor : Integrable (fun _t : ℝ ↦ (2 : ℝ) * (C₀ : ℝ)) μIoc01 := by
    simpa using (MeasureTheory.integrable_const (μ := μIoc01) ((2 : ℝ) * (C₀ : ℝ)))
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) μIoc01 := by
    have hker :
        AEStronglyMeasurable (permI2Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
      permI2Kernel_measurable (w := w)
    simpa using
      (SpherePacking.ForMathlib.aestronglyMeasurable_integral_norm_prod_right'
        (μ := μIoc01) (ν := (volume : Measure ℝ⁸)) (f := permI2Kernel w) hker)
  refine Integrable.mono' hmajor hmeas ?_
  -- Prove the bound a.e. on `Ioc (0,1)`, excluding `t = 1` (a null set).
  have hne1 : ∀ᵐ t : ℝ ∂μIoc01, t ≠ 1 := by
    have hμ : μIoc01 ({(1 : ℝ)} : Set ℝ) = 0 := by
      simp [μIoc01]
    simpa [Set.mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.1 hμ)
  have hmem : ∀ᵐ t : ℝ ∂μIoc01, t ∈ Ioc (0 : ℝ) 1 := by
    simpa [μIoc01] using (ae_restrict_mem measurableSet_Ioc : ∀ᵐ t ∂μIoc01, t ∈ Ioc (0 : ℝ) 1)
  filter_upwards [hmem, hne1] with t ht htne1
  have ht_lt1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  -- Bound `‖φ₀''(-1 / (z₂line t + 1))‖` by `C₀` using `norm_φ₀_le` on the upper half-plane.
  have him_pos : 0 < ((-1 : ℂ) / ((t : ℂ) + I)).im := by
    -- This is `neg_one_div_im_pos` specialized to `z = t + I`.
    have : 0 < (((t : ℂ) + I)).im := by simp
    simpa using (neg_one_div_im_pos ((t : ℂ) + I) this)
  let z : UpperHalfPlane := ⟨(-1 : ℂ) / ((t : ℂ) + I), him_pos⟩
  have hz_im : z.im = ((-1 : ℂ) / ((t : ℂ) + I)).im := by
    rfl
  have hz_half : (1 / 2 : ℝ) < z.im := by
    have ht0 : 0 < t := ht.1
    have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht_lt1⟩
    have him : ((-1 : ℂ) / ((t : ℂ) + I)).im = 1 / (t ^ 2 + 1) := by
      simpa using SpherePacking.Integration.im_neg_one_div_ofReal_add_I (t := t)
    have : (1 / 2 : ℝ) < 1 / (t ^ 2 + 1) :=
      SpherePacking.Integration.one_half_lt_one_div_sq_add_one_of_mem_Ioo01 htIoo
    simpa [z, UpperHalfPlane.im, him] using this
  have hφ₀ : ‖φ₀ z‖ ≤ (C₀ : ℝ) * rexp (-2 * π * z.im) := hC₀ z hz_half
  have hφ₀_eq : φ₀ z = φ₀'' ((-1 : ℂ) / ((t : ℂ) + I)) := by
    simpa [z] using (φ₀''_def (z := (-1 : ℂ) / ((t : ℂ) + I)) him_pos).symm
  have hφ₀'' :
      ‖φ₀'' ((-1 : ℂ) / ((t : ℂ) + I))‖ ≤ (C₀ : ℝ) := by
    have hexp : rexp (-2 * π * z.im) ≤ 1 := by
      have : (-2 * π * z.im) ≤ 0 := by
        have : 0 ≤ z.im := (le_of_lt z.2)
        nlinarith [Real.pi_pos, this]
      simpa using (Real.exp_le_one_iff.2 this)
    have hC₀_nonneg : 0 ≤ C₀ := hC₀_pos.le
    have hmul : (C₀ : ℝ) * rexp (-2 * π * z.im) ≤ (C₀ : ℝ) := by
      calc
        (C₀ : ℝ) * rexp (-2 * π * z.im) ≤ (C₀ : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left hexp hC₀_nonneg
        _ = (C₀ : ℝ) := by simp
    have : ‖φ₀'' ((-1 : ℂ) / ((t : ℂ) + I))‖ ≤ (C₀ : ℝ) * rexp (-2 * π * z.im) := by
      simpa [hφ₀_eq] using hφ₀
    exact this.trans hmul
  have hkernel := integral_norm_permI2Kernel_bound (w := w) (t := t) ht
  have hφ₀''_seg : ‖φ₀'' (-1 / (z₂line t + 1))‖ ≤ (C₀ : ℝ) := by
    rw [z₂line_add_one (t := t)]
    simpa using hφ₀''
  have hn0 : 0 ≤ ∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖ := by
    exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have habs :
      ‖∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖‖ = ∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖ := by
    simp [Real.norm_eq_abs, abs_of_nonneg hn0]
  have : (∫ x : ℝ⁸, ‖permI2Kernel w (x, t)‖) ≤ (2 : ℝ) * (C₀ : ℝ) := by
    have hmul : (2 : ℝ) * ‖φ₀'' (-1 / (z₂line t + 1))‖ ≤ (2 : ℝ) * (C₀ : ℝ) := by
      exact mul_le_mul_of_nonneg_left hφ₀''_seg (by positivity)
    exact hkernel.trans hmul
  simpa [habs] using this

/-- Integrability of `permI2Kernel` on the product measure `volume × μIoc01`. -/
public lemma integrable_perm_I₂_kernel (w : ℝ⁸) :
    Integrable (permI2Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) := by
  have hmeas :
      AEStronglyMeasurable (permI2Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
    permI2Kernel_measurable (w := w)
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01) hmeas).2 ?_
  exact ⟨ae_integrable_permI2Kernel_slice (w := w), integrable_integral_norm_permI2Kernel (w := w)⟩

end Integral_Permutations.PermI12Fourier_Integrable
end
end MagicFunction.a.Fourier

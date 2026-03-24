module

public import Mathlib.Init
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Fourier transform lemmas

This file provides Gaussian and Fourier transform calculations shared across the project.
It is specialized to even-dimensional Euclidean spaces `Fin (2 * k)` so that exponents become the
natural number `k`.
-/

namespace SpherePacking.ForMathlib

open scoped FourierTransform RealInnerProductSpace Topology

open Complex Real MeasureTheory

noncomputable section

/-- The norm of the Gaussian factor `cexp (π * I * ‖x‖^2 * z)` depends only on `Im z`. -/
public lemma norm_cexp_pi_mul_I_mul_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z : ℂ) (x : V) :
    ‖cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)‖ = rexp (-π * (‖x‖ ^ 2) * z.im) := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im, pow_two]

/-- A complex Gaussian with positive imaginary parameter is integrable. -/
public lemma integrable_gaussian_cexp_pi_mul_I_mul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun x : V ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)) (volume : Measure V) := by
  simpa [mul_assoc, mul_comm] using
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := -((π : ℂ) * I * z))
      (c := (0 : ℂ)) (w := (0 : V))
      (by simpa [Complex.mul_re, Complex.mul_im, mul_comm] using mul_pos Real.pi_pos hz))

private lemma finrank_div_two_eq_even (k : ℕ) :
    ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * k))) : ℂ) / 2) = (k : ℂ) := by
  simp [Nat.cast_mul]

/-- Fourier transform of the complex Gaussian in even dimension `2k`. -/
public lemma fourier_gaussian_pi_mul_I_mul_even (k : ℕ) (z : ℂ) (hz : 0 < z.im)
    (w : EuclideanSpace ℝ (Fin (2 * k))) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)) w =
      (((I : ℂ) / z) ^ k) * cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    exact (ne_of_gt hz) (by simp [hz0])
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set b : ℂ := -((π : ℂ) * I * z)
  have hb : 0 < b.re := by
    simpa [b, Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm] using
      (mul_pos Real.pi_pos hz : 0 < Real.pi * z.im)
  have hL :
      (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp (-(b * ‖x‖ ^ 2))) =
        fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z) := by
    funext x
    simp [b, mul_assoc, mul_comm]
  have hdiv : π / b = (I : ℂ) / z := by
    have hb0 : b ≠ 0 := by
      have : (π : ℂ) * I * z ≠ 0 := mul_ne_zero (mul_ne_zero hπ0 Complex.I_ne_zero) hz0
      simpa [b] using (neg_ne_zero.2 this)
    field_simp [b, hb0, hz0]
    have hIIπ : (I : ℂ) * (I * (π : ℂ)) = -(π : ℂ) := by
      calc
        (I : ℂ) * (I * (π : ℂ)) = (I * I) * (π : ℂ) := by ac_rfl
        _ = -(π : ℂ) := by simp [Complex.I_mul_I]
    simp [b, hIIπ, mul_left_comm, mul_comm]
  have hexp : cexp (-(π ^ 2 * ‖w‖ ^ 2) / b) = cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
    congr 1
    calc
      (-(π ^ 2 * ‖w‖ ^ 2) / b : ℂ) = (-π ^ 2 * (‖w‖ : ℂ) ^ (2 : ℕ) / b) := by simp [pow_two]
      _ = (-(π : ℂ) * ((‖w‖ : ℂ) ^ (2 : ℕ))) * (π / b) := by
        simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (-(π : ℂ) * (‖w‖ ^ 2 : ℝ)) * ((I : ℂ) / z) := by simp [hdiv]
      _ = (π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have h := fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin (2 * k))) (b := b) hb w
  simpa [hL, hdiv, hexp, mul_assoc, mul_left_comm, mul_comm] using h

/-- Integral of the phase factor times a complex Gaussian in even dimension `2k`. -/
public lemma integral_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z)) =
      (((I : ℂ) / z) ^ k) * cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
  simpa [fourier_eq', smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (fourier_gaussian_pi_mul_I_mul_even (k := k) (z := z) hz (w := w))

/-- Fourier transform of the real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` in even dimension `2k`. -/
public lemma fourier_gaussian_norm_sq_div_even (k : ℕ) (s : ℝ) (hs : 0 < s)
    (w : EuclideanSpace ℝ (Fin (2 * k))) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp (-π * (‖v‖ ^ 2) / s)) w =
      (s ^ k : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  have hb : 0 < ((π / s : ℂ).re) := by simpa using (div_pos Real.pi_pos hs)
  have hbase : (π : ℂ) / (π / s : ℂ) = (s : ℂ) := by
    field_simp [(by exact_mod_cast (ne_of_gt hs) : (s : ℂ) ≠ 0),
      (by exact_mod_cast Real.pi_ne_zero : (π : ℂ) ≠ 0)]
  simpa [div_eq_mul_inv, hbase, finrank_div_two_eq_even (k := k), pow_two, mul_assoc,
    mul_left_comm, mul_comm] using
    (fourier_gaussian_innerProductSpace
      (V := EuclideanSpace ℝ (Fin (2 * k))) (b := (π / s : ℂ)) hb w)

/-- Integral of the phase factor times the real Gaussian in even dimension `2k`. -/
public lemma integral_phase_gaussian_even (k : ℕ) (w : EuclideanSpace ℝ (Fin (2 * k)))
    (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) =
      (s ^ k : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  simpa [fourier_eq', smul_eq_mul, mul_assoc] using
    (fourier_gaussian_norm_sq_div_even (k := k) (s := s) hs (w := w))

end

end SpherePacking.ForMathlib

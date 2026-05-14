module

public import Mathlib.Init
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Fourier transform lemmas

Specialized to even-dimensional Euclidean spaces `Fin (2 * k)` so exponents become `k`.

Also includes boilerplate measurability and norm facts about the bounded Fourier phase
`x ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)`.
-/

namespace SpherePacking.ForMathlib

open scoped FourierTransform RealInnerProductSpace Topology
open Complex Real MeasureTheory Filter

noncomputable section

/-! ## Fourier phase factor -/

/-- The phase factor `exp (i * real)` has norm `1`. -/
public lemma norm_phase_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w x : V) :
    ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)‖ = (1 : ℝ) := by
  simpa using (Complex.norm_exp_ofReal_mul_I (-2 * (π * ⟪x, w⟫)))

/-- The phase factor is a.e. strongly measurable with respect to Lebesgue measure. -/
public lemma aestronglyMeasurable_phase {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasureSpace V] [BorelSpace V] (w : V) :
    AEStronglyMeasurable (fun x : V ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I))
      (volume : Measure V) :=
  Continuous.aestronglyMeasurable (by continuity)

/-- Almost everywhere, the phase factor has norm at most `1`. -/
public lemma ae_norm_phase_le_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasureSpace V] (w : V) :
    (∀ᵐ x : V ∂(volume : Measure V),
      ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)‖ ≤ (1 : ℝ)) :=
  Filter.Eventually.of_forall (fun x => (norm_phase_eq_one (w := w) (x := x)).le)

/-! ## Gaussian factor identities -/

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

/-- Fourier transform of the complex Gaussian in even dimension `2k`. -/
public lemma fourier_gaussian_pi_mul_I_mul_even (k : ℕ) (z : ℂ) (hz : 0 < z.im)
    (w : EuclideanSpace ℝ (Fin (2 * k))) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z)) w =
      (((I : ℂ) / z) ^ k) * cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
  have hz0 : z ≠ 0 := fun hz0 => (ne_of_gt hz) (by simp [hz0])
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set b : ℂ := -((π : ℂ) * I * z)
  have hb : 0 < b.re := by
    simpa [b, Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm] using
      (mul_pos Real.pi_pos hz : 0 < Real.pi * z.im)
  have hL :
      (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp (-(b * ‖x‖ ^ 2))) =
        fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z) := by
    funext x; simp [b, mul_assoc, mul_comm]
  have hb0 : b ≠ 0 := by
    simpa [b] using neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hπ0 Complex.I_ne_zero) hz0)
  have hdiv : π / b = (I : ℂ) / z := by
    field_simp [b, hb0, hz0]
    have hIIπ : (I : ℂ) * (I * (π : ℂ)) = -(π : ℂ) := by
      rw [show (I : ℂ) * (I * (π : ℂ)) = (I * I) * (π : ℂ) by ac_rfl]; simp [Complex.I_mul_I]
    simp [b, hIIπ, mul_left_comm, mul_comm]
  have hexp : cexp (-(π ^ 2 * ‖w‖ ^ 2) / b) = cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
    congr 1
    calc (-(π ^ 2 * ‖w‖ ^ 2) / b : ℂ) = (-(π : ℂ) * ((‖w‖ : ℂ) ^ (2 : ℕ))) * (π / b) := by
          simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z) := by
          simp [hdiv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simpa [hL, hdiv, hexp, mul_assoc, mul_left_comm, mul_comm] using
    fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin (2 * k))) (b := b) hb w

/-- Integral of the phase factor times a complex Gaussian in even dimension `2k`. -/
public lemma integral_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z)) =
      (((I : ℂ) / z) ^ k) * cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z)) := by
  simpa [fourier_eq', smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (fourier_gaussian_pi_mul_I_mul_even (k := k) (z := z) hz (w := w))

/-- Evaluate a Fourier-type Gaussian integral in even real dimension, pulling out a constant `c`. -/
public lemma integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 * k))) (z : ℂ) (hz : 0 < z.im) (c : ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), c *
        (Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z))) =
      c * ((((Complex.I : ℂ) / z) ^ k) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / z))) := by
  simpa [MeasureTheory.integral_const_mul] using congrArg (fun I : ℂ => c * I)
    (integral_phase_gaussian_pi_mul_I_mul_even (k := k) (w := w) (z := z) hz)

/-- Fourier transform of the real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` in even dimension `2k`. -/
public lemma fourier_gaussian_norm_sq_div_even (k : ℕ) (s : ℝ) (hs : 0 < s)
    (w : EuclideanSpace ℝ (Fin (2 * k))) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin (2 * k)) ↦ cexp (-π * (‖v‖ ^ 2) / s)) w =
      (s ^ k : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  have hbase : (π : ℂ) / (π / s : ℂ) = (s : ℂ) := by
    field_simp [(by exact_mod_cast (ne_of_gt hs) : (s : ℂ) ≠ 0),
      (by exact_mod_cast Real.pi_ne_zero : (π : ℂ) ≠ 0)]
  have hfinrank : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * k))) : ℂ) / 2) = (k : ℂ) := by
    simp [Nat.cast_mul]
  simpa [div_eq_mul_inv, hbase, hfinrank, pow_two, mul_assoc,
    mul_left_comm, mul_comm] using
    (fourier_gaussian_innerProductSpace
      (V := EuclideanSpace ℝ (Fin (2 * k))) (b := (π / s : ℂ))
      (by simpa using (div_pos Real.pi_pos hs)) w)

/-- Integral of the phase factor times the real Gaussian in even dimension `2k`. -/
public lemma integral_phase_gaussian_even (k : ℕ) (w : EuclideanSpace ℝ (Fin (2 * k)))
    (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) =
      (s ^ k : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  simpa [fourier_eq', smul_eq_mul, mul_assoc] using
    (fourier_gaussian_norm_sq_div_even (k := k) (s := s) hs (w := w))

/-! ## `rexp` Gaussian integrals on `ℝ⁸` -/

/-- For `s > 0`, `∫ exp (-π ‖x‖² / s)` over `ℝ^(2k)` equals `s ^ k`. -/
public lemma integral_gaussian_rexp_even (k : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin (2 * k)), rexp (-π * (‖x‖ ^ 2) / s)) = s ^ k := by
  rw [integral_congr_ae (ae_of_all _ fun x => show rexp (-π * (‖x‖ ^ 2) / s) =
        rexp (-(π / s) * ‖x‖ ^ 2) by ring_nf),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (div_pos Real.pi_pos hs)]
  simp [show (π / (π / s)) = s from by field_simp]

/-- Gaussian `rexp` integral over `ℝ⁸` with a scale parameter. -/
public lemma integral_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-π * (‖x‖ ^ 2) / s)) = s ^ 4 := by
  simpa using integral_gaussian_rexp_even (k := 4) s hs

/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ⁸` for `s > 0`. -/
public lemma integrable_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ rexp (-π * (‖x‖ ^ 2) / s))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  simpa using
    (MeasureTheory.Integrable.of_integral_ne_zero (μ := volume) <| by
      rw [integral_gaussian_rexp_even (k := 4) (s := s) hs]; exact pow_ne_zero 4 hs.ne' :
      Integrable (fun x : EuclideanSpace ℝ (Fin (2 * 4)) ↦ rexp (-π * (‖x‖ ^ 2) / s))
        (volume : Measure (EuclideanSpace ℝ (Fin (2 * 4)))))

end

end SpherePacking.ForMathlib

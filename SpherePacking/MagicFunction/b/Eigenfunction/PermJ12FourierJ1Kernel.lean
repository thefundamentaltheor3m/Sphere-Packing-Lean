module
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.Contour.MobiusInv.Basic
public import SpherePacking.MagicFunction.PsiTPrimeZ1
public import SpherePacking.Contour.Segments
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Integration.Measure
import SpherePacking.Integration.InvChangeOfVariables
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ1
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.ForMathlib.GaussianRexpIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay


/-!
# Perm J12 Curve Integrals and the J₁ Fourier kernel

Curve-integral representations of the primed real integrals `J₁', J₂', J₃', J₄'` plus the kernel
used to rewrite the Fourier transform of `J₁` using Fubini.

## Main statements
* `J₃'_add_J₄'_eq_curveIntegral_segments`
* `J₁'_eq_Ioc`, `J₂'_eq_Ioc`
* `integral_rexp_neg_pi_mul_sq_norm`
* `integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Real Interval
open Set Complex Real MeasureTheory Filter SpherePacking

/-- The integrand for the primed real integrals `J₁'` and `J₂'`. -/
@[expose] public def Ψ₁' (r : ℝ) (z : ℂ) : ℂ := ψT' z * cexp ((π : ℂ) * I * (r : ℂ) * z)

/-- The Fourier-side integrand: `Ψ₁'` after Gaussian Fourier transform and `z ↦ -1 / z`. -/
@[expose] public def Ψ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  ψT' z * (((I : ℂ) / z) ^ (4 : ℕ)) * cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z))

/-- Modular relation for `ψT'` under Mobius inversion `z ↦ -1 / z`. -/
public lemma ψT'_mobiusInv_eq_div (z : ℂ) (hz : 0 < z.im) :
    ψT' (mobiusInv z) = -(ψT' z) / z ^ (2 : ℕ) := by
  let zH : UpperHalfPlane := ⟨z, hz⟩
  have hz0 : (zH : ℂ) ≠ 0 :=
    fun hz0 => hz.ne' (by simpa [zH] using congrArg Complex.im hz0)
  have hdiv : ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) =
      (-ψT zH) / (zH : ℂ) ^ (2 : ℕ) :=
    (eq_div_iff (pow_ne_zero 2 hz0)).2 <| by
      simpa using (modular_slash_S_apply (f := ψT) (k := (-2 : ℤ)) (z := zH)).symm.trans
        (congrArg (fun F : UpperHalfPlane → ℂ => F zH) ψT_slash_S)
  have hz' : 0 < (mobiusInv z).im := by
    simpa [mobiusInv, Complex.inv_im, div_eq_mul_inv] using
      div_pos hz (Complex.normSq_pos.2 fun hz0 => hz.ne' (by simp [hz0]))
  calc
    ψT' (mobiusInv z) = ψT ⟨mobiusInv z, hz'⟩ := by simp [ψT', hz']
    _ = ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) := by
      congr 1; ext1; simp [zH, mobiusInv, inv_neg]
    _ = (-ψT zH) / (zH : ℂ) ^ (2 : ℕ) := hdiv
    _ = -(ψT' z) / z ^ (2 : ℕ) := by simp [ψT', hz, zH, div_eq_mul_inv]

/-- Express `Ψ₁_fourier` as the pullback of `Ψ₁'` under Mobius inversion, including the Jacobian
factor `-deriv mobiusInv`. -/
public lemma Ψ₁_fourier_eq_neg_deriv_mul (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z) := by
  have hz0 : z ≠ 0 := fun hz0 => (ne_of_gt hz) (by simp [hz0])
  have hψz_eq : ψT' (mobiusInv z) = -(ψT' z) / z ^ (2 : ℕ) := ψT'_mobiusInv_eq_div (z := z) hz
  have hmob : mobiusInv z = (-1 : ℂ) / z := by simp [mobiusInv, div_eq_mul_inv]
  have hI4 : (Complex.I : ℂ) ^ (4 : ℕ) = 1 := by simp
  by_cases hψz : ψT' z = 0
  · simp [Ψ₁', Ψ₁_fourier, hψz,
      show ψT' (mobiusInv z) = 0 by simpa [hψz] using hψz_eq, mul_assoc, mul_left_comm, mul_comm]
  simp only [Ψ₁', Ψ₁_fourier, hmob, deriv_mobiusInv,
    show ψT' ((-1 : ℂ) / z) = -(ψT' z) / z ^ (2 : ℕ) by simpa [hmob] using hψz_eq,
    div_pow, hI4]
  field_simp [hz0, hψz]

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral
open SpherePacking.ForMathlib
open SpherePacking.Contour


section PermJ12

open MeasureTheory Set Complex Real
open Filter
open scoped Interval

private lemma curveIntegral_segment_eq_intervalIntegral (a b : ℂ) (f : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → AffineMap.lineMap a b t = g t) :
    (∫ᶜ z in Path.segment a b, scalarOneForm f z) = ∫ t in (0 : ℝ)..1, (b - a) * f (g t) := by
  rw [curveIntegral_segment (ω := scalarOneForm f) a b]
  exact intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) fun t ht => by
    simp [scalarOneForm_apply, hg t (by simpa [Set.uIcc_of_le zero_le_one] using ht)]

/-- Rewrite the segment integral on `1 → 1 + I` as an interval integral in the parameter `t`. -/
public lemma curveIntegral_segment_z₃ (f : ℂ → ℂ) :
    (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm f z) =
      ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * f (z₃' t) := by
  simpa using curveIntegral_segment_eq_intervalIntegral (1 : ℂ) ((1 : ℂ) + Complex.I) f z₃'
    lineMap_z₃_eq_z₃'

/-- Rewrite the segment integral on `1 + I → I` as an interval integral in the parameter `t`. -/
public lemma curveIntegral_segment_z₄ (f : ℂ → ℂ) :
    (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm f z) =
      ∫ t in (0 : ℝ)..1, (-1 : ℂ) * f (z₄' t) := by
  simpa using curveIntegral_segment_eq_intervalIntegral ((1 : ℂ) + Complex.I) Complex.I f z₄'
    lineMap_z₄_eq_z₄'

/-- Combine the segment formulas for `J₃'` and `J₄'` into a single identity. -/
public lemma J₃'_add_J₄'_eq_curveIntegral_segments (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₃' r + MagicFunction.b.RealIntegrals.J₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁' r) z := by
  simpa [MagicFunction.b.RealIntegrals.J₃', MagicFunction.b.RealIntegrals.J₄', Ψ₁',
    mul_assoc, mul_left_comm, mul_comm] using congrArg₂ (· + ·)
      (curveIntegral_segment_z₃ (f := Ψ₁' r)).symm
      (curveIntegral_segment_z₄ (f := Ψ₁' r)).symm

/-! #### Fourier transform of the `J₁,J₂` kernels -/

/-! ##### Auxiliary integrability lemmas (`t ↦ 1/t` substitution) -/

/-- Gaussian integral in dimension `8`: `∫ exp (-π * t * ‖x‖^2) = (1 / t)^4`. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ (4 : ℕ) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    SpherePacking.ForMathlib.integral_gaussian_rexp_even (k := 4) (s := 1 / t) (one_div_pos.2 ht)

/-- Rewrite `J₁'` as a set integral over `Ioc (0, 1)`. -/
public lemma J₁'_eq_Ioc (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₁' r =
      ∫ t in Ioc (0 : ℝ) 1,
        (Complex.I : ℂ) * ψT' (z₁' t) * cexp ((π : ℂ) * I * (r : ℂ) * (z₁' t)) := by
  simp [MagicFunction.b.RealIntegrals.J₁', intervalIntegral_eq_integral_uIoc, zero_le_one,
    uIoc_of_le, mul_assoc, mul_left_comm, mul_comm]

open scoped ModularForm

/-- Modular rewrite for `ψT'` on the line `z₁line`, in terms of `ψS` on the imaginary axis. -/
public lemma ψT'_z₁line_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁line t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  simpa [SpherePacking.Contour.z₁'_eq_z₁line (t := t) (mem_Icc_of_Ioc ht)] using
    MagicFunction.b.Schwartz.J1Smooth.ψT'_z₁'_eq (t := t) ht

/-- Continuity of `t ↦ ψT' (z₁line t)` on `Ioc (0, 1)`. -/
public lemma continuousOn_ψT'_z₁line :
    ContinuousOn (fun t : ℝ => ψT' (z₁line t)) (Ioc (0 : ℝ) 1) :=
  MagicFunction.continuousOn_ψT'_Ioc_of
      (k := 2) (ψS := ψS) (ψT' := ψT') (z := z₁line)
      (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
        MagicFunction.b.PsiBounds.continuous_ψS)
      (fun t ht => by simpa using ψT'_z₁line_eq (t := t) ht)

/-- Rewrite `J₂'` as a set integral over `Ioc (0, 1)`. -/
public lemma J₂'_eq_Ioc (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₂' r =
      ∫ t in Ioc (0 : ℝ) 1,
        ψT' (z₂' t) * cexp ((π : ℂ) * I * (r : ℂ) * (z₂' t)) := by
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
  obtain ⟨M, hM⟩ := SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
      (f := fun t : ℝ => ψT' (z₂line t)) continuous_ψT'_z₂line
  refine ⟨M, fun t ht => ?_⟩
  simpa [SpherePacking.Contour.z₂'_eq_z₂line (t := t) (mem_Icc_of_Ioc ht)] using
    hM t (by simpa [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)


end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier

namespace MagicFunction

open scoped Interval Topology
open MeasureTheory Set Complex Real Filter
open SpherePacking.Integration (μIoc01)

noncomputable section

/-- Integrability on `μIoc01` of `t ↦ ‖ψT' (z₁line t)‖ * (1 / t)^(k+2)`, given the standard modular
bound by `exp(-π/t) * t^k`. -/
public lemma integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
    (ψT' : ℂ → ℂ) (k : ℕ) (Cψ : ℝ)
    (hcont : ContinuousOn (fun t : ℝ => ψT' (SpherePacking.Contour.z₁line t)) (Ioc (0 : ℝ) 1))
    (hbound :
      ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
        ‖ψT' (SpherePacking.Contour.z₁line t)‖ ≤ (Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) :
    Integrable
      (fun t : ℝ => ‖ψT' (SpherePacking.Contour.z₁line t)‖ * (1 / t) ^ (k + 2)) μIoc01 := by
  let g : ℝ → ℝ := fun t => ‖ψT' (SpherePacking.Contour.z₁line t)‖ * (1 / t) ^ (k + 2)
  have hmajor0 :
      IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-Real.pi / t)) (Ioc (0 : ℝ) 1) volume := by
    simpa using SpherePacking.Integration.integrableOn_one_div_sq_mul_exp_neg_div
      (c := Real.pi) (by simpa using Real.pi_pos)
  have hmajor :
      Integrable (fun t : ℝ ↦ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t))) μIoc01 := by
    have h0' : Integrable (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-Real.pi / t))
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
      by simpa [MeasureTheory.IntegrableOn] using hmajor0
    simpa [μIoc01, mul_assoc, mul_left_comm, mul_comm] using h0'.const_mul Cψ
  have hmeas_g : AEStronglyMeasurable g μIoc01 := by
    have hcont_inv : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) (Ioc (0 : ℝ) 1) :=
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono
        (fun t ht => by simp [ne_of_gt ht.1])
    have hcont_g : ContinuousOn g (Ioc (0 : ℝ) 1) := by
      simpa [g, one_div] using hcont.norm.mul (hcont_inv.pow (k + 2))
    simpa [μIoc01] using hcont_g.aestronglyMeasurable
      (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
  have hg_bound :
      ∀ᵐ t : ℝ ∂μIoc01, ‖g t‖ ≤ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht_ne0 : t ≠ 0 := ht0.ne'
    have hpow_nonneg : 0 ≤ (1 / t : ℝ) ^ (k + 2) := pow_nonneg (one_div_nonneg.2 ht0.le) (k + 2)
    have hgt0 : 0 ≤ g t := mul_nonneg (norm_nonneg _) hpow_nonneg
    have hnorm_g : ‖g t‖ = g t := by simp [Real.norm_eq_abs, abs_of_nonneg hgt0]
    have hpow_simp : (t ^ k) * (1 / t) ^ (k + 2) = 1 / t ^ (2 : ℕ) := by
      calc (t ^ k) * (1 / t) ^ (k + 2)
          = (t ^ k * (1 / t) ^ k) * (1 / t) ^ (2 : ℕ) := by simp [pow_add]; ac_rfl
        _ = ((t * (1 / t)) ^ k) * (1 / t) ^ (2 : ℕ) := by simp [mul_pow, mul_assoc]
        _ = 1 / t ^ (2 : ℕ) := by simp [one_div, ht_ne0]
    have : g t ≤ (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
      have hmul := mul_le_mul_of_nonneg_right (hbound t ht) hpow_nonneg
      have hR :
          ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2) =
            (Cψ : ℝ) * ((1 / t ^ 2) * rexp (-Real.pi / t)) := by
        calc ((Cψ : ℝ) * rexp (-Real.pi / t) * t ^ k) * (1 / t) ^ (k + 2)
            = (Cψ : ℝ) * (rexp (-Real.pi / t) * (t ^ k * (1 / t) ^ (k + 2))) := by ac_rfl
          _ = (Cψ : ℝ) * (rexp (-Real.pi / t) * (1 / t ^ (2 : ℕ))) := by
                simpa [mul_assoc] using
                  congrArg (fun u : ℝ => (Cψ : ℝ) * (rexp (-Real.pi / t) * u)) hpow_simp
          _ = (Cψ : ℝ) * ((1 / t ^ (2 : ℕ)) * rexp (-Real.pi / t)) := by ac_rfl
      exact hmul.trans_eq hR
    simpa [hnorm_g] using this
  exact Integrable.mono' hmajor hmeas_g hg_bound

end

end MagicFunction

namespace MagicFunction.b.Fourier

noncomputable section

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral Filter
open SpherePacking.ForMathlib SpherePacking.Integration SpherePacking.Contour
open scoped FourierTransform RealInnerProductSpace Topology Real Interval

/-- Rewrite `J₁'` using the explicit line parametrisation `z₁line`. -/
public lemma J₁'_eq_integral_z₁line (r : ℝ) :
    MagicFunction.b.RealIntegrals.J₁' r =
      ∫ t in Ioc (0 : ℝ) 1,
        (Complex.I : ℂ) * ψT' (z₁line t) *
          cexp ((π : ℂ) * I * (r : ℂ) * (z₁line t)) := by
  rw [J₁'_eq_Ioc (r := r)]
  refine MeasureTheory.integral_congr_ae <|
    (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
      simpa [z₁line, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
        congrArg (fun z : ℂ => (Complex.I : ℂ) * ψT' z * cexp ((π : ℂ) * I * (r : ℂ) * z))
          (z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht))

/-- The `(x,t)`-kernel used in the `J₁` Fourier-transform calculation. -/
@[expose] public def permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    EuclideanSpace ℝ (Fin 8) × ℝ → ℂ :=
  fun p =>
    cexp ((-2 * (π * ⟪p.1, w⟫)) * I) *
      ((Complex.I : ℂ) * ψT' (z₁line p.2) *
        cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)))

/-- Move the Fourier phase inside the `t`-integral, rewriting `J₁'` using `permJ1Kernel`. -/
public lemma phase_mul_J₁'_eq_integral_permJ1Kernel (w x : EuclideanSpace ℝ (Fin 8)) :
    cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) *
        MagicFunction.b.RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ1Kernel w (x, t) ∂μIoc01 := by
  rw [show MagicFunction.b.RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
        ∫ t : ℝ,
          (Complex.I : ℂ) * ψT' (z₁line t) *
            cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₁line t)) ∂μIoc01 from by
      simpa [μIoc01] using (J₁'_eq_integral_z₁line (r := (‖x‖ ^ (2 : ℕ)))),
    (MeasureTheory.integral_const_mul (μ := μIoc01)
      (r := cexp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I))
      (f := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁line t) *
        cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₁line t)))).symm]
  exact MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun t => by
    simp [permJ1Kernel, mul_assoc, mul_left_comm, mul_comm]

lemma integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =
      ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ) := by
  rw [show (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =
        ∫ x : EuclideanSpace ℝ (Fin 8), ‖ψT' (z₁line t)‖ * rexp (-(π * (t * (‖x‖ ^ 2)))) from
      MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun x => by
        simpa [mul_assoc] using
          show ‖permJ1Kernel w (x, t)‖ = ‖ψT' (z₁line t)‖ * rexp (-(π * t * (‖x‖ ^ 2))) by
            rw [show ‖permJ1Kernel w (x, t)‖ =
                ‖cexp ((-2 * (π * ⟪x, w⟫)) * I)‖ *
                  (‖ψT' (z₁line t)‖ *
                    ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖) from by
              simp [permJ1Kernel, mul_assoc],
              show ‖cexp ((-2 * (π * ⟪x, w⟫)) * I)‖ = (1 : ℝ) by
                simpa using Complex.norm_exp_ofReal_mul_I (-2 * (π * ⟪x, w⟫)),
              show ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖ =
                  rexp (-(π * t * (‖x‖ ^ 2))) by
                simpa [z₁line, mul_assoc, mul_left_comm, mul_comm] using
                  norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)]
            simp [mul_assoc],
    MeasureTheory.integral_const_mul ‖ψT' (z₁line t)‖ fun a ↦ rexp (-(π * (t * ‖a‖ ^ 2)))]
  simp [show (∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ)
    from by simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integral_rexp_neg_pi_mul_sq_norm (t := t) ht.1)]

lemma integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  have hgauss' :
      Integrable
          (fun x : EuclideanSpace ℝ (Fin 8) ↦
            ((Complex.I : ℂ) * ψT' (z₁line t)) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
        (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
    simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (z := z₁line t)
          (by simpa [z₁line] using ht.1)).const_mul ((Complex.I : ℂ) * ψT' (z₁line t))
  simpa [permJ1Kernel, mul_assoc] using
    Integrable.bdd_mul (hg := hgauss')
      (f := fun x : EuclideanSpace ℝ (Fin 8) ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I))
      (g := fun x : EuclideanSpace ℝ (Fin 8) ↦
        ((Complex.I : ℂ) * ψT' (z₁line t)) *
          cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
      (c := (1 : ℝ)) (SpherePacking.ForMathlib.aestronglyMeasurable_phase (w := w))
      (SpherePacking.ForMathlib.ae_norm_phase_le_one (w := w))

/-- Almost-everywhere integrability of the `x`-slices of `permJ1Kernel` over `μIoc01`. -/
public lemma ae_integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 8)))) :=
  (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
    simpa using integrable_permJ1Kernel_slice (w := w) (t := t) ht

/-- Integrability of `t ↦ ∫ ‖permJ1Kernel w (x,t)‖ dx` over `μIoc01`. -/
public lemma integrable_integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) μIoc01 := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let g : ℝ → ℝ := fun t => ‖ψT' (z₁line t)‖ * (1 / t) ^ (4 : ℕ)
  have hAE :
      (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ1Kernel w (x, t)‖) =ᵐ[μIoc01] g :=
    (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
      simpa [g] using (integral_norm_permJ1Kernel (w := w) (t := t) ht)
  refine (show Integrable g μIoc01 from ?_).congr hAE.symm
  simpa [g] using
    MagicFunction.integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
      (ψT' := ψT') (k := 2) (Cψ := Cψ) continuousOn_ψT'_z₁line fun t ht => by
        simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
          MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS)
            (ψZ := ψT') (z := z₁line) (hCψ := hCψ)
            (hEq := fun s hs => ψT'_z₁line_eq (t := s) hs) (t := t) ht

end

end MagicFunction.b.Fourier

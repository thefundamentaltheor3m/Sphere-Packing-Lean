module
public import SpherePacking.MagicFunction.b.Schwartz.Basic
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.Psi
public import SpherePacking.Contour.MobiusInv.WedgeSetContour
public import SpherePacking.MagicFunction.PsiTPrimeZ1
public import SpherePacking.Integration.Measure
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import SpherePacking.ForMathlib.ScalarOneForm
import Mathlib.MeasureTheory.Integral.Prod
import SpherePacking.MagicFunction.b.PsiBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.Integration.InvChangeOfVariables
import SpherePacking.MagicFunction.b.Schwartz.SmoothJ1
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay

/-!
# Regularity and contour deformation for `perm_J₁_J₂`

Holomorphicity of `ψT'`, `Ψ₁'` and vanishing of `Ψ₁'` at the cusp `1` within `closure wedgeSet`.
Also includes the Fourier transforms of `J₁` and `J₂` as curve integrals along vertical segments,
together with the curve-integral representations of `J₁', J₂', J₃', J₄'` and the kernel used to
rewrite the Fourier transform of `J₁` using Fubini.
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

namespace SpherePacking.Contour

noncomputable section

open Set Filter MeasureTheory
open MagicFunction
open scoped Topology Complex FourierTransform RealInnerProductSpace

/-- Bundles the hypotheses for `tendsto_Ψ₁'_one_within_closure_wedgeSet_of`. -/
public structure TendstoPsiOneHypotheses (wedgeSet : Set ℂ) (ψS : UpperHalfPlane → ℂ)
    (ψT' : ℂ → ℂ) (Ψ₁' : ℝ → ℂ → ℂ) (gAct : UpperHalfPlane → UpperHalfPlane) (k : ℕ) : Prop where
  hk : (1 : ℕ) ≤ k
  Ψ₁'_eq : ∀ r : ℝ, ∀ z : ℂ,
    Ψ₁' r z = ψT' z * cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)
  ψT'_one : ψT' (1 : ℂ) = 0
  tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
  gAct_im : ∀ {z : ℂ} (hz : 0 < z.im),
    (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1)
  ψT'_eq_neg_ψS_mul : ∀ {z : ℂ} (hz : 0 < z.im),
    ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ k
  mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → z ≠ (1 : ℂ) → z ∈ UpperHalfPlane.upperHalfPlaneSet
  closure_wedgeSet_subset_abs_re_sub_one_le_im :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → |z.re - 1| ≤ z.im

private def expNorm (r : ℝ) (z : ℂ) : ℝ := ‖cexp (z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))))‖

/-- Under `TendstoPsiOneHypotheses`, `Ψ₁' r` tends to `0` as `z → 1` within `closure wedgeSet`. -/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet_of {wedgeSet : Set ℂ}
    {ψS : UpperHalfPlane → ℂ} {ψT' : ℂ → ℂ} {Ψ₁' : ℝ → ℂ → ℂ}
    {gAct : UpperHalfPlane → UpperHalfPlane} {k : ℕ}
    (h : TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct k) (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  let M : ℝ := expNorm r (1 : ℂ) + 1
  have hMpos : 0 < M := by linarith [show 0 ≤ expNorm r 1 from norm_nonneg _]
  obtain ⟨δexp, hδexp_pos, hExpBound⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ {z : ℂ}, dist z (1 : ℂ) < δ → expNorm r z ≤ expNorm r (1 : ℂ) + 1 := by
    rcases (Metric.continuousAt_iff.1 (by
      simpa [expNorm] using (continuousAt_id.mul continuousAt_const).cexp.norm :
      ContinuousAt (expNorm r) (1 : ℂ))) 1 (by norm_num) with ⟨δ, hδ_pos, hδ⟩
    exact ⟨δ, hδ_pos, fun {z} hz => le_of_lt (sub_lt_iff_lt_add'.1
      (abs_sub_lt_iff.1 (by simpa [Real.dist_eq] using hδ hz)).1)⟩
  obtain ⟨A, hApos, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im → ‖ψS τ‖ ≤ (1 : ℝ) := by
    rcases (UpperHalfPlane.atImInfty_mem (S := {τ : UpperHalfPlane | ‖ψS τ‖ < (1 : ℝ)})).1
      (((tendsto_zero_iff_norm_tendsto_zero).1 h.tendsto_ψS_atImInfty).eventually
        (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))) with ⟨A0, hA0⟩
    exact ⟨max A0 1, zero_lt_one.trans_le (le_max_right _ _),
      fun τ hτ => (hA0 τ ((le_max_left _ _).trans hτ)).le⟩
  refine (Metric.tendsto_nhdsWithin_nhds).2 fun ε hε => ?_
  refine ⟨min δexp (min (min 1 (ε / M)) (1 / (2 * A))),
    lt_min hδexp_pos (lt_min (lt_min (by norm_num) (div_pos hε hMpos)) (by positivity)),
    fun z hzcl hdistz => ?_⟩
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1; simpa [h.Ψ₁'_eq, h.ψT'_one] using hε
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      h.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1
  let zH : UpperHalfPlane := ⟨z, hz_im_pos⟩
  have hexpZ : expNorm r z ≤ M := hExpBound (lt_of_lt_of_le hdistz (min_le_left _ _))
  have hdist_min := lt_of_lt_of_le hdistz (min_le_right _ _)
  have hdist_lt := lt_of_lt_of_le hdist_min (min_le_left _ _)
  have hdist_lt_one : dist z (1 : ℂ) < 1 := lt_of_lt_of_le hdist_lt (min_le_left _ _)
  have hdist_pow : (dist z (1 : ℂ)) ^ k < ε / M :=
    ((by simpa [pow_one] using pow_le_pow_of_le_one dist_nonneg hdist_lt_one.le h.hk
      : (dist z (1 : ℂ)) ^ k ≤ dist z (1 : ℂ))).trans_lt
        (lt_of_lt_of_le hdist_lt (min_le_right _ _))
  have hdist_im : dist z (1 : ℂ) < 1 / (2 * A) := lt_of_lt_of_le hdist_min (min_le_right _ _)
  have hA_le_im : A ≤ (gAct zH).im := by
    have hz_im_lt : z.im < 1 / (2 * A) := lt_of_le_of_lt
      (by simpa [abs_of_nonneg hz_im_pos.le] using Complex.abs_im_le_norm (z - 1))
      (by simpa [dist_eq_norm] using hdist_im)
    have habs_re : |z.re - 1| ≤ z.im :=
      h.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
    have hbound : (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) := by
      have hnormSq_pos : 0 < Complex.normSq (z - 1) :=
        Complex.normSq_pos.2 (sub_ne_zero.mpr hz1)
      have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
        have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs_re 2
        nlinarith [show Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 by
          simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm], hre_sq]
      calc (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := by field_simp
        _ ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le hnormSq_pos hnormSq_le) hz_im_pos.le
        _ = z.im / Complex.normSq (z - 1) := by simp [div_eq_mul_inv]
    simpa [zH, h.gAct_im (z := z) (hz := hz_im_pos)] using ((lt_div_iff₀
      (by positivity : (0:ℝ) < 2 * z.im)).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using
        (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * A)).1 hz_im_lt)).trans_le hbound |>.le
  have hψT_norm : ‖ψT' z‖ ≤ ‖(z - 1) ^ k‖ :=
    calc ‖ψT' z‖ = ‖ψS (gAct zH)‖ * ‖(z - 1) ^ k‖ := by
            simp [show ψT' z = -ψS (gAct zH) * (z - 1) ^ k by
              simpa [zH] using h.ψT'_eq_neg_ψS_mul (z := z) (hz := hz_im_pos), norm_neg]
      _ ≤ 1 * ‖(z - 1) ^ k‖ := mul_le_mul_of_nonneg_right (hA _ hA_le_im) (norm_nonneg _)
      _ = _ := by simp
  have hmain : ‖Ψ₁' r z‖ ≤ (dist z (1 : ℂ)) ^ k * M :=
    calc ‖Ψ₁' r z‖ = ‖ψT' z‖ * expNorm r z := by
            simp [h.Ψ₁'_eq, expNorm, show ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z) =
              z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))) by ac_rfl]
      _ ≤ ‖(z - 1) ^ k‖ * expNorm r z :=
          mul_le_mul_of_nonneg_right hψT_norm (by simp [expNorm])
      _ ≤ ‖(z - 1) ^ k‖ * M := mul_le_mul_of_nonneg_left hexpZ (norm_nonneg _)
      _ = (dist z (1 : ℂ)) ^ k * M := by simp [dist_eq_norm, norm_pow]
  simpa [dist_eq_norm] using hmain.trans_lt ((lt_div_iff₀ hMpos).mp hdist_pow)

/-- Fubini-based curve-integral formula for the Fourier transform of a radial Schwartz map. -/
public theorem fourier_J_eq_curveIntegral_of
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure ℝ} [MeasureTheory.SFinite μ]
    {J : SchwartzMap V ℂ} {J' : ℝ → ℂ}
    {permJKernel : V → V × ℝ → ℂ}
    {g : V → ℝ → ℂ}
    {Ψ_fourier : ℝ → ℂ → ℂ}
    (a b : ℂ)
    (J_apply : ∀ x : V, (J : V → ℂ) x = J' (‖x‖ ^ (2 : ℕ)))
    (phase_mul_J'_eq_integral_permJKernel :
      ∀ w x : V,
        Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) * J' (‖x‖ ^ (2 : ℕ)) =
          ∫ t : ℝ, permJKernel w (x, t) ∂μ)
    (integrable_permJKernel :
      ∀ w : V, MeasureTheory.Integrable (permJKernel w)
        ((MeasureTheory.volume : MeasureTheory.Measure V).prod μ))
    (integral_permJKernel_x_ae :
      ∀ w : V,
        (fun t : ℝ => (∫ x : V, permJKernel w (x, t)
          ∂(MeasureTheory.volume : MeasureTheory.Measure V))) =ᵐ[μ] fun t => g w t)
    (integral_g_eq_curveIntegral :
      ∀ w : V,
        (∫ t : ℝ, g w t ∂μ) =
          (∫ᶜ z in Path.segment a b,
            MagicFunction.scalarOneForm (Ψ_fourier (‖w‖ ^ (2 : ℕ))) z))
  (w : V) :
    (𝓕 (J : V → ℂ)) w =
      (∫ᶜ z in Path.segment a b,
        MagicFunction.scalarOneForm (Ψ_fourier (‖w‖ ^ (2 : ℕ))) z) := by
  rw [Real.fourier_eq' (J : V → ℂ) w]
  simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul]
  have htoIter :
      (fun x : V =>
          Complex.exp (-(2 * (↑Real.pi : ℂ) * (↑⟪x, w⟫ : ℂ) * Complex.I)) * (J : V → ℂ) x) =
        fun x : V => ∫ t : ℝ, permJKernel w (x, t) ∂μ := by
    funext x
    simpa [J_apply (x := x), mul_assoc] using
      phase_mul_J'_eq_integral_permJKernel (w := w) (x := x)
  rw [htoIter, MeasureTheory.integral_integral_swap
    (μ := (MeasureTheory.volume : MeasureTheory.Measure V)) (ν := μ)
    (f := fun x t => permJKernel w (x, t))
    (by simpa [Function.uncurry] using integrable_permJKernel w),
    MeasureTheory.integral_congr_ae (integral_permJKernel_x_ae w)]
  exact integral_g_eq_curveIntegral w

end

end SpherePacking.Contour

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap
open SpherePacking

section Integral_Permutations

open scoped Real
open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral

section PermJ12

open MeasureTheory Set Complex Real Filter
open scoped Interval ModularForm

/-- Holomorphicity of `ψT` when viewed as a complex function on the upper half-plane. -/
public lemma differentiableOn_ψT_ofComplex :
    DifferentiableOn ℂ (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hH2 := (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
  have hH3 := (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
  have hH4 := (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
  have hterm1 := (hH3.add hH4).div (hH2.pow 2)
    fun z _ => pow_ne_zero 2 (H₂_ne_zero (UpperHalfPlane.ofComplex z))
  have hterm2 := (hH2.add hH3).div (hH4.pow 2)
    fun z _ => pow_ne_zero 2 (H₄_ne_zero (UpperHalfPlane.ofComplex z))
  have hExpr :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (128 : ℂ) *
            (((H₃ (UpperHalfPlane.ofComplex z) + H₄ (UpperHalfPlane.ofComplex z)) /
                    (H₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) +
              ((H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
                    (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))))
        UpperHalfPlane.upperHalfPlaneSet := by
    simpa [mul_assoc] using (DifferentiableOn.const_mul (hterm1.add hterm2) (128 : ℂ))
  exact hExpr.congr fun z _ =>
    congrArg (fun f : UpperHalfPlane → ℂ => f (UpperHalfPlane.ofComplex z)) ψT_eq

/-- Holomorphicity of `Ψ₁' r` on the upper half-plane. -/
public lemma differentiableOn_Ψ₁'_upper (r : ℝ) :
    DifferentiableOn ℂ (Ψ₁' r) UpperHalfPlane.upperHalfPlaneSet :=
  (differentiableOn_ψT_ofComplex.congr fun z hz => by
    have hz' : 0 < z.im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hz
    simp [ψT', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']).mul
    ((differentiable_id.const_mul
      ((Real.pi : ℂ) * Complex.I * (r : ℂ))).cexp.differentiableOn)

open UpperHalfPlane Complex ModularGroup MatrixGroups ModularForm SlashAction Matrix
open scoped Real ModularForm MatrixGroups

/-- `Ψ₁' r` tends to `0` at the cusp `1` when restricted to `closure wedgeSet`. -/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ModularGroup.S * ModularGroup.T * ModularGroup.S
  let gAct : UpperHalfPlane → UpperHalfPlane := fun zH =>
    HSMul.hSMul (α := Matrix.SpecialLinearGroup (Fin 2) ℤ) (β := UpperHalfPlane)
      (γ := UpperHalfPlane) g zH
  have hg : g = ⟨!![-1, 0; 1, -1], by norm_num [Matrix.det_fin_two_of]⟩ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [g, ModularGroup.S, ModularGroup.T]
  have hdenom : ∀ {z : ℂ} (hz : 0 < z.im),
      UpperHalfPlane.denom g (⟨z, hz⟩ : UpperHalfPlane) = (z : ℂ) - 1 := fun {z} hz => by
    simp [UpperHalfPlane.denom, hg, sub_eq_add_neg]
  have hgAct_im :
      ∀ {z : ℂ} (hz : 0 < z.im),
        (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1) := fun {z} hz => by
    simpa [hdenom hz, gAct] using
      (ModularGroup.im_smul_eq_div_normSq (g := g) (z := (⟨z, hz⟩ : UpperHalfPlane)))
  have hψT' :
      ∀ {z : ℂ} (hz : 0 < z.im),
        ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ (2 : ℕ) := fun {z} hz => by
    let zH : UpperHalfPlane := ⟨z, hz⟩
    have h1 : ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) = -ψT zH := by
      simpa [ModularForm.SL_slash_apply, gAct, g] using
        congrArg (fun F : UpperHalfPlane → ℂ => F zH) ψS_slash_STS
    calc ψT' z = ψT zH := by simp [ψT', hz, zH]
      _ = -ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (2 : ℤ) := by
            simpa [neg_mul, mul_assoc] using (congrArg Neg.neg h1).symm
      _ = -ψS (gAct zH) * ((z : ℂ) - 1) ^ (2 : ℤ) := by rw [hdenom hz]
      _ = -ψS (gAct zH) * (z - 1) ^ (2 : ℕ) := by
            simpa using congrArg (fun t : ℂ => -ψS (gAct zH) * t) (zpow_ofNat (z - 1) 2)
  simpa using
    (SpherePacking.Contour.tendsto_Ψ₁'_one_within_closure_wedgeSet_of
      (h := ({
        hk := by decide
        Ψ₁'_eq := by intro r z; rfl
        ψT'_one := by simp [ψT']
        tendsto_ψS_atImInfty := MagicFunction.b.PsiBounds.tendsto_ψS_atImInfty
        gAct_im := hgAct_im
        ψT'_eq_neg_ψS_mul := hψT'
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :=
          mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one
        closure_wedgeSet_subset_abs_re_sub_one_le_im := fun {z} hz => by
          simpa using (closure_wedgeSet_subset_abs_re_sub_one_le_im (a := z) hz)
      } : SpherePacking.Contour.TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct 2))
      (r := r))

end Integral_Permutations.PermJ12
end

end MagicFunction.b.Fourier

/-! ## Fourier transform of `J₂` -/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Real Interval
open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap
open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral Filter
open SpherePacking.ForMathlib SpherePacking.Contour SpherePacking.Integration

def permJ2Kernel (w : EuclideanSpace ℝ (Fin 8)) : EuclideanSpace ℝ (Fin 8) × ℝ → ℂ :=
  fun p =>
    cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
      (ψT' (z₂line p.2) *
        cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)))

lemma phase_mul_J₂'_eq_integral_permJ2Kernel (w x : EuclideanSpace ℝ (Fin 8)) :
    cexp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
        MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ2Kernel w (x, t) ∂μIoc01 := by
  rw [show MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, ψT' (z₂line t) *
        cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)) ∂μIoc01 from by
    simpa [μIoc01] using (J₂'_eq_Ioc (r := ‖x‖ ^ (2 : ℕ))).trans
      (MeasureTheory.integral_congr_ae <| (ae_restrict_iff' measurableSet_Ioc).2 <|
        .of_forall fun t ht => by
          simp [SpherePacking.Contour.z₂'_eq_z₂line (t := t) (mem_Icc_of_Ioc ht)])]
  simpa [permJ2Kernel] using
    (MeasureTheory.integral_const_mul (μ := μIoc01)
      (r := cexp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I))
      (f := fun t => ψT' (z₂line t) *
        cexp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)))).symm

lemma integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ2Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 8))) := by
  simpa [permJ2Kernel, mul_assoc] using Integrable.bdd_mul (c := (1 : ℝ))
    (hg := by simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul
        (z := z₂line t) (by simp [z₂line] : 0 < (z₂line t).im)).const_mul (ψT' (z₂line t)))
    (aestronglyMeasurable_phase (w := w)) (ae_norm_phase_le_one (w := w))

lemma integral_permJ2Kernel_x (w : EuclideanSpace ℝ (Fin 8)) (t : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ2Kernel w (x, t)) =
      Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  simpa [permJ2Kernel, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm] using
    SpherePacking.ForMathlib.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₂line t) (by simp [z₂line]) (c := ψT' (z₂line t))

lemma integrable_permJ2Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (permJ2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  have hψ : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => ψT' (z₂line p.2) :=
    continuous_ψT'_z₂line.comp continuous_snd
  have hzline : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => z₂line p.2 :=
    continuous_z₂line.comp continuous_snd
  rcases exists_bound_norm_ψT'_z₂' with ⟨Mψ, hMψ'⟩
  set Cgauss : ℝ := ∫ x : EuclideanSpace ℝ (Fin 8), rexp (-(π * ‖x‖ ^ 2))
  have hCgauss : 0 ≤ Cgauss := MeasureTheory.integral_nonneg fun x => by positivity
  have hbound :
      ∀ᵐ t : ℝ ∂μIoc01,
        (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) ≤ (Mψ : ℝ) * Cgauss := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
    rw [show (∫ x : EuclideanSpace ℝ (Fin 8), ‖permJ2Kernel w (x, t)‖) =
        ‖ψT' (z₂line t)‖ * Cgauss from by
      simpa [funext fun x : EuclideanSpace ℝ (Fin 8) =>
        show ‖permJ2Kernel w (x, t)‖ = ‖ψT' (z₂line t)‖ * rexp (-(π * ‖x‖ ^ 2)) by
          have hgauss :
              ‖cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))‖ = rexp (-(π * ‖x‖ ^ 2)) := by
            simpa [z₂line, show (-π * (‖x‖ ^ 2) : ℝ) = -(π * ‖x‖ ^ 2) from by ring] using
              norm_cexp_pi_mul_I_mul_sq (z := z₂line t) (x := x)
          dsimp [permJ2Kernel]
          rw [norm_mul, norm_phase_eq_one (w := w) (x := x)]
          simp_all, Cgauss, mul_assoc]
        using MeasureTheory.integral_const_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
          (r := ‖ψT' (z₂line t)‖) (f := fun x => rexp (-(π * ‖x‖ ^ 2)))]
    refine mul_le_mul_of_nonneg_right ?_ hCgauss
    simpa [show z₂' t = z₂line t from by
      simpa [z₂line, add_assoc, add_left_comm, add_comm] using
        z₂'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht)] using hMψ' t ht
  have hcont : Continuous (permJ2Kernel w) := by unfold permJ2Kernel; fun_prop
  exact (MeasureTheory.integrable_prod_iff'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))) (ν := μIoc01)
    (hcont.aestronglyMeasurable
      (μ := ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01)))).2
    ⟨.of_forall fun t => integrable_permJ2Kernel_slice (w := w) (t := t),
      Integrable.mono' (integrable_const ((Mψ : ℝ) * Cgauss))
        (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
          (μ := μIoc01) (ν := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
          (f := fun p : ℝ × EuclideanSpace ℝ (Fin 8) => ‖permJ2Kernel w (p.2, p.1)‖) (by fun_prop))
        (hbound.mono fun t ht => by
          simpa [Real.norm_eq_abs, abs_of_nonneg
            (MeasureTheory.integral_nonneg fun x => norm_nonneg _ : (0 : ℝ) ≤ _)] using ht)⟩

/-- Fourier transform of `J₂` as a curve integral of `Ψ₁_fourier` along the segment
`Path.segment (-1 + I) I`. -/
public lemma fourier_J₂_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 8)) :
    (𝓕 (J₂ : EuclideanSpace ℝ (Fin 8) → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using
    SpherePacking.Contour.fourier_J_eq_curveIntegral_of
      (a := (-1 : ℂ) + I) (b := I)
      (fun x => show (J₂ : EuclideanSpace ℝ (Fin 8) → ℂ) x =
        MagicFunction.b.RealIntegrals.J₂' (‖x‖ ^ 2) by simp [J₂])
      (fun w x => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          phase_mul_J₂'_eq_integral_permJ2Kernel (w := w) (x := x))
      integrable_permJ2Kernel
      (fun w' => .of_forall fun t => integral_permJ2Kernel_x (w := w') (t := t))
      (fun w' => by
        simpa [SpherePacking.Contour.dir_z₂line, one_mul] using
          SpherePacking.Integration.integral_dir_mul_muIoc01_eq_curveIntegral_segment
            (F := Ψ₁_fourier (‖w'‖ ^ 2)) (a := (-1 : ℂ) + Complex.I) (b := Complex.I)
            (zline := z₂line) SpherePacking.Contour.lineMap_z₂line)
      w

end

end MagicFunction.b.Fourier

/-! ## Fourier transform of `J₁` -/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Real Interval
open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral Filter
open MagicFunction.b.SchwartzIntegrals SpherePacking.ForMathlib SpherePacking.Integration
  SpherePacking.Contour

lemma integrable_permJ1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    Integrable (permJ1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  let sProd : Set (EuclideanSpace ℝ (Fin 8) × ℝ) :=
    (Set.univ : Set (EuclideanSpace ℝ (Fin 8))) ×ˢ (Ioc (0 : ℝ) 1)
  have hsProd : MeasurableSet sProd := by
    simpa [sProd] using (MeasurableSet.univ.prod measurableSet_Ioc)
  have hmeas :
      AEStronglyMeasurable (permJ1Kernel w)
        ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
    let μProd : Measure (EuclideanSpace ℝ (Fin 8) × ℝ) :=
      (volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)
    have hμ : ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) =
        μProd.restrict sProd := by
      simpa [sProd, μProd] using
        (SpherePacking.Integration.prod_muIoc01_eq_restrict
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8)))))
    have hcont : ContinuousOn (permJ1Kernel w) sProd := by
      have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ => (⟪p.1, w⟫ : ℝ) := by
        simpa using (continuous_fst.inner continuous_const)
      have hphase : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
            cexp ((-2 * (π * ⟪p.1, w⟫)) * I) := by
        have harg : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              ((((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ))) : ℝ) : ℂ) * (Complex.I : ℂ) :=
          (Complex.continuous_ofReal.comp
            (continuous_const.mul (continuous_const.mul hinner))).mul continuous_const
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg)
      have hψ : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 8) × ℝ => ψT' (z₁line p.2)) sProd :=
        continuousOn_ψT'_z₁line.comp continuousOn_snd fun _ hp => (Set.mem_prod.mp hp).2
      have hgauss : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
            cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) := by
        have harg' : Continuous fun p : EuclideanSpace ℝ (Fin 8) × ℝ =>
              (π : ℂ) * I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) :=
          continuous_const.mul ((continuous_ofReal.comp (continuous_fst.norm.pow 2)).mul
            (continuous_z₁line.comp continuous_snd))
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg')
      have hconst : ContinuousOn (fun _p : EuclideanSpace ℝ (Fin 8) × ℝ => (Complex.I : ℂ)) sProd :=
        continuousOn_const
      refine (hphase.continuousOn.mul ((hconst.mul hψ).mul hgauss.continuousOn)).congr fun p _ => ?_
      simp [permJ1Kernel, mul_assoc]
    simpa [hμ, μProd] using (hcont.aestronglyMeasurable (μ := μProd) (s := sProd) hsProd)
  exact (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
      (ν := μIoc01) hmeas).2
    ⟨ae_integrable_permJ1Kernel_slice (w := w), integrable_integral_norm_permJ1Kernel (w := w)⟩

lemma integral_permJ1Kernel_x (w : EuclideanSpace ℝ (Fin 8))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ1Kernel w (x, t)) =
      (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := by simpa [z₁line] using ht.1
  let c : ℂ := (Complex.I : ℂ) * ψT' (z₁line t)
  have hfactor :
      (fun x : EuclideanSpace ℝ (Fin 8) ↦ permJ1Kernel w (x, t)) =
        fun x : EuclideanSpace ℝ (Fin 8) ↦
          c * (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))) := by
    funext x; dsimp [permJ1Kernel, c]; simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    (∫ x : EuclideanSpace ℝ (Fin 8), permJ1Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₁line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / (z₁line t)))) := by
          simpa [hfactor] using
            SpherePacking.ForMathlib.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
              (k := 4) (w := w) (z := z₁line t) hz (c := c)
    _ = (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
          simp [c, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

/-- Fourier transform of `J₁` as a curve integral of `Ψ₁_fourier` along the segment
`Path.segment (-1) (-1 + I)`. -/
public lemma fourier_J₁_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 8)) :
    𝓕 (J₁ : EuclideanSpace ℝ (Fin 8) → ℂ) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using
    SpherePacking.Contour.fourier_J_eq_curveIntegral_of
      (a := (-1 : ℂ)) (b := (-1 : ℂ) + I)
      (fun x => by simp [J₁])
      phase_mul_J₁'_eq_integral_permJ1Kernel
      integrable_permJ1Kernel
      (fun w' => by
        simpa [SpherePacking.Integration.μIoc01] using
          (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc).2 <|
            .of_forall fun t ht => by simpa using (integral_permJ1Kernel_x (w := w') (t := t) ht))
      (fun w' => by
        simpa [SpherePacking.Contour.dir_z₁line] using
          SpherePacking.Integration.integral_dir_mul_muIoc01_eq_curveIntegral_segment
            (F := Ψ₁_fourier (‖w'‖ ^ 2)) (a := (-1 : ℂ)) (b := (-1 : ℂ) + Complex.I)
            (zline := z₁line) SpherePacking.Contour.lineMap_z₁line)
      w

end

end MagicFunction.b.Fourier

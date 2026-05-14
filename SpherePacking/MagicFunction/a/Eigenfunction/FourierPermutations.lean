module
public import SpherePacking.MagicFunction.a.Schwartz.Basic
public import SpherePacking.MagicFunction.a.Schwartz.DecayI1
public import SpherePacking.Integration.InvChangeOfVariables
public import SpherePacking.ModularForms.PhiTransform
public import SpherePacking.ForMathlib.GaussianRexpIntegral
public import SpherePacking.Integration.Measure
public import SpherePacking.MagicFunction.a.SpecialValues
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Contour.MobiusInv.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import SpherePacking.Basic.Domains.WedgeSet
public import SpherePacking.Contour.MobiusInv.WedgeSetContour
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import SpherePacking.Contour.Segments
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.ForMathlib.IntegrablePowMulExp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Fourier Permutations

We show that the Fourier transform permutes the integral pieces defining `a`, and deduce that `a`
is a Fourier eigenfunction. Also defines kernels (`I₅.g`, `permI5Phase`, `permI5Kernel`) used to
rewrite the Fourier transform of `I₅` as an iterated integral, bridges `intervalIntegral`
definitions to `curveIntegral` along straight segments, and defines the auxiliary Fourier-side
integrand `Φ₁_fourier`.

## Main statements
* `eig_a`
-/

namespace MagicFunction.a.IntegralEstimates.I₅

open scoped Function UpperHalfPlane Real Complex
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open SpherePacking.Integration.InvChangeOfVariables

noncomputable section Change_of_Variables

/-- The integrand on `Ici 1` obtained from `I₅'` after an inversion change of variables. -/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦
  -I * φ₀'' (I * s) * (s ^ (-4 : ℤ)) * cexp (-π * r / s)

/-- Rewrite `I₅' r` as an integral of `g r` over `Ici 1` (up to the factor `-2`). -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    I₅' r = -2 * ∫ s in Ici (1 : ℝ), g r s := by
  have hRecon : I₅' r = -2 * ∫ t in Ioc 0 1, |(-1 / t ^ 2)| • (g r (1 / t)) := by
    simp only [I₅'_eq_Ioc, g]
    congr 1
    refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc (ae_of_all _ fun t ht ↦ ?_)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      MagicFunction.a.IntegralEstimates.I₃.inv_integrand_eq_integrand (t := t) ht.1 r (1 : ℂ)
  refine hRecon.trans ?_
  simpa using congrArg (fun z : ℂ ↦ (-2 : ℂ) * z)
    (integral_Ici_one_eq_integral_abs_deriv_smul (g := g r)).symm

end Change_of_Variables

end MagicFunction.a.IntegralEstimates.I₅

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MeasureTheory Set Complex Real

/-- Continuity of the integrand `I₅.g` on the domain `univ ×ˢ Ici 1`. -/
public lemma continuousOn_I₅_g :
    ContinuousOn
      (fun p : ℝ⁸ × ℝ ↦ MagicFunction.a.IntegralEstimates.I₅.g (‖p.1‖ ^ 2) p.2)
      (univ ×ˢ Ici (1 : ℝ)) := by
  have hφ' : ContinuousOn (fun p : ℝ⁸ × ℝ ↦ φ₀'' (I * (p.2 : ℂ))) (univ ×ˢ Ici (1 : ℝ)) :=
    MagicFunction.a.Schwartz.I1Decay.φ₀''_I_mul_continuousOn.comp continuousOn_snd mapsTo_snd_prod
  have hzpow' : ContinuousOn (fun p : ℝ⁸ × ℝ ↦ (p.2 : ℂ) ^ (-4 : ℤ)) (univ ×ˢ Ici (1 : ℝ)) :=
    MagicFunction.a.Schwartz.I1Decay.zpow_neg_four_continuousOn.comp continuousOn_snd
      mapsTo_snd_prod
  refine ((((continuousOn_const (c := (-I : ℂ))).mul hφ').mul hzpow').mul
      (show ContinuousOn (fun p : ℝ⁸ × ℝ ↦
          cexp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ))) (univ ×ˢ Ici (1 : ℝ)) from
        fun p hp ↦ by
          have hp2 : (p.2 : ℂ) ≠ 0 := mod_cast (zero_lt_one.trans_le (by simpa using hp)).ne'
          fun_prop (disch := exact hp2))).congr fun p _ ↦ ?_
  simp [MagicFunction.a.IntegralEstimates.I₅.g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The phase factor `v ↦ exp(-2π i ⟪v, w⟫)` used in the kernel for `perm_I₅`. -/
@[expose] public def permI5Phase (w : ℝ⁸) : ℝ⁸ → ℂ :=
  fun v ↦ cexp ((↑(-2 * (π * ⟪v, w⟫)) : ℂ) * I)

/-- The product kernel used to rewrite the Fourier transform of `I₅` as an iterated integral. -/
@[expose] public def permI5Kernel (w : ℝ⁸) : ℝ⁸ × ℝ → ℂ :=
  fun p ↦ permI5Phase w p.1 * MagicFunction.a.IntegralEstimates.I₅.g (‖p.1‖ ^ 2) p.2

/-- Measurability of `permI5Kernel` w.r.t. `volume × (volume.restrict (Ici 1))`. -/
public lemma aestronglyMeasurable_perm_I₅_kernel (w : ℝ⁸) :
    AEStronglyMeasurable
      (permI5Kernel w)
      ((volume : Measure ℝ⁸).prod ((volume : Measure ℝ).restrict (Ici (1 : ℝ)))) := by
  have hphase : Continuous fun p : ℝ⁸ × ℝ ↦ permI5Phase w p.1 := by unfold permI5Phase; fun_prop
  have hkernel : ContinuousOn (permI5Kernel w) (univ ×ˢ Ici (1 : ℝ)) := by
    simpa [permI5Kernel] using hphase.continuousOn.mul continuousOn_I₅_g
  have hμ : (volume : Measure ℝ⁸).prod ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) =
      ((volume : Measure ℝ⁸).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ)) := by
    simpa [Measure.restrict_univ] using
      Measure.prod_restrict (μ := (volume : Measure ℝ⁸)) (ν := (volume : Measure ℝ))
        (s := univ) (t := Ici (1 : ℝ))
  simpa [hμ] using hkernel.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ici)

/-- Unfolding lemma for `I₅` as a radial function in terms of `I₅'`. -/
public lemma I₅_apply (x : ℝ⁸) :
    (I₅ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) := by simp [I₅]

/-- Unfolding lemma for `I₆` as a radial function in terms of `I₆'`. -/
public lemma I₆_apply (x : ℝ⁸) :
    (I₆ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₆' (‖x‖ ^ 2) := by simp [I₆]

/-- Unfolding lemma for `I₁` as a radial function in terms of `I₁'`. -/
public lemma I₁_apply (x : ℝ⁸) :
    (I₁ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₁' (‖x‖ ^ 2) := by simp [I₁]

/-- Unfolding lemma for `I₂` as a radial function in terms of `I₂'`. -/
public lemma I₂_apply (x : ℝ⁸) :
    (I₂ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₂' (‖x‖ ^ 2) := by simp [I₂]

/-- Unfolding lemma for `I₃` as a radial function in terms of `I₃'`. -/
public lemma I₃_apply (x : ℝ⁸) :
    (I₃ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₃' (‖x‖ ^ 2) := by simp [I₃]

/-- Unfolding lemma for `I₄` as a radial function in terms of `I₄'`. -/
public lemma I₄_apply (x : ℝ⁸) :
    (I₄ : ℝ⁸ → ℂ) x = MagicFunction.a.RealIntegrals.I₄' (‖x‖ ^ 2) := by simp [I₄]

end
end MagicFunction.a.Fourier

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open SpherePacking.ForMathlib SpherePacking.Integration
open MeasureTheory Set Complex Real

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

private instance : MeasureTheory.SFinite μIciOne := by dsimp [μIciOne]; infer_instance

/-- Cancellation lemma for the normalization factor `s ^ (-4)` appearing in `permI5Kernel`. -/
public lemma zpow_neg_four_mul_pow_four (s : ℝ) (hs : s ≠ 0) :
    ((s : ℂ) ^ (-4 : ℤ)) * (s ^ 4 : ℂ) = 1 := by
  simpa using zpow_neg_mul_zpow_self (a := (s : ℂ)) (n := (4 : ℤ)) (mod_cast hs)

private lemma norm_permI5Kernel_le (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) (x : ℝ⁸) :
    ‖permI5Kernel w (x, s)‖ ≤ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) := by
  have hπ' : ‖cexp ((((π * (‖x‖ ^ 2)) : ℝ) : ℂ) * I)‖ = (1 : ℝ) :=
    norm_exp_ofReal_mul_I (π * (‖x‖ ^ 2))
  have hπ : ‖cexp (π * I * (‖x‖ ^ 2))‖ = (1 : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hπ'
  have hnormg :
      ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖ =
        ‖MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s‖ := by
    rw [show MagicFunction.a.IntegralEstimates.I₃.g (‖x‖ ^ 2) s =
        MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s * cexp (π * I * (‖x‖ ^ 2)) from by
      simp [MagicFunction.a.IntegralEstimates.I₃.g, MagicFunction.a.IntegralEstimates.I₅.g,
        mul_assoc, mul_left_comm, mul_comm], norm_mul, hπ, mul_one]
  refine (show ‖permI5Kernel w (x, s)‖ = ‖MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s‖
    by simp [permI5Kernel, permI5Phase, norm_exp]).le.trans <| hnormg.le.trans <|
    MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding_aux_1 (r := ‖x‖ ^ 2) s hs

lemma integral_norm_permI5Kernel_bound (w : ℝ⁸) (s : ℝ) (hs : 1 ≤ s) :
    (∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) ≤ ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  calc (∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖)
      ≤ ∫ x : ℝ⁸, ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s) :=
        MeasureTheory.integral_mono_of_nonneg (μ := (volume : Measure ℝ⁸))
          (.of_forall fun _ => norm_nonneg _)
          (by simpa [mul_assoc] using
            (integrable_gaussian_rexp (s := s) hs0).const_mul ‖φ₀'' (I * (s : ℂ))‖)
          (.of_forall (norm_permI5Kernel_le w s hs))
    _ = ‖φ₀'' (I * (s : ℂ))‖ * s ^ 4 := by
      rw [integral_const_mul, SpherePacking.ForMathlib.integral_gaussian_rexp (s := s) hs0]

lemma integrable_integral_norm_permI5Kernel (w : ℝ⁸) :
    Integrable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) μIciOne := by
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : ℝ⁸, ‖permI5Kernel w (x, s)‖) μIciOne := by
    simpa using ((by simpa [μIciOne] using aestronglyMeasurable_perm_I₅_kernel (w := w) :
      AEStronglyMeasurable (permI5Kernel w) ((volume : Measure ℝ⁸).prod μIciOne)
      ).norm.prod_swap.integral_prod_right'
        (μ := μIciOne) (ν := (volume : Measure ℝ⁸)))
  refine (show Integrable (fun s : ℝ ↦
        (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ) * s ^ 4 * rexp (-2 * π * s)) μIciOne by
      simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm,
          show ∀ s : ℝ, (-(2 * π) * s) = (-2 * π * s) from fun s => by ring] using
        ((SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 4) (b := (2 * π))
          (by positivity) : IntegrableOn (fun s : ℝ ↦ s ^ 4 * rexp (-(2 * π) * s))
            (Set.Ici (1 : ℝ)) volume)).const_mul
            (MagicFunction.a.Schwartz.I1Decay.Cφ : ℝ)).mono' hmeas <|
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => ?_
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)]
  linarith [(integral_norm_permI5Kernel_bound w s hs).trans <|
    mul_le_mul_of_nonneg_right (MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := s) hs)
      (pow_nonneg (le_trans (by norm_num) hs) 4)]

/-- Integrability of `permI5Kernel` on the product measure `volume × μIciOne`. -/
public lemma integrable_perm_I₅_kernel (w : ℝ⁸) :
    Integrable (permI5Kernel w) ((volume : Measure ℝ⁸).prod μIciOne) :=
  (MeasureTheory.integrable_prod_iff' (ν := μIciOne)
    (by simpa [μIciOne] using aestronglyMeasurable_perm_I₅_kernel (w := w))).2
    ⟨(ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs => by
      have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
      have hphase : Continuous fun x : ℝ⁸ => permI5Phase w x := by unfold permI5Phase; fun_prop
      have hg : Continuous fun x : ℝ⁸ => MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s := by
        simpa [continuousOn_univ] using continuousOn_I₅_g.comp
          (continuous_id.prodMk continuous_const).continuousOn
          (fun _ _ => ⟨Set.mem_univ _, hs⟩ :
            MapsTo (fun x : ℝ⁸ => (x, s)) (univ : Set ℝ⁸) (univ ×ˢ Ici (1 : ℝ)))
      exact (by simpa [mul_assoc] using
          (integrable_gaussian_rexp (s := s) hs0).const_mul ‖φ₀'' (I * (s : ℂ))‖ :
          Integrable (fun x : ℝ⁸ ↦ ‖φ₀'' (I * (s : ℂ))‖ * rexp (-π * (‖x‖ ^ 2) / s)) volume).mono'
        (by simpa [permI5Kernel] using hphase.mul hg : Continuous _).aestronglyMeasurable
        (.of_forall (norm_permI5Kernel_le w s hs)),
      integrable_integral_norm_permI5Kernel w⟩

/-- The phase-shifted Gaussian integral used in the computation of `𝓕 I₅`. -/
public lemma integral_phase_gaussian (w : ℝ⁸) (s : ℝ) (hs0 : 0 < s) :
    (∫ x : ℝ⁸, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) =
      (s ^ 4 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s) := by
  have h := _root_.SpherePacking.ForMathlib.fourier_gaussian_norm_sq_div_even
    (k := 4) (s := s) hs0 (w := w)
  rw [fourier_eq' (fun v : ℝ⁸ ↦ cexp (-π * (‖v‖ ^ 2) / s)) w] at h
  simpa [smul_eq_mul, mul_assoc] using h

section Integral_Permutations

section PermI5

/-- Fourier transform of `I₅` is `I₆`. -/
public theorem perm_I₅ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₅ = I₆ := by
  ext w
  simp only [FourierTransform.fourierCLE_apply, I₆_apply]
  change 𝓕 (I₅ : ℝ⁸ → ℂ) w = _
  rw [fourier_eq' (I₅ : ℝ⁸ → ℂ) w]
  simp only [smul_eq_mul, I₅_apply]
  simp only [show ∀ x : ℝ⁸, MagicFunction.a.RealIntegrals.I₅' (‖x‖ ^ 2) =
        -2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s from
      fun x ↦ by simpa only [neg_mul] using
        MagicFunction.a.IntegralEstimates.I₅.Complete_Change_of_Variables (r := ‖x‖ ^ 2),
    mul_assoc]
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  let f : ℝ⁸ → ℝ → ℂ := fun x s => permI5Kernel w (x, s)
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ⁸).prod μs) := by
    simpa only [μIciOne] using integrable_perm_I₅_kernel (w := w)
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ⁸, f x s) =
      (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hfactor :
        (fun x : ℝ⁸ ↦ f x s) =
          fun x : ℝ⁸ ↦
            ((-I) * φ₀'' (I * s) * ((s : ℂ) ^ (-4 : ℤ))) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      simp [f, permI5Kernel, permI5Phase, MagicFunction.a.IntegralEstimates.I₅.g]
      ac_rfl
    rw [congrArg (fun F : ℝ⁸ → ℂ => ∫ x, F x) hfactor, integral_const_mul,
      integral_phase_gaussian (w := w) (s := s) hs0,
      ← mul_assoc, mul_assoc (-I * φ₀'' (I * ↑s)) _ _,
      zpow_neg_four_mul_pow_four (s := s) hs0.ne', mul_one]
  have hmain :
      (∫ x : ℝ⁸,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)) =
        (-2 : ℂ) * ∫ s in Ici (1 : ℝ),
          (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hrew : (fun x : ℝ⁸ ↦
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          (-2 * ∫ s in Ici (1 : ℝ), MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s)) =
        fun x : ℝ⁸ ↦ (-2 : ℂ) * ∫ s in Ici (1 : ℝ), f x s := by
      funext x
      rw [show (∫ s in Ici (1 : ℝ), f x s) =
            ∫ s in Ici (1 : ℝ), cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              MagicFunction.a.IntegralEstimates.I₅.g (‖x‖ ^ 2) s
          from integral_congr_ae <| .of_forall fun _ ↦ by simp [f, permI5Kernel, permI5Phase],
        MeasureTheory.integral_const_mul (μ := μs)]
      ring
    rw [congrArg (fun F : ℝ⁸ → ℂ => ∫ x, F x) hrew, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ⁸)) (ν := μs) (f := f) hint]
    congr 1
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s hs ↦ ?_)
    simpa [f] using hinner s hs
  rw [hmain, show ((-2 : ℂ) * ∫ s in Ici (1 : ℝ),
            (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) =
          2 * ∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s) by
    rw [show ((-2 : ℂ) * ∫ s in Ici (1 : ℝ),
              (-I) * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) =
        (-2 : ℂ) * -(∫ s in Ici (1 : ℝ), I * φ₀'' (I * s) * cexp (-π * (‖w‖ ^ 2) * s)) by
      congr 1
      rw [← MeasureTheory.integral_neg]
      exact integral_congr_ae <| .of_forall fun _ ↦ by ring]
    ring]
  simp only [neg_mul, mul_comm, mul_neg, mul_assoc,
    MagicFunction.a.RadialFunctions.I₆'_eq, ofReal_pow]

end PermI5
end Integral_Permutations

section Integral_Permutations

/-- For even Schwartz `f`, applying the Fourier transform twice gives back `f`. -/
public lemma radial_inversion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : 𝓢(V, E)) (hf : Function.Even f) :
    FourierTransform.fourierCLE ℂ (SchwartzMap V E)
        (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f) = f := by
  ext x
  simpa [hf x, Real.fourierInv_eq_fourier_neg, neg_neg] using congrFun
    (f.continuous.fourierInv_fourier_eq f.integrable
      (by simpa using (FourierTransform.fourierCLE ℂ (SchwartzMap V E) f).integrable)) (-x)

lemma φ₀''_inv_add_one_mul_sq' (w : ℂ) (hw : 0 < w.im) :
    φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 *
        (((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹) =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
  have hw0 : w ≠ 0 := fun h => absurd (show w.im = 0 by simp [h]) hw.ne'
  have hw' : 0 < (w - 1).im := by simpa using hw
  have hw1 : w - 1 ≠ 0 := fun h => absurd (show (w - 1).im = 0 by simp [h]) hw'.ne'
  have hzpos : 0 < (-1 / (w - 1)).im := by
    simpa [div_eq_mul_inv, sub_eq_add_neg, Complex.inv_im] using
      div_pos hw' (Complex.normSq_pos.2 hw1)
  have hbase : φ₀'' (-1 / ((-1 / w) + 1)) * ((-1 / w) + 1) ^ 2 * w ^ 2 =
      φ₀'' (-1 / (w - 1)) * (w - 1) ^ 2 := by
    rw [mul_assoc, show ((-1 / w + 1) ^ 2) * w ^ 2 = (w - 1) ^ 2 by field_simp [hw0]; ring,
      show (-1 / ((-1 / w) + 1) : ℂ) = (-1 / (w - 1)) - 1 by grind only,
      show φ₀'' ((-1 / (w - 1)) - 1) = φ₀'' (-1 / (w - 1)) by
        simpa using (MagicFunction.a.SpecialValues.φ₀''_add_one
          (z := -1 / (w - 1) - 1) (by simpa using hzpos)).symm]
  simpa [show ((Complex.I : ℂ) / (-1 / w)) ^ (4 : ℕ) * (w ^ (2 : ℕ))⁻¹ = w ^ (2 : ℕ) by
    field_simp; simp [Complex.I_pow_four]] using hbase

section CurveIntegral
open scoped Interval
open Complex MagicFunction.a.ComplexIntegrands SpherePacking.Contour
open MagicFunction.a.RealIntegrands (Φ₁_def Φ₂_def Φ₃_def Φ₄_def)

private lemma uIcc_aux {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht

/-- Rewrite `I₁'` as a curve integral of `Φ₁'` along the segment `-1 → -1 + i`. -/
public lemma I₁'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) (-1 + Complex.I), scalarOneForm (Φ₁' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' r)) (-1 : ℂ) (-1 + Complex.I)]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [Φ₁_def, scalarOneForm_apply,
      (lineMap_z₁line t).trans (z₁'_eq_z₁line t (uIcc_aux ht)).symm]

/-- Rewrite `I₂'` as a curve integral of `Φ₁'` along the segment `-1 + i → i`. -/
public lemma I₂'_eq_curveIntegral_segment (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Φ₁' r) z) := by
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' r)) ((-1 : ℂ) + Complex.I) Complex.I]
  exact intervalIntegral.integral_congr fun t ht => by
    simp [Φ₂_def, scalarOneForm_apply,
      (lineMap_z₂line t).trans (z₂'_eq_z₂line t (uIcc_aux ht)).symm, Φ₂']

/-- `I₃' + I₄'` as a sum of curve integrals of `Φ₃'` along `1 → 1 + i` and `1 + i → i`. -/
public lemma I₃'_add_I₄'_eq_curveIntegral_segments (r : ℝ) :
    MagicFunction.a.RealIntegrals.I₃' r + MagicFunction.a.RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm (Φ₃' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm (Φ₃' r) z := by
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₃' r)) (1 : ℂ) ((1 : ℂ) + Complex.I),
    curveIntegral_segment (ω := scalarOneForm (Φ₃' r)) ((1 : ℂ) + Complex.I) Complex.I]
  refine congr_arg₂ _ (intervalIntegral.integral_congr fun t ht => ?_)
    (intervalIntegral.integral_congr fun t ht => ?_)
  · simp [Φ₃_def, scalarOneForm_apply, lineMap_z₃_eq_z₃' (t := t) (uIcc_aux ht)]
  · simp [Φ₄_def, scalarOneForm_apply, lineMap_z₄_eq_z₄' (t := t) (uIcc_aux ht), Φ₄']

/-- If `z` lies in the upper half-plane, then so does `-1 / z` (in terms of imaginary part). -/
public lemma neg_one_div_im_pos (z : ℂ) (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h => absurd (by simp [h] : z.im = 0) hz.ne'
  simpa [div_eq_mul_inv, Complex.inv_im] using div_pos hz (Complex.normSq_pos.2 hz0)

/-- The Fourier-side integrand corresponding to `Φ₁'`, including the Mobius inversion Jacobian. -/
@[expose] public def Φ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 *
    (((Complex.I : ℂ) / z) ^ (4 : ℕ)) *
      cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * (-1 / z))

/-- Modular identity relating `Φ₁_fourier` to `Φ₃'` via `mobiusInv` and its derivative. -/
public lemma Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃' (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z = (deriv SpherePacking.mobiusInv z) * Φ₃' r (SpherePacking.mobiusInv z) := by
  have hz0 : z ≠ 0 := fun h => absurd (show z.im = 0 by simp [h]) hz.ne'
  have hz2 : z ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hz0
  have hφ := φ₀''_inv_add_one_mul_sq' (w := -1 / z) (neg_one_div_im_pos z hz)
  have hrew : (-1 / (-1 / z) : ℂ) = z := by field_simp
  have h₁ : Φ₁_fourier r z = (1 / z ^ (2 : ℕ)) * Φ₃' r (-1 / z) := by
    simp [Φ₁_fourier, Φ₃',
      show φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * (((Complex.I : ℂ) / z) ^ (4 : ℕ)) =
        (1 / z ^ (2 : ℕ)) * (φ₀'' (-1 / ((-1 / z) - 1)) * ((-1 / z) - 1) ^ 2) from by grind only,
      mul_assoc, mul_left_comm, mul_comm]
  simpa [SpherePacking.mobiusInv, SpherePacking.deriv_mobiusInv (z := z), div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm] using h₁

end CurveIntegral

end Integral_Permutations

end
end MagicFunction.a.Fourier

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

open MeasureTheory Set Complex Real SpherePacking.Integration SpherePacking.Contour
open scoped Interval

/-! ## Kernels and measurability (merged from `PermI12FourierIntegrableI1`) -/

/-- The kernel used to rewrite `𝓕 I₁` as an integral over `x` and the segment parameter `t`. -/
@[expose] public def permI1Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
    ((I : ℂ) * MagicFunction.a.ComplexIntegrands.Φ₁' (‖p.1‖ ^ 2) (z₁line p.2))

/-- The kernel used to rewrite `𝓕 I₂` as an integral over `x` and the segment parameter `t`. -/
@[expose] public def permI2Kernel (w : EuclideanSpace ℝ (Fin 8)) :
    (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
    MagicFunction.a.ComplexIntegrands.Φ₁' (‖p.1‖ ^ 2) (z₂line p.2)

/-- Continuity of `(x, t) ↦ Φ₁'(‖x‖², z t)` at points where `(z p.2 + 1).im > 0`. -/
private lemma continuousAt_Φ₁'_comp {z : ℝ → ℂ} (hz : Continuous z)
    {p : (EuclideanSpace ℝ (Fin 8)) × ℝ} (hpos : 0 < (z p.2 + 1).im) :
    ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
      MagicFunction.a.ComplexIntegrands.Φ₁' (‖q.1‖ ^ 2) (z q.2)) p := by
  have hφterm : ContinuousAt
      (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => φ₀'' ((-1 : ℂ) / (z q.2 + 1))) p := by
    have hcont : ContinuousAt (fun s : ℝ => φ₀'' ((-1 : ℂ) / (z s + 1))) p.2 := by
      have hden : z p.2 + 1 ≠ 0 := fun h => hpos.ne' (by simp [h])
      have hmem : (-1 : ℂ) / (z p.2 + 1) ∈ UpperHalfPlane.upperHalfPlaneSet := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using neg_one_div_im_pos (z p.2 + 1) hpos
      have hφ : ContinuousAt (fun w : ℂ => φ₀'' w) ((-1 : ℂ) / (z p.2 + 1)) :=
        (MagicFunction.a.ComplexIntegrands.φ₀''_holo.differentiableAt
          (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem)).continuousAt
      exact ContinuousAt.comp (f := fun s : ℝ => (-1 : ℂ) / (z s + 1)) hφ
        (continuousAt_const.div ((hz.continuousAt).add continuousAt_const) (by simpa using hden))
    simpa [Function.comp] using hcont.comp continuousAt_snd
  have hz_pt : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => z q.2) p :=
    (hz.continuousAt).comp continuousAt_snd
  have hpow : ContinuousAt
      (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ => (z q.2 + 1) ^ (2 : ℕ)) p :=
    (hz_pt.add continuousAt_const).pow 2
  have hexp : ContinuousAt
      (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
        cexp ((π : ℂ) * I * ((‖q.1‖ ^ 2 : ℝ) : ℂ) * z q.2)) p :=
    (((continuousAt_const.mul continuousAt_const).mul (by fun_prop)).mul hz_pt).cexp
  dsimp [MagicFunction.a.ComplexIntegrands.Φ₁']
  exact (hφterm.mul hpow).mul hexp

/-- Measurability for the restricted product measure via continuity on `univ ×ˢ Ioc 0 1`. -/
private lemma aestronglyMeasurable_of_continuousOn_univ_prod_Ioc01
    {f : (EuclideanSpace ℝ (Fin 8)) × ℝ → ℂ}
    (hcont : ContinuousOn f (univ ×ˢ Ioc (0 : ℝ) 1)) :
    AEStronglyMeasurable f ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) := by
  have hμ : ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod μIoc01) =
      (((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (volume : Measure ℝ)).restrict
        (univ ×ˢ Ioc (0 : ℝ) 1)) := by
    simpa using prod_muIoc01_eq_restrict (μ := (volume : Measure (EuclideanSpace ℝ (Fin 8))))
  simpa [hμ] using hcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioc)

/-- Measurability of `permI1Kernel` with respect to the product measure `volume × μIoc01`. -/
public lemma permI1Kernel_measurable (w : EuclideanSpace ℝ (Fin 8)) :
    AEStronglyMeasurable (permI1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (μIoc01)) := by
  refine aestronglyMeasurable_of_continuousOn_univ_prod_Ioc01 fun p hp => ?_
  have hpos : 0 < (z₁line p.2 + 1).im := by simpa using ((Set.mem_prod.mp hp).2).1
  have hphase : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
      cexp (↑(-2 * (π * ⟪q.1, w⟫)) * I)) p := by fun_prop
  exact (hphase.mul (continuousAt_const.mul
    (continuousAt_Φ₁'_comp continuous_z₁line hpos))).continuousWithinAt

/-- Measurability of `permI2Kernel` with respect to the product measure `volume × μIoc01`. -/
public lemma permI2Kernel_measurable (w : EuclideanSpace ℝ (Fin 8)) :
    AEStronglyMeasurable (permI2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 8))).prod (μIoc01)) := by
  refine aestronglyMeasurable_of_continuousOn_univ_prod_Ioc01 fun p _ => ?_
  have hphase : ContinuousAt (fun q : (EuclideanSpace ℝ (Fin 8)) × ℝ =>
      cexp (↑(-2 * (π * ⟪q.1, w⟫)) * I)) p := by fun_prop
  exact (hphase.mul (continuousAt_Φ₁'_comp continuous_z₂line (by simp))).continuousWithinAt

end

end MagicFunction.a.Fourier

namespace MagicFunction.a.Fourier

noncomputable section

open scoped RealInnerProductSpace
open scoped FourierTransform Topology
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter

section Integral_Permutations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section PermI12Fourier_Integrable

open MeasureTheory Set Complex Real
open SpherePacking.ForMathlib SpherePacking.Contour SpherePacking.Integration
open MagicFunction.a.ComplexIntegrands

/-- Closed form for the `ℝ⁸` Gaussian integral used in the kernel bounds. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ⁸, rexp (-Real.pi * t * (‖x‖ ^ 2))) = (1 / t) ^ (4 : ℕ) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    integral_gaussian_rexp (s := (1 / t)) (by positivity)

/-- For almost every `t ∈ Ioc 0 1`, the slice `x ↦ permI2Kernel w (x, t)` is integrable. -/
public lemma ae_integrable_permI2Kernel_slice (w : ℝ⁸) :
    (∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ⁸ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ⁸)) :=
  (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t _ => by
    have hz : 0 < (z₂line t).im := by simp
    let phase : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)
    let g : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ Φ₁' (‖x‖ ^ 2) (z₂line t)
    have hg : Integrable g (volume : Measure ℝ⁸) := by
      have hc : Integrable (fun x : ℝ⁸ ↦
          (φ₀'' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ 2) *
            cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₂line t)) (volume : Measure ℝ⁸) :=
        (integrable_gaussian_cexp_pi_mul_I_mul (z := z₂line t) hz).const_mul _
      simpa [g, Φ₁'] using hc
    have hprod : Integrable (fun x : ℝ⁸ ↦ phase x * g x) (volume : Measure ℝ⁸) :=
      hg.bdd_mul (c := (1 : ℝ))
        (by simpa [phase] using aestronglyMeasurable_phase (V := ℝ⁸) (w := w))
        (by simpa [phase] using ae_norm_phase_le_one (V := ℝ⁸) (w := w))
    simpa [phase, g, permI2Kernel, permI5Phase, mul_assoc] using hprod

lemma integral_norm_permI1Kernel_bound (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) ≤ ‖φ₀'' ((I : ℂ) / t)‖ * (1 / t ^ 2) := by
  have ht0 : 0 < t := ht.1
  have harg : (-1 / (z₁line t + 1) : ℂ) = (I : ℂ) / t := by
    simpa [z₁line_add_one] using show (-1 / ((I : ℂ) * (t : ℂ)) : ℂ) = (I : ℂ) / t by
      field_simp [ht0.ne']; simp [Complex.I_sq]
  have hexp (x : ℝ⁸) : ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ =
      rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
    rw [show ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ =
        rexp (-Real.pi * (‖x‖ ^ 2) * t) from by
      simpa [z₁line_im, mul_assoc, mul_left_comm, mul_comm] using
        norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)]; ring_nf
  have hnorm (x : ℝ⁸) :
      ‖permI1Kernel w (x, t)‖ =
        ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := calc
    ‖permI1Kernel w (x, t)‖
        = ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ *
            ‖(I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by simp [permI1Kernel, mul_assoc]
      _ = ‖Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by simp [show ‖cexp (-(2 * (↑π * ↑⟪x, w⟫) * I))‖ = (1 : ℝ)
            from by simpa [mul_assoc, mul_left_comm, mul_comm] using
              norm_phase_eq_one (w := w) (x := x)]
      _ = ‖φ₀'' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ 2‖ *
            ‖cexp (Real.pi * I * (‖x‖ ^ 2) * (z₁line t : ℂ))‖ := by simp [Φ₁', mul_assoc]
      _ = ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) := by
            rw [harg, show ‖(z₁line t + 1) ^ 2‖ = t ^ 2 by simp, hexp x]
  refine le_of_eq ?_
  rw [show (fun x : ℝ⁸ => ‖permI1Kernel w (x, t)‖) =
        fun x : ℝ⁸ => ‖φ₀'' ((I : ℂ) / t)‖ * t ^ 2 * rexp (-(Real.pi * (t * (‖x‖ ^ 2)))) from
      funext hnorm, integral_const_mul,
    show (∫ x : ℝ⁸, rexp (-(Real.pi * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (4 : ℕ) from by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        integral_rexp_neg_pi_mul_sq_norm (t := t) ht0]
  field_simp

lemma integrable_integral_norm_permI1Kernel (w : ℝ⁸) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ⁸, ‖permI1Kernel w (x, t)‖) μIoc01 := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hmajor :
      Integrable (fun t : ℝ ↦ (C₀ : ℝ) * (1 / t ^ 2) * rexp (-(2 * π) / t)) μIoc01 := by
    simpa [μIoc01, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      ((show IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * rexp (-(2 * π) / t)) (Ioc (0 : ℝ) 1) volume by
        simpa [div_eq_mul_inv] using
          integrableOn_one_div_sq_mul_exp_neg_div (c := (2 * π)) (by positivity)).const_mul C₀)
  refine Integrable.mono' hmajor (by
    simpa using ((permI1Kernel_measurable w).norm.prod_swap.integral_prod_right'
      (μ := μIoc01) (ν := (volume : Measure ℝ⁸)))) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have hzpos : 0 < ((I : ℂ) / t).im := by
    simpa [show ((I : ℂ) / t).im = t⁻¹ by norm_num] using inv_pos.2 ht0
  let z : UpperHalfPlane := ⟨(I : ℂ) / t, hzpos⟩
  have hz_im : z.im = t⁻¹ := by simp [z, UpperHalfPlane.im]
  have hφ_bound : ‖φ₀'' ((I : ℂ) / t)‖ ≤ (C₀ : ℝ) * rexp (-(2 * π) / t) := by
    simpa [show φ₀ z = φ₀'' ((I : ℂ) / t) from by
        simpa [z] using (φ₀''_def (z := (I : ℂ) / t) hzpos).symm,
      show rexp (-(2 * π * z.im)) = rexp (-(2 * π) / t) by
        rw [hz_im]; congr 1; simp [div_eq_mul_inv, mul_assoc]] using
      hC₀ z (by rw [hz_im]
                exact lt_of_lt_of_le (by norm_num) (one_le_inv_iff₀.2 ⟨ht0, ht.2⟩))
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (integral_norm_permI1Kernel_bound (w := w) (t := t) ht).trans
      (mul_le_mul_of_nonneg_right hφ_bound (by positivity))

/-- Integrability of `permI1Kernel` on the product measure `volume × μIoc01`. -/
public lemma integrable_perm_I₁_kernel (w : ℝ⁸) :
    Integrable (permI1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) :=
  (integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01) (permI1Kernel_measurable w)).2
    ⟨(ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => by
      have hz : 0 < (z₁line t).im := by simpa using z₁line_im_pos_Ioc (t := t) ht
      let phase : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ cexp (↑(-2 * (π * ⟪x, w⟫)) * I)
      let g : ℝ⁸ → ℂ := fun x : ℝ⁸ ↦ (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)
      have hg : Integrable g (volume : Measure ℝ⁸) := by
        have hc : Integrable (fun x : ℝ⁸ ↦
            ((I : ℂ) * (φ₀'' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ 2)) *
              cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₁line t)) (volume : Measure ℝ⁸) :=
          (integrable_gaussian_cexp_pi_mul_I_mul (z := z₁line t) hz).const_mul _
        simpa [g, Φ₁', mul_assoc] using hc
      have hprod : Integrable (fun x : ℝ⁸ ↦ phase x * g x) (volume : Measure ℝ⁸) :=
        hg.bdd_mul (c := (1 : ℝ))
          (by simpa [phase] using aestronglyMeasurable_phase (V := ℝ⁸) (w := w))
          (by simpa [phase] using ae_norm_phase_le_one (V := ℝ⁸) (w := w))
      simpa [phase, g, permI1Kernel, permI5Phase, mul_assoc] using hprod,
      integrable_integral_norm_permI1Kernel w⟩

end PermI12Fourier_Integrable

open MeasureTheory Set Complex Real SpherePacking.Integration SpherePacking.Contour
  SpherePacking.ForMathlib
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

end PermI12Fourier_Main
end Integral_Permutations
end
end MagicFunction.a.Fourier

namespace MagicFunction.a.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology Interval
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter
open Filter SpherePacking SpherePacking.ForMathlib MeasureTheory Set Complex Real

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- `Φ₃' r` tends to `0` as `z → 1` within `closure wedgeSet`. -/
public lemma tendsto_Φ₃'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (MagicFunction.a.ComplexIntegrands.Φ₃' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let expNorm : ℂ → ℝ := fun z ↦ ‖cexp (Real.pi * Complex.I * r * z)‖
  have hExp : ContinuousAt expNorm (1 : ℂ) := by fun_prop
  let M : ℝ := expNorm (1 : ℂ) + 1
  have hMpos : 0 < M := by positivity
  obtain ⟨δexp, hδexp_pos, hδexp⟩ := (Metric.continuousAt_iff.1 hExp) 1 (by norm_num)
  have hExpBound : ∀ {z : ℂ}, dist z (1 : ℂ) < δexp → expNorm z ≤ M := fun {z} hz ↦ by
    have habs : |expNorm z - expNorm (1 : ℂ)| < 1 := by simpa [Real.dist_eq] using hδexp hz
    simp only [M]
    linarith [le_abs_self (expNorm z - expNorm (1 : ℂ))]
  refine (Metric.tendsto_nhdsWithin_nhds).2 ?_
  intro ε hε
  have hub : Tendsto (fun z : ℂ => (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (𝓝 (1 : ℂ))
      (𝓝 (0 : ℝ)) := by
    simpa using (by fun_prop : Continuous (fun z : ℂ => (C₀ : ℝ) *
      (dist z (1 : ℂ)) ^ (2 : ℕ) * M)).tendsto (1 : ℂ)
  obtain ⟨δpow, hδpow_pos, hδpow⟩ :=
    Metric.mem_nhds_iff.1 <| Metric.tendsto_nhds.1 hub ε hε
  let δ : ℝ := min δexp (min 1 δpow)
  have hδ_pos : 0 < δ := lt_min hδexp_pos (lt_min (by norm_num) hδpow_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro z hzcl hdistz
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simpa [MagicFunction.a.ComplexIntegrands.Φ₃'] using hε
  have hdist_exp : dist z (1 : ℂ) < δexp := hdistz.trans_le (min_le_left _ _)
  have hdist_lt1 : dist z (1 : ℂ) < 1 :=
    hdistz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdist_pow : dist z (1 : ℂ) < δpow :=
    hdistz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hexpZ : expNorm z ≤ M := hExpBound hdist_exp
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1
  have habs_re : |z.re - 1| ≤ z.im :=
    SpherePacking.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
  have hnormSq_pos : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.2 (sub_ne_zero.mpr hz1)
  have hz_im_lt1 : z.im < 1 :=
    (by simpa [abs_of_nonneg hz_im_pos.le] using Complex.abs_im_le_norm (z - 1) :
        z.im ≤ ‖z - 1‖).trans_lt (by simpa [dist_eq_norm] using hdist_lt1)
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs_re 2
    have : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    linarith
  have hw_half : (1 / 2 : ℝ) < (-1 / (z - 1)).im := by
    have him : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
      simp [div_eq_mul_inv, Complex.inv_im, sub_eq_add_neg]
    rw [him, lt_div_iff₀ hnormSq_pos]
    nlinarith [hnormSq_le, hz_im_pos, hz_im_lt1]
  have hw_pos : 0 < (-1 / (z - 1)).im := lt_trans (by norm_num) hw_half
  have hφ₀'' : ‖φ₀'' (-1 / (z - 1))‖ ≤ (C₀ : ℝ) := by
    let wH : UpperHalfPlane := ⟨-1 / (z - 1), hw_pos⟩
    have hφ₀_eq : φ₀ wH = φ₀'' (-1 / (z - 1)) := by
      simpa [wH] using (φ₀''_def (z := (-1 / (z - 1))) hw_pos).symm
    have hexp : Real.exp (-2 * Real.pi * wH.im) ≤ 1 := Real.exp_le_one_iff.2 <| by
      have : 0 ≤ Real.pi * wH.im := mul_nonneg Real.pi_pos.le wH.2.le; linarith
    calc ‖φ₀'' (-1 / (z - 1))‖
        = ‖φ₀ wH‖ := by rw [hφ₀_eq]
      _ ≤ (C₀ : ℝ) * Real.exp (-2 * Real.pi * wH.im) := hC₀ wH hw_half
      _ ≤ (C₀ : ℝ) * 1 := by gcongr
      _ = (C₀ : ℝ) := mul_one _
  have hmain :
      ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖ ≤ (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M := by
    have heq : ‖MagicFunction.a.ComplexIntegrands.Φ₃' r z‖
        = ‖φ₀'' (-1 / (z - 1))‖ * (dist z (1 : ℂ)) ^ (2 : ℕ) * expNorm z := by
      simp [MagicFunction.a.ComplexIntegrands.Φ₃', expNorm, dist_eq_norm, mul_left_comm, mul_comm]
    rw [heq]; gcongr
  have hpow_small : (C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M < ε := by
    have h : dist ((C₀ : ℝ) * (dist z (1 : ℂ)) ^ (2 : ℕ) * M) (0 : ℝ) < ε :=
      hδpow (show z ∈ Metric.ball (1 : ℂ) δpow from hdist_pow)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
  simpa [dist_eq_norm] using hmain.trans_lt hpow_small

section Integral_Permutations

/-- The `1`-form built from `Φ₃'` is differentiable on `wedgeSet` with continuous extension. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet :=
  ForMathlib.diffContOnCl_scalarOneForm (s := wedgeSet) <| by
    refine ⟨((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).differentiableOn
        (by simp)).mono wedgeSet_subset_upperHalfPlaneSet, fun z hz => ?_⟩
    by_cases h1 : z = (1 : ℂ)
    · subst h1
      have hval : MagicFunction.a.ComplexIntegrands.Φ₃' r (1 : ℂ) = 0 := by
        simp [MagicFunction.a.ComplexIntegrands.Φ₃']
      simpa [ContinuousWithinAt, hval] using tendsto_Φ₃'_one_within_closure_wedgeSet (r := r)
    · have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hz h1
      exact ((MagicFunction.a.ComplexIntegrands.Φ₃'_contDiffOn (r := r)).continuousOn.continuousAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzU)).continuousWithinAt

/-- Symmetry of the derivative of `scalarOneForm (Φ₃' r)` on `wedgeSet`.

This is the key hypothesis needed to apply the Poincare lemma. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r))
          wedgeSet x v u := by
  intro x hx _ _ _ _
  have hxU : x ∈ UpperHalfPlane.upperHalfPlaneSet := wedgeSet_subset_upperHalfPlaneSet hx
  have hfdiff : DifferentiableAt ℂ (MagicFunction.a.ComplexIntegrands.Φ₃' r) x :=
    (MagicFunction.a.ComplexIntegrands.Φ₃'_holo (r := r)).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hxU)
  exact SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen
    (s := wedgeSet) isOpen_wedgeSet hx (hfdiff := hfdiff)

open MeasureTheory Set Complex Real

/-- The contour permutation identity underlying the Fourier invariance of the `I₁`/`I₂` part. -/
private lemma perm_I12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Φ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Φ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z :=
  SpherePacking.perm_I12_contour_mobiusInv_wedgeSet
    (Ψ₁_fourier := Φ₁_fourier)
    (Ψ₁' := MagicFunction.a.ComplexIntegrands.Φ₃')
    (Ψ₁_fourier_eq_deriv_mul := Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃')
    (closed_ω_wedgeSet := fun r =>
      ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
    (r := r)

theorem perm_I₁_I₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) =
      (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) := by
  ext w
  simp only [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, add_apply, I₃_apply,
    I₄_apply, fourier_coe]
  rw [fourier_I₁_eq_curveIntegral (w := w), fourier_I₂_eq_curveIntegral (w := w),
    I₃'_add_I₄'_eq_curveIntegral_segments (r := ‖w‖ ^ 2)]
  simpa using perm_I12_contour (r := ‖w‖ ^ 2)

theorem perm_I₃_I₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) =
      (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) := by
  rw [← perm_I₁_I₂]
  simpa using radial_inversion (I₁ + I₂) fun _ => by simp [I₁, I₂]

theorem perm_I₆ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₆ = I₅ := by
  simpa [← perm_I₅] using radial_inversion I₅ fun _ => by
    simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]

end Integral_Permutations

section Eigenfunction

/-- The magic function `a` is invariant under the Fourier transform. -/
public theorem eig_a : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) a = a := by
  rw [show a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ from rfl,
    show I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ by ac_rfl,
    map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_I₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end
end MagicFunction.a.Fourier

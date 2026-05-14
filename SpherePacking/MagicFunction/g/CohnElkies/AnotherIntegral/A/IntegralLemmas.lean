module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.MagicFunction.b.Schwartz.Basic
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.Tactic.NormNumI
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Integral.Gamma
public import SpherePacking.ModularForms.Delta
public import SpherePacking.ModularForms.PhiTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import SpherePacking.MagicFunction.a.Schwartz.Basic
import SpherePacking.Integration.Measure
public import SpherePacking.ModularForms.DimensionFormulas
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Complex.Periodic
import SpherePacking.ForMathlib.ModularFormsHelpers
import SpherePacking.ModularForms.PhiTransformLemmas

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Laplace-type integrals and analytic continuation for `AnotherIntegral.A`

Explicit evaluations and integrability facts for basic Laplace-type integrals on `t > 0`,
in the complex-valued form used by the "another integral" representation of `a'`. Also includes
the analytic-continuation step that extends the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`.

This file also provides the generic analytic-continuation wrapper used by both the `a'` and `b'`
representations: the punctured right half-plane `ACDomain = {u : ℂ | 0 < re u} \ {2}` and the
theorem `analytic_continuation_of_gt2`.

Also contains the Laplace representation for `a'` (merged from `LaplaceA/LaplaceRepresentation`):
the tail-deformation lemma `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail` and the main theorem
`aRadial_eq_laplace_phi0_main`.

Includes the complex analytic extension `aPrimeC` of `a'` (merged from `APrimeExtension`):
complexified integrals `I₁'C` ... `I₆'C`, their sum `aPrimeC`, and analyticity on the right
half-plane.

## Main definitions
* `ACDomain`, `aAnotherBase`, `aAnotherIntegrandC`, `aAnotherIntegralC`, `aAnotherRHS`
* `rightHalfPlane`, `aPrimeC`

## Main statements
* `analytic_continuation_of_gt2`
* `aRadial_eq_another_integral_analytic_continuation_of_gt2`
* `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail`, `aRadial_eq_laplace_phi0_main`
* `aPrimeC_ofReal`, `aPrimeC_analyticOnNhd`
-/

section MagicG

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.SpecialValues
  MagicFunction.b.SpecialValues

noncomputable section

/-- The Magic Function, `g`. -/
@[expose] public def g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a - (I / (240 * π)) • b

/-- Normalization of `g` at the origin. -/
public theorem g_zero : g 0 = 1 := by
  simp [g, a_zero, b_zero, sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1

/-- Normalization of the Fourier transform of `g` at the origin. -/
public theorem fourier_g_zero : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) g 0 = 1 := by
  simp only [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
    sub_apply, smul_apply, smul_eq_mul]
  simp [a_zero, b_zero, sub_eq_add_neg, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1

end

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap

open Real Complex SchwartzMap
open MagicFunction.FourierEigenfunctions

noncomputable section

/-- Radial profile of `g` in the variable `‖x‖^2`. -/
@[expose] public def gRadial : 𝓢(ℝ, ℂ) :=
  ((π * I) / 8640) • a' - (I / (240 * π)) • b'

/-- The function `g` is radial, with profile `gRadial` in the variable `‖x‖ ^ 2`. -/
public theorem g_apply_eq_gRadial_norm_sq (x : ℝ⁸) : g x = gRadial (‖x‖ ^ 2) := by
  simp [g, gRadial, a, b, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]

/--
Auxiliary function `A(t)` from the blueprint, defined as the real part of
`-t^2 * φ₀(i/t) - (36/π^2) * ψI(i t)`.

We only use `A(t)` for `t > 0`, but define it on all `ℝ`.
-/
@[expose] public def A (t : ℝ) : ℝ :=
  (-(t ^ 2)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
    (36 / (π ^ (2 : ℕ)) : ℝ) * (ψI' ((Complex.I : ℂ) * (t : ℂ))).re

/--
Auxiliary function `B(t)` from the blueprint, defined as the real part of
`-t^2 * φ₀(i/t) + (36/π^2) * ψI(i t)`.

We only use `B(t)` for `t > 0`, but define it on all `ℝ`.
-/
@[expose] public def B (t : ℝ) : ℝ :=
  (-(t ^ 2)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re +
    (36 / (π ^ (2 : ℕ)) : ℝ) * (ψI' ((Complex.I : ℂ) * (t : ℂ))).re

end

end MagicFunction.g.CohnElkies

end MagicG

namespace MagicFunction.g.CohnElkies

open scoped BigOperators
open MeasureTheory Real

private lemma gamma_two : Real.Gamma (2 : ℝ) = 1 := by simp

lemma integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-a * t)) = 1 / a := by
  simpa [Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg_one, one_div] using
    (integral_exp_neg_mul_rpow (p := (1 : ℝ)) (b := a) (hp := by norm_num) (hb := ha))

/-- Evaluate `∫ exp(-π * u * t)` over `t ∈ (0, ∞)` (for `0 < u`). -/
public lemma integral_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-π * u * t)) = 1 / (π * u) := by
  simpa [mul_assoc] using (integral_exp_neg_mul_Ioi (a := π * u) (by positivity [Real.pi_pos, hu]))

/-- Evaluate `∫ t * exp(-π * u * t)` over `t ∈ (0, ∞)` (for `0 < u`). -/
public lemma integral_mul_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-π * u * t)) = 1 / (π * u) ^ (2 : ℕ) := by
  have ha : 0 < π * u := by positivity [Real.pi_pos, hu]
  simpa [mul_assoc, Real.rpow_one, one_add_one_eq_two, gamma_two, Real.rpow_neg ha.le, div_one]
    using (integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ)) (b := π * u)
      (hp := by norm_num) (hq := by norm_num) (hb := ha))

/-- Algebraic identity: `exp(2πt) · exp(-πut) = exp(-(π(u-2))t)`. -/
public lemma exp_two_pi_mul_mul_exp_neg_pi_mul (u t : ℝ) :
    Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-(π * (u - 2)) * t) := by
  rw [← Real.exp_add]; congr 1; ring

/-- Evaluate `∫ exp(2π t) * exp(-π u t)` over `t ∈ (0, ∞)` (for `2 < u`). -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (2 * π * t) * Real.exp (-π * u * t)) =
      1 / (π * (u - 2)) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (g := fun t => Real.exp (-(π * (u - 2)) * t))
    (fun t _ => by simpa using exp_two_pi_mul_mul_exp_neg_pi_mul u t)]
  simpa [mul_assoc] using
    (integral_exp_neg_mul_Ioi (a := π * (u - 2)) (by positivity [Real.pi_pos, sub_pos.2 hu]))

namespace Trig

/-- Rewrite `2 - exp(π u i) - exp(-π u i)` as `2 - 2 cos(π u)`. -/
public lemma two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I (u : ℝ) :
    (2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) =
      ((2 - 2 * Real.cos (π * u) : ℝ) : ℂ) := by
  set z : ℂ := ((π * u : ℝ) : ℂ)
  have hcos : Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) =
      (2 : ℂ) * Complex.cos z := by
    simpa [neg_mul] using (Complex.two_cos (x := z)).symm
  calc
    (2 : ℂ) - Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) =
        (2 : ℂ) - (Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))) := by
          simpa using sub_sub (2 : ℂ) (Complex.exp (z * Complex.I)) (Complex.exp (-(z * Complex.I)))
    _ = (2 : ℂ) - (2 : ℂ) * Complex.cos z := by simp [hcos]
    _ = ((2 - 2 * Real.cos (π * u) : ℝ) : ℂ) := by simp [z, sub_eq_add_neg]

/-- Rewrite `2 - 2 cos(π u)` as `4 sin(π u / 2)^2`. -/
public lemma two_sub_two_cos_eq_four_sin_sq (u : ℝ) :
    (2 - 2 * Real.cos (π * u) : ℝ) = 4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by
  have hsin : (Real.sin (π * u / 2)) ^ (2 : ℕ) = 1 / 2 - Real.cos (π * u) / 2 := by
    have : (2 : ℝ) * (π * u / 2) = π * u := by ring
    simpa [pow_two, this] using (Real.sin_sq_eq_half_sub (x := π * u / 2))
  calc
    (2 - 2 * Real.cos (π * u) : ℝ) = 4 * (1 / 2 - Real.cos (π * u) / 2) := by ring
    _ = 4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) := by simp [hsin]

end Trig

end MagicFunction.g.CohnElkies

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped UpperHalfPlane Real
open UpperHalfPlane Filter

/-- Exponential growth bound for `Δ⁻¹` for `im z` sufficiently large. -/
public lemma exists_inv_Delta_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖(Δ z)⁻¹‖ ≤ C * Real.exp (2 * π * z.im) := by
  obtain ⟨c, hcpos, hEvent⟩ := (Asymptotics.isBigO_iff'').1
    (by simpa using Delta_isTheta_rexp.2 :
      (fun τ : ℍ => Real.exp (-2 * π * τ.im)) =O[atImInfty] Delta)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 (by simpa using hEvent)
  refine ⟨c⁻¹, A, inv_pos.2 hcpos, fun z hz => ?_⟩
  calc
    ‖(Δ z)⁻¹‖ = ‖Δ z‖⁻¹ := by simp [norm_inv]
    _ ≤ (c * Real.exp (-2 * π * z.im))⁻¹ :=
          (inv_le_inv₀ (by simpa [norm_pos_iff] using Δ_ne_zero z)
            (mul_pos hcpos (Real.exp_pos _))).2 (by simpa [Delta_apply] using hA z hz)
    _ = c⁻¹ * Real.exp (2 * π * z.im) := by
          simp [mul_inv_rev, Real.exp_neg, mul_assoc, mul_comm]

end MagicFunction.g.CohnElkies.IntegralReps

namespace SpherePacking

/-- The open right half-plane `{u : ℂ | 0 < u.re}`. -/
@[expose] public def rightHalfPlane : Set ℂ := {u : ℂ | 0 < u.re}

/-- The right half-plane is an open subset of `ℂ`. -/
public lemma rightHalfPlane_isOpen : IsOpen rightHalfPlane := by
  simpa [rightHalfPlane] using (isOpen_Ioi.preimage Complex.continuous_re)

end SpherePacking

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter MagicFunction.FourierEigenfunctions
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrals
  MagicFunction.a.RealIntegrands MagicFunction.Parametrisations

/-! ## Laplace integrand and convergence (merged from `LaplaceA.Basic`) -/

noncomputable section LaplaceIntegrand

/-- The Laplace integrand appearing in the representation of the radial profile `a'`. -/
@[expose] public def aLaplaceIntegrand (u t : ℝ) : ℂ :=
  ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) * Real.exp (-π * u * t)

lemma continuousOn_phi0''_div_Ioi :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
  MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
    (continuousOn_const.div Complex.continuous_ofReal.continuousOn fun _ ht => mod_cast ht.ne')
    fun _ ht => by simp_all

/-- Integrability of `t^2 * exp(-a * t)` on a ray `Set.Ioi A` (for `0 < a`). -/
public lemma integrableOn_sq_mul_exp_neg (A a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) (Set.Ioi A) :=
  integrable_of_isBigO_exp_neg (a := A) (b := a / 2) (half_pos ha) (by fun_prop)
    (((isLittleO_pow_exp_pos_mul_atTop (k := 2) (half_pos ha)).isBigO.mul
      (Asymptotics.isBigO_refl _ _)).congr_right fun t => by rw [← Real.exp_add]; congr 1; ring)

/-- Convergence of the Laplace integral defining `a'` (integrability on `(0, ∞)` for `u > 2`). -/
public lemma aLaplaceIntegral_convergent {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hMeasIoi : AEStronglyMeasurable (fun t : ℝ => aLaplaceIntegrand u t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have ht2 : AEStronglyMeasurable (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((continuous_ofReal.comp (continuous_id.pow 2)).aestronglyMeasurable
          (μ := (volume : Measure ℝ))).mono_measure Measure.restrict_le_self
    simpa [aLaplaceIntegrand, mul_assoc] using
      (ht2.mul (continuousOn_phi0''_div_Ioi.aestronglyMeasurable measurableSet_Ioi)).mul
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-π * u * t) : ℂ))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
  have hsmall : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
    let C₀ : ℝ := MagicFunction.a.Schwartz.I1Decay.Cφ
    refine MeasureTheory.IntegrableOn.of_bound (by simp : (MeasureTheory.volume : Measure ℝ)
      (Set.Ioc (0 : ℝ) 1) < ⊤)
      (hMeasIoi.mono_measure <| Measure.restrict_mono_set (MeasureTheory.volume : Measure ℝ)
        fun t ht => ht.1) C₀ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have hC₀ : 0 ≤ C₀ := MagicFunction.a.Schwartz.I1Decay.Cφ_pos.le
    have hφ₀'' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ :=
      (show ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ C₀ * rexp (-2 * π * t⁻¹) by
        simpa [div_eq_mul_inv, Complex.ofReal_inv, C₀] using
          MagicFunction.a.Schwartz.I1Decay.norm_φ₀''_le (s := t⁻¹)
            (one_le_inv_iff₀.2 ⟨ht0, ht.2⟩)).trans <| by
        simpa using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, inv_nonneg.2 ht0.le])) hC₀
    have ht2_le : ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real] using
        pow_le_one₀ (n := 2) (abs_nonneg t) (by simpa [abs_of_pos ht0] using ht.2)
    have hexp_le : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
      rw [show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) by
        simpa [Complex.ofReal_exp] using Complex.norm_exp (-(π * u * t : ℂ))]
      exact Real.exp_le_one_iff.2
        (by linarith [mul_nonneg (mul_nonneg Real.pi_pos.le (lt_trans two_pos hu).le) ht0.le])
    calc ‖aLaplaceIntegrand u t‖
          ≤ ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ *
            ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ *
              ‖(Real.exp (-π * u * t) : ℂ)‖ := by simp [aLaplaceIntegrand, mul_assoc]
      _ ≤ 1 * C₀ * 1 := by gcongr
      _ = C₀ := by ring
  have htail : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) := by
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 E₂_isBoundedAtImInfty with ⟨B2, A2, hB2⟩
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 (ModularFormClass.bdd_at_infty E₄) with
      ⟨B4, A4, hB4⟩
    rcases (UpperHalfPlane.isBoundedAtImInfty_iff).1 (ModularFormClass.bdd_at_infty E₆) with
      ⟨B6, A6, hB6⟩
    obtain ⟨CΔ, AΔ, hCΔpos, hΔinv⟩ := exists_inv_Delta_bound_exp
    let A : ℝ := max (1 : ℝ) (max AΔ (max A2 (max A4 A6)))
    have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
    have hmid : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) :=
      (((show ContinuousOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) by
          simpa [aLaplaceIntegrand, mul_assoc] using
            (((by fun_prop : Continuous fun t : ℝ ↦ ((t ^ (2 : ℕ) : ℝ) : ℂ)
              ).continuousOn.mul continuousOn_phi0''_div_Ioi).mul
              (by fun_prop : Continuous fun t : ℝ ↦ (Real.exp (-π * u * t) : ℂ)).continuousOn)
        ).mono fun _ ht => lt_of_lt_of_le one_pos ht.1).integrableOn_Icc
        (μ := MeasureTheory.volume)).mono_set Set.Ioc_subset_Icc_self
    have hbig : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi A) := by
      let a : ℝ := π * (u - 2)
      have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
      let BA : ℝ := B2 * B4 + B6
      let C2 : ℝ := ‖(12 * Complex.I : ℂ) / (π : ℂ)‖
      let C4 : ℝ := ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖
      let Cφ : ℝ := (BA ^ (2 : ℕ) + C2 * (B4 * BA) + C4 * (B4 ^ (2 : ℕ))) * CΔ
      have hdomReal : Integrable (fun t : ℝ => Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)))
            (MeasureTheory.volume.restrict (Set.Ioi A)) :=
        (integrableOn_sq_mul_exp_neg A a ha).const_mul Cφ
      have hdom :
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi A)),
            ‖aLaplaceIntegrand u t‖ ≤ Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := hA1.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        let zH : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), by simpa using ht0⟩
        have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
        have htAim : A ≤ zH.im := hz_im ▸ ht.le
        have hAle : AΔ ≤ A ∧ A2 ≤ A ∧ A4 ≤ A ∧ A6 ≤ A := by dsimp [A]; simp
        have hE4 : ‖E₄ zH‖ ≤ B4 := hB4 zH (hAle.2.2.1.trans htAim)
        have hΔ : ‖(Δ zH)⁻¹‖ ≤ CΔ * Real.exp (2 * π * t) := by
          simpa [hz_im] using hΔinv zH (hAle.1.trans htAim)
        have hAterm : ‖E₂ zH * E₄ zH - E₆ zH‖ ≤ BA :=
          norm_sub_le_of_le (norm_mul_le_of_le (hB2 zH (hAle.2.1.trans htAim)) hE4)
            (hB6 zH (hAle.2.2.2.trans htAim))
        have hBA_nonneg : 0 ≤ BA := le_trans (norm_nonneg _) hAterm
        have hB4_nonneg : 0 ≤ B4 := le_trans (norm_nonneg _) hE4
        have hφ0 : ‖φ₀ zH‖ ≤ (BA ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
          rw [show ‖φ₀ zH‖ = ‖(E₂ zH * E₄ zH - E₆ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ by
            simp [φ₀, div_eq_mul_inv]]
          refine mul_le_mul ?_ hΔ (norm_nonneg _) (pow_nonneg hBA_nonneg _)
          simpa [norm_pow, pow_two] using mul_le_mul hAterm hAterm (norm_nonneg _) hBA_nonneg
        have hφ2 : ‖φ₂' zH‖ ≤ (B4 * BA) * (CΔ * Real.exp (2 * π * t)) := by
          rw [show ‖φ₂' zH‖ = (‖E₄ zH‖ * ‖E₂ zH * E₄ zH - E₆ zH‖) * ‖(Δ zH)⁻¹‖ by
            simp [φ₂', div_eq_mul_inv, mul_assoc]]
          exact mul_le_mul (mul_le_mul hE4 hAterm (norm_nonneg _) hB4_nonneg) hΔ
            (norm_nonneg _) (mul_nonneg hB4_nonneg hBA_nonneg)
        have hφ4 : ‖φ₄' zH‖ ≤ (B4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * t)) := by
          rw [show ‖φ₄' zH‖ = ‖(E₄ zH) ^ (2 : ℕ)‖ * ‖(Δ zH)⁻¹‖ by simp [φ₄', div_eq_mul_inv]]
          refine mul_le_mul ?_ hΔ (norm_nonneg _) (pow_nonneg hB4_nonneg _)
          simpa [norm_pow, pow_two] using mul_le_mul hE4 hE4 (norm_nonneg _) hB4_nonneg
        have hphiS : φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • zH) :=
          (congrArg φ₀'' ((ModularGroup.coe_S_smul (z := zH)).trans
            (by simp [zH, div_eq_mul_inv, mul_inv_rev, mul_comm])).symm).trans
            (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • zH))
        have hz_norm : ‖(zH : ℂ)‖ = t := by simp [zH, abs_of_pos ht0]
        have hz_inv : ‖(zH : ℂ)⁻¹‖ ≤ 1 := by
          simpa [norm_inv] using inv_le_one_of_one_le₀ (by simpa [hz_norm] using ht1)
        have hz2_inv : ‖((zH : ℂ) ^ (2 : ℕ))⁻¹‖ ≤ 1 := by
          simpa [norm_inv] using inv_le_one_of_one_le₀
            (by simpa [norm_pow, hz_norm] using (one_le_pow₀ ht1 : (1 : ℝ) ≤ t ^ (2 : ℕ)))
        have hcoeff2 : ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖ ≤ C2 :=
          calc ‖(12 * Complex.I : ℂ) / (π * (zH : ℂ))‖
                = ‖(12 * Complex.I : ℂ) / (π : ℂ)‖ * ‖(zH : ℂ)⁻¹‖ := by
                  simp [show (12 * Complex.I : ℂ) / (π * (zH : ℂ)) =
                    ((12 * Complex.I : ℂ) / (π : ℂ)) * (zH : ℂ)⁻¹ from by
                    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]]
            _ ≤ C2 * 1 := by gcongr
            _ = C2 := by simp
        have hcoeff4 : ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖ ≤ C4 :=
          calc ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ))‖
                = ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * ‖((zH : ℂ) ^ (2 : ℕ))⁻¹‖ := by
                  simp [show (36 : ℂ) / ((π : ℂ) ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) =
                    ((36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((zH : ℂ) ^ (2 : ℕ))⁻¹ from by
                    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_inv_rev]]
            _ ≤ C4 * 1 := by gcongr
            _ = C4 := by simp
        have hphi_bound : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ * Real.exp (2 * π * t) := by
          have htri : ‖φ₀ (ModularGroup.S • zH)‖ ≤
              ‖φ₀ zH‖ + ‖(12 * Complex.I) / (π * (zH : ℂ)) * φ₂' zH‖ +
                ‖36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH‖ := by
            rw [show φ₀ (ModularGroup.S • zH) = φ₀ zH - (12 * Complex.I) / (π * zH) * φ₂' zH
                - 36 / (π ^ (2 : ℕ) * (zH : ℂ) ^ (2 : ℕ)) * φ₄' zH by simpa using φ₀_S_transform zH]
            exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
          have h2 := norm_mul_le_of_le hcoeff2 hφ2
          have h4 := norm_mul_le_of_le hcoeff4 hφ4
          grind only
        have hExpRew : Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-a * t) := by
          simpa [a, mul_assoc, mul_left_comm, mul_comm] using
            exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t)
        calc ‖aLaplaceIntegrand u t‖
              ≤ ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ *
                ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ *
                  ‖(Real.exp (-π * u * t) : ℂ)‖ := by simp [aLaplaceIntegrand, mul_assoc]
          _ ≤ (t ^ (2 : ℕ)) * (Cφ * Real.exp (2 * π * t)) * Real.exp (-π * u * t) := by
                rw [show ‖((t ^ (2 : ℕ) : ℝ) : ℂ)‖ = t ^ (2 : ℕ) from by simp [Complex.norm_real],
                  show ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) from by
                    simp [Complex.ofReal_exp, Complex.norm_exp, mul_assoc]]
                gcongr
          _ = Cφ * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by rw [← hExpRew]; ring
      exact MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Set.Ioi A))
        hdomReal (hMeasIoi.mono_measure <| Measure.restrict_mono_set _
          fun _ ht => zero_lt_one.trans_le (hA1.trans ht.le)) hdom
    rw [← Set.Ioc_union_Ioi_eq_Ioi hA1]; exact hmid.union hbig
  rw [← Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]; exact hsmall.union htail

end LaplaceIntegrand

/-! ## Finite-difference identities (merged from `LaplaceA.FiniteDifference`) -/

/-- Shift `Φ₁'` by `-1` and rewrite it in terms of `Φ₅'` at the point `it`. -/
public lemma Φ₁'_shift_left (u t : ℝ) :
    Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₁', Φ₅', mul_add, div_eq_mul_inv, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]

/-- Shift `Φ₃'` by `+1` and rewrite it in terms of `Φ₅'` at the point `it`. -/
public lemma Φ₃'_shift_right (u t : ℝ) :
    Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₃', Φ₅', mul_add, add_assoc, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg,
    div_eq_mul_inv, Complex.exp_add]

/-- Identify `Φ₅'` on the imaginary axis with `-aLaplaceIntegrand`. -/
public lemma Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u t : ℝ) :
    Φ₅' u ((t : ℂ) * Complex.I) = -aLaplaceIntegrand u t := by
  have harg : (-1 : ℂ) / ((t : ℂ) * Complex.I) = (Complex.I : ℂ) / (t : ℂ) := by
    simp [div_eq_mul_inv]
  have hpow : ((t : ℂ) * Complex.I) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [mul_pow]; simp [pow_two, Complex.I_mul_I]
  dsimp [MagicFunction.a.ComplexIntegrands.Φ₅', aLaplaceIntegrand]
  rw [harg, hpow, show Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
    (Real.exp (-Real.pi * u * t) : ℂ) by
    simp [show (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) = (-Real.pi * u * t : ℂ)
      from by ring_nf; simp [Complex.I_sq]]]
  ring_nf

/-- Imaginary-axis specialization of the finite-difference identity for `φ₀`. -/
public lemma Φ_finite_difference_imag_axis {u t : ℝ} (ht : 0 < t) :
    Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
      2 * Φ₆' u ((t : ℂ) * Complex.I) := by
  let zH : ℍ := UpperHalfPlane.mk (Complex.I * t) (by simp [ht])
  have hfd := MagicFunction.a.SpecialValues.φ₀_finite_difference (z := zH)
  have hcore :
      φ₀'' ((-1 : ℂ) / (((1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
          - 2 * (φ₀'' ((-1 : ℂ) / (zH : ℂ)) * ((zH : ℂ) ^ (2 : ℕ)))
          + φ₀'' ((-1 : ℂ) / (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
        = (2 : ℂ) * φ₀'' (zH : ℂ) := by
    have hS (w : ℍ) : φ₀ (ModularGroup.S • w) = φ₀'' ((-1 : ℂ) / (w : ℂ)) := by
      have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = (-1 : ℂ) / (w : ℂ) := by
        simpa using ModularGroup.coe_S_smul (z := w)
      calc φ₀ (ModularGroup.S • w) = φ₀'' ((ModularGroup.S • w : ℍ) : ℂ) :=
            (φ₀''_coe_upperHalfPlane (z := ModularGroup.S • w)).symm
        _ = φ₀'' ((-1 : ℂ) / (w : ℂ)) := by rw [hcoe]
    rw [hS ((1 : ℝ) +ᵥ zH), hS zH, hS ((-1 : ℝ) +ᵥ zH),
      show φ₀ zH = φ₀'' (zH : ℂ) from (φ₀''_coe_upperHalfPlane (z := zH)).symm] at hfd
    simpa [mul_assoc] using hfd
  have hzH : (zH : ℂ) = (t : ℂ) * Complex.I := by simp [zH, mul_comm]
  set e : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * (zH : ℂ))
  set core : ℂ :=
      φ₀'' ((-1 : ℂ) / (((1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
          - 2 * (φ₀'' ((-1 : ℂ) / (zH : ℂ)) * ((zH : ℂ) ^ (2 : ℕ)))
          + φ₀'' ((-1 : ℂ) / (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ)) * (((-1 : ℝ) +ᵥ zH : ℍ) : ℂ) ^ (2 : ℕ)
    with hcore_def
  have hcore_eq : core = (2 : ℂ) * φ₀'' (zH : ℂ) := by simpa [core, hcore_def] using hcore
  have hL :
      Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
        core * e := by
    rw [hcore_def]
    simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
      MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
      MagicFunction.a.ComplexIntegrands.Φ₅', hzH, e, sub_eq_add_neg]
    ring_nf
  have hR : 2 * Φ₆' u ((t : ℂ) * Complex.I) = ((2 : ℂ) * φ₀'' (zH : ℂ)) * e := by
    simp [MagicFunction.a.ComplexIntegrands.Φ₆', hzH, e, mul_assoc, mul_left_comm, mul_comm]
  simpa [hL, hR] using congrArg (fun w : ℂ => w * e) hcore_eq

/-! ## Strip bounds -/

local notation "c12π" => ‖(12 * (I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/-- `IsBoundedAtImInfty` as an explicit uniform bound with positive constant. -/
lemma exists_bound_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C :=
  let ⟨C, A, hC⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp hbdd
  ⟨max 1 C, A, by positivity, fun z hz ↦ (hC z hz).trans (le_max_right _ _)⟩

/-- Exponential growth bounds for `φ₂'` and `φ₄'` on vertical rays in the upper half-plane. -/
public lemma exists_phi2'_phi4'_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im →
      ‖φ₂' z‖ ≤ C * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ C * Real.exp (2 * π * z.im) := by
  obtain ⟨CE2, AE2, _, hE2⟩ := exists_bound_of_isBoundedAtImInfty E₂_isBoundedAtImInfty
  obtain ⟨CE4, AE4, _, hE4⟩ := exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₄ z)
    (by simpa using ModularFormClass.bdd_at_infty E₄)
  obtain ⟨CE6, AE6, _, hE6⟩ := exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₆ z)
    (by simpa using ModularFormClass.bdd_at_infty E₆)
  obtain ⟨CΔ, AΔ, _, hΔ⟩ := exists_inv_Delta_bound_exp
  refine ⟨max 1 (max (CE4 ^ 2 * CΔ) (CE4 * (CE2 * CE4 + CE6) * CΔ)),
    max AΔ (max AE2 (max AE4 AE6)), by positivity, fun z hzA => ?_⟩
  have hzE2 : AE2 ≤ z.im := by simp_all
  have hzE4 : AE4 ≤ z.im := by simp_all
  have hzE6 : AE6 ≤ z.im := by simp_all
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * π * z.im) := hΔ z ((le_max_left _ _).trans hzA)
  have hcore : ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ CE2 * CE4 + CE6 :=
    (by simpa [norm_mul] using norm_sub_le (E₂ z * E₄ z) (E₆ z) :
      ‖E₂ z * E₄ z - E₆ z‖ ≤ ‖E₂ z‖ * ‖E₄ z‖ + ‖E₆ z‖).trans <| by
      gcongr <;> [exact hE2 z hzE2; exact hE4 z hzE4; exact hE6 z hzE6]
  have hφ2 : ‖φ₂' z‖ ≤ (CE4 * (CE2 * CE4 + CE6) * CΔ) * Real.exp (2 * π * z.im) := calc
    ‖φ₂' z‖ = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) * (Δ z)⁻¹‖ := by
      simp [φ₂', div_eq_mul_inv, mul_assoc]
    _ ≤ ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ * ‖(Δ z)⁻¹‖ := norm_mul_le _ _
    _ ≤ (CE4 * (CE2 * CE4 + CE6)) * (CΔ * Real.exp (2 * π * z.im)) :=
        mul_le_mul (norm_mul_le_of_le (hE4 z hzE4) hcore) hΔz (norm_nonneg _) (by positivity)
    _ = _ := by ring
  have hφ4 : ‖φ₄' z‖ ≤ (CE4 ^ 2 * CΔ) * Real.exp (2 * π * z.im) := calc
    ‖φ₄' z‖ = ‖E₄ z‖ ^ 2 * ‖(Δ z)⁻¹‖ := by simp [φ₄', div_eq_mul_inv, pow_two]
    _ ≤ CE4 ^ 2 * (CΔ * Real.exp (2 * π * z.im)) := by gcongr; exact hE4 z hzE4
    _ = _ := by ring
  exact ⟨hφ2.trans <| mul_le_mul_of_nonneg_right (by simp_all) (Real.exp_pos _).le,
    hφ4.trans <| mul_le_mul_of_nonneg_right (by simp_all) (Real.exp_pos _).le⟩

/-- Integrability of `Φ₆'` on the imaginary axis tail `t > 1`. -/
lemma integrableOn_Φ₆'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨C₀, _, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set b : ℝ := π * (u + 2) with hb_def
  refine MeasureTheory.Integrable.mono'
    (by simpa [IntegrableOn, mul_assoc] using
      ((exp_neg_integrableOn_Ioi 1 (hb_def ▸ mul_pos Real.pi_pos (by linarith))).const_mul C₀ :
        IntegrableOn (fun t : ℝ => C₀ * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume))
    (((Φ₆'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
      (fun t ht => by simpa using lt_trans zero_lt_one ht :
        Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi (1 : ℝ))
          {z : ℂ | 0 < z.im})).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht => ?_
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using lt_trans zero_lt_one ht⟩
  refine (show ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤
      (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) by
    rw [show Φ₆' u ((t : ℂ) * Complex.I) = φ₀'' ((t : ℂ) * Complex.I) *
        cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) by simp [Φ₆']]
    have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
    refine norm_mul_le_of_le (show ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * t) by
      simpa [φ₀''_coe_upperHalfPlane, hz_im] using
        hC₀ zH (by simpa [hz_im] using lt_trans (by norm_num : (1/2:ℝ) < 1) ht)) ?_
    rw [show cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
        (Real.exp (-π * u * t) : ℂ) by ring_nf; simp [Complex.ofReal_exp],
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]).trans ?_
  rw [mul_assoc, ← Real.exp_add, show -2 * π * t + -π * u * t = -(b * t) by dsimp [b]; ring]

/-- Integrability of `Φ₅'` on the imaginary-axis tail `t > 1`. -/
public lemma integrableOn_Φ₅'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume :=
  IntegrableOn.congr_fun (((aLaplaceIntegral_convergent (u := u) hu).mono_set
    fun _ ht => lt_trans (by norm_num : (0:ℝ) < 1) ht).neg)
    (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)).symm)
    measurableSet_Ioi

/-- Modular-growth bound for `‖φ₀(S•w)‖‖w‖^2` depending only on `t = Im w`. -/
public lemma norm_phi0S_mul_sq_le {t : ℝ} (wH : ℍ) (hw_im : wH.im = t)
    {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
  (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) (hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t) :
    ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
  obtain ⟨hφ2, hφ4⟩ : ‖φ₂' wH‖ ≤ Cφ * Real.exp (2 * π * t) ∧
      ‖φ₄' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by
    simpa [hw_im] using hφbd wH (by simpa [hw_im] using htAφ)
  have hCφ_nonneg : 0 ≤ Cφ :=
    le_of_mul_le_mul_right (by simpa using (norm_nonneg _).trans hφ2) (Real.exp_pos _)
  have htri : ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ + ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
        ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
    rw [show φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) =
        φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) - (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH by simpa using _root_.φ₀_S_transform_mul_sq wH]
    exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  have hA : ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have h1 : ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤ C₀ * (2 * t) ^ 2 := (norm_mul_le _ _).trans
      (mul_le_mul ((hC₀ wH (by rw [hw_im]; linarith)).trans
          (mul_le_of_le_one_right hC₀_pos.le (Real.exp_le_one_iff.2 <| by
            nlinarith [Real.pi_pos, wH.im_pos])))
        (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hw_norm 2)
        (norm_nonneg _) hC₀_pos.le)
    nlinarith [h1, sq_nonneg t, Real.one_le_exp_iff.2 (by positivity : (0:ℝ) ≤ 2*π*t),
      mul_nonneg (by positivity : (0:ℝ) ≤ 4 * C₀) (sq_nonneg t)]
  have hB : ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
      (2 * c12π * Cφ) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    refine norm_mul₃_le.trans <| (mul_le_mul (mul_le_mul_of_nonneg_left hw_norm (norm_nonneg _))
      hφ2 (norm_nonneg _) (by positivity)).trans ?_
    rw [show (c12π * (2 * t)) * (Cφ * Real.exp (2 * π * t)) =
      (2 * c12π * Cφ) * (t * Real.exp (2 * π * t)) by ring]
    gcongr; nlinarith
  have hC : ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ ≤
      c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    refine ((norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_left hφ4 (norm_nonneg _)).trans ?_
    rw [show c36π2 * (Cφ * Real.exp (2 * π * t)) = c36π2 * Cφ * (1 * Real.exp (2 * π * t)) by ring]
    gcongr; exact one_le_pow₀ ht1
  linarith [htri, hA, hB, hC]

/-- Pointwise bound for `‖Φ₂' u (tI)‖` on the tail `t ≥ 1`. -/
lemma norm_Φ₂'_imag_axis_le {u t : ℝ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₂' u ((t : ℂ) * I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  let wH : ℍ := ⟨(t : ℂ) * I + 1, by simpa using ht0⟩
  have hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t := (norm_add_le (_ : ℂ) _).trans <| by
    simpa [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le] using by linarith
  calc ‖Φ₂' u ((t : ℂ) * I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
        rw [show Φ₂' u ((t : ℂ) * I) = (φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
            cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) by
            rw [show Φ₂' u ((t : ℂ) * I) =
                  (φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ))) *
                    cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) by simp [Φ₂', Φ₁', mul_assoc],
              show ((t : ℂ) * I + 1) = (wH : ℂ) from rfl, show φ₀ (ModularGroup.S • wH) =
                φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
              show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
                simpa using ModularGroup.coe_S_smul (z := wH)],
          norm_mul, show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
              Real.exp (-π * u * t) by
            rw [show cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
              (Real.exp (-π * u * t) : ℂ) by ring_nf; simp [Complex.ofReal_exp],
              Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
        mul_le_mul_of_nonneg_right (norm_phi0S_mul_sq_le wH (by simp [wH, UpperHalfPlane.im])
          hC₀_pos hC₀ hφbd ht1 htAφ hw_norm) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
        rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Integrability of `Φ₂'` on the tail `(A,∞)` via modular bounds. -/
lemma integrableOn_Φ₂'_imag_axis_Ioi {u : ℝ} (hu : 2 < u) {Cφ Aφ C₀ A : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hA1 : (1 : ℝ) ≤ A) (hAA : Aφ ≤ A) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioi A) volume := by
  refine MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi A)) (by
      simpa [IntegrableOn, mul_assoc] using ((integrableOn_sq_mul_exp_neg A (π * (u - 2))
        (mul_pos Real.pi_pos (sub_pos.mpr hu))).const_mul
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) :
        IntegrableOn (fun t : ℝ => (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
          (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t))) (Set.Ioi A) volume))
    (((Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
      (fun t ht ↦ by simpa using lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hA1) ht :
        Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi A)
          {z : ℂ | 0 < z.im})).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht =>
      norm_Φ₂'_imag_axis_le (u := u) hC₀_pos hC₀ hφbd (le_trans hA1 ht.le) (le_trans hAA ht.le))

/-- Integrability of `Φ₂'` on the imaginary-axis tail `t > 1`. -/
public lemma integrableOn_Φ₂'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let A : ℝ := max 1 Aφ
  simpa [(Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) (le_max_left _ _)).symm] using
    ((((Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
        (fun t ht => by simpa using lt_of_lt_of_le zero_lt_one ht.1 :
          Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Icc (1 : ℝ) A)
            {z : ℂ | 0 < z.im})).integrableOn_compact isCompact_Icc).mono_set
            Set.Ioc_subset_Icc_self).union
      (integrableOn_Φ₂'_imag_axis_Ioi (u := u) hu (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀) (A := A)
        hC₀_pos hC₀ hφbd (le_max_left _ _) (le_max_right _ _))

/-- Integrability of `Φ₄'` on the imaginary-axis tail `t > 1` via finite differences. -/
public lemma integrableOn_Φ₄'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₄' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume := by
  have hcomb : IntegrableOn
      (fun t : ℝ => (2 : ℂ) * Φ₆' u ((t : ℂ) * I) - Φ₂' u ((t : ℂ) * I) +
        (2 : ℂ) * Φ₅' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume :=
    ((show IntegrableOn (fun t : ℝ => (2 : ℂ) * Φ₆' u ((t : ℂ) * I)) (Set.Ioi (1:ℝ)) volume by
        simpa [mul_assoc] using (integrableOn_Φ₆'_imag_axis (u := u) hu).const_mul (2:ℂ)).sub
      (integrableOn_Φ₂'_imag_axis (u := u) hu)).add <| by
        simpa [mul_assoc] using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul (2:ℂ)
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have hfd := Φ_finite_difference_imag_axis (u := u) (t := t) (lt_trans zero_lt_one ht)
  grind only

/-- Rewrite `I₁' + I₃' + I₅'` as the imaginary-axis segment integral of `Φ₅'`. -/
public lemma I₁'_add_I₃'_add_I₅'_eq_imag_axis (u : ℝ) :
    I₁' u + I₃' u + I₅' u =
      (I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * I)) - (2 : ℂ)) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I))) := by
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)
  have hmem : ∀ {t : ℝ}, t ∈ Set.uIcc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 := fun ht ↦ by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  have hIshift : ∀ (sign : ℂ) (zp : ℝ → ℂ) (Φⱼ : ℝ → ℂ → ℂ)
      (_ : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → zp t = sign + (t : ℂ) * I)
      (_ : ∀ t : ℝ, Φⱼ u (sign + (t : ℂ) * I) =
        Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)),
      (∫ t in (0 : ℝ)..1, (I : ℂ) * Φⱼ u (zp t)) =
        (I : ℂ) * Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * V0 := fun sign zp Φⱼ hzp hΦ ↦ by
    rw [intervalIntegral.integral_congr (g := fun t ↦ (I : ℂ) *
      (Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)))
      fun t ht ↦ by simp [hzp (hmem ht), hΦ, mul_assoc]]
    simp [V0, mul_assoc]
  rw [show I₁' u = (I : ℂ) * Complex.exp (-(((π * u : ℝ) : ℂ) * I)) * V0 from by
        simpa [I₁', Φ₁, mul_assoc, neg_mul, one_mul] using hIshift (-1 : ℂ) z₁' Φ₁'
          (fun ht ↦ by simpa [mul_comm] using z₁'_eq_of_mem ht)
          (fun t ↦ by simpa [neg_mul, one_mul, mul_comm] using Φ₁'_shift_left (u := u) (t := t)),
      show I₃' u = (I : ℂ) * Complex.exp (((π * u : ℝ) : ℂ) * I) * V0 from by
        simpa [I₃', Φ₃, mul_assoc, one_mul] using hIshift (1 : ℂ) z₃' Φ₃'
          (fun ht ↦ by simpa [mul_comm] using z₃'_eq_of_mem ht)
          (fun t ↦ by simpa [one_mul, mul_comm] using Φ₃'_shift_right (u := u) (t := t)),
      show I₅' u = (-2 : ℂ) * (I : ℂ) * V0 from by
        simpa [I₅', Φ₅, mul_assoc] using congrArg (fun z : ℂ ↦ (-2 : ℂ) * z) (by
          rw [intervalIntegral.integral_congr (g := fun t ↦ (I : ℂ) * Φ₅' u ((t : ℂ) * I))
            fun t ht ↦ by simp [z₅'_eq_of_mem (hmem ht), mul_comm]]; simp [V0] :
          (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u (z₅' t)) = (I : ℂ) * V0)]
  ring

end MagicFunction.g.CohnElkies.IntegralReps
namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology Interval UpperHalfPlane

open MeasureTheory Real Complex Filter
open SpherePacking intervalIntegral
open MagicFunction.a.RealIntegrals

/-- Differentiability of a parameter-dependent interval integral with an exponential factor. -/
public lemma differentiableAt_intervalIntegral_mul_exp
    {base k : ℝ → ℂ} (u0 : ℂ) (Cbase K : ℝ)
    (hbase : ContinuousOn base (Ι (0 : ℝ) 1))
    (hk : ContinuousOn k (Ι (0 : ℝ) 1))
    (hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase)
    (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ K) :
    DifferentiableAt ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
  have hCbase : 0 ≤ Cbase := (norm_nonneg (base 1)).trans (hbase_bound 1 (by simp))
  have hK : 0 ≤ K := (norm_nonneg (k 1)).trans (hk_bound 1 (by simp))
  let F : ℂ → ℝ → ℂ := fun u t => base t * Complex.exp (u * k t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * (k t) * Complex.exp (u * k t)
  have hexp (u : ℂ) : ContinuousOn (fun t : ℝ => Complex.exp (u * k t)) (Ι (0 : ℝ) 1) := by
    fun_prop
  have hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) (volume.restrict (Ι (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall fun u => (hbase.mul (hexp u)).aestronglyMeasurable
      (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF'_meas : AEStronglyMeasurable (F' u0) (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa [F', mul_assoc] using (hbase.mul (hk.mul (hexp u0))).aestronglyMeasurable
      (μ := (volume : Measure ℝ)) measurableSet_uIoc
  have hF_int : IntervalIntegrable (F u0) volume (0 : ℝ) 1 := by
    refine intervalIntegrable_iff.2 ?_
    refine MeasureTheory.IntegrableOn.of_bound (by simp : (volume : Measure ℝ) (Ι (0 : ℝ) 1) < ⊤)
      hF_meas.self_of_nhds (Cbase * Real.exp (‖u0‖ * K)) <|
      (ae_restrict_iff' measurableSet_uIoc).2 <| .of_forall fun t ht => ?_
    refine norm_mul_le_of_le (hbase_bound t ht) ?_
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2
      ((norm_mul_le u0 (k t)).trans (by gcongr; exact hk_bound t ht)))
  let E : ℝ := Real.exp ((‖u0‖ + 1) * K)
  let bound : ℝ → ℝ := fun _ => Cbase * (K * E)
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
      ∀ u ∈ Metric.ball u0 (1 : ℝ), ‖F' u t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall (fun t ht u hu => ?_)
    have hk' : ‖k t‖ ≤ K := hk_bound t ht
    have hu' : ‖u‖ ≤ ‖u0‖ + 1 := by
      have : ‖u‖ ≤ ‖u0‖ + ‖u - u0‖ := by
        simpa [sub_eq_add_neg, add_assoc] using norm_add_le u0 (u - u0)
      linarith [show ‖u - u0‖ < 1 from by simpa [Metric.mem_ball, dist_eq_norm] using hu]
    have hstep1 : ‖F' u t‖ ≤ ‖base t‖ * (‖k t‖ * E) := by
      calc
        ‖F' u t‖ = ‖base t‖ * (‖k t‖ * ‖Complex.exp (u * k t)‖) := by
          simp [F', mul_left_comm, mul_comm]
        _ ≤ ‖base t‖ * (‖k t‖ * E) := by
          gcongr
          exact (Complex.norm_exp_le_exp_norm _).trans
            (Real.exp_le_exp.2 (norm_mul_le_of_le hu' hk'))
    simpa [bound, E, mul_assoc] using hstep1.trans (by gcongr; exact hbase_bound t ht)
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
      ∀ u ∈ Metric.ball u0 (1 : ℝ), HasDerivAt (fun u : ℂ => F u t) (F' u t) u :=
    Filter.Eventually.of_forall fun t _ u _ => by
      simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
        ((Complex.hasDerivAt_exp (u * k t)).comp u
          (hasDerivAt_mul_const (k t) (x := u))).const_mul (base t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    (F := F) (F' := F') (x₀ := u0) (s := Metric.ball u0 (1 : ℝ)) (bound := bound)
    (Metric.ball_mem_nhds u0 (by norm_num)) (hF_meas := hF_meas) (hF_int := hF_int)
    (hF'_meas := hF'_meas) (h_bound := h_bound)
    (bound_integrable := by simp [bound]) (h_diff := h_diff)).2.differentiableAt

noncomputable section

def I₁'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (-π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ))

def I₂'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / ((t : ℂ) + (Complex.I : ℂ))) * (((t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ)) *
      Complex.exp (-π * (Complex.I : ℂ) * u) *
      Complex.exp (π * (Complex.I : ℂ) * u * (t : ℂ)) *
      Complex.exp (-π * u)

def I₃'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (π * (Complex.I : ℂ) * u) * Complex.exp (-π * u * (t : ℂ))

def I₄'C (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-1 : ℂ) * φ₀'' (-1 / (-(t : ℂ) + (Complex.I : ℂ))) *
      ((-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ)) *
      Complex.exp (π * (Complex.I : ℂ) * u) *
      Complex.exp (-π * (Complex.I : ℂ) * u * (t : ℂ)) *
      Complex.exp (-π * u)

def I₅'C (u : ℂ) : ℂ :=
  -2 * ∫ t in (0 : ℝ)..1,
    (-Complex.I) * φ₀'' (-1 / ((Complex.I : ℂ) * (t : ℂ))) * (t ^ (2 : ℕ) : ℝ) *
      Complex.exp (-π * u * (t : ℂ))

def I₆'C (u : ℂ) : ℂ :=
  2 * ∫ t in Set.Ici (1 : ℝ),
    (Complex.I : ℂ) * φ₀'' ((Complex.I : ℂ) * (t : ℂ)) * Complex.exp (-π * u * (t : ℂ))

/-- Complex-parameter extension of `a'`, defined as the sum of the complexified integral pieces.

This is analytic on the right half-plane and restricts to `a'` on `ℝ`. -/
public def aPrimeC (u : ℂ) : ℂ :=
  I₁'C u + I₂'C u + I₃'C u + I₄'C u + I₅'C u + I₆'C u

@[simp] lemma I₁'C_ofReal (u : ℝ) : I₁'C (u : ℂ) = I₁' u := by
  simp [I₁'C, MagicFunction.a.RadialFunctions.I₁'_eq]
@[simp] lemma I₂'C_ofReal (u : ℝ) : I₂'C (u : ℂ) = I₂' u := by
  simp [I₂'C, MagicFunction.a.RadialFunctions.I₂'_eq]
@[simp] lemma I₃'C_ofReal (u : ℝ) : I₃'C (u : ℂ) = I₃' u := by
  simp [I₃'C, MagicFunction.a.RadialFunctions.I₃'_eq]
@[simp] lemma I₄'C_ofReal (u : ℝ) : I₄'C (u : ℂ) = I₄' u := by
  simp [I₄'C, MagicFunction.a.RadialFunctions.I₄'_eq]
@[simp] lemma I₅'C_ofReal (u : ℝ) : I₅'C (u : ℂ) = I₅' u := by
  simp [I₅'C, MagicFunction.a.RadialFunctions.I₅'_eq]
@[simp] lemma I₆'C_ofReal (u : ℝ) : I₆'C (u : ℂ) = I₆' u := by
  simp [I₆'C, MagicFunction.a.RadialFunctions.I₆'_eq]

/-- Restriction of `aPrimeC` to real parameters recovers `a'`. -/
public lemma aPrimeC_ofReal (u : ℝ) : aPrimeC (u : ℂ) = a' u := by
  simp [aPrimeC, MagicFunction.a.RealIntegrals.a']

lemma norm_φ₀''_le_of_half_lt {C₀ : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀ : ∀ z : ℍ, 1 / 2 < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : 1 / 2 < z.im) :
    ‖φ₀'' z‖ ≤ C₀ := by
  refine (show ‖φ₀'' z‖ ≤ C₀ * Real.exp (-2 * π * z.im) from ?_).trans
    (mul_le_of_le_one_right hC₀_nonneg <| Real.exp_le_one_iff.2
      (by nlinarith [Real.pi_pos, hzpos.le]))
  simpa [φ₀''_def hzpos] using hC₀ ⟨z, hzpos⟩ (by simpa [UpperHalfPlane.im] using hzhalf)

def arg₁ (t : ℝ) : ℂ := (Complex.I : ℂ) / (t : ℂ)

lemma neg_one_div_I_mul_eq_arg₁ (t : ℝ) :
    (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) = arg₁ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [arg₁]
  · simp only [arg₁]
    field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ht, Complex.I_ne_zero]
    simp [Complex.I_sq]

def base₁ (t : ℝ) : ℂ := (-Complex.I) * φ₀'' (arg₁ t) * (t ^ (2 : ℕ) : ℝ)
def k₁ (t : ℝ) : ℂ := (-π * (Complex.I : ℂ)) + (-π * (t : ℂ))
def k₃ (t : ℝ) : ℂ := (π * (Complex.I : ℂ)) + (-π * (t : ℂ))
def k₅ (t : ℝ) : ℂ := (-π * (t : ℂ))

lemma I₁'C_eq (u : ℂ) :
    I₁'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₁ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₁, neg_one_div_I_mul_eq_arg₁, mul_add, Complex.exp_add,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₃'C_eq (u : ℂ) :
    I₃'C u = ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₃ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₃, neg_one_div_I_mul_eq_arg₁, mul_add, Complex.exp_add,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₅'C_eq (u : ℂ) :
    I₅'C u = -2 * ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k₅ t) :=
  congrArg (fun x : ℂ => -2 * x) <| intervalIntegral.integral_congr fun t _ => by
    simp [base₁, k₅, neg_one_div_I_mul_eq_arg₁, mul_left_comm, mul_comm]

lemma base₁_continuousOn : ContinuousOn base₁ (Ι (0 : ℝ) 1) :=
  (continuousOn_const.mul
    ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
      (continuousOn_const.div (by fun_prop) fun t ht => by
        exact_mod_cast (by simpa using ht.1 : (0 : ℝ) < t).ne')
      fun t ht => by
        simpa [UpperHalfPlane.upperHalfPlaneSet, arg₁] using
          inv_pos.2 (by simpa using ht.1 : (0:ℝ) < t))).mul (by fun_prop)

lemma base₁_bound :
    ∃ C₀ > 0, ∀ t ∈ Ι (0 : ℝ) 1, ‖base₁ t‖ ≤ C₀ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  have ht0 : 0 < t := by simpa using ht.1
  have ht1 : t ≤ 1 := by simpa using ht.2
  have hzhalf : (1 / 2 : ℝ) < (arg₁ t).im := by
    simpa [arg₁] using lt_of_lt_of_le (by norm_num : (1/2:ℝ) < 1) (one_le_inv_iff₀.2 ⟨ht0, ht1⟩)
  have ht2 : ‖(t ^ (2 : ℕ) : ℝ)‖ ≤ 1 := by
    have : |t| ^ (2 : ℕ) ≤ (1 : ℝ) :=
      pow_le_one₀ (abs_nonneg t) (by simpa [abs_of_nonneg ht0.le] using ht1)
    simpa [Real.norm_eq_abs, abs_pow] using this
  calc ‖base₁ t‖
      = ‖φ₀'' (arg₁ t)‖ * ‖(t ^ (2 : ℕ) : ℝ)‖ := by simp [base₁]
    _ ≤ C₀ * 1 := mul_le_mul (norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀
          (by simpa [arg₁] using inv_pos.2 ht0) hzhalf) ht2 (norm_nonneg _) hC₀_pos.le
    _ = C₀ := mul_one _

private lemma norm_of_mem_uIoc_le_one {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : ‖(t : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, abs_of_nonneg (by simpa using ht.1 : (0:ℝ) < t).le] using ht.2

private lemma norm_neg_pi_mul_t_le {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(-π : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
  have : ‖(-π : ℂ) * (t : ℂ)‖ = Real.pi * ‖(t : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  nlinarith [Real.pi_pos, norm_of_mem_uIoc_le_one ht]

private lemma norm_sign_pi_I_eq_pi {s : ℝ} (hs : |s| = 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ)‖ = Real.pi := by
  simp [Complex.norm_real, hs, abs_of_nonneg Real.pi_pos.le]

/-- Shared bound for `k₁` and `k₃`: `‖±π * I + (-π * t)‖ ≤ 2π`. -/
private lemma k_bound_two_pi {s : ℝ} (hs : |s| = 1) (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s * π : ℂ) * (Complex.I : ℂ) + (-π * (t : ℂ))‖ ≤ (2 * Real.pi) := by
  linarith [(norm_add_le ((s * π : ℂ) * (Complex.I : ℂ)) (-π * (t : ℂ))).trans
    (add_le_add (norm_sign_pi_I_eq_pi hs).le (norm_neg_pi_mul_t_le ht))]

/-- Shared wrapper: `u ↦ ∫ t in 0..1, base₁ t * exp (u * k t)` is differentiable at `u0`. -/
private lemma base₁_integral_differentiableAt {k : ℝ → ℂ} (u0 : ℂ) (K : ℝ)
    (hk : ContinuousOn k (Ι (0 : ℝ) 1)) (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ K) :
    DifferentiableAt ℂ
      (fun u : ℂ => ∫ t in (0 : ℝ)..1, base₁ t * Complex.exp (u * k t)) u0 :=
  let ⟨Cbase, _, hbase_bound⟩ := base₁_bound
  differentiableAt_intervalIntegral_mul_exp u0 Cbase K
    base₁_continuousOn hk hbase_bound hk_bound

lemma I₁'C_differentiableOn : DifferentiableOn ℂ I₁'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₁'C_eq] using
    base₁_integral_differentiableAt u (2 * Real.pi) (by unfold k₁; fun_prop)
      (fun t ht => by
        simpa [k₁, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring] using
          k_bound_two_pi (s := -1) (by norm_num) t ht)

lemma I₃'C_differentiableOn : DifferentiableOn ℂ I₃'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₃'C_eq] using
    base₁_integral_differentiableAt u (2 * Real.pi) (by unfold k₃; fun_prop)
      (fun t ht => by
        simpa [k₃, show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
          k_bound_two_pi (s := 1) (by norm_num) t ht)

lemma I₅'C_differentiableOn : DifferentiableOn ℂ I₅'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext fun u => by simpa [mul_assoc] using I₅'C_eq u, mul_assoc] using
    (base₁_integral_differentiableAt u Real.pi (by unfold k₅; fun_prop)
      (fun t ht => by simpa [k₅] using norm_neg_pi_mul_t_le ht)).const_mul (-2 : ℂ)

def arg₂ (t : ℝ) : ℂ := (-1 : ℂ) / ((t : ℂ) + (Complex.I : ℂ))
def base₂ (t : ℝ) : ℂ := φ₀'' (arg₂ t) * (((t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))
def k₂ (t : ℝ) : ℂ := (-π * (Complex.I : ℂ)) + (π * (Complex.I : ℂ) * (t : ℂ)) + (-π)
def arg₄ (t : ℝ) : ℂ := (-1 : ℂ) / (-(t : ℂ) + (Complex.I : ℂ))
def base₄ (t : ℝ) : ℂ := (-1 : ℂ) * φ₀'' (arg₄ t) * ((-(t : ℂ) + (Complex.I : ℂ)) ^ (2 : ℕ))
def k₄ (t : ℝ) : ℂ := (π * (Complex.I : ℂ)) + (-π * (Complex.I : ℂ) * (t : ℂ)) + (-π)

lemma I₂'C_eq (u : ℂ) :
    I₂'C u = ∫ t in (0 : ℝ)..1, base₂ t * Complex.exp (u * k₂ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₂, arg₂, k₂, mul_add, Complex.exp_add, add_assoc,
      mul_assoc, mul_left_comm, mul_comm]

lemma I₄'C_eq (u : ℂ) :
    I₄'C u = ∫ t in (0 : ℝ)..1, base₄ t * Complex.exp (u * k₄ t) :=
  intervalIntegral.integral_congr fun t _ => by
    simp [base₄, arg₄, k₄, mul_add, Complex.exp_add, add_assoc,
      mul_assoc, mul_left_comm, mul_comm]

/-- Shared continuity argument for `base₂` and `base₄`: if `d : ℝ → ℂ` is continuous with
imaginary part `1` (so nonzero), then `t ↦ φ₀'' (-1 / d t) * d t ^ 2` is continuous. -/
private lemma phi_div_pow_continuousOn {d : ℝ → ℂ} (hd : Continuous d)
    (hd_im : ∀ t, (d t).im = 1) :
    ContinuousOn (fun t : ℝ => φ₀'' (-1 / d t) * (d t) ^ (2 : ℕ)) (Ι (0 : ℝ) 1) := by
  have hden0 : ∀ t : ℝ, d t ≠ 0 := fun t ht0 =>
    (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa [hd_im] using congrArg Complex.im ht0)
  exact ((MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn).comp
    (continuousOn_const.div hd.continuousOn fun t _ => hden0 t) (fun t _ => by
      have him : ((-1 : ℂ) / d t).im = 1 / Complex.normSq (d t) := by
        rw [show ((-1 : ℂ) / d t).im = -(d t)⁻¹.im from by simp [div_eq_mul_inv],
          Complex.inv_im, hd_im]; field_simp
      simpa [UpperHalfPlane.upperHalfPlaneSet, him] using
        one_div_pos.2 (Complex.normSq_pos.2 (hden0 t)))).mul (by fun_prop)

/-- Shared bound for `k₂` and `k₄`: `‖±π * I + ∓π * I * t + (-π)‖ ≤ 3π`. -/
private lemma k_bound_three_pi {s₁ s₂ : ℝ} (hs₁ : |s₁| = 1) (hs₂ : |s₂| = 1)
    (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
    ‖(s₁ * π : ℂ) * (Complex.I : ℂ) + (s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ) + (-π)‖ ≤
      (3 * Real.pi) := by
  have hpi : ‖(-π : ℂ)‖ = Real.pi := by simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
  have h_t_le : ‖(s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
    have h : ‖(s₂ * π : ℂ) * (Complex.I : ℂ) * (t : ℂ)‖ = Real.pi * ‖(t : ℂ)‖ := by
      simpa [mul_assoc] using congrArg (· * ‖(t : ℂ)‖) (norm_sign_pi_I_eq_pi hs₂)
    nlinarith [Real.pi_pos, norm_of_mem_uIoc_le_one ht]
  linarith [(norm_add_le _ (-π : ℂ)).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sign_pi_I_eq_pi hs₁).le h_t_le)) hpi.le)]

/-- Shared differentiability wrapper for I₂/I₄. -/
private lemma base_pow_diffAt_of
    {base k : ℝ → ℂ} (arg d : ℝ → ℂ) (u0 : ℂ)
    (hbase_eq : ∀ t : ℝ, ‖base t‖ = ‖φ₀'' (arg t)‖ * ‖(d t) ^ (2 : ℕ)‖)
    (hbase_cont : ContinuousOn base (Ι (0 : ℝ) 1))
    (hd_norm : ∀ t : ℝ, ‖d t‖ ≤ ‖(t : ℂ)‖ + 1)
    (him : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < (arg t).im)
    (hk_cont : ContinuousOn k (Ι (0 : ℝ) 1))
    (hk_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖k t‖ ≤ (3 * Real.pi)) :
    DifferentiableAt ℂ (fun u : ℂ =>
      ∫ t in (0 : ℝ)..1, base t * Complex.exp (u * k t)) u0 := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set Cφ : ℝ := max C₀ ‖φ₀'' (arg 1)‖
  refine differentiableAt_intervalIntegral_mul_exp u0 (4 * Cφ) (3 * Real.pi)
    hbase_cont hk_cont (fun t ht => (hbase_eq t).le.trans ?_) hk_bound
  have hphi : ‖φ₀'' (arg t)‖ ≤ Cφ := by
    by_cases ht1 : t = 1
    · exact ht1 ▸ le_max_right _ _
    · have hh := him t ⟨by simpa using ht.1, lt_of_le_of_ne (by simpa using ht.2) ht1⟩
      exact (norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀ (one_half_pos.trans hh) hh).trans
        (le_max_left _ _)
  have hpow : ‖(d t) ^ (2 : ℕ)‖ ≤ 4 := by
    have hnorm : ‖d t‖ ≤ 2 := (hd_norm t).trans (by linarith [norm_of_mem_uIoc_le_one ht])
    calc ‖(d t) ^ (2 : ℕ)‖ = ‖d t‖ ^ (2 : ℕ) := by simp
      _ ≤ (2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 4 := by norm_num
  calc ‖φ₀'' (arg t)‖ * ‖(d t) ^ (2 : ℕ)‖
      ≤ Cφ * 4 := mul_le_mul hphi hpow (norm_nonneg _) (by positivity)
    _ = 4 * Cφ := by ring

lemma I₂'C_differentiableOn : DifferentiableOn ℂ I₂'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₂'C_eq] using
    base_pow_diffAt_of arg₂ (fun t => (t : ℂ) + (Complex.I : ℂ)) u
      (fun t => by simp [base₂])
      (by unfold base₂ arg₂; exact phi_div_pow_continuousOn (by fun_prop) (fun _ => by simp))
      (fun t => by simpa using (norm_add_le (t : ℂ) (Complex.I : ℂ)))
      (fun t htIoo => by
        simpa [arg₂] using MagicFunction.a.IntegralEstimates.I₂.im_parametrisation_lower t htIoo)
      (by unfold k₂; fun_prop) fun t ht => by
        simpa [k₂, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring,
          show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
          k_bound_three_pi (s₁ := -1) (s₂ := 1) (by norm_num) (by norm_num) t ht

lemma I₄'C_differentiableOn : DifferentiableOn ℂ I₄'C rightHalfPlane := fun u _ => by
  refine DifferentiableAt.differentiableWithinAt ?_
  simpa [funext I₄'C_eq] using
    base_pow_diffAt_of arg₄ (fun t => -(t : ℂ) + (Complex.I : ℂ)) u
      (fun t => by simp [base₄])
      ((show (fun t : ℝ => (-1 : ℂ) * (φ₀'' (arg₄ t) * (-(t:ℂ) + (Complex.I:ℂ)) ^ (2:ℕ))) = base₄
        from funext fun _ => by simp [base₄, arg₄]) ▸
        continuousOn_const.mul (phi_div_pow_continuousOn
          (d := fun t : ℝ => -(t : ℂ) + (Complex.I : ℂ)) (by fun_prop) (fun _ => by simp)))
      (fun t => (norm_add_le _ _).trans (by simp))
      (fun t htIoo => by
        simpa [arg₄] using MagicFunction.a.IntegralEstimates.I₄.im_parametrisation_lower t htIoo)
      (by unfold k₄; fun_prop) fun t ht => by
        simpa [k₄, show ((-1 : ℝ) * Real.pi : ℂ) = (-π : ℂ) by push_cast; ring,
          show ((1 : ℝ) * Real.pi : ℂ) = (π : ℂ) by push_cast; ring] using
          k_bound_three_pi (s₁ := 1) (s₂ := -1) (by norm_num) (by norm_num) t ht

def base₆ (t : ℝ) : ℂ := (Complex.I : ℂ) * φ₀'' ((t : ℂ) * (Complex.I : ℂ))

def I₆IntegrandC (u : ℂ) (t : ℝ) : ℂ := base₆ t * Complex.exp (-(π : ℂ) * u * (t : ℂ))
def I₆IntegrandC_deriv (u : ℂ) (t : ℝ) : ℂ := (-(π : ℂ) * (t : ℂ)) * I₆IntegrandC u t

lemma base₆_continuousOn : ContinuousOn base₆ (Set.Ici (1 : ℝ)) := by
  simpa [base₆, mul_assoc] using continuousOn_const.mul
    (MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn.comp
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (Complex.I : ℂ)).continuousOn
      fun t ht => by
        simpa [UpperHalfPlane.upperHalfPlaneSet, mul_assoc] using lt_of_lt_of_le (by norm_num) ht)

lemma I₆'C_differentiableAt (u0 : ℂ) (hu0 : u0 ∈ rightHalfPlane) :
    DifferentiableAt ℂ I₆'C u0 := by
  have hu0re : 0 < u0.re := by simpa [rightHalfPlane] using hu0
  set ε : ℝ := u0.re / 2 with hε_def
  have hε : 0 < ε := by positivity
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hbase_bound : ∀ t ∈ Set.Ici (1 : ℝ), ‖base₆ t‖ ≤ C₀ := fun t ht => by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [base₆, norm_mul] using norm_φ₀''_le_of_half_lt hC₀_pos.le hC₀
      (z := (t : ℂ) * (Complex.I : ℂ)) (by simpa [mul_assoc] using ht0)
      (by simpa [mul_assoc] using lt_of_lt_of_le (by norm_num : (1/2:ℝ) < 1) ht)
  have hIntegrand_le : ∀ z : ℂ, ∀ t ∈ Set.Ici (1 : ℝ),
      ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-Real.pi * z.re * t) := fun z t ht => by
    have hExp : ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-Real.pi * z.re * t) := by
      simp [Complex.norm_exp, mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]
    calc ‖I₆IntegrandC z t‖
        = ‖base₆ t‖ * ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ := by simp [I₆IntegrandC]
      _ ≤ C₀ * Real.exp (-Real.pi * z.re * t) :=
        mul_le_mul (hbase_bound t ht) hExp (norm_nonneg _) (by positivity)
  have hIntegrandC_continuousOn : ∀ z : ℂ,
      ContinuousOn (fun t : ℝ => I₆IntegrandC z t) (Set.Ici (1 : ℝ)) := fun z => by
    simpa [I₆IntegrandC] using base₆_continuousOn.mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(π : ℂ) * z * (t : ℂ))).continuousOn
  have hF_meas : ∀ z : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC z t) μ := fun z =>
    (hIntegrandC_continuousOn z).aestronglyMeasurable measurableSet_Ici
  have hF_int : MeasureTheory.Integrable (fun t : ℝ => I₆IntegrandC u0 t) μ := by
    have hExp : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((Real.pi * u0.re) * t)))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [mul_assoc] using
        exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := (Real.pi * u0.re)) (by positivity)
    refine MeasureTheory.Integrable.mono' (μ := μ) (by
      simpa [MeasureTheory.IntegrableOn, μ] using
        (integrableOn_Ici_iff_integrableOn_Ioi (μ := (MeasureTheory.volume : Measure ℝ))
          (f := fun t : ℝ => C₀ * Real.exp (-(Real.pi * u0.re) * t)) (b := (1 : ℝ))
          (by finiteness)).2
            (by simpa [MeasureTheory.IntegrableOn, mul_assoc] using hExp.const_mul C₀))
      (hF_meas u0) (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht => ?_)
    simpa [← mul_assoc] using hIntegrand_le u0 t ht
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => I₆IntegrandC_deriv u0 t) μ :=
    (((by fun_prop : Continuous fun t : ℝ => (-(π : ℂ) * (t : ℂ))).continuousOn.mul
      (hIntegrandC_continuousOn u0)).congr fun t _ => by
      simp [I₆IntegrandC_deriv, mul_assoc]).aestronglyMeasurable measurableSet_Ici
  let bound : ℝ → ℝ := fun t => (C₀ * Real.pi) * t * Real.exp (-(Real.pi * ε) * t)
  have hbound :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε, ‖I₆IntegrandC_deriv z t‖ ≤ bound t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht z hz => ?_
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have hzRe : ε ≤ z.re := by
      have habs := (abs_lt.mp (lt_of_le_of_lt
        (by simpa using abs_re_le_norm (z - u0) : |z.re - u0.re| ≤ ‖z - u0‖)
        (by simpa [Metric.mem_ball, dist_eq_norm] using hz : ‖z - u0‖ < ε))).1
      simp only [hε_def]; linarith
    have hnorm_int : ‖I₆IntegrandC z t‖ ≤ C₀ * Real.exp (-π * ε * t) :=
      (hIntegrand_le z t ht).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg Real.pi_pos.le ht0, hzRe])) hC₀_pos.le)
    calc ‖I₆IntegrandC_deriv z t‖
        = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖I₆IntegrandC z t‖ := by
          simp [I₆IntegrandC_deriv, mul_assoc]
      _ ≤ (Real.pi * t) * (C₀ * Real.exp (-π * ε * t)) := by
          gcongr; simp [Complex.norm_real, abs_of_nonneg ht0, abs_of_nonneg Real.pi_pos.le]
      _ = bound t := by simp [bound]; ring
  have hbound_int : MeasureTheory.Integrable bound μ := by
    have hb : 0 < Real.pi * ε := by positivity
    have hIoi1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * Real.exp (-(Real.pi * ε) * t)) (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
      ((by simpa [Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
          (hs := by linarith) (hp := le_rfl) (b := Real.pi * ε) hb) :
        MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-(Real.pi * ε) * t))
          (Set.Ioi (0:ℝ)) MeasureTheory.volume)).mono_set (Set.Ioi_subset_Ioi (by norm_num))
    simpa [bound, μ, MeasureTheory.IntegrableOn, mul_assoc] using
      (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun t : ℝ => (C₀ * Real.pi) * t * Real.exp (-(Real.pi * ε) * t))
        (b := (1 : ℝ)) (by finiteness)).2 (by simpa [mul_assoc] using hIoi1.const_mul (C₀ * Real.pi))
  have hdiff :
      ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball u0 ε,
        HasDerivAt (fun w : ℂ => I₆IntegrandC w t) (I₆IntegrandC_deriv z t) z :=
    Filter.Eventually.of_forall fun t z _ => by
      have hlin : HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))
      simpa [I₆IntegrandC_deriv, I₆IntegrandC, mul_assoc, mul_left_comm, mul_comm] using
        (by simpa using hlin.cexp : HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
          (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z).const_mul (base₆ t)
  have hμ : (fun z : ℂ => ∫ t, I₆IntegrandC z t ∂μ) =
      fun z : ℂ => ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC z t := funext fun _ => by simp [μ]
  exact (show HasDerivAt I₆'C (2 * ∫ t, I₆IntegrandC_deriv u0 t ∂μ) u0 by
    simpa [funext fun u => show I₆'C u = 2 * ∫ t in Set.Ici (1 : ℝ), I₆IntegrandC u t by
        simp [I₆'C, I₆IntegrandC, base₆, mul_assoc, mul_left_comm, mul_comm], mul_assoc] using
      (hμ ▸ (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := u0)
        (F := I₆IntegrandC) (F' := I₆IntegrandC_deriv) (bound := bound)
        (hs := Metric.ball_mem_nhds u0 hε) (hF_meas := Filter.Eventually.of_forall hF_meas)
        (hF_int := hF_int) (hF'_meas := hF'_meas)
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2).const_mul
      (2 : ℂ)).differentiableAt

/-- `aPrimeC` is analytic on the right half-plane. -/
public lemma aPrimeC_analyticOnNhd : AnalyticOnNhd ℂ aPrimeC rightHalfPlane :=
  (show DifferentiableOn ℂ aPrimeC rightHalfPlane by
    simpa [aPrimeC] using ((((I₁'C_differentiableOn.add I₂'C_differentiableOn).add
      I₃'C_differentiableOn).add I₄'C_differentiableOn).add
      I₅'C_differentiableOn).add (fun u hu =>
        (I₆'C_differentiableAt u hu).differentiableWithinAt)).analyticOnNhd rightHalfPlane_isOpen
end

end MagicFunction.g.CohnElkies.IntegralReps

namespace MagicFunction.g.CohnElkies

/--
For `u ≥ 0`, the radial profile `a'` from `MagicFunction.FourierEigenfunctions` agrees with the
real-integral definition `MagicFunction.a.RealIntegrals.a'`.

The prime `'` is part of the standard notation for this radial profile (it is not a derivative).
-/
public lemma a'_eq_realIntegrals_a' {u : ℝ} (hu : 0 ≤ u) :
    (MagicFunction.FourierEigenfunctions.a' : ℝ → ℂ) u = MagicFunction.a.RealIntegrals.a' u := by
  simp [MagicFunction.FourierEigenfunctions.a', MagicFunction.a.RealIntegrals.a',
    MagicFunction.a.SchwartzIntegrals.I₁'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₂'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₃'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₄'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₅'_apply_of_nonneg,
    MagicFunction.a.SchwartzIntegrals.I₆'_apply_of_nonneg, hu]

end MagicFunction.g.CohnElkies

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators Topology MatrixGroups CongruenceSubgroup ModularForm NNReal ENNReal
open scoped ArithmeticFunction.sigma

open Real Complex MeasureTheory Filter Function
open ArithmeticFunction

open MagicFunction.FourierEigenfunctions
open UpperHalfPlane ModularForm EisensteinSeries
open SlashInvariantFormClass ModularFormClass

noncomputable section

/-! ## Imaginary-axis helpers (merged from `Cancellation.ImagAxis`) -/

/-- The integrand used in the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrand (u t : ℝ) : ℂ :=
  ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
        ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
        ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
    Real.exp (-π * u * t))

/-- The "another integral" associated to `a'`, defined as `∫_{t>0} aAnotherIntegrand u t`. -/
@[expose] public def aAnotherIntegral (u : ℝ) : ℂ := ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t

/-- The point `it` in the upper half-plane. -/
@[expose] public def zI (t : ℝ) (ht : 0 < t) : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), by simpa using ht⟩

public lemma zI_im (t : ℝ) (ht : 0 < t) : (zI t ht).im = t := by simp [zI, UpperHalfPlane.im]

lemma qParam_zI (t : ℝ) (ht : 0 < t) :
    Periodic.qParam (1 : ℝ) (zI t ht) = (Real.exp (-2 * π * t) : ℂ) := by
  simp [Periodic.qParam, zI, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    show (Complex.I : ℂ) * (Complex.I * (↑t * (↑π * 2))) = -(↑t * (↑π * 2)) by ring_nf; simp]

public lemma imag_I_div (t : ℝ) : ((Complex.I : ℂ) / (t : ℂ)).im = t⁻¹ := by
  simp [Complex.div_im, Complex.normSq]

public lemma norm_ofReal_exp (x : ℝ) : ‖(Real.exp x : ℂ)‖ = Real.exp x := by simp

public lemma exp_neg_two_pi_lt_one : Real.exp (-2 * π) < 1 :=
  Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])

public lemma q_le_q1 {t : ℝ} (ht : 1 ≤ t) : Real.exp (-2 * π * t) ≤ Real.exp (-2 * π) :=
  Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-- Exponential decay bound for `φ₀'' (it)` on `t ≥ 1`. -/
public lemma norm_φ₀_imag_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖φ₀'' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ C * Real.exp (-2 * π * t) :=
  MagicFunction.PolyFourierCoeffBound.norm_φ₀_le.imp fun _ ⟨hCpos, hC⟩ =>
    ⟨hCpos, fun t ht => have ht0 := zero_lt_one.trans_le ht
      by simpa [show φ₀ (zI t ht0) = φ₀'' ((Complex.I : ℂ) * (t : ℂ)) by
          simpa [zI] using (φ₀''_def (z := (Complex.I : ℂ) * (t : ℂ)) (by simpa using ht0)).symm,
        zI_im] using hC (zI t ht0) (by linarith [zI_im t ht0])⟩

private lemma norm_cexp_mul_le_split {z : ℍ} {q q1 : ℝ} (hq_nonneg : 0 ≤ q) (hq_le : q ≤ q1)
    (hqC : (Periodic.qParam (1 : ℝ) z) = (q : ℂ)) (j k : ℕ) :
    ‖cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z)‖ ≤ q ^ j * q1 ^ k := by
  rw [show ‖cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z)‖ = q ^ (j + k) by
      rw [show cexp (2 * π * Complex.I * ((j + k : ℕ) : ℂ) * z) = (q : ℂ) ^ (j + k) by
        rw [← (by simpa [Periodic.qParam] using hqC : cexp (2 * π * Complex.I * z) = (q : ℂ))]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Complex.exp_nat_mul (2 * π * Complex.I * z) (j + k)]
      simp [abs_of_nonneg hq_nonneg], pow_add]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq_nonneg hq_le _) (pow_nonneg hq_nonneg _)

private lemma norm_mul_sigma_le (m M : ℕ) (hM : m ≤ M) :
    ‖((m : ℂ) * (σ 3 m : ℂ))‖ ≤ ((M : ℝ) ^ 5 : ℝ) := by
  exact_mod_cast (show m * (σ 3 m) ≤ m ^ 5 by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left m (sigma_bound 3 m)).trans
    (Nat.pow_le_pow_left hM 5)

lemma qExpansionFormalMultilinearSeries_partialSum_two
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (q : ℂ) :
    (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum 2 q =
      (qExpansion (1 : ℝ) f).coeff 0 + (qExpansion (1 : ℝ) f).coeff 1 * q := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum,
    Finset.sum_range_succ, mul_comm]

private lemma hΓ1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma (↑1)).strictPeriods := by simp
private def r0 : ℝ≥0 := ⟨Real.exp (-π), (Real.exp_pos _).le⟩

private lemma exists_sub_partialSum_bound
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : F)
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖f (zI t ht) -
          (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum n
            (Periodic.qParam (1 : ℝ) (zI t ht))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ n := by
  obtain ⟨a, ha, C, hCpos, hbound⟩ := (ModularFormClass.hasFPowerSeries_cuspFunction
    (f := f) (h := (1 : ℝ)) zero_lt_one hΓ).uniform_geometric_approx' (r' := r0) (by
      simpa using ENNReal.coe_lt_one_iff.2 (Real.exp_lt_one_iff.2 (neg_lt_zero.mpr Real.pi_pos)))
  refine ⟨C * (a / (r0 : ℝ)) ^ n,
    mul_pos hCpos (pow_pos (div_pos ha.1 (Real.exp_pos (-π))) _), fun t ht ht1 => ?_⟩
  let z : ℍ := zI t ht
  let q : ℂ := Periodic.qParam (1 : ℝ) z
  have hqn : ‖q‖ = Real.exp (-2 * π * t) := by
    simpa [q, z, zI, mul_comm, div_one] using
      Periodic.norm_qParam (h := (1 : ℝ)) (z := (zI t ht : ℂ))
  simpa [z, q, hqn] using
    (show ‖f z - (qExpansionFormalMultilinearSeries (h := (1 : ℝ)) f).partialSum n q‖ ≤
        (C * (a / (r0 : ℝ)) ^ n) * ‖q‖ ^ n by
      simpa [show cuspFunction (1 : ℝ) f q = f z by
          simpa [q] using SlashInvariantFormClass.eq_cuspFunction (f := f) (τ := z) hΓ one_ne_zero,
        show C * (a * (‖q‖ / r0)) ^ n = (C * (a / (r0 : ℝ)) ^ n) * ‖q‖ ^ n by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_pow]] using
        hbound q (by simpa [Metric.mem_ball, dist_zero_right, r0, q, z, hqn] using
          Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos, ht1])) n)

/-- Uniform bound `‖E₄ (it) - 1‖ = O(exp (-2πt))` valid for all `t ≥ 1`. -/
public lemma exists_E4_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖E₄ (zI t ht) - (1 : ℂ)‖ ≤ C * Real.exp (-2 * π * t) :=
  (exists_sub_partialSum_bound (f := E₄) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 4) hΓ1 1).imp
    fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
      simpa [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum, E4_q_exp_zero]
        using hC t ht0 ht1⟩

/-- Second-order remainder bound for `E₄ (it) - (1 + 240 q)` with `q = exp (-2π t)`, `t ≥ 1`. -/
public lemma exists_E4_sub_one_sub_240q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖E₄ (zI t ht) - ((1 : ℂ) + (240 : ℂ) * (Real.exp (-2 * π * t) : ℂ))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) :=
  (exists_sub_partialSum_bound (f := E₄) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 4) hΓ1 2).imp
    fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
      simpa [qExpansionFormalMultilinearSeries_partialSum_two (f := E₄), E4_q_exp_zero,
        E4_q_exp_one, qParam_zI t ht0] using hC t ht0 ht1⟩

private lemma Delta_q_exp_zero : (qExpansion 1 Delta).coeff 0 = (0 : ℂ) := by
  simp [ModularFormClass.qExpansion_coeff_zero (f := Delta) (h := (1 : ℝ)) zero_lt_one hΓ1,
    show valueAtInfty (Delta : ℍ → ℂ) = (0 : ℂ) by
      simpa using (ModularFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ))
        zero_lt_one hΓ1).symm.trans
        (CuspFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) zero_lt_one hΓ1)]

/-- Second-order remainder bound for `Δ (it) - q` with `q = exp (-2π t)`, `t ≥ 1`. -/
public lemma exists_Delta_sub_q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖Δ (zI t ht) - (Real.exp (-2 * π * t) : ℂ)‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) :=
  (exists_sub_partialSum_bound (f := Delta) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 12)
      hΓ1 2).imp fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries_partialSum_two (f := Delta), Delta_q_exp_zero,
      Delta_q_one_term, qParam_zI t ht0, Delta_apply] using hC t ht0 ht1⟩

/-- Third-order remainder bound for `Δ (it) - (q - 24 q²)` with `q = exp (-2π t)`, `t ≥ 1`. -/
public lemma exists_Delta_sub_q_sub_neg24_qsq_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖Δ (zI t ht) -
          ((Real.exp (-2 * π * t) : ℂ) + (-24 : ℂ) * ((Real.exp (-2 * π * t)) ^ (2 : ℕ) : ℂ))‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (3 : ℕ) :=
  (exists_sub_partialSum_bound (f := Delta) (Γ := CongruenceSubgroup.Gamma (↑1)) (k := 12)
      hΓ1 3).imp fun _ ⟨hCpos, hC⟩ => ⟨hCpos, fun t ht0 ht1 => by
    simpa [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.partialSum,
      Finset.sum_range_succ, mul_comm, Delta_q_exp_zero,
      Delta_q_one_term, Delta_q_exp_two, qParam_zI t ht0, Delta_apply] using hC t ht0 ht1⟩

/-- Second-order remainder bound for `E₂E₄ - E₆ - 720 q` with `q = exp (-2π t)`, `t ≥ 1`. -/
public lemma exists_E2E4_sub_E6_sub_720q_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (ht : 0 < t) → 1 ≤ t →
      ‖(E₂ (zI t ht)) * (E₄ (zI t ht)) - (E₆ (zI t ht)) -
            (720 : ℂ) * (Real.exp (-2 * π * t) : ℂ)‖ ≤
        C * (Real.exp (-2 * π * t)) ^ (2 : ℕ) := by
  let q1 : ℝ := Real.exp (-2 * π)
  have hq1_nonneg : 0 ≤ q1 := (Real.exp_pos _).le
  have hq1_lt_one : q1 < 1 := exp_neg_two_pi_lt_one
  let b : ℕ → ℝ := fun n => ((n + 2 : ℝ) ^ 5) * q1 ^ n
  have hb_summ : Summable b := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (512 : ℝ) * ((((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n))
      (g := b) (fun n => by positivity) (fun n => ?_) <| Summable.mul_left (512 : ℝ) <| by
        simpa [show (fun n : ℕ => (((n : ℝ) ^ 5 + 1) : ℝ) * q1 ^ n) =
            (fun n : ℕ => ((n : ℝ) ^ 5 : ℝ) * q1 ^ n) + fun n : ℕ => q1 ^ n by
          funext n; simp [add_mul]] using
          (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5
            (by simpa [Real.norm_of_nonneg hq1_nonneg] using hq1_lt_one)).add
            (summable_geometric_of_lt_one hq1_nonneg hq1_lt_one)
    have hbase := add_pow_le (a := (n : ℝ)) (b := (2 : ℝ)) (by positivity) (by positivity) 5
    simp only [show (5 - 1 : ℕ) = 4 from rfl] at hbase
    nlinarith [hbase, pow_nonneg (by positivity : (0 : ℝ) ≤ n) 5, pow_nonneg hq1_nonneg n]
  refine ⟨1 + (720 : ℝ) * (∑' n : ℕ, b n), by positivity, fun t ht0 ht1 => ?_⟩
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le : q ≤ q1 := q_le_q1 (t := t) ht1
  have hqC : (Periodic.qParam (1 : ℝ) z) = (q : ℂ) := by simpa [q, z] using qParam_zI t ht0
  let f : ℕ → ℂ := fun n =>
    ((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ)) * cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)
  have hf_le : ∀ n : ℕ, ‖f n‖ ≤ q ^ (2 : ℕ) * b n := fun n => by
    rw [show ‖f n‖ = ‖((n + 2 : ℂ) * (σ 3 (n + 2) : ℂ))‖ *
        ‖cexp (2 * π * Complex.I * (n + 2 : ℂ) * z)‖ by simp [f, mul_assoc],
      show q ^ (2 : ℕ) * b n = ((n + 2 : ℝ) ^ 5 : ℝ) * (q ^ (2 : ℕ) * q1 ^ n) by simp [b]; ring]
    gcongr
    · exact_mod_cast norm_mul_sigma_le (n + 2) (n + 2) le_rfl
    · simpa [show ((2 + n : ℕ) : ℂ) = (n : ℂ) + 2 by push_cast; ring] using
        norm_cexp_mul_le_split (z := z) hq_nonneg hq_le hqC 2 n
  have hqexp : cexp (2 * π * Complex.I * z) = (q : ℂ) := by simpa [Periodic.qParam] using hqC
  let g : ℕ → ℂ := fun n => (n + 1) * (σ 3 (n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z)
  have hg_summ : Summable g := .of_norm_bounded (hb_summ.mul_left q) fun n => by
    rw [show ‖g n‖ = ‖((n + 1 : ℂ) * (σ 3 (n + 1) : ℂ))‖ *
        ‖cexp (2 * π * Complex.I * (n + 1) * z)‖ by simp [g, mul_assoc],
      show q * b n = ((n + 2 : ℝ) ^ 5 : ℝ) * (q * q1 ^ n) by simp [b]; ring]
    gcongr
    · exact_mod_cast norm_mul_sigma_le (n + 1) (n + 2) (by omega)
    · simpa [pow_one, show ((1 + n : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring] using
        norm_cexp_mul_le_split (z := z) hq_nonneg hq_le hqC 1 n
  have hsplit :
      (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - cexp (2 * π * Complex.I * z) =
        ∑' n : ℕ, f n := by
    rw [show (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) = ∑' n : ℕ, g n from by
        simpa [g, mul_assoc, mul_left_comm, mul_comm] using tsum_pnat_eq_tsum_succ
          (f := fun n : ℕ => (n : ℂ) * (σ 3 n : ℂ) * cexp (2 * π * Complex.I * n * z)),
      show cexp (2 * π * Complex.I * z) = g 0 by simp [g],
      show (∑' n : ℕ, g n) = g 0 + ∑' n : ℕ, g (n + 1) by
        simpa [Finset.range_one] using (hg_summ.sum_add_tsum_nat_add 1).symm]
    grind only [tsum_eq_tsum_of_ne_zero_bij]
  have hnorm_summ : Summable (fun n : ℕ => ‖f n‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hf_le (hb_summ.mul_left (q ^ (2 : ℕ)))
  have hmain : ‖(E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)‖ ≤
      (720 : ℝ) * (q ^ (2 : ℕ)) * (∑' n : ℕ, b n) := by
    rw [show (E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ) = (720 : ℂ) * (∑' n : ℕ, f n) by
        rw [E₂_mul_E₄_sub_E₆ z,
          ← show (∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)) - (q : ℂ) =
            ∑' n : ℕ, f n by simpa [hqexp] using hsplit]
        ring,
      norm_mul, show ‖(720 : ℂ)‖ = 720 by simp, mul_assoc]
    gcongr; exact (norm_tsum_le_tsum_norm hnorm_summ).trans <|
      (hnorm_summ.tsum_le_tsum hf_le (hb_summ.mul_left _)).trans_eq tsum_mul_left
  refine (show _ ≤ ((720 : ℝ) * (∑' n : ℕ, b n)) * q ^ (2 : ℕ) by
      simpa [q, mul_assoc, mul_left_comm, mul_comm] using hmain).trans ?_
  simpa [z, q] using mul_le_mul_of_nonneg_right
    (by linarith : (720 : ℝ) * (∑' n : ℕ, b n) ≤ 1 + (720 : ℝ) * (∑' n : ℕ, b n))
    (pow_nonneg hq_nonneg _)

/-! ## Large-imaginary asymptotics (merged from `LargeImagApprox`) -/

/-- For large `t`, `φ₂' (it)` differs from `720` by `O(exp (-2π t))`. -/
public lemma exists_phi2'_sub_720_bound_ge :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ t : ℝ, (ht : 0 < t) → A ≤ t →
        ‖φ₂' (zI t ht) - (720 : ℂ)‖ ≤ C * Real.exp (-2 * π * t) := by
  rcases exists_inv_Delta_bound_exp with ⟨CΔinv, AΔ, hCΔinv_pos, hΔinv⟩
  rcases exists_E4_sub_one_bound with ⟨CE4, hCE4_pos, hE4⟩
  rcases exists_Delta_sub_q_bound with ⟨CΔq, hCΔq_pos, hΔq⟩
  rcases exists_E2E4_sub_E6_sub_720q_bound with ⟨CA, hCA_pos, hAq⟩
  let A : ℝ := max (1 : ℝ) AΔ
  let q1 : ℝ := Real.exp (-2 * π)
  let E4B : ℝ := 1 + CE4 * q1
  let C : ℝ := 1 + CΔinv * (E4B * CA + 720 * (CE4 + CΔq))
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C, A, by positivity, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hE4sub : ‖E₄ z - (1 : ℂ)‖ ≤ CE4 * q := by simpa [z, q] using hE4 t ht0 ht1
  have hE4norm : ‖E₄ z‖ ≤ E4B := by
    simp only [E4B]; linarith [hE4sub.trans (mul_le_mul_of_nonneg_left hq_le_q1 hCE4_pos.le),
      show ‖E₄ z‖ ≤ ‖E₄ z - (1 : ℂ)‖ + 1 from by simpa using norm_add_le (E₄ z - (1 : ℂ)) 1]
  have hΔerr : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ) := by
    simpa [z, q] using hΔq t ht0 ht1
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    simpa [z, zI_im t ht0] using hΔinv z
      (by simpa [z, zI_im t ht0] using (le_max_right _ _ : AΔ ≤ A).trans htA)
  have hE4qΔ : ‖E₄ z * (q : ℂ) - Δ z‖ ≤ (CE4 + CΔq) * q ^ (2 : ℕ) := by
    have h1 : ‖(E₄ z - (1 : ℂ)) * (q : ℂ)‖ ≤ CE4 * q ^ (2 : ℕ) := by
      rw [norm_mul, show ‖(q : ℂ)‖ = q from by simp [abs_of_nonneg hq_nonneg], pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hE4sub hq_nonneg
    calc ‖E₄ z * (q : ℂ) - Δ z‖
          = ‖(E₄ z - (1 : ℂ)) * (q : ℂ) + ((q : ℂ) - Δ z)‖ := by congr 1; ring
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ _ := by linarith [show ‖(q : ℂ) - Δ z‖ ≤ CΔq * q ^ (2 : ℕ) from by
                    simpa [norm_sub_rev] using hΔerr]
  have hrew : φ₂' z - (720 : ℂ) =
      ((E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)) / (Δ z) := by
    dsimp [φ₂']; field_simp [Δ_ne_zero z]
  have hnum :
      ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ ≤
        (E4B * CA + 720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
    have hB : ‖(720 : ℂ) * (E₄ z * (q : ℂ) - Δ z)‖ ≤ (720 * (CE4 + CΔq)) * q ^ (2 : ℕ) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [mul_le_mul_of_nonneg_left hE4qΔ (by norm_num : (0:ℝ) ≤ 720)]
    calc ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖
          = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z) - (720 : ℂ) * (q : ℂ)) +
              (720 : ℂ) * (E₄ z * (q : ℂ) - Δ z)‖ := by congr 1; ring
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_mul_le_of_le hE4norm (hAq t ht0 ht1)]
  have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
    simp only [q]; rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have : ‖φ₂' z - (720 : ℂ)‖ ≤ (CΔinv * (E4B * CA + 720 * (CE4 + CΔq))) * q := by
    set K : ℝ := E4B * CA + 720 * (CE4 + CΔq)
    calc ‖φ₂' z - (720 : ℂ)‖
          = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) - (720 : ℂ) * (Δ z)‖ * ‖(Δ z)⁻¹‖ := by
              simp [hrew, div_eq_mul_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) := mul_le_mul
            (by simpa [K] using hnum) hΔinv' (norm_nonneg _) (by positivity)
      _ = (CΔinv * K) * q := by linear_combination (CΔinv * K) * hq2
  exact this.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq_nonneg)

lemma norm_base_add_e_sq_sub_one_sub_480q_le
    {q CE4 B240 : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) {e : ℂ}
    (he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ))
    (hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240) :
    ‖((((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e) ^ (2 : ℕ) -
          ((1 : ℂ) + (480 : ℂ) * (q : ℂ)))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
  set b : ℂ := (1 : ℂ) + (240 : ℂ) * (q : ℂ)
  set t : ℂ := (1 : ℂ) + (480 : ℂ) * (q : ℂ)
  have hB240 : 0 ≤ B240 := (norm_nonneg _).trans hbase_norm
  have hbase2 : ‖b ^ (2 : ℕ) - t‖ ≤ (240 ^ 2 : ℝ) * q ^ (2 : ℕ) := by
    rw [show b ^ (2 : ℕ) - t = (240 ^ 2 : ℂ) * (q : ℂ) ^ (2 : ℕ) by simp [b, t]; ring]; simp
  have hlin : ‖(2 : ℂ) * b * e‖ ≤ (2 * B240 * CE4) * q ^ (2 : ℕ) := by
    rw [show ‖(2 : ℂ) * b * e‖ = 2 * ‖b‖ * ‖e‖ by simp [mul_assoc]]
    nlinarith [mul_le_mul hbase_norm he (norm_nonneg _) hB240, norm_nonneg b, norm_nonneg e]
  have hquad : ‖e ^ (2 : ℕ)‖ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := by
    rw [show ‖e ^ (2 : ℕ)‖ = ‖e‖ ^ (2 : ℕ) by simp [norm_pow]]
    calc ‖e‖ ^ (2 : ℕ) ≤ (CE4 * q ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) he _
      _ = (CE4 ^ 2) * q ^ (4 : ℕ) := by ring
      _ ≤ (CE4 ^ 2) * q ^ (2 : ℕ) := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hq_nonneg hq_le_one (by decide)) (sq_nonneg _)
  have heq : (b + e) ^ (2 : ℕ) - t = (b ^ (2 : ℕ) - t) + (2 : ℂ) * b * e + e ^ (2 : ℕ) := by ring
  linarith [heq ▸ norm_add₃_le (a := b ^ (2 : ℕ) - t) (b := (2 : ℂ) * b * e) (c := e ^ (2 : ℕ))]

lemma phi4_numerator_bound
    {t q : ℝ} {z : ℍ} {B240 CE4 CΔ3 CΔq : ℝ}
    (hE4sq : ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ))
    (hExpΔ : ‖(Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤
        CΔ3 * q ^ (2 : ℕ))
    (hΔ2err : ‖Δ z - (q : ℂ)‖ ≤ CΔq * q ^ (2 : ℕ)) :
    ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq) * q ^ (2 : ℕ) := by
  set qC : ℂ := (q : ℂ)
  set A : ℂ := (E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * qC)
  set B : ℂ := (Real.exp (2 * π * t) : ℂ) * (Δ z) - ((1 : ℂ) + (-24 : ℂ) * qC)
  set C : ℂ := (504 : ℂ) * (Δ z - qC)
  have hterm3 : ‖C‖ ≤ (504 * CΔq) * q ^ (2 : ℕ) := by
    rw [show ‖C‖ = 504 * ‖Δ z - qC‖ by simp [C]]; nlinarith [hΔ2err]
  calc ‖(E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)‖
        = ‖A - B - C‖ := by simp only [A, B, C]; ring_nf
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := (norm_sub_le _ C).trans (by linarith [norm_sub_le A B])
    _ ≤ _ := by linarith

/-- For large `t`, `φ₄' (it)` differs from `exp (2π t) + 504` by `O(exp (-2π t))`. -/
public lemma exists_phi4'_sub_exp_sub_504_bound_ge :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ t : ℝ, ∀ ht : 0 < t, A ≤ t →
        ‖φ₄' (zI t ht) - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤
          C * Real.exp (-2 * π * t) := by
  rcases exists_inv_Delta_bound_exp with ⟨CΔinv, AΔ, hCΔinv_pos, hΔinv⟩
  rcases exists_E4_sub_one_sub_240q_bound with ⟨CE4, hCE4_pos, hE4⟩
  rcases exists_Delta_sub_q_bound with ⟨CΔq, hCΔq_pos, hΔq⟩
  rcases exists_Delta_sub_q_sub_neg24_qsq_bound with ⟨CΔ3, hCΔ3_pos, hΔ3⟩
  let A : ℝ := max (1 : ℝ) AΔ
  let q1 : ℝ := Real.exp (-2 * π)
  let B240 : ℝ := 1 + 240 * q1
  let C : ℝ := 1 + CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C, A, by positivity, hA1, ?_⟩
  intro t ht0 htA
  have ht1 : 1 ≤ t := le_trans hA1 htA
  let z : ℍ := zI t ht0
  let q : ℝ := Real.exp (-2 * π * t)
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_q1 : q ≤ q1 := by simpa [q, q1] using q_le_q1 (t := t) ht1
  have hq_le_one : q ≤ 1 :=
    hq_le_q1.trans (by simpa [q1] using exp_neg_two_pi_lt_one.le)
  have hΔinv' : ‖(Δ z)⁻¹‖ ≤ CΔinv * Real.exp (2 * π * t) := by
    simpa [z, zI_im t ht0] using hΔinv z
      (by simpa [z, zI_im t ht0] using (le_max_right _ _ : AΔ ≤ A).trans htA)
  have hE4err : ‖E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ CE4 * q ^ (2 : ℕ) := by
    simpa [z, q] using hE4 t ht0 ht1
  have hE4sq :
      ‖(E₄ z) ^ (2 : ℕ) - ((1 : ℂ) + (480 : ℂ) * (q : ℂ))‖ ≤
        ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2) * q ^ (2 : ℕ) := by
    set e : ℂ := E₄ z - ((1 : ℂ) + (240 : ℂ) * (q : ℂ))
    have he : ‖e‖ ≤ CE4 * q ^ (2 : ℕ) := by simpa [e, sub_eq_add_neg, add_assoc] using hE4err
    have hE : E₄ z = ((1 : ℂ) + (240 : ℂ) * (q : ℂ)) + e := by
      simp [e, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hbase_norm : ‖((1 : ℂ) + (240 : ℂ) * (q : ℂ))‖ ≤ B240 := by
      have := norm_add_le ((1 : ℂ)) ((240 : ℂ) * (q : ℂ))
      simp [abs_of_nonneg hq_nonneg, B240] at this ⊢; linarith [hq_le_q1]
    simpa [hE.symm] using norm_base_add_e_sq_sub_one_sub_480q_le (q := q) (CE4 := CE4)
      (B240 := B240) hq_nonneg hq_le_one he hbase_norm
  have hΔ3err : ‖Δ z - ((q : ℂ) + (-24 : ℂ) * ((q : ℂ) ^ (2 : ℕ)))‖ ≤ CΔ3 * q ^ (3 : ℕ) := by
    simpa [z, q, pow_two] using hΔ3 t ht0 ht1
  have hExpq : (Real.exp (2 * π * t)) * q = 1 := by rw [← Real.exp_add]; simp
  have hExpΔ :
      ‖(Real.exp (2 * π * t) : ℂ) * Δ z - ((1 : ℂ) + (-24 : ℂ) * (q : ℂ))‖ ≤ CΔ3 * q ^ (2 : ℕ) := by
    set E : ℂ := (Real.exp (2 * π * t) : ℂ)
    set qC : ℂ := (q : ℂ)
    set approx : ℂ := qC + (-24 : ℂ) * (qC ^ (2 : ℕ))
    have hExpqC : E * qC = (1 : ℂ) := by
      simpa [E, qC, Complex.ofReal_mul] using congrArg (fun x : ℝ => (x : ℂ)) hExpq
    rw [show E * Δ z - ((1 : ℂ) + (-24 : ℂ) * qC) = E * (Δ z - approx) by
        simp only [approx, mul_sub, mul_add]
        linear_combination hExpqC + (-24 : ℂ) * (qC * hExpqC),
      norm_mul, show ‖E‖ = Real.exp (2 * π * t) from norm_ofReal_exp _]
    calc Real.exp (2*π*t) * ‖Δ z - approx‖
        ≤ Real.exp (2*π*t) * (CΔ3 * q ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left
            (by simpa [approx, qC] using hΔ3err) (Real.exp_pos _).le
      _ = CΔ3 * q ^ (2 : ℕ) := by linear_combination CΔ3 * (q ^ 2 * hExpq)
  have hrew : φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ) =
      ((E₄ z) ^ (2 : ℕ) - (Real.exp (2 * π * t) : ℂ) * (Δ z) - (504 : ℂ) * (Δ z)) / (Δ z) := by
    dsimp [φ₄']; field_simp [Δ_ne_zero z]
  have hq2 : q ^ (2 : ℕ) * Real.exp (2 * π * t) = q := by
    simp only [q]; rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have : ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤
      (CΔinv * ((240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq)) * q := by
    set K : ℝ := (240 ^ 2 : ℝ) + 2 * B240 * CE4 + CE4 ^ 2 + CΔ3 + 504 * CΔq
    calc ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖
          = ‖(E₄ z)^2 - (Real.exp (2*π*t) : ℂ) * Δ z - (504:ℂ) * Δ z‖ * ‖(Δ z)⁻¹‖ := by
            rw [hrew, norm_div, div_eq_mul_inv, norm_inv]
      _ ≤ (K * q ^ (2 : ℕ)) * (CΔinv * Real.exp (2 * π * t)) := mul_le_mul
          (phi4_numerator_bound hE4sq hExpΔ (hΔq t ht0 ht1)) hΔinv' (norm_nonneg _) (by positivity)
      _ = (CΔinv * K) * q := by linear_combination (CΔinv * K) * hq2
  exact this.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq_nonneg)

/-! ## Integrability of `AnotherIntegral.A` integrand -/

private lemma continuousOn_phi0''_Idiv {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) s :=
  ((by simpa [upperHalfPlaneSet] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
    ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im})).comp
    (continuous_const.continuousOn.div continuous_ofReal.continuousOn
      fun t ht => mod_cast (hs t ht).ne')
    fun t ht => by simpa [imag_I_div] using inv_pos.2 (hs t ht)

private def cancelExpr (t : ℝ) : ℂ :=
  ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
    ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)

lemma exists_phi0_cancellation_bound :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
        ‖cancelExpr t‖ ≤ C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
  rcases norm_φ₀_imag_le with ⟨C₀, hC₀pos, hφ₀⟩
  rcases exists_phi2'_sub_720_bound_ge with ⟨C₂, A₂, hC₂pos, hA₂, hφ₂⟩
  rcases exists_phi4'_sub_exp_sub_504_bound_ge with ⟨C₄, A₄, hC₄pos, hA₄, hφ₄⟩
  let A : ℝ := max A₂ A₄
  have hrewrite :
      ∀ {t : ℝ} (ht0 : 0 < t),
        cancelExpr t =
          (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (zI t ht0) -
              ((12 / π : ℝ) : ℂ) * t * (φ₂' (zI t ht0) - (720 : ℂ)) +
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                (φ₄' (zI t ht0) - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))) := by
    intro t ht0
    let z : ℍ := zI t ht0
    have hzsq : (z : ℂ) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
      dsimp [z, zI]; push_cast; simp [mul_pow]
    have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by
      rw [show ModularGroup.S • z = zI t⁻¹ (inv_pos.2 ht0) by
        ext1; simpa [zI, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using
          ModularGroup.coe_S_smul (z := zI t ht0)]
      simp [zI, div_eq_mul_inv]
    have hST' :
        ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (ModularGroup.S • z) =
          ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
            ((12 / π : ℝ) : ℂ) * t * φ₂' z +
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * φ₄' z := by
      have hneg' : (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
          (t : ℂ) * ((t : ℂ) * φ₀ z) +
            (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z +
              (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ))) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
          mul_comm, pow_two, neg_add, neg_mul, mul_neg, neg_neg] using congrArg (fun w : ℂ => -w)
          (show φ₀ (ModularGroup.S • z) * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) =
              φ₀ z * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) + (-( (12 * Complex.I) / π * (z : ℂ) * φ₂' z)) +
              (-(36 / (π ^ 2) * φ₄' z)) by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, hzsq]
              using φ₀_S_transform_mul_sq z)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm, pow_two] using
        (by simpa [show (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ)) =
            -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z)) by dsimp [z, zI]; ring_nf; simp] using hneg' :
          (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
            (t : ℂ) * ((t : ℂ) * φ₀ z) +
              (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z + -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z))))
    have hSTpow :
        (↑t ^ (2 : ℕ)) * φ₀'' (Complex.I / ↑t) =
          (↑t ^ (2 : ℕ)) * φ₀ z - (12 / (π : ℂ)) * (t : ℂ) * φ₂' z +
            (36 / (π : ℂ) ^ (2 : ℕ)) * φ₄' z := by
      simpa [show φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • z) by
        simpa using congrArg φ₀'' hcoe.symm] using hST'
    unfold cancelExpr; push_cast; linear_combination hSTpow
  let Clarge : ℝ := C₀ + (12 / π) * C₂ + (36 / (π ^ (2 : ℕ))) * C₄
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → t ≤ A → ‖cancelExpr t‖ ≤ M := by
    obtain ⟨t₀, _, ht₀max⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (1 : ℝ) A)
      ⟨1, le_rfl, hA₂.trans (le_max_left _ _)⟩
      (show ContinuousOn (fun t => ‖cancelExpr t‖) (Set.Icc (1 : ℝ) A) by
        simpa [cancelExpr] using (((((by fun_prop :
          ContinuousOn (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)) (Set.Icc (1 : ℝ) A)).mul
          (continuousOn_phi0''_Idiv fun t ht => lt_of_lt_of_le (by norm_num) ht.1)).sub
          (by fun_prop)).add (by fun_prop)).sub (by fun_prop)).norm)
    exact ⟨_, fun t ht1 htA => (isMaxOn_iff.mp ht₀max) t ⟨ht1, htA⟩⟩
  let C : ℝ := max Clarge (M / Real.exp (-2 * π * A))
  refine ⟨C, fun t ht1 => ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  by_cases htA : A ≤ t
  · let z : ℍ := zI t ht0
    have hφ₀z : ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * t) := by
      simpa [show φ₀'' ((Complex.I : ℂ) * (t : ℂ)) = φ₀ z by
        simpa [z, zI] using (φ₀''_coe_upperHalfPlane z)] using hφ₀ t ht1
    have hφ₂z : ‖φ₂' z - (720 : ℂ)‖ ≤ C₂ * Real.exp (-2 * π * t) := by
      simpa [z] using hφ₂ t ht0 ((le_max_left _ _).trans htA)
    have hφ₄z : ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤ C₄ * Real.exp (-2 * π * t) := by
      simpa [z] using hφ₄ t ht0 ((le_max_right _ _).trans htA)
    have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hle_t : t ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hexp0 : 0 ≤ Real.exp (-2 * π * t) := (Real.exp_pos _).le
    have hnorm1 : ‖((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z‖ ≤
        C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hφ₀z, hC₀pos, norm_nonneg (φ₀ z), hexp0]
    have hnorm2 :
        ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖ ≤
          ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      calc ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖
          = (12 / π) * t * ‖φ₂' z - (720 : ℂ)‖ := by
            simp [mul_assoc, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ht0.le, abs_of_pos Real.pi_pos]
        _ ≤ (12 / π) * t * (C₂ * Real.exp (-2 * π * t)) := by gcongr
        _ ≤ ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
            nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_t
              (mul_nonneg hC₂pos.le hexp0)) (show (0 : ℝ) ≤ 12 / π by positivity)]
    have hnorm3 :
        ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖ ≤
          ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      calc ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖
          = (36 / (π ^ (2 : ℕ))) * ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ := by
            simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (36 / (π ^ (2 : ℕ))) * (C₄ * Real.exp (-2 * π * t)) := by gcongr
        _ ≤ ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
            nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht2
              (mul_nonneg hC₄pos.le hexp0)) (show (0 : ℝ) ≤ 36 / (π ^ (2 : ℕ)) by positivity)]
    have htri : ‖cancelExpr t‖ ≤ Clarge * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
      set x : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z
      set y : ℂ := ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))
      set z' : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
        (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))
      rw [show cancelExpr t = x - y + z' by simpa [x, y, z'] using hrewrite ht0]
      refine (((norm_add_le _ _).trans (by linarith [norm_sub_le x y, norm_nonneg z'])).trans
        (add_le_add_three hnorm1 hnorm2 hnorm3)).trans ?_
      dsimp [Clarge]; nlinarith [hexp0, sq_nonneg t]
    exact htri.trans (by gcongr; exact le_max_left _ _)
  · have hbound := hM t ht1 (le_of_not_ge htA)
    have hscale : M ≤ (M / Real.exp (-2 * π * A)) * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) := by
      simpa [show (M / Real.exp (-2 * π * A)) * Real.exp (-2 * π * A) = M by
        field_simp [Real.exp_ne_zero]] using mul_le_mul_of_nonneg_left
        ((Real.exp_le_exp.2 <| mul_le_mul_of_nonpos_left (le_of_not_ge htA)
          (by nlinarith [Real.pi_pos])).trans <| by
          simpa using mul_le_mul_of_nonneg_right (by nlinarith [ht1] : (1 : ℝ) ≤ t ^ (2 : ℕ))
            (Real.exp_pos _).le : Real.exp (-2 * π * A) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t))
        (div_nonneg (le_trans (norm_nonneg _) hbound) (Real.exp_pos (-2 * π * A)).le)
    nlinarith [hbound, hscale, mul_le_mul_of_nonneg_right (le_max_right Clarge _ : _ ≤ C)
      (by positivity : (0 : ℝ) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t))]

private lemma continuousOn_aAnotherIntegrand_of_subset_Ioi
    {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) (u : ℝ) :
    ContinuousOn (fun t : ℝ => aAnotherIntegrand u t) s :=
  ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
    (continuousOn_phi0''_Idiv hs)).sub (by fun_prop) |>.add (by fun_prop)).sub (by fun_prop)).mul
      (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-π * u * t)) : ℂ)).continuousOn

lemma aAnotherIntegrand_integrableOn_Ioc {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨Cφ₀, hCφ₀_pos, hCφ₀⟩
  refine MeasureTheory.IntegrableOn.of_bound (by simp : (volume : Measure ℝ) (Set.Ioc 0 1) < ⊤)
    ((continuousOn_aAnotherIntegrand_of_subset_Ioi (fun t ht => ht.1) u).aestronglyMeasurable
      measurableSet_Ioc) (Cφ₀ + ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
        ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_))
  have him_pos : 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im := by
    simpa [imag_I_div] using inv_pos.2 ht.1
  let z : ℍ := ⟨(Complex.I : ℂ) / (t : ℂ), him_pos⟩
  have hzHalf : (1 / 2 : ℝ) < z.im := by
    linarith [(by simpa [z, UpperHalfPlane.im, imag_I_div] using (one_le_inv₀ ht.1).2 ht.2 :
      (1 : ℝ) ≤ z.im)]
  have hφ0'' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ₀ := by
    simpa [show φ₀ z = φ₀'' ((Complex.I : ℂ) / (t : ℂ)) by
      simpa [z] using (φ₀''_def (z := (Complex.I : ℂ) / (t : ℂ)) him_pos).symm] using
      (hCφ₀ z hzHalf).trans
        (by simpa using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2
          (by nlinarith [Real.pi_pos, (z.2).le])) hCφ₀_pos.le)
  have ht2_le : (t ^ (2 : ℕ) : ℝ) ≤ 1 := by nlinarith [ht.1.le, ht.2]
  have hbr : ‖cancelExpr t‖ ≤
      (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
        ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
        ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by
    unfold cancelExpr
    set A : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))
    set B : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t)
    set Cc : ℂ := ((8640 / π : ℝ) : ℂ) * t
    set D : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
    have ht2nn : (0 : ℝ) ≤ t ^ (2 : ℕ) := by positivity
    have hA : ‖A‖ ≤ (t ^ (2 : ℕ) : ℝ) * Cφ₀ := by
      simpa [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht2nn]
        using mul_le_mul_of_nonneg_left hφ0'' ht2nn
    have hB : ‖B‖ ≤ ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) := by
      rw [show ‖B‖ = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π * t) by
        simp [-Complex.ofReal_exp, B]]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht.2])) (norm_nonneg _)
    have hC : ‖Cc‖ ≤ ‖((8640 / π : ℝ) : ℂ)‖ := by
      simpa [Cc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le] using
        mul_le_mul_of_nonneg_left ht.2 (norm_nonneg ((8640 / π : ℝ) : ℂ))
    linarith [((show ‖A - B + Cc - D‖ = ‖(A - B) + (Cc - D)‖ by ring_nf).le.trans
      (norm_add_le _ _)).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))]
  have hmul : ‖aAnotherIntegrand u t‖ ≤ ‖cancelExpr t‖ := by
    simpa [cancelExpr, aAnotherIntegrand, norm_mul, mul_assoc] using mul_le_mul_of_nonneg_left
      (by rw [norm_ofReal_exp]; exact Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hu.le) ht.1.le]) :
        ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1) (norm_nonneg _)
  nlinarith [hmul.trans hbr, mul_le_mul_of_nonneg_right ht2_le hCφ₀_pos.le]

/-- For `u > 0`, the function `t ↦ aAnotherIntegrand u t` is integrable on `(0, ∞)`. -/
public lemma aAnotherIntegrand_integrable_of_pos {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ici_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_lt_one]
  refine (aAnotherIntegrand_integrableOn_Ioc hu).union ?_
  rcases exists_phi0_cancellation_bound with ⟨C, hC⟩
  have hbound : ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) → ‖aAnotherIntegrand u t‖ ≤
      C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) := fun t ht => by
    rw [show C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) =
      (C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) by
        rw [mul_assoc (C * _), ← Real.exp_add]; ring_nf]
    simpa [-Complex.ofReal_exp, cancelExpr, aAnotherIntegrand, mul_assoc, mul_left_comm,
        mul_comm] using mul_le_mul_of_nonneg_right (hC t ht) (Real.exp_pos (-π * u * t)).le
  have hdom :
      IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
        (Set.Ici (1 : ℝ)) := by
    simpa [mul_assoc] using (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
      (n := 2) (b := 2 * π + π * u) (by positivity)).const_mul C
  exact MeasureTheory.Integrable.mono' hdom.integrable
    ((continuousOn_aAnotherIntegrand_of_subset_Ioi
      (fun t ht => lt_of_lt_of_le (by norm_num) ht) u).aestronglyMeasurable measurableSet_Ici)
    ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall hbound))

end

section LaplaceRepresentation

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrals MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

local notation "c12π" => ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/-! ## Tail deformation -/

/-- Strip-bound core: bound `‖F (x + tI)‖` by the standard envelope when
`F (x + tI) = (φ₀''(-1/w) * w²) * exp(πIu(x + tI))` with `w = s + tI`, `|s| ≤ 1`. -/
private lemma norm_strip_le_of_hdef {u s t x : ℝ} {F : ℂ → ℂ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hs : |s| ≤ (1 : ℝ)) (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t)
    (hdef : F ((x : ℂ) + (t : ℂ) * Complex.I) =
      (φ₀'' ((-1 : ℂ) / (((s : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
        ((((s : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (2 : ℕ))) *
          cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))) :
    ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  let wH : ℍ := ⟨((s : ℝ) : ℂ) + (t : ℂ) * Complex.I, by simpa using by linarith⟩
  have hw_im : (wH : ℂ).im = t := by simp [wH]
  calc ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
          rw [hdef, show φ₀'' ((-1 : ℂ) / (wH : ℂ)) * ((wH : ℂ) ^ 2) =
              φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) by
            rw [show φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
              show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
                simpa using ModularGroup.coe_S_smul (z := wH)], norm_mul,
            show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))‖ =
                Real.exp (-π * u * t) by
              rw [show ((π : ℂ) * Complex.I * (u : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)) =
                  ((π * u * x : ℝ) : ℂ) * Complex.I - ((π * u * t : ℝ) : ℂ) by
                push_cast; ring_nf; simp [mul_left_comm, mul_comm, sub_eq_add_neg],
                Complex.norm_exp]
              simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
          mul_le_mul_of_nonneg_right (norm_phi0S_mul_sq_le wH hw_im hC₀_pos hC₀ hφbd ht1 htAφ <| by
            simp only [wH]
            linarith [norm_add_le ((s : ℝ) : ℂ) ((t : ℂ) * Complex.I),
              (by simpa [Complex.norm_real] using hs : ‖((s : ℝ) : ℂ)‖ ≤ (1 : ℝ)),
              (by simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ t)] :
                ‖(t : ℂ) * Complex.I‖ = t)]) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
          rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Top-edge decay: reduce `tendsto` of an interval integral to a pointwise strip bound. -/
private lemma tendsto_intervalIntegral_top_of_strip_bound {u : ℝ} (hu : 2 < u) {F : ℂ → ℂ}
    {x₁ x₂ : ℝ} (hlen : |x₂ - x₁| ≤ 1)
    (hF : ∀ Cφ Aφ C₀ x t : ℝ, 0 < C₀ →
      (∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im)) →
      (∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im)) →
      x ∈ Set.uIoc x₁ x₂ → (1 : ℝ) ≤ t → Aφ ≤ t →
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
          (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t))) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, F ((x : ℂ) + (m : ℂ) * Complex.I)) atTop (𝓝 0) := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  set a : ℝ := π * (u - 2)
  have ha : 0 < a := mul_pos Real.pi_pos (sub_pos.2 hu)
  refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨max 1 Aφ, fun m hm => ?_⟩) (by
    simpa [mul_zero] using tendsto_const_nhds.mul
      (by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (2 : ℝ)) (b := a) ha :
        Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-a * t)) atTop (𝓝 0)) :
      Tendsto (fun m : ℝ => K * (m ^ (2 : ℕ) * Real.exp (-a * m))) atTop (𝓝 0))
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := x₁) (b := x₂)
    (C := K * (m ^ (2 : ℕ) * Real.exp (-a * m)))
    (fun x hx => hF Cφ Aφ C₀ x m hC₀_pos hC₀ hφbd hx ((le_max_left _ _).trans hm)
      ((le_max_right _ _).trans hm))).trans ?_
  nlinarith [hlen, show 0 ≤ K * (m ^ (2 : ℕ) * Real.exp (-a * m)) by positivity]

private lemma tendsto_intervalIntegral_Φ₂'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := -1) (x₂ := 0) (by norm_num)
    fun _ _ _ x t h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (-1 : ℝ) 0 := Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0) ▸ hx
      norm_strip_le_of_hdef (s := x + 1) (F := Φ₂' u) h1 h2 h3
        (by rw [abs_of_nonneg (by linarith [hx'.1.le] : (0:ℝ) ≤ x + 1)]; linarith [hx'.2])
        h4 h5 <| by
        simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
          show (x : ℂ) + (t : ℂ) * Complex.I + 1 = ((x + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by
            push_cast; ring, mul_assoc]

private lemma tendsto_intervalIntegral_Φ₄'_top {u : ℝ} (hu : 2 < u) :
    Tendsto (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0) :=
  tendsto_intervalIntegral_top_of_strip_bound hu (x₁ := 1) (x₂ := 0) (by norm_num)
    fun _ _ _ x t h1 h2 h3 hx h4 h5 =>
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_ge (by norm_num : (0:ℝ) ≤ 1) ▸ hx
      norm_strip_le_of_hdef (s := x - 1) (F := Φ₄' u) h1 h2 h3
        (by rw [abs_sub_comm, abs_of_nonneg (by linarith [hx'.2] : (0:ℝ) ≤ 1 - x)]
            linarith [hx'.1.le]) h4 h5 <| by
        simp [MagicFunction.a.ComplexIntegrands.Φ₄', MagicFunction.a.ComplexIntegrands.Φ₃',
          show (x : ℂ) + (t : ℂ) * Complex.I - 1 = ((x - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by
            push_cast; ring, mul_assoc]

private lemma bottom_eq_I_smul_sub_of_rect_deform {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (hcontU : ContinuousOn f {z : ℂ | 0 < z.im})
    (hdiffU : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hint₁ : IntegrableOn (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) volume)
    (hint₂ : IntegrableOn (fun t : ℝ => f ((x₂ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (1 : ℝ)) volume)
    (htop : Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f ((x : ℂ) + Complex.I)) =
      (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), f ((x₂ : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa [smul_eq_mul, mul_sub, one_mul] using eq_sub_of_add_eq (by
    simpa [one_mul] using sub_eq_zero.mp <| Complex.rect_deform_of_tendsto_top (f := f)
      (x₁ := x₁) (x₂ := x₂) (y := (1 : ℝ))
      (hcontU.mono fun z hz => show 0 < z.im from lt_of_lt_of_le zero_lt_one
        (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ici (1 : ℝ)).2)
      (fun z hz =>
        have hz0 : 0 < z.im :=
          lt_trans zero_lt_one (by simpa [mem_reProdIm] using hz : _ ∧ z.im ∈ Set.Ioi (1 : ℝ)).2
        (hdiffU z hz0).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz0))
      hint₁ hint₂ htop)

lemma I₂'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₂' u = (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  have hΦ₁' := Φ₁'_contDiffOn_ℂ (r := u)
  rw [show I₂' u = ∫ x in (-1 : ℝ)..0, g x by
    dsimp [I₂', Φ₂]
    rw [show (∫ t in (0 : ℝ)..1, Φ₂' u (z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) from intervalIntegral.integral_congr fun t ht => by
          simp [g, show z₂' t = (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) by
            simpa using z₂'_eq_of_mem (by simpa [Set.uIcc_of_le zero_le_one] using ht), add_comm],
      show (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x by norm_num]]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₂' u)
    (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ)) hΦ₁'.continuousOn (hΦ₁'.differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I)
        from funext fun t => Φ₁'_shift_left (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₂'_imag_axis hu) (tendsto_intervalIntegral_Φ₂'_top hu)

lemma I₄'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₄' u = (Complex.I : ℂ) •
        ((∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  have hΦ₃' := Φ₃'_contDiffOn_ℂ (r := u)
  rw [show I₄' u = ∫ x in (1 : ℝ)..0, g x by
    dsimp [I₄', Φ₄]
    rw [show (∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (z₄' t)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) from
      intervalIntegral.integral_congr fun t ht => by
        simp [g, sub_eq_add_neg, show z₄' t = (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) by
          simpa using z₄'_eq_of_mem (t := t) (by simpa [Set.uIcc_of_le zero_le_one] using ht)],
      intervalIntegral.integral_const_mul,
      show (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t by norm_num]
    simpa using (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm]
  simpa [zero_add] using bottom_eq_I_smul_sub_of_rect_deform (f := Φ₄' u)
    (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ)) hΦ₃'.continuousOn (hΦ₃'.differentiableOn (by simp))
    (by simpa [show (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I)
        from funext fun t => Φ₃'_shift_right (u := u) (t := t)]
      using (integrableOn_Φ₅'_imag_axis hu).const_mul _)
    (by simpa using integrableOn_Φ₄'_imag_axis hu) (tendsto_intervalIntegral_Φ₄'_top hu)

lemma I₆'_eq_deform_imag_axis {u : ℝ} (hu : 2 < u) :
    I₆' u = (Complex.I : ℂ) *
        ((∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((t : ℂ) * Complex.I)) -
            2 * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) +
              ∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((t : ℂ) * Complex.I)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  let f2 : ℝ → ℂ := fun t => Φ₂' u ((t : ℂ) * Complex.I)
  let f5 : ℝ → ℂ := fun t => Φ₅' u ((t : ℂ) * Complex.I)
  let f4 : ℝ → ℂ := fun t => Φ₄' u ((t : ℂ) * Complex.I)
  have hf2 : Integrable f2 μ := integrableOn_Φ₂'_imag_axis hu
  have hf5 : Integrable f5 μ := integrableOn_Φ₅'_imag_axis hu
  have hf4 : Integrable f4 μ := integrableOn_Φ₄'_imag_axis hu
  dsimp [I₆', Φ₆]
  rw [show (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u (z₆' t))
        = ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) from
      setIntegral_congr_fun measurableSet_Ici fun t ht => by
        simp [show z₆' t = (Complex.I : ℂ) * (t : ℂ) by
          simpa [mul_assoc, mul_comm, mul_left_comm] using z₆'_eq_of_mem ht, mul_comm],
    integral_Ici_eq_integral_Ioi,
    (integral_const_mul (μ := μ) (r := (2 : ℂ))
      (f := fun t : ℝ => (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I))).symm,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      simpa [f2, f5, f4, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
        using (congrArg (fun z : ℂ => (Complex.I : ℂ) * z)
        (Φ_finite_difference_imag_axis (lt_trans zero_lt_one ht))).symm :
      ∀ t ∈ Set.Ioi (1 : ℝ), (2 : ℂ) * ((Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I)) =
        (Complex.I : ℂ) * (f2 t - 2 * f5 t + f4 t)),
    integral_const_mul (μ := μ) (r := (Complex.I : ℂ)) (f := fun t => f2 t - 2 * f5 t + f4 t)]
  calc (Complex.I : ℂ) * (∫ t, (f2 t - 2 * f5 t + f4 t) ∂μ)
      = (Complex.I : ℂ) * ((∫ t, f2 t - 2 * f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        simpa using congrArg ((Complex.I : ℂ) * ·)
          (integral_add (μ := μ) (hf2.sub (hf5.const_mul 2)) hf4)
    _ = (Complex.I : ℂ) * ((∫ t, f2 t ∂μ) - 2 * (∫ t, f5 t ∂μ) + ∫ t, f4 t ∂μ) := by
        rw [integral_sub (μ := μ) hf2 (hf5.const_mul 2),
          integral_const_mul (μ := μ) (r := (2 : ℂ)) (f := f5)]

/-- If `G t = E * Φ₅' u (tI)` for `t > 1`, then `∫ G = E * ∫ central` over `Ioi 1`. -/
private lemma ray_integral_eq_const_mul_central {u : ℝ} {G : ℝ → ℂ} {E : ℂ}
    (hG : ∀ t, 1 < t → G t = E * Φ₅' u ((t : ℂ) * Complex.I)) :
    (∫ t in Set.Ioi (1 : ℝ), G t) = E * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi hG, integral_const_mul]

/-- Rewrite `I₂' + I₄' + I₆'` as an imaginary-axis integral of `Φ₅'` over `t ≥ 1`. -/
public lemma I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail {u : ℝ} (hu : 2 < u) :
    I₂' u + I₄' u + I₆' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
  rw [I₂'_eq_deform_imag_axis hu, I₄'_eq_deform_imag_axis hu, I₆'_eq_deform_imag_axis hu,
    ray_integral_eq_const_mul_central (G := fun t => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)))
      (fun t _ => by simpa [mul_assoc] using Φ₁'_shift_left (u := u) (t := t)),
    ray_integral_eq_const_mul_central (G := fun t => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I))
      (E := Complex.exp (((π * u : ℝ) : ℂ) * Complex.I))
      (fun t _ => by simpa [mul_assoc] using Φ₃'_shift_right (u := u) (t := t))]
  simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]; ring

/-! ## Main Laplace representation -/

/-- Main lemma for blueprint proposition `prop:a-double-zeros`. -/
public theorem aRadial_eq_laplace_phi0_main {u : ℝ} (hu : 2 < u) :
    MagicFunction.FourierEigenfunctions.a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
            ((t ^ (2 : ℕ) : ℝ) : ℂ) *
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  have hu0 : 0 ≤ u := (lt_trans (by norm_num : (0 : ℝ) < 2) hu).le
  have ha : MagicFunction.FourierEigenfunctions.a' u = MagicFunction.a.RealIntegrals.a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) hu0)
  rw [ha]
  dsimp [MagicFunction.a.RealIntegrals.a']
  have hsplit :
      MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₂' u +
            MagicFunction.a.RealIntegrals.I₃' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₅' u + MagicFunction.a.RealIntegrals.I₆' u =
          (MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
              MagicFunction.a.RealIntegrals.I₅' u) +
            (MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₆' u) := by ring
  rw [hsplit, I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u),
    I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail (u := u) hu]
  have hseg : (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
      ∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I) := by
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [hseg]
  have hIoi :
      (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I)) +
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := by
    have h5Ioi0 : IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume :=
      by simpa [IntegrableOn, Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand] using
        (aLaplaceIntegral_convergent hu).neg'
    have h5Ioc := h5Ioi0.mono_set (fun t (ht : t ∈ Set.Ioc (0 : ℝ) 1) => ht.1)
    rw [show (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) by
      simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]]
    simpa [add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.setIntegral_union (μ := volume)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I))
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ))
        (hst := Set.Ioc_disjoint_Ioi_same)
        (ht := measurableSet_Ioi) h5Ioc (integrableOn_Φ₅'_imag_axis (u := u) hu)).symm
  set coeff : ℂ :=
    (Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))
  have hcomb :
      (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I))) +
          (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) =
        (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
    rw [← hIoi]; ring
  rw [hcomb]
  have hcoeff : coeff = -((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hrew : coeff = -((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) := by simp [coeff]; ring
    have htrig := MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u
    have hhalf := MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq u
    grind only
  have hΦ5 : (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
      - (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (g := fun t => -aLaplaceIntegrand u t)
      (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)))]
    simp [integral_neg]
  rw [hcoeff, hΦ5]
  simp [aLaplaceIntegrand, mul_assoc, mul_left_comm, mul_comm]

end LaplaceRepresentation

open scoped BigOperators Topology UpperHalfPlane

open MeasureTheory Real Complex UpperHalfPlane Filter
open SpherePacking
open SpherePacking.Integration (μIoi0)
open MagicFunction.FourierEigenfunctions

/-- The analytic continuation domain `U = {u : ℂ | 0 < re u} \ {2}`. -/
@[expose] public def ACDomain : Set ℂ := rightHalfPlane \ {2}

/-- The analytic continuation domain `ACDomain` is preconnected. -/
public lemma ACDomain_isPreconnected : IsPreconnected ACDomain := by
  -- We use a homeomorphism `ℂ ≃ₜ {u : ℂ // 0 < u.re}` to reduce to connectedness of the
  -- complement of a singleton in `ℂ`.
  let z2 : {u : ℂ // 0 < u.re} := ⟨(2 : ℂ), by simp⟩
  let h₃ : (Set.Ioi (0 : ℝ) × ℝ) ≃ₜ {u : ℂ // 0 < u.re} :=
    { toEquiv :=
        { toFun := fun p =>
            ⟨(p.1 : ℝ) + p.2 * Complex.I, by
              have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
              simpa using hp⟩
          invFun := fun z => (⟨z.1.re, z.2⟩, z.1.im)
          left_inv := by
            rintro ⟨x, y⟩
            ext <;> simp
          right_inv := by
            rintro ⟨z, hz⟩
            apply Subtype.ext
            simp [Complex.re_add_im] }
      continuous_toFun := by
        refine
            (show Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => (p.1 : ℝ) + p.2 * Complex.I) by
              fun_prop).subtype_mk fun p => by
            have hp : (0 : ℝ) < (p.1 : ℝ) := p.1.2
            simpa using hp
      continuous_invFun := by
        fun_prop }
  let h : ℂ ≃ₜ {u : ℂ // 0 < u.re} :=
    (Complex.equivRealProdCLM.toHomeomorph.trans
          ((Real.expOrderIso.toHomeomorph).prodCongr (Homeomorph.refl ℝ))).trans h₃
  have hpre : IsPreconnected ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
    have hconn : IsConnected ({h.symm z2}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) (h.symm z2)
    have himage :
        h '' ({h.symm z2}ᶜ : Set ℂ) = ({z2}ᶜ : Set {u : ℂ // 0 < u.re}) := by
      ext z
      refine ⟨?_, fun hz => ⟨h.symm z, by simpa, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      have hx' : x ≠ h.symm z2 := by simpa using hx
      simpa using fun hz => hx' (by simpa using congrArg h.symm hz)
    simpa [himage] using hconn.isPreconnected.image h h.continuous.continuousOn
  have hval :
      ((Subtype.val : {u : ℂ // 0 < u.re} → ℂ) '' ({z2}ᶜ :
          Set {u : ℂ // 0 < u.re})) = ACDomain := by
    ext u
    refine ⟨?_, ?_⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≠ z2 := by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
      exact ⟨z.2, by simpa using fun hEq => hz' (Subtype.ext hEq)⟩
    · rintro hu
      have hu_re : 0 < u.re := by simpa [rightHalfPlane] using hu.1
      refine ⟨⟨u, hu_re⟩, ?_, rfl⟩
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using fun hEq =>
        (by simpa using hu.2 : u ≠ (2 : ℂ)) (congrArg Subtype.val hEq)
  simpa [hval] using
    hpre.image (Subtype.val : {u : ℂ // 0 < u.re} → ℂ) continuous_subtype_val.continuousOn

/-- Generic analytic continuation on `ACDomain = {Re u > 0} \ {2}`. -/
public theorem analytic_continuation_of_gt2
    {value : ℝ → ℂ} {rhsC : ℂ → ℂ} {rhsR : ℝ → ℂ}
    (h_extension : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f ACDomain ∧
      ∀ u : ℝ, 0 < u → u ≠ 2 → f (u : ℂ) = value u)
    (h_rhs_analytic : AnalyticOnNhd ℂ rhsC ACDomain)
    (h_rhs_ofReal : ∀ u : ℝ, rhsC (u : ℂ) = rhsR u)
    (h_gt2 : ∀ r : ℝ, 2 < r → value r = rhsR r)
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    value u = rhsR u := by
  rcases h_extension with ⟨f, hf_analytic, hf_ofReal⟩
  have hf_gt2 : ∀ r : ℝ, 2 < r → f (r : ℂ) = rhsC (r : ℂ) := fun r hr =>
    (hf_ofReal r (lt_trans (by norm_num) hr) (by linarith)).trans
      ((h_gt2 r hr).trans (h_rhs_ofReal r).symm)
  have hFreq : (∃ᶠ z in 𝓝[≠] (3 : ℂ), f z = rhsC z) := Filter.frequently_iff.2 <| by
    intro U hU
    obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.1 hVnhds
    refine ⟨((3 + ε / 2 : ℝ) : ℂ), hVsub ⟨hball ?_, ?_⟩, by
      simpa using hf_gt2 (3 + ε / 2) (by nlinarith [hεpos])⟩
    · simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2),
        abs_of_nonneg hεpos.le] using half_lt_self hεpos
    · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show ((3 + ε / 2 : ℝ) : ℂ) ≠ 3 by exact_mod_cast
          (by nlinarith [hεpos.ne'] : (3 + ε / 2 : ℝ) ≠ 3))
  have hEqOn : Set.EqOn f rhsC ACDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf_analytic h_rhs_analytic
      ACDomain_isPreconnected (by simp [ACDomain, rightHalfPlane]) hFreq
  have hu_mem : (u : ℂ) ∈ ACDomain :=
    ⟨by simpa [rightHalfPlane] using hu,
      by simpa [ACDomain, Set.mem_singleton_iff] using (show (u : ℂ) ≠ 2 by exact_mod_cast hu2)⟩
  exact (hf_ofReal u hu hu2).symm.trans ((hEqOn hu_mem).trans (h_rhs_ofReal u))

/-- If `inner` is analytic on `ACDomain`, then so is
`u ↦ sign * (sin (π u / 2))^2 * inner u` for any constant `sign : ℂ`. -/
public lemma analyticOnNhd_sinSq_prefactor_mul
    (sign : ℂ) {inner : ℂ → ℂ} (hinner : AnalyticOnNhd ℂ inner ACDomain) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => sign * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) * inner u) ACDomain :=
  (analyticOnNhd_const.mul (by
    have hsin : AnalyticOnNhd ℂ (fun u : ℂ => Complex.sin ((π : ℂ) * u / 2)) ACDomain := by
      simpa [Function.comp] using ((by simpa using (analyticOnNhd_sin (s := (Set.univ : Set ℂ)))) :
          AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin z) (Set.univ : Set ℂ)).comp
        (AnalyticOnNhd.div_const (analyticOnNhd_const.mul analyticOnNhd_id) :
          AnalyticOnNhd ℂ (fun u : ℂ => (π : ℂ) * u / 2) ACDomain) (by intro _ _; simp)
    exact hsin.pow 2)).mul hinner

noncomputable section

/-- The `u`-independent bracket in the "another integral" integrand for `a'`. -/
@[expose] public def aAnotherBase (t : ℝ) : ℂ :=
  (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
    ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
    ((8640 / π : ℝ) : ℂ) * t - ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))

/-- Complex-parameter integrand for the "another integral" representation of `a'`. -/
@[expose] public def aAnotherIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  aAnotherBase t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Complex-parameter "another integral" for `a'`. -/
@[expose] public def aAnotherIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrandC u t

private lemma norm_exp_le_of_re_ge {z : ℂ} {t c : ℝ} (ht0 : 0 ≤ t) (hcz : c ≤ z.re) :
    ‖Complex.exp (-(π : ℂ) * z * (t : ℂ))‖ ≤ Real.exp (-π * c * t) := by
  simpa [Complex.norm_exp, show (-(π : ℂ) * z * (t : ℂ)).re = -π * z.re * t by
    simp [mul_assoc, Complex.mul_re, sub_eq_add_neg, add_comm]] using
    Real.exp_le_exp.mpr <| by simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonpos_left hcz (by nlinarith [Real.pi_pos, ht0] : (-π * t : ℝ) ≤ 0)

/-- Analyticity of `u ↦ ∫ t ∈ (0, ∞), base(t) * Complex.exp(-π u t)` on the right half-plane. -/
public theorem analyticOnNhd_integral_base_exp
    {base : ℝ → ℂ}
    (hbase_cont : ContinuousOn base (Set.Ioi (0 : ℝ)))
    (hbase_int : ∀ u : ℝ, 0 < u →
      IntegrableOn (fun t : ℝ => base t * (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ))) :
    AnalyticOnNhd ℂ
      (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
      rightHalfPlane := by
  have hDiff :
      DifferentiableOn ℂ
        (fun u : ℂ => ∫ t in Set.Ioi (0 : ℝ), base t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
        rightHalfPlane := by
    intro u hu
    have hu0 : 0 < u.re := by simpa [rightHalfPlane] using hu
    set ε : ℝ := u.re / 2
    have hε : 0 < ε := by positivity
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
    let F : ℂ → ℝ → ℂ := fun z t => base t * Complex.exp (-(π : ℂ) * z * (t : ℂ))
    let F' : ℂ → ℝ → ℂ := fun z t => (-(π : ℂ) * (t : ℂ)) * F z t
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) μ := fun z =>
      (hbase_cont.aestronglyMeasurable measurableSet_Ioi).mul
        ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-(π : ℂ) * z * (t : ℂ))).aestronglyMeasurable)
    have hBase_ε2 :
        Integrable (fun t : ℝ => base t * (Real.exp (-π * (ε / 2) * t) : ℂ)) μ := by
      simpa [μ, IntegrableOn] using (hbase_int (ε / 2) (by positivity))
    have hmem_Ioi : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
      simpa [μ] using ae_restrict_mem (μ := (volume : Measure ℝ))
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    have hF_int : Integrable (F u) μ := by
      refine Integrable.mono' (g := fun t : ℝ => ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖)
        hBase_ε2.norm (hF_meas u) ?_
      filter_upwards [hmem_Ioi] with t ht
      calc ‖F u t‖ = ‖base t‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by simp [F]
        _ ≤ ‖base t‖ * Real.exp (-π * (ε / 2) * t) := mul_le_mul_of_nonneg_left
            (norm_exp_le_of_re_ge ht.le (by dsimp [ε]; linarith : (ε / 2 : ℝ) ≤ u.re))
            (norm_nonneg _)
        _ = ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ := by
          rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
    let bound : ℝ → ℝ := fun t => (2 / ε) * ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖
    have hbound_int : Integrable bound μ := by
      simpa [bound] using hBase_ε2.norm.const_mul (2 / ε)
    have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε, ‖F' z t‖ ≤ bound t := by
      filter_upwards [hmem_Ioi] with t ht z hz
      have htpos : (0 : ℝ) < t := ht
      have hzre : ε ≤ z.re := by
        have hlt : |z.re - u.re| < ε := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            lt_of_le_of_lt (abs_re_le_norm (z - u))
              (by simpa [Metric.mem_ball] using hz : ‖z - u‖ < ε)
        dsimp [ε] at hlt ⊢; nlinarith [(abs_lt.mp hlt).1]
      have hExpTrade :
          (π * t) * Real.exp (-π * ε * t) ≤ (2 / ε) * Real.exp (-π * (ε / 2) * t) := by
        have hπε : (0 : ℝ) < π * ε := by positivity
        have hc2 : (0 : ℝ) ≤ 2 / (π * ε) := (div_pos (by norm_num) hπε).le
        have ht_le : t ≤ (2 / (π * ε)) * Real.exp ((π * ε / 2) * t) := by
          simpa [mul_assoc, show (2 / (π * ε)) * ((π * ε / 2) * t) = t by field_simp [hπε.ne']]
            using mul_le_mul_of_nonneg_left
              (by linarith [Real.add_one_le_exp ((π * ε / 2) * t)] :
                (π * ε / 2) * t ≤ Real.exp ((π * ε / 2) * t)) hc2
        have hbase : t * Real.exp (-(π * ε) * t) ≤ (2 / (π * ε)) * Real.exp (-(π * ε / 2) * t) := by
          refine (mul_le_mul_of_nonneg_right ht_le (Real.exp_nonneg (-(π * ε) * t))).trans_eq ?_
          rw [mul_assoc, ← Real.exp_add]; ring_nf
        simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, Real.pi_ne_zero,
          ne_of_gt hε] using mul_le_mul_of_nonneg_left hbase Real.pi_pos.le
      have hnorm_integ : ‖F z t‖ ≤ ‖base t‖ * Real.exp (-π * ε * t) := by
        simpa [F, norm_mul, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left (norm_exp_le_of_re_ge htpos.le hzre) (norm_nonneg _)
      have hnorm_base_exp : ‖base t * (Real.exp (-π * (ε / 2) * t) : ℂ)‖ =
          ‖base t‖ * Real.exp (-π * (ε / 2) * t) := by
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      calc ‖F' z t‖ = ‖(-(π : ℂ) * (t : ℂ))‖ * ‖F z t‖ := by simp [F']
        _ ≤ (π * t) * ‖F z t‖ := by rw [show ‖(-(π : ℂ) * (t : ℂ))‖ = π * t from by
              simp [abs_of_pos htpos, Real.pi_pos.le]]
        _ ≤ (π * t) * (‖base t‖ * Real.exp (-π * ε * t)) :=
          mul_le_mul_of_nonneg_left hnorm_integ (by nlinarith [Real.pi_pos, htpos.le])
        _ ≤ (2 / ε) * (‖base t‖ * Real.exp (-π * (ε / 2) * t)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hExpTrade (norm_nonneg (base t))
        _ = bound t := by rw [← hnorm_base_exp]
    have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball u ε,
        HasDerivAt (fun w : ℂ => F w t) (F' z t) z :=
      Filter.Eventually.of_forall fun t z _hz => by
        simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
          (show HasDerivAt (fun w : ℂ => Complex.exp (-(π : ℂ) * w * (t : ℂ)))
              (Complex.exp (-(π : ℂ) * z * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) z from
            (show HasDerivAt (fun w : ℂ => (-(π : ℂ) * w * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) z by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                ((hasDerivAt_id z).const_mul (-(π : ℂ) * (t : ℂ)))).cexp).const_mul (base t)
    have hDeriv : HasDerivAt (fun z : ℂ => ∫ t, F z t ∂μ) (∫ t, F' u t ∂μ) u :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (s := Metric.ball u ε) (Metric.ball_mem_nhds u hε) (x₀ := u)
        (F := F) (F' := F') (bound := bound)
        (hF_meas := Filter.Eventually.of_forall hF_meas) (hF_int := hF_int)
        (hF'_meas := ((by fun_prop : Continuous fun t : ℝ =>
            (-(π : ℂ) * (t : ℂ))).aestronglyMeasurable).mul (hF_meas u))
        (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hdiff)).2
    exact hDeriv.differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd rightHalfPlane_isOpen

/-- `aAnotherIntegralC` is analytic on the right half-plane. -/
public lemma aAnotherIntegralC_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherIntegralC rightHalfPlane := by
  have hcontIdiv : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) / (t : ℂ)) (Set.Ioi (0 : ℝ)) :=
    continuous_const.continuousOn.div continuous_ofReal.continuousOn fun t ht => by
      exact_mod_cast ne_of_gt ht
  have hφcomp : ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) (Set.Ioi (0 : ℝ)) :=
    (by simpa using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
      ContinuousOn (fun z : ℂ => φ₀'' z) upperHalfPlaneSet).comp hcontIdiv fun t ht => by
        change 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im
        rw [imag_I_div t]; exact inv_pos.2 (by simpa using ht)
  have hbase : ContinuousOn aAnotherBase (Set.Ioi (0 : ℝ)) :=
    ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
      hφcomp).sub (continuousOn_const.mul (by fun_prop : Continuous fun t : ℝ =>
      ((Real.exp (2 * π * t)) : ℂ)).continuousOn)).add
      (continuousOn_const.mul continuous_ofReal.continuousOn)).sub continuousOn_const
  convert analyticOnNhd_integral_base_exp (base := aAnotherBase)
    hbase (fun u hu => (aAnotherIntegrand_integrable_of_pos hu).congr <|
      Filter.Eventually.of_forall fun t => by
        simp [aAnotherIntegrand, aAnotherBase, mul_assoc]) using 1

/-!
## Analytic RHS function on `ℂ`

This is the complex-analytic function whose restriction to the real axis is the blueprint RHS.
-/

def aAnotherRHS (u : ℂ) : ℂ :=
  (4 * Complex.I) * (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ) *
    ((36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
      (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
      (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)

lemma aAnotherRHS_analyticOnNhd :
    AnalyticOnNhd ℂ aAnotherRHS ACDomain := by
  have hπ : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  have hu_ne0 : ∀ u ∈ ACDomain, u ≠ 0 := fun u hu h0 =>
    absurd (by simpa [rightHalfPlane] using hu.1) (by simp [h0])
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (sub_ne_zero.2 (by simpa using hu.2))
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ))) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (pow_ne_zero _ (hu_ne0 u hu))
  have hterm3 :
      AnalyticOnNhd ℂ (fun u : ℂ => (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u)) ACDomain :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul analyticOnNhd_id)
      fun u hu => mul_ne_zero (pow_ne_zero _ hπ) (hu_ne0 u hu)
  have hinner :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (36 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * (u - 2)) -
              (8640 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u ^ (2 : ℕ)) +
            (18144 : ℂ) / ((π : ℂ) ^ (3 : ℕ) * u) + aAnotherIntegralC u)
        ACDomain := by
    simpa [sub_eq_add_neg, add_assoc] using (hterm1.sub hterm2).add
      (hterm3.add (aAnotherIntegralC_analyticOnNhd.mono fun u hu => hu.1))
  simpa [aAnotherRHS] using
    analyticOnNhd_sinSq_prefactor_mul (sign := 4 * Complex.I) hinner

/-- Analytic-continuation step: extend the "another integral" identity for `a'` from `u > 2`
to all real `0 < u` with `u ≠ 2`. -/
public theorem aRadial_eq_another_integral_analytic_continuation_of_gt2
  (h_gt2 :
      ∀ r : ℝ, 2 < r →
        a' r =
          (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
            ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
              (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
              (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
                ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) :
    a' u =
      (4 * Complex.I) * (Real.sin (π * u / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * u) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand u t) := by
  refine analytic_continuation_of_gt2
    ⟨aPrimeC, aPrimeC_analyticOnNhd.mono (fun u hu => hu.1), fun u hu _ => by
      simpa [show MagicFunction.a.RealIntegrals.a' u = a' u by
        simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) (hu := hu.le)).symm]
        using aPrimeC_ofReal u⟩
    aAnotherRHS_analyticOnNhd
    (rhsR := fun r : ℝ =>
      (4 * Complex.I) * (Real.sin (π * r / 2)) ^ (2 : ℕ) *
        ((36 : ℂ) / (π ^ (3 : ℕ) * (r - 2)) -
          (8640 : ℂ) / (π ^ (3 : ℕ) * r ^ (2 : ℕ)) +
          (18144 : ℂ) / (π ^ (3 : ℕ) * r) +
            ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t))
    (fun r => by
      simp only [aAnotherRHS, show (Complex.sin ((π : ℂ) * (r : ℂ) / 2)) ^ (2 : ℕ) =
        ((Real.sin (π * r / 2)) ^ (2 : ℕ) : ℂ) by simp,
        show aAnotherIntegralC (r : ℂ) = ∫ t in Set.Ioi (0 : ℝ), aAnotherIntegrand r t from
          MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
            measurableSet_Ioi (fun t _ => by
              simp [aAnotherIntegrandC, aAnotherBase, aAnotherIntegrand])])
    h_gt2 hu hu2

/-- Integral of a triple sum is the sum of the integrals, under integrability assumptions. -/
public lemma integral_add_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ((f x + g x) + h x) ∂ μ) =
      (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) + (∫ x, h x ∂ μ) := by
  simpa [add_assoc, MeasureTheory.integral_add (μ := μ) hf hg] using
    MeasureTheory.integral_add (μ := μ) (hf.add hg) hh

/-- `∫_{t > 0} exp (-π u t) dt = 1 / (π u)` as a complex-valued integral, for `u > 0`. -/
public lemma integral_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) : ℝ) : ℂ) := by
  rw [← MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi (u := u) hu]
  exact integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ)

/-- `∫_{t > 0} t * exp (-π u t) dt = 1 / (π u)^2` as a complex-valued integral, for `u > 0`. -/
public lemma integral_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [← MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using
    integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ)
      (f := fun t : ℝ => t * Real.exp (-π * u * t))

/-- `∫_{t > 0} exp (2π t) * exp (-π u t) dt = 1 / (π (u - 2))` as a complex-valued integral,
for `u > 2`. -/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
  rw [← MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi (u := u) hu]
  simpa [Complex.ofReal_mul] using
    integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ)
      (f := fun t : ℝ => Real.exp (2 * π * t) * Real.exp (-π * u * t))

/-- Helper: derive `IntegrableOn` on `Ioi 0` from a nonzero integral identity. -/
private lemma integrableOn_Ioi_of_integral_eq_ne_zero {f : ℝ → ℂ} {c : ℝ} (hc : c ≠ 0)
    (heq : (∫ t : ℝ, f t ∂μIoi0) = ((c : ℝ) : ℂ)) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  simpa [MeasureTheory.IntegrableOn, μIoi0] using
    MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0)
      (by rw [heq]; exact_mod_cast hc)

/-- Integrability of `t ↦ exp (-π u t)` on `t > 0` as a complex-valued function, for `u > 0`. -/
public lemma integrableOn_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
  integrableOn_Ioi_of_integral_eq_ne_zero (one_div_ne_zero (mul_ne_zero Real.pi_ne_zero hu.ne'))
    (by simpa [μIoi0] using integral_exp_neg_pi_mul_Ioi_complex (u := u) hu)

/-- Integrability of `t ↦ t * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 0`. -/
public lemma integrableOn_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
  integrableOn_Ioi_of_integral_eq_ne_zero
    (one_div_ne_zero (pow_ne_zero 2 (mul_ne_zero Real.pi_ne_zero hu.ne')))
    (by simpa [μIoi0] using integral_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu)

/-- Integrability of `t ↦ exp (2π t) * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 2`. -/
public lemma integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) :=
  integrableOn_Ioi_of_integral_eq_ne_zero
    (one_div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_pos.2 hu).ne'))
    (by simpa [μIoi0] using integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu)

end

end MagicFunction.g.CohnElkies.IntegralReps

/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module

public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.Integration.Measure
import SpherePacking.ModularForms.SlashActionAuxil
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# `b` is a Schwartz function

Builds Schwartz functions from the radial integrals `J₁', ..., J₆'` and assembles the
`(-1)`-Fourier eigenfunction `b`. On `ℝ`, radial profiles are only used at `r = ‖x‖^2 ≥ 0`; a
smooth cutoff yields global Schwartz functions on `ℝ` without changing induced functions on `ℝ⁸`.

Also packages the `SmoothJ24Common` skeleton used by `J₂'` and `J₄'`, and the derived
smoothness/decay statements for those two primed profiles.

Also includes the smoothness/decay developments for `J₁'`, `J₅'`, and `J₆'` (originally in
`Schwartz.SmoothJ1`).
-/

namespace SpherePacking.Integration

noncomputable section

open Complex Real Set MeasureTheory Filter

/-- The `n`-th `x`-derivative integrand appearing in `J₆'`-type formulas. -/
@[expose] public def gN_J6_integrand (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℝ → ℂ :=
  fun t : ℝ ↦ ((-Real.pi * t : ℂ) ^ n) *
    ((Complex.I : ℂ) * (f t * cexp ((x : ℂ) * (-Real.pi * t : ℂ))))

/-- Integrability of `gN_J6_integrand` on `Ici 1` under an exponential bound on `f`. -/
public lemma integrable_gN_J6 (f : ℝ → ℂ)
    (hBound : ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-Real.pi * t))
    (n : ℕ) (x : ℝ) (hx : -1 < x)
    (hmeas : AEStronglyMeasurable (gN_J6_integrand f n x)
        ((volume : Measure ℝ).restrict (Ici (1 : ℝ)))) :
    Integrable (gN_J6_integrand f n x) ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
  rcases hBound with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C :=
    ForMathlib.nonneg_of_nonneg_le_mul (a := ‖f 1‖) (b := Real.exp (-Real.pi * (1 : ℝ)))
      (C := C) (norm_nonneg _) (by positivity) (by simpa using hC 1 le_rfl)
  have hb : 0 < Real.pi * (x + 1) := mul_pos Real.pi_pos (by linarith)
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
  have hbound_int : Integrable bound ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    simpa [bound, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi * (x + 1))
        (by simpa [mul_assoc] using hb)).const_mul ((Real.pi ^ n) * C)
  refine Integrable.mono' hbound_int hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  calc
    ‖gN_J6_integrand f n x t‖
        = (Real.pi * t) ^ n * (‖f t‖ * Real.exp (-Real.pi * x * t)) := by
          simp [gN_J6_integrand, norm_pow, Complex.norm_exp, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, abs_of_nonneg ht0, mul_left_comm, mul_comm]
    _ ≤ (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) := by
          gcongr; exact hC t ht
    _ = bound t := by
          change (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) =
            (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
          rw [show (-(Real.pi * (x + 1)) * t) = (-Real.pi * t) + (-Real.pi * x * t) by ring,
            Real.exp_add]; ring

end

end SpherePacking.Integration

namespace MagicFunction.b.Schwartz.J6Smooth

noncomputable section

open scoped Topology ContDiff
open Complex Real Set MeasureTheory Filter MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds
  MagicFunction.b.PsiBounds.PsiExpBounds SpherePacking.ForMathlib SpherePacking.Integration

def μ : Measure ℝ := μIciOne
def s : Set ℝ := Ioi (-1 : ℝ)

lemma isOpen_s : IsOpen s := isOpen_Ioi

abbrev coeff (t : ℝ) : ℂ := SmoothIntegralIciOne.coeff t
abbrev g (x t : ℝ) : ℂ := SmoothIntegralIciOne.g (hf := ψS.resToImagAxis) x t
abbrev gN (n : ℕ) (x t : ℝ) : ℂ := SmoothIntegralIciOne.gN (hf := ψS.resToImagAxis) n x t

lemma gN_measurable (n : ℕ) (x : ℝ) : AEStronglyMeasurable (gN n x) (μ) := by
  have hcoeff : Continuous coeff := by
    simpa [coeff] using (continuous_const.mul Complex.continuous_ofReal : Continuous fun t : ℝ =>
      (-Real.pi : ℂ) * (t : ℂ))
  refine (ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ))
    (s := Ici (1 : ℝ)) ?_ measurableSet_Ici).mono_measure (by simp [μ, μIciOne])
  simpa [gN] using (hcoeff.pow n).continuousOn.mul
    (by simpa [g, mul_assoc] using (continuousOn_const.mul
      ((Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) continuous_ψS).mul
        ((continuous_const.mul hcoeff).cexp).continuousOn)) :
      ContinuousOn (g x) (Ici (1 : ℝ)))

lemma gN_integrable (n : ℕ) (x : ℝ) (hx : x ∈ s) : Integrable (gN n x) μ := by
  simpa [μ, μIciOne] using
    (integrable_gN_J6 (f := ψS.resToImagAxis)
      (hBound := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
      (n := n) (x := x) hx (hmeas := gN_measurable (n := n) (x := x)))

def F (n : ℕ) (x : ℝ) : ℂ := ∫ t in Ici (1 : ℝ), gN n x t

/-- `G` incorporates the outer `-2` factor from the definition of `J₆'`. -/
def G (n : ℕ) (x : ℝ) : ℂ := (-2 : ℂ) * F n x

lemma hasDerivAt_F (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => F n y) (F (n + 1) x) x := by
  simpa [F, μ] using
    (SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := ψS.resToImagAxis) (shift := (1 : ℝ))
      (exists_bound_norm_hf := by
        simpa [one_mul, mul_assoc] using exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
      (gN_measurable := fun n x => by simpa [μ] using gN_measurable (n := n) (x := x))
      (n := n) (x := x) hx (hF_int := by simpa [μ] using gN_integrable (n := n) (x := x) hx))

lemma iteratedDeriv_G_eq : ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := fun n => by
  induction n with
  | zero => intro m x _; simp [iteratedDeriv_zero]
  | succ n ih =>
      intro m x hx
      have hEq : iteratedDeriv n (G m) =ᶠ[𝓝 x] G (n + m) := by
        filter_upwards [isOpen_s.mem_nhds hx] with y hy using ih (m := m) hy
      simpa [iteratedDeriv_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Filter.EventuallyEq.deriv_eq hEq).trans
          ((by simpa [G] using (hasDerivAt_F (n := n + m) (x := x) hx).const_mul (-2 : ℂ) :
            HasDerivAt (fun y : ℝ => G (n + m) y) (G (n + m + 1) x) x).deriv)

private lemma J₆'_eq_G0 (x : ℝ) : RealIntegrals.J₆' x = G 0 x := by
  have hint : (∫ t in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' (z₆' t) * cexp (π * (Complex.I : ℂ) * x * (z₆' t))) =
        ∫ t in Ici (1 : ℝ), g x t := by
    refine integral_congr_ae <| (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
    dsimp
    rw [show ψS' (z₆' t) = ψS.resToImagAxis t by
      simp [ψS', Function.resToImagAxis, ResToImagAxis, hz, ht0, mul_comm],
      show cexp ((π : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)) = cexp ((x : ℂ) * coeff t) from
        congrArg cexp (by simp [coeff, SmoothIntegralIciOne.coeff, hz]; ring_nf; simp)]
    simp [g, SmoothIntegralIciOne.g, Function.resToImagAxis, ResToImagAxis, mul_assoc]
  simpa [G, F, gN, SmoothIntegralIciOne.gN, g, RealIntegrals.J₆', mul_assoc, mul_left_comm,
    mul_comm] using congrArg (fun J : ℂ => (-2 : ℂ) * J) hint

/-- Smoothness of `RealIntegrals.J₆'` on the open half-line `Ioi (-1)`. -/
public theorem contDiffOn_J₆'_Ioi_neg1 :
    ContDiffOn ℝ ∞ RealIntegrals.J₆' (Ioi (-1 : ℝ)) :=
  (by simpa [G] using contDiffOn_const.mul (by simpa using
      (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
        (fun n x hx => by simpa using (hasDerivAt_F (n := n) (x := x) hx)) 0)) :
    ContDiffOn ℝ ∞ (G 0) s).congr (fun x _ => J₆'_eq_G0 x)

/-- Schwartz-type decay bounds for `RealIntegrals.J₆'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₆' : ∀ (k n : ℕ),
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := fun k n => by
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  obtain ⟨Cψ, hCψ⟩ := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hCψ0 : 0 ≤ Cψ := SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
    (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity)
    (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) * Cψ
  have hbound_int : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm, IntegrableOn, μ, μIciOne] using
      (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi)
        Real.pi_pos).const_mul ((Real.pi ^ n) * Cψ)
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := integral_nonneg_of_ae <|
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall fun t ht => by
      have : 0 ≤ t := zero_le_one.trans ht; positivity
  refine ⟨2 * Kn * B, fun x hx => ?_⟩
  have hGbound : ‖G n x‖ ≤ 2 * Kn * Real.exp (-Real.pi * x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) :=
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall fun t ht => by
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
      have hxexp : Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Real.exp_le_exp.2 (neg_le_neg (le_mul_of_one_le_right
            (mul_nonneg Real.pi_pos.le hx) ht))
      calc
        ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
              simp [gN, SmoothIntegralIciOne.gN, g, coeff, norm_pow]
        _ ≤ (Real.pi * t) ^ n * (‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by
              gcongr ?_ * ?_
              · simp [coeff, SmoothIntegralIciOne.coeff_norm (t := t) ht]
              · simpa [g] using SmoothIntegralIciOne.g_norm_bound
                  (hf := ψS.resToImagAxis) (x := x) (t := t)
        _ ≤ (Real.pi * t) ^ n * ((Cψ * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x)) := by
              gcongr; exact hCψ t ht
        _ = bound t * Real.exp (-Real.pi * x) := by ring
    have hFn : ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) := calc
      ‖F n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := by
            simpa [show F n x = ∫ t, gN n x t ∂μ by simp [F, μ, μIciOne]] using
              (norm_integral_le_integral_norm (μ := μ) (f := gN n x))
      _ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg (gN n x t))
              (by simpa [mul_assoc, mul_left_comm, mul_comm] using
                hbound_int.mul_const (Real.exp (-Real.pi * x))) hbound_ae
      _ = Kn * Real.exp (-Real.pi * x) := by simpa [Kn] using
            (integral_mul_const (μ := μ) (r := Real.exp (-Real.pi * x)) (f := bound))
    calc ‖G n x‖
        ≤ 2 * (Kn * Real.exp (-Real.pi * x)) := by
          simpa [G, norm_mul, mul_assoc] using
            mul_le_mul_of_nonneg_left hFn (by positivity : (0 : ℝ) ≤ 2)
      _ = 2 * Kn * Real.exp (-Real.pi * x) := by ring
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖
        = x ^ k * ‖G n x‖ := by
          simp [Real.norm_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
            show iteratedDeriv n RealIntegrals.J₆' x = G n x by
              simpa [show RealIntegrals.J₆' = G 0 from funext J₆'_eq_G0] using
                (iteratedDeriv_G_eq (n := n) (m := 0))
                  (lt_of_lt_of_le (by norm_num) hx : x ∈ s)]
    _ ≤ x ^ k * (2 * Kn * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-Real.pi * x)) := by ring
    _ ≤ (2 * Kn) * B :=
      mul_le_mul_of_nonneg_left (hB x hx) (by positivity)

end

end MagicFunction.b.Schwartz.J6Smooth

namespace MagicFunction.b.Schwartz.J1Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm
open Complex Real Set MeasureTheory Filter intervalIntegral UpperHalfPlane
open MagicFunction.Parametrisations MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds
open Matrix ModularGroup ModularForm

def μ : Measure ℝ := SpherePacking.Integration.μIoo01

attribute [irreducible] μ

instance : IsFiniteMeasure μ :=
  ⟨by simp [μ, SpherePacking.Integration.μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩

def coeff (t : ℝ) : ℂ := ((π : ℂ) * (Complex.I : ℂ)) * z₁' t
def hf (t : ℝ) : ℂ := (Complex.I : ℂ) * ψT' (z₁' t)
def gN (n : ℕ) (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.gN (coeff := coeff) (hf := hf) n x t

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using
    SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₁' t) (hz := norm_z₁'_le_two t)

/-- Modular rewrite for `ψT' (z₁' t)`, used to control the integrand near `t = 0`. -/
public lemma ψT'_z₁'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  have ht0 : 0 < t := ht.1
  have hz_im : 0 < (z₁' t).im := im_z₁'_pos (t := t) ht
  let z : ℍ := ⟨z₁' t, hz_im⟩
  have hψT : ψT z = ψS ((S * T) • z) * (z + 1 : ℂ) ^ (2 : ℕ) := by
    simpa using ((by simpa using congrArg (fun f : ℍ → ℂ => f z) ψS_slash_ST :
      (ψS ∣[(-2 : ℤ)] (S * T)) z = ψT z).symm.trans (by simpa using slashST' (z := z) (F := ψS)))
  have hzplus : (z + 1 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, add_left_comm, add_comm] using
      congrArg (fun w : ℂ => w + (1 : ℂ)) (z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht))
  have hsmul : (S * T) • z = (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    rw [coe_ST_smul (z := z), show ((z : ℂ) + 1) = (Complex.I : ℂ) * (t : ℂ) from hzplus]
    field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ne_of_gt ht0, Complex.I_ne_zero]; simp
  have hψS' : ψS ((S * T) • z) = ψS.resToImagAxis (1 / t) := by
    rw [hsmul]; simp [Function.resToImagAxis, ResToImagAxis, ht0]
  have heq : ψT' (z₁' t) = ψT z := by simp [ψT', hz_im, z]
  rw [hψS', hzplus] at hψT
  simpa [heq] using hψT

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using continuous_const.mul continuous_z₁'

lemma continuousOn_hf :
    ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  simpa [hf] using
    (continuousOn_const.mul <| by
      simpa using
        MagicFunction.continuousOn_ψT'_z₁'_of (k := 2) (ψS := ψS) (ψT' := ψT')
          (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) continuous_ψS)
          ψT'_z₁'_eq)

lemma exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M :=
  let ⟨Mψ, hMψ⟩ := MagicFunction.exists_bound_norm_ψT'_z₁'_of (k := 2) (ψS := ψS) (ψT' := ψT')
    exists_bound_norm_ψS_resToImagAxis_Ici_one ψT'_z₁'_eq
  ⟨Mψ, fun t ht => by simpa [hf] using hMψ t ht⟩

def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μ

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, μ, SpherePacking.Integration.μIoo01, gN] using
    SpherePacking.Integration.DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo
      (coeff := coeff) (hf := hf)
      continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le n x₀

private lemma I_zero_eq_J₁' : (fun x : ℝ => I 0 x) = J₁' := by
  funext x
  simp [RealIntegrals.J₁', I, μ, SpherePacking.Integration.μIoo01, gN, hf, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN, mul_assoc, mul_left_comm, mul_comm,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo]

/-- Smoothness of `J₁'` (the primed radial profile). -/
public theorem contDiff_J₁' : ContDiff ℝ (⊤ : ℕ∞) J₁' := by
  simpa [I_zero_eq_J₁'] using SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I)
    (fun n x => by simpa using hasDerivAt_integral_gN (n := n) (x₀ := x))

/-- Schwartz-type decay bounds for `J₁'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₁' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖ ≤ C := fun k n => by
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt k (b := 2*π) (by positivity)
  obtain ⟨Cψ, hCψ⟩ :=
    MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hCψ0 : 0 ≤ Cψ :=
    SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity)
      (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ 2
  have hbound_int : Integrable bound μ := by
    simpa [bound, μ, SpherePacking.Integration.μIoo01, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.Integration.integrable_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 2 (by positivity [hCψ0]))
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    refine integral_nonneg_of_ae <| ?_
    filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
      simpa [μ] using SpherePacking.Integration.ae_mem_Ioo01_muIoo01] with t ht
    exact mul_nonneg (by positivity [hCψ0]) (pow_nonneg ht.1.le _)
  refine ⟨Kn * B, fun x hx => ?_⟩
  have hIn : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
        simpa [μ] using SpherePacking.Integration.ae_mem_Ioo01_muIoo01] with t ht
      have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        simpa using
          SpherePacking.Integration.DifferentiationUnderIntegral.norm_cexp_ofReal_mul_coeff_of_coeff_re
            (coeff := coeff) (x := x) (t := t)
          (show (coeff t).re = -Real.pi * t by
            simp [coeff, Complex.mul_re, show (z₁' t).im = t from by
              simp [show z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) from by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht)], mul_assoc])
      exact le_mul_of_le_mul_of_nonneg_left
        (by simpa [gN, hf, bound, mul_assoc, mul_left_comm, mul_comm] using
            SpherePacking.Integration.DifferentiationUnderIntegral.norm_gN_le_bound_mul_exp
              (coeff := coeff) (ψ := ψT')
              (z := z₁') (n := n) (Cψ := Cψ) (x := x) (t := t) hCψ0
              (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n)
              (by simpa using
                (MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS)
                  (ψZ := ψT') (z := z₁') (hCψ := hCψ) (hEq := ψT'_z₁'_eq) (t := t)
                  ⟨ht.1, le_of_lt ht.2⟩))
              hcexp :
          ‖gN n x t‖ ≤ bound t * (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)))
        (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx ht.1 :
          Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x))
        (by positivity [hCψ0])
    simpa [I, Kn] using
      (SpherePacking.Integration.DifferentiationUnderIntegral.norm_integral_le_integral_bound_mul_const
        (μ := μ) (f := gN n x) (bound := bound)
        (E := Real.exp (-2 * Real.pi * Real.sqrt x)) (hbound_int := hbound_int) hbound_ae)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖
      = x ^ k * ‖I n x‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          congrArg (fun F : ℝ → ℂ => F x) (show iteratedDeriv n J₁' = fun x : ℝ ↦ I n x by
            simpa [I_zero_eq_J₁'] using SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
              (I := I) (hI := fun n x => hasDerivAt_integral_gN (n := n) (x₀ := x)) n)]
    _ ≤ x ^ k * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x)) := by gcongr
    _ = Kn * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring
    _ ≤ Kn * B := mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hB x hx) hKn_nonneg

end

end MagicFunction.b.Schwartz.J1Smooth

/-! # Smooth J5: smoothness and decay bounds for `RealIntegrals.J₅'` via differentiation under
the integral sign. -/

namespace MagicFunction.b.Schwartz.J5Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm
open Complex Real Set MeasureTheory Filter intervalIntegral UpperHalfPlane SpherePacking.ForMathlib
open MagicFunction.Parametrisations MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds
  MagicFunction.b.PsiBounds.PsiExpBounds SpherePacking.Integration Matrix ModularGroup ModularForm
  MagicFunction MagicFunction.b.Schwartz

def μ : Measure ℝ := μIoo01

attribute [irreducible] μ

instance : IsFiniteMeasure μ :=
  ⟨by simp [μ, μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩

def coeff (t : ℝ) : ℂ := ((π : ℂ) * (Complex.I : ℂ)) * z₅' t
def hf (t : ℝ) : ℂ := (Complex.I : ℂ) * ψI' (z₅' t)
def gN (n : ℕ) (x t : ℝ) : ℂ :=
  DifferentiationUnderIntegral.gN (coeff := coeff) (hf := hf) n x t

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using
    norm_mul_pi_I_le_two_pi (z := z₅' t) (hz := (norm_z₅'_le_one t).trans (by norm_num))

lemma continuousOn_ψI'_z₅' : ContinuousOn (fun t : ℝ => ψI' (z₅' t)) (Ioo (0 : ℝ) 1) := by
  refine continuousOn_iff_continuous_restrict.2 ?_
  have him : ∀ t : Ioo (0 : ℝ) 1, 0 < (z₅' (t : ℝ)).im := fun t =>
    im_z₅'_pos (t := (t : ℝ)) ⟨t.2.1, t.2.2.le⟩
  simpa [Set.restrict] using continuous_comp_upperHalfPlane_mk (ψT := ψI) (ψT' := ψI')
    MagicFunction.b.PsiBounds.continuous_ψI (z := fun t : Ioo (0 : ℝ) 1 => z₅' (t : ℝ))
    (continuous_z₅'.comp continuous_subtype_val) him (fun t => by simp [ψI', him t])

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using continuous_const.mul continuous_z₅'

lemma continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  simpa [hf] using continuousOn_const.mul continuousOn_ψI'_z₅'

/-- Modular rewrite for `ψI' (z₅' t)` in terms of `ψS.resToImagAxis (1 / t)`. -/
public lemma ψI'_z₅'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  have ht0 : 0 < t := ht.1
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using z₅'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht)
  have hz_im : 0 < (z₅' t).im := by simpa [hz5] using ht0
  let z : ℍ := ⟨z₅' t, hz_im⟩
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hsmul : S • z = (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    calc (↑(S • z) : ℂ) = (-1 : ℂ) / (z : ℂ) := by simpa using ModularGroup.coe_S_smul z
      _ = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [z, hz5]
      _ = (Complex.I : ℂ) * (1 / t) := by field_simp [htne, Complex.I_ne_zero]; simp
  have hψS' :
      ψS (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) S) • z) =
        ψS.resToImagAxis (1 / t) := by
    simp [Function.resToImagAxis, ResToImagAxis, ht0,
      show SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) S) • z =
        (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) by simpa using hsmul]
  have hzcoe : (z : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by simp [z, hz5]
  simpa [show ψI' (z₅' t) = ψI z from by simp [ψI', hz_im, z], hψS', hzcoe] using
    ((congrArg (fun f : ℍ → ℂ => f z) ψS_slash_S).symm.trans
      (by simpa using slashS' (z := z) (F := ψS)) :
      ψI z = ψS (S • z) * (z : ℂ) ^ (2 : ℕ))

lemma exists_bound_norm_ψI'_z₅' :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖ψI' (z₅' t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_norm_ψS_resToImagAxis_Ici_one
  refine ⟨M, fun t ht => ?_⟩
  have ht0 : 0 < t := ht.1
  have htle : t ≤ 1 := ht.2.le
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M :=
    hM (1 / t) (by simpa using one_div_le_one_div_of_le ht0 htle)
  calc ‖ψI' (z₅' t)‖ ≤ M * t ^ 2 := by
        have hEq := ψI'_z₅'_eq (t := t) ⟨ht.1, htle⟩; simp_all
    _ ≤ M := by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ ht0.le htle)
        ((norm_nonneg _).trans hψS)

lemma exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M :=
  exists_bound_norm_ψI'_z₅'.imp fun _ hM t ht => by simpa [hf] using hM t ht

def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μ

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, μ, μIoo01, gN] using
    DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo (coeff := coeff) (hf := hf)
      continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le n x₀

lemma J₅'_eq_integral_g_Ioo (x : ℝ) :
    J₅' x = (-2 : ℂ) * I 0 x := by
  simp [RealIntegrals.J₅', I, gN, hf, coeff, μ, μIoo01,
    DifferentiationUnderIntegral.gN, DifferentiationUnderIntegral.g,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₅'`. -/
public theorem contDiff_J₅' : ContDiff ℝ (⊤ : ℕ∞) J₅' := by
  have hmul : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (-2 : ℂ) * I 0 x) :=
    contDiff_const.mul (contDiff_of_hasDerivAt_succ (I := I) (fun n x => by
      simpa using hasDerivAt_integral_gN (n := n) (x₀ := x)))
  -- `simp` normalizes `(-2) * f` to `-(2 * f)`, so match that normal form.
  simpa [show (fun x : ℝ ↦ -(2 * I 0 x)) = J₅' from
    funext fun x => by simpa [mul_assoc] using (J₅'_eq_integral_g_Ioo (x := x)).symm] using hmul

/-- Schwartz-type decay bounds for `J₅'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₅' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖ ≤ C := fun k n => by
  obtain ⟨B, hB⟩ :=
    exists_bound_pow_mul_exp_neg_mul_sqrt (k := k) (b := 2 * Real.pi) (by positivity)
  obtain ⟨Cψ, hCψ⟩ := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hCψ0 : 0 ≤ Cψ :=
    nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖) (b := Real.exp (-Real.pi * (1 : ℝ)))
      (C := Cψ) (norm_nonneg _) (by positivity) (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ 2
  have hbound_int : Integrable bound μ := by
    simpa [bound, μ, μIoo01, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_const_mul_pow_muIoo01 (((2 * Real.pi) ^ n) * Cψ) 2 (by positivity [hCψ0]))
  let Kn : ℝ := ∫ t, bound t ∂μ
  refine ⟨2 * Kn * B, fun x hx => ?_⟩
  have hiterJ : iteratedDeriv n J₅' x = (-2 : ℂ) * I n x := by
    rw [show J₅' = (-2 : ℂ) • (fun y : ℝ => I 0 y) from funext fun y => by
      simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using J₅'_eq_integral_g_Ioo (x := y)]
    simp [iteratedDeriv_eq_of_hasDerivAt_succ (I := I)
      (fun m y => by simpa using hasDerivAt_integral_gN (n := m) (x₀ := y)) n, smul_eq_mul]
  have hIn : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
        simpa [μ] using ae_mem_Ioo01_muIoo01] with t ht
      have hψI : ‖ψI' (z₅' t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ 2 := by
        simpa [one_div] using
          (norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS) (ψZ := ψI')
            (z := z₅') (hCψ := hCψ) (hEq := fun s hs => ψI'_z₅'_eq (t := s) hs)
            (t := t) ⟨ht.1, le_of_lt ht.2⟩)
      have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        simpa using
          SpherePacking.Integration.DifferentiationUnderIntegral.norm_cexp_ofReal_mul_coeff_of_coeff_re
            (coeff := coeff) (x := x) (t := t)
            (show (coeff t).re = -Real.pi * t by
              simp [coeff, Complex.mul_re, show (z₅' t).im = t by
                simp [show z₅' t = (Complex.I : ℂ) * (t : ℂ) by
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    z₅'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht)], mul_assoc])
      exact le_mul_of_le_mul_of_nonneg_left
        (by simpa [gN, hf, bound, mul_assoc, mul_left_comm, mul_comm] using
            SpherePacking.Integration.DifferentiationUnderIntegral.norm_gN_le_bound_mul_exp
              (coeff := coeff) (ψ := ψI') (z := z₅') (n := n) (Cψ := Cψ)
              (x := x) (t := t) hCψ0 (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n)
              hψI hcexp :
          ‖gN n x t‖ ≤ bound t * (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)))
        (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx ht.1 :
          Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x))
        (by positivity [hCψ0])
    simpa [I, Kn] using
      (SpherePacking.Integration.DifferentiationUnderIntegral.norm_integral_le_integral_bound_mul_const
        (μ := μ) (f := gN n x) (bound := bound)
        (E := Real.exp (-2 * Real.pi * Real.sqrt x)) (hbound_int := hbound_int) hbound_ae)
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖
        = x ^ k * ‖iteratedDeriv n J₅' x‖ := by
          simp [Real.norm_of_nonneg hx,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n) (f := J₅') (x := x)]
    _ ≤ x ^ k * (2 * ‖I n x‖) :=
      mul_le_mul_of_nonneg_left (le_of_eq (by simp [hiterJ])) (pow_nonneg hx k)
    _ ≤ x ^ k * (2 * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x))) := by gcongr
    _ ≤ (2 * Kn) * B := by
      nlinarith [mul_le_mul_of_nonneg_left
        (by simpa [mul_assoc] using hB x hx : x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x) ≤ B)
        (by positivity : (0 : ℝ) ≤ 2 * Kn)]

end

end MagicFunction.b.Schwartz.J5Smooth

noncomputable section

namespace Complex

open Set Real intervalIntegral Metric Filter MeasureTheory
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {x₁ x₂ : ℝ} (y : ℝ)

lemma hzero (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (m : ℝ) (hm : m ≥ y) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
      + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) - (I • ∫ (t : ℝ) in y..m, f (x₁ + t * I))
    = 0 := by
  simpa using
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (x₁ + y * I)
      (x₂ + m * I) s hs
      (hcont.mono (by
        rw [reProdIm_subset_iff]
        gcongr
        · simp
        · simpa [uIcc_of_le hm] using (Icc_subset_Ici_self : Icc y m ⊆ Ici y)))
      (fun z hz => by
        obtain ⟨hz, hzns⟩ : z ∈ Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Ioo (min y m) (max y m) ∧ z ∉ s := by
          simpa using hz
        refine hdiff z ⟨?_, hzns⟩
        rw [mem_reProdIm] at hz ⊢
        exact ⟨hz.1, by simpa [min_eq_left hm] using (mem_Ioo.1 hz.2).1⟩)

/-- **Deformation of open rectangular contours** under integrability of `f` along both verticals. -/
public theorem
    integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
    (hcont : ContinuousOn f ([[x₁, x₂]] ×ℂ (Ici y))) (s : Set ℂ) (hs : s.Countable)
    (hdiff : ∀ x ∈ ((Ioo (min x₁ x₂) (max x₁ x₂)) ×ℂ (Ioi y)) \ s, DifferentiableAt ℂ f x)
    (hint₁ : IntegrableOn (fun (t : ℝ) ↦ f (x₁ + t * I)) (Ioi y) volume)
    (hint₂ : IntegrableOn (fun (t : ℝ) ↦ f (x₂ + t * I)) (Ioi y) volume)
    (htendsto : ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε) :
    (∫ (x : ℝ) in x₁..x₂, f (x + y * I)) + (I • ∫ (t : ℝ) in Ioi y, f (x₂ + t * I))
      - (I • ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)) = 0 := by
  set C₁ := ∫ (t : ℝ) in Ioi y, f (x₁ + t * I)
  set C₂ := ∫ (t : ℝ) in Ioi y, f (x₂ + t * I)
  have hC₁ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop (𝓝 (I • C₁)) :=
    (intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id).const_smul I
  have hC₂ : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)) atTop (𝓝 (I • C₂)) :=
    (intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id).const_smul I
  have heventually : (fun (m : ℝ) ↦
      (∫ (x : ℝ) in x₁..x₂, f (x + y * I))
        - (∫ (x : ℝ) in x₁..x₂, f (x + m * I))
        + (I • ∫ (t : ℝ) in y..m, f (x₂ + t * I)))
      =ᶠ[atTop] (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) := by
    filter_upwards [eventually_ge_atTop y] with m hm
    rw [← sub_eq_zero, ← (hzero y hcont s hs hdiff m hm)]
  have hC₁' : Tendsto (fun m ↦ I • ∫ (t : ℝ) in y..m, f (x₁ + t * I)) atTop
      (𝓝 ((∫ (t : ℝ) in x₁..x₂, f (t + y * I)) + I • C₂)) := by
    rw [tendsto_congr' heventually.symm, ← sub_zero (∫ (t : ℝ) in x₁..x₂, f (↑t + ↑y * I))]
    refine (Tendsto.sub ?_ ?_).add hC₂
    · rw [sub_zero, tendsto_const_nhds_iff]
    · show Tendsto (fun (m : ℝ) ↦ ∫ (x : ℝ) in x₁..x₂, f (x + m * I)) atTop (𝓝 0)
      by_cases h : x₁ = x₂
      · subst h; simp
      simp only [NormedAddCommGroup.tendsto_nhds_zero, eventually_atTop, ge_iff_le]
      intro ε hε
      have hx : 0 < |x₂ - x₁| := abs_sub_pos.mpr (ne_comm.mp h)
      obtain ⟨M, hM⟩ :=
        htendsto ((1 / 2 : ℝ) * (ε / |x₂ - x₁|)) (mul_pos (by norm_num) (div_pos hε hx))
      refine ⟨M, fun m hm => ?_⟩
      calc ‖∫ (x : ℝ) in x₁..x₂, f (x + m * I)‖
      _ ≤ ((1 / 2) * (ε / |x₂ - x₁|)) * |x₂ - x₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun x _ =>
            (hM (x + m * I) (by simpa using hm)).le
      _ < ε := by field_simp [hx.ne']; linarith
  exact sub_eq_zero.2 (tendsto_nhds_unique hC₁ hC₁').symm

/-- Finite-rectangle deformation when the top-edge integral tends to `0` as height → ∞. -/
public theorem rect_deform_of_tendsto_top {f : ℂ → E} {x₁ x₂ y : ℝ}
    (hcont : ContinuousOn f (Set.uIcc x₁ x₂ ×ℂ Set.Ici y))
    (hdiff :
      ∀ z ∈ (Set.Ioo (min x₁ x₂) (max x₁ x₂) ×ℂ Set.Ioi y), DifferentiableAt ℂ f z)
    (hint₁ :
      IntegrableOn (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * I)) (Set.Ioi y) volume)
    (hint₂ :
      IntegrableOn (fun t : ℝ => f ((x₂ : ℂ) + (t : ℂ) * I)) (Set.Ioi y) volume)
    (htop :
      Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I)) atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
          (I • ∫ t in Set.Ioi y, f ((x₂ : ℂ) + (t : ℂ) * I)) -
            (I • ∫ t in Set.Ioi y, f ((x₁ : ℂ) + (t : ℂ) * I)) = 0 := by
  have hEq :
      (fun m : ℝ =>
          (∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)) +
              (I • ∫ t in y..m, f ((x₂ : ℂ) + (t : ℂ) * I)) -
                (I • ∫ t in y..m, f ((x₁ : ℂ) + (t : ℂ) * I))) =ᶠ[atTop]
        fun m : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (m : ℂ) * I) := by
    filter_upwards [eventually_ge_atTop y] with m hm
    have hr := Complex.hzero (f := f) (x₁ := x₁) (x₂ := x₂) (y := y) hcont (s := (∅ : Set ℂ))
      (hs := by simp) (fun z hz => hdiff z (by simpa using hz.1)) m hm
    grind only
  simpa using tendsto_nhds_unique
    ((tendsto_const_nhds.add ((intervalIntegral_tendsto_integral_Ioi y hint₂
      tendsto_id).const_smul I)).sub
      ((intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id).const_smul I))
    ((tendsto_congr' hEq).2 htop)

end Complex

namespace SpherePacking.Integration.SmoothIntegralCommon

open scoped Interval
open Complex Real Set MeasureTheory Filter intervalIntegral
open SpherePacking.Integration.DifferentiationUnderIntegral

variable {coeff hf : ℝ → ℂ}

/-- The basic family of interval integrals, with the `n`-th derivative integrand `gN n`. -/
@[expose] public def I (n : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t

/-- Smoothness of `x ↦ I 0 x` under the hypotheses needed for dominated differentiation. -/
public theorem contDiff_integral
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) := by
  simpa using
    SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I (coeff := coeff) (hf := hf))
      (fun n x => by
        simpa [I] using hasDerivAt_integral_gN_of_continuous (coeff := coeff) (hf := hf)
          continuous_hf continuous_coeff exists_bound_norm_h coeff_norm_le n x)

/-- One-sided decay for `I 0 x`, specialized when `Re (coeff t) = -π` for all `t`. -/
public theorem decay_integral_of_coeff_re
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (coeff_re : ∀ t : ℝ, (coeff t).re = (-Real.pi : ℝ)) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖ ≤ C :=
    fun k n => by
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_h
  have hMh0 : 0 ≤ Mh := (norm_nonneg (hf 1)).trans (hMh 1 (by simp))
  have norm_cexp : ∀ x t : ℝ, ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x) := fun x t => by
    simp [Complex.norm_exp, Complex.mul_re, coeff_re t, mul_comm]
  refine ⟨(2 * Real.pi) ^ n * Mh * B, fun x hx => ?_⟩
  have hrepr := congrArg (fun f : ℝ → ℂ => f x) <|
    show iteratedDeriv n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) =
        fun x : ℝ ↦ I (coeff := coeff) (hf := hf) n x by
      simpa using
        SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
          (I := fun (n : ℕ) (x : ℝ) => I (coeff := coeff) (hf := hf) n x)
          (fun n x => by
            simpa [I] using hasDerivAt_integral_gN_of_continuous (coeff := coeff) (hf := hf)
              continuous_hf continuous_coeff ⟨Mh, hMh⟩ coeff_norm_le (n := n) (x₀ := x)) n
  have hnormI :
      ‖I (coeff := coeff) (hf := hf) n x‖ ≤
        (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x) := by
    rw [I]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (C := (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x))
      (f := fun t : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t) (fun t ht => ?_)).trans_eq (by simp)
    have hmul : ‖coeff t‖ ^ n * ‖hf t‖ ≤ (2 * Real.pi) ^ n * Mh :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n) (hMh t ht)
        (norm_nonneg _) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)
    calc ‖gN (coeff := coeff) (hf := hf) n x t‖
        = ‖coeff t‖ ^ n * ‖hf t‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by
          simp [gN, g, norm_pow, mul_left_comm, mul_comm, mul_assoc]
      _ ≤ (2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x) := by
          simpa [mul_assoc, norm_cexp] using
            mul_le_mul_of_nonneg_right hmul (norm_nonneg (cexp ((x : ℂ) * coeff t)))
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ ↦ I (coeff := coeff) (hf := hf) 0 x) x‖
      = x ^ k * ‖I (coeff := coeff) (hf := hf) n x‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hrepr]
    _ ≤ x ^ k * ((2 * Real.pi) ^ n * Mh * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Real.pi) ^ n * Mh * (x ^ k * Real.exp (-Real.pi * x)) := by ring
    _ ≤ (2 * Real.pi) ^ n * Mh * B :=
        mul_le_mul_of_nonneg_left (hB x hx)
          (mul_nonneg (pow_nonneg (by positivity) n) hMh0)

end SpherePacking.Integration.SmoothIntegralCommon

namespace MagicFunction.b.Schwartz.SmoothJ24Common

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory Filter intervalIntegral
open MagicFunction.b.PsiBounds SpherePacking.ForMathlib

/-- The coefficient function `t ↦ (π * I) * z t` used for smooth integral kernels. -/
@[expose] public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t : ℝ ↦ ((π : ℂ) * I) * z t

private lemma continuous_ψT'_comp {z : ℝ → ℂ} (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) :
    Continuous fun t : ℝ => ψT' (z t) := by
  refine SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
    (ψT := ψT) (ψT' := ψT') (MagicFunction.b.PsiBounds.continuous_ψT)
    (z := z) hz him (fun t => by simp [ψT', him t])

private lemma coeff_norm_le {z : ℝ → ℂ} (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) (t : ℝ) :
    ‖coeff z t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using norm_mul_pi_I_le_two_pi (z := z t) (hz := hnorm t)
private lemma exists_bound_norm_hf_mul {z : ℝ → ℂ} (c : ℂ) (hz : Continuous z)
    (him : ∀ t : ℝ, 0 < (z t).im) :
    ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖c * ψT' (z t)‖ ≤ M := by
  simpa using SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
    (f := fun t : ℝ => c * ψT' (z t)) (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))

/-- `ContDiff` for a function defined as `SmoothIntegralCommon.I` with `coeff t = (π * I) * z t`. -/
public theorem contDiff_of_eq_I0_mul {z : ℝ → ℂ} {c : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ,
        f x =
          SpherePacking.Integration.SmoothIntegralCommon.I
            (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) 0 x)
    (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  simpa [funext hfEq] using
    (SpherePacking.Integration.SmoothIntegralCommon.contDiff_integral
      (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t))
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))
      (by simpa [coeff] using (continuous_const.mul hz))
      (exists_bound_norm_hf_mul (z := z) (c := c) hz him) (coeff_norm_le (z := z) hnorm))

/-- Polynomial decay bounds for iterated derivatives of `f`, assuming `im (z t) = 1`. -/
public theorem decay_of_eq_I0_of_coeff_re_mul {z : ℝ → ℂ} {c : ℂ} {f : ℝ → ℂ}
    (hfEq :
      ∀ x : ℝ,
        f x =
          SpherePacking.Integration.SmoothIntegralCommon.I
            (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t)) 0 x)
    (hz : Continuous z) (him : ∀ t : ℝ, 0 < (z t).im) (hnorm : ∀ t : ℝ, ‖z t‖ ≤ 2)
    (him1 : ∀ t : ℝ, (z t).im = 1) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  simpa [funext hfEq] using
    (SpherePacking.Integration.SmoothIntegralCommon.decay_integral_of_coeff_re
      (coeff := coeff z) (hf := fun t : ℝ ↦ c * ψT' (z t))
      (continuous_const.mul (continuous_ψT'_comp (z := z) hz him))
      (by simpa [coeff] using (continuous_const.mul hz))
      (exists_bound_norm_hf_mul (z := z) (c := c) hz him) (coeff_norm_le (z := z) hnorm)
      (coeff_re := fun t => by
        simp [coeff, Complex.mul_re, him1 t, mul_assoc]))

end MagicFunction.b.Schwartz.SmoothJ24Common

namespace MagicFunction.b.Schwartz.J2Smooth

open scoped Interval Manifold Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds SpherePacking.ForMathlib

private lemma hfEq_J₂' (x : ℝ) :
    J₂' x = SpherePacking.Integration.SmoothIntegralCommon.I
      (coeff := SmoothJ24Common.coeff z₂')
      (hf := fun t : ℝ ↦ (1 : ℂ) * ψT' (z₂' t)) 0 x := by
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₂'` (the primed radial profile used to define the Schwartz kernel `J₂`). -/
public theorem contDiff_J₂' : ContDiff ℝ (⊤ : ℕ∞) J₂' :=
  SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₂') (c := (1 : ℂ)) hfEq_J₂'
    continuous_z₂' (fun t => by simpa using im_z₂'_pos_all t) norm_z₂'_le_two

/-- Schwartz-type decay bounds for `J₂'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₂' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₂' x‖ ≤ C :=
  SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₂') (c := (1 : ℂ)) hfEq_J₂'
    continuous_z₂' (fun t => by simpa using im_z₂'_pos_all t) norm_z₂'_le_two im_z₂'_eq_one

end MagicFunction.b.Schwartz.J2Smooth

namespace MagicFunction.b.Schwartz.J4Smooth

open scoped Interval Manifold Topology UpperHalfPlane
open Complex Real Set MeasureTheory Filter intervalIntegral MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds SpherePacking.ForMathlib

private lemma hfEq_J₄' (x : ℝ) :
    J₄' x = SpherePacking.Integration.SmoothIntegralCommon.I
      (coeff := SmoothJ24Common.coeff z₄')
      (hf := fun t : ℝ ↦ (-1 : ℂ) * ψT' (z₄' t)) 0 x := by
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', SmoothJ24Common.coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- Smoothness of `J₄'` (the primed radial profile). -/
public theorem contDiff_J₄' : ContDiff ℝ (⊤ : ℕ∞) J₄' :=
  SmoothJ24Common.contDiff_of_eq_I0_mul (z := z₄') (c := (-1 : ℂ)) hfEq_J₄'
    continuous_z₄' (fun t => by simpa using im_z₄'_pos_all t) norm_z₄'_le_two

/-- Schwartz-type decay bounds for `J₄'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₄' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C :=
  SmoothJ24Common.decay_of_eq_I0_of_coeff_re_mul (z := z₄') (c := (-1 : ℂ)) hfEq_J₄'
    continuous_z₄' (fun t => by simpa using im_z₄'_pos_all t) norm_z₄'_le_two im_z₄'_eq_one

end MagicFunction.b.Schwartz.J4Smooth

namespace MagicFunction.b.Schwartz.J3Smooth

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm
open Complex Real Set intervalIntegral
open MagicFunction.Parametrisations MagicFunction.b.RealIntegrals
open Matrix ModularGroup ModularForm

/-- Compatibility of `ψT'` and `ψI'` along the parametrisations `z₃'`/`z₅'`. -/
public lemma ψT'_z₃'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₃' t) = ψI' (z₅' t) := by
  simpa using MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t) ht

lemma J₃'_eq (x : ℝ) :
    J₃' x = (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by
  have hJ3 :
      J₃' x =
        (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) *
          cexp (π * (Complex.I : ℂ) * x) := by
    calc
      J₃' x
          = ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψT' (z₃' t) * cexp (π * (Complex.I : ℂ) * x * (z₃' t)) := by
              simp [RealIntegrals.J₃']
      _ = ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t)) *
                cexp (π * (Complex.I : ℂ) * x) := by
              refine intervalIntegral.integral_congr fun t ht => ?_
              have htIcc : t ∈ Icc (0 : ℝ) 1 := by
                simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
              have hψ := ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
              have hcexp : cexp (π * (Complex.I : ℂ) * x * (z₃' t)) =
                  cexp (π * (Complex.I : ℂ) * x * (z₅' t)) *
                    cexp (π * (Complex.I : ℂ) * x) := by
                have hz : z₃' t = z₅' t + 1 := by
                  simp [z₃'_eq_of_mem htIcc, z₅'_eq_of_mem htIcc, add_comm]
                simp [hz, mul_add, mul_assoc, mul_left_comm, mul_comm, Complex.exp_add]
              grind only
      _ = (∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) *
            cexp (π * (Complex.I : ℂ) * x) := integral_mul_const _ _
  have hK :
      (∫ t in (0 : ℝ)..1,
          (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))) =
        (-1 / 2 : ℂ) * J₅' x := by
    set K : ℂ :=
      ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * cexp (π * (Complex.I : ℂ) * x * (z₅' t))
    have hJ5 : J₅' x = (-2 : ℂ) * K := by simp [RealIntegrals.J₅', K]
    grind only
  calc
    J₃' x = ((-1 / 2 : ℂ) * J₅' x) * cexp (π * (Complex.I : ℂ) * x) := by simpa [hK] using hJ3
    _ = (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by ring_nf

/-- Smoothness of `J₃'`. -/
public theorem contDiff_J₃' : ContDiff ℝ (⊤ : ℕ∞) J₃' := by
  have hExp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ cexp ((π : ℂ) * Complex.I * (x : ℂ))) :=
    ((contDiff_const.mul contDiff_const).mul ofRealCLM.contDiff).cexp
  have hmul : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x) :=
    (contDiff_const.mul hExp).mul MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅'
  have hEq : (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((π : ℂ) * Complex.I * (x : ℂ)) * J₅' x) = J₃' :=
    funext fun x => by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (J₃'_eq (x := x)).symm
  simpa [hEq] using hmul

/-- Schwartz-type decay bounds for `J₃'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₃' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₃' x‖ ≤ C := fun k n => by
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c)
  let f : ℝ → ℂ := fun x ↦ (-1 / 2 : ℂ) • e x
  have hf_cont : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f, e] using ((ofRealCLM.contDiff.mul contDiff_const).cexp.const_smul (-1 / 2 : ℂ))
  obtain ⟨C, hC⟩ := SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left
    (f := f) (g := J₅') (k := k) (n := n) (B := fun m ↦ (1 / 2 : ℝ) * Real.pi ^ m)
    hf_cont MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅'
    (fun m x => SpherePacking.ForMathlib.norm_iteratedFDeriv_smul_cexp_mul_pi_I_le m x)
    (fun m => by simpa using (MagicFunction.b.Schwartz.J5Smooth.decay_J₅' (k := k) (n := m)))
  refine ⟨C, fun x hx => ?_⟩
  have hJ3fun : J₃' = fun y : ℝ ↦ f y * J₅' y :=
    funext fun y => by simp [f, e, c, mul_assoc, mul_left_comm, mul_comm, J₃'_eq (x := y)]
  simpa [hJ3fun] using hC x hx

end MagicFunction.b.Schwartz.J3Smooth

namespace MagicFunction.b.SchwartzIntegrals

open scoped ContDiff Topology
open MagicFunction MagicFunction.b MagicFunction.b.RealIntegrals
open Set Complex Real SchwartzMap RadialSchwartz.Bridge

/-- 1-D Schwartz functions from the primed radial integrals `J₁'`-`J₅'`. -/
public def J₁' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₁')
  MagicFunction.b.Schwartz.J1Smooth.contDiff_J₁' MagicFunction.b.Schwartz.J1Smooth.decay_J₁'
public def J₂' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₂')
  MagicFunction.b.Schwartz.J2Smooth.contDiff_J₂' MagicFunction.b.Schwartz.J2Smooth.decay_J₂'
public def J₃' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₃')
  MagicFunction.b.Schwartz.J3Smooth.contDiff_J₃' MagicFunction.b.Schwartz.J3Smooth.decay_J₃'
public def J₄' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₄')
  MagicFunction.b.Schwartz.J4Smooth.contDiff_J₄' MagicFunction.b.Schwartz.J4Smooth.decay_J₄'
public def J₅' : 𝓢(ℝ, ℂ) := RadialSchwartz.Bridge.fCutSchwartz (f := RealIntegrals.J₅')
  MagicFunction.b.Schwartz.J5Smooth.contDiff_J₅' MagicFunction.b.Schwartz.J5Smooth.decay_J₅'

private theorem J₆'_smooth_aux :
    ContDiff ℝ ∞ (fun r ↦ RadialSchwartz.cutoffC r * RealIntegrals.J₆' r) := by
  simpa using (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1
    (f := RealIntegrals.J₆') MagicFunction.b.Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1)

/-- 1-D Schwartz function from the primed radial integral `J₆'`. -/
public def J₆' : 𝓢(ℝ, ℂ) where
  toFun := RadialSchwartz.Bridge.fCut MagicFunction.b.RealIntegrals.J₆'
  smooth' := by simpa [RadialSchwartz.Bridge.fCut] using J₆'_smooth_aux
  decay' := by
    simpa using (RadialSchwartz.cutoffC_mul_decay_of_nonneg_of_contDiff
      (f := MagicFunction.b.RealIntegrals.J₆') (hg_smooth := J₆'_smooth_aux)
      MagicFunction.b.Schwartz.J6Smooth.decay_J₆')

/-- Schwartz functions on `ℝ⁸` from the radial profiles `J₁'`-`J₆'`. -/
@[expose] public def J₁ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₁'
@[expose] public def J₂ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₂'
@[expose] public def J₃ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₃'
@[expose] public def J₄ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₄'
@[expose] public def J₅ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₅'
@[expose] public def J₆ : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real _ J₆'

@[simp] public lemma J₁'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₁' : ℝ → ℂ) r = RealIntegrals.J₁' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₂'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₂' : ℝ → ℂ) r = RealIntegrals.J₂' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₃'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₃' : ℝ → ℂ) r = RealIntegrals.J₃' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₄'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₄' : ℝ → ℂ) r = RealIntegrals.J₄' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₅'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₅' : ℝ → ℂ) r = RealIntegrals.J₅' r := fCut_apply_of_nonneg _ hr
@[simp] public lemma J₆'_apply_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (J₆' : ℝ → ℂ) r = RealIntegrals.J₆' r := fCut_apply_of_nonneg _ hr

end MagicFunction.b.SchwartzIntegrals
namespace MagicFunction.FourierEigenfunctions

open SchwartzMap MagicFunction.b.SchwartzIntegrals

/-- Radial component of the -1-Fourier eigenfunction of Viazovska's magic function. -/
@[expose] public def b' : 𝓢(ℝ, ℂ) :=
  J₁' + J₂' + J₃' + J₄' + J₅' + J₆'

/-- The -1-Fourier eigenfunction of Viazovska's magic function. -/
@[expose] public def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real (EuclideanSpace ℝ (Fin 8)) b'

/-- Expand `b` as a sum of `MagicFunction.b.RadialFunctions.J₁`-`J₆`. -/
public theorem b_eq_sum_integrals_RadialFunctions : b =
    MagicFunction.b.RadialFunctions.J₁ + MagicFunction.b.RadialFunctions.J₂ +
      MagicFunction.b.RadialFunctions.J₃ + MagicFunction.b.RadialFunctions.J₄ +
      MagicFunction.b.RadialFunctions.J₅ + MagicFunction.b.RadialFunctions.J₆ := by
  ext x
  simp [b, b', MagicFunction.b.RadialFunctions.J₁, MagicFunction.b.RadialFunctions.J₂,
    MagicFunction.b.RadialFunctions.J₃, MagicFunction.b.RadialFunctions.J₄,
    MagicFunction.b.RadialFunctions.J₅, MagicFunction.b.RadialFunctions.J₆,
    sq_nonneg ‖x‖, add_assoc]

end MagicFunction.FourierEigenfunctions

end

/-! ## Special values for `b`, notably `b 0 = 0`. -/

namespace MagicFunction.b.SpecialValuesProof

open scoped UpperHalfPlane Topology
open Set SchwartzMap Real Complex Filter UpperHalfPlane ModularForm
  MagicFunction.FourierEigenfunctions MagicFunction.b.RealIntegrals
  MagicFunction.b.RadialFunctions MagicFunction.Parametrisations

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

lemma J₁'_J₃_eq_neg_J₅'_zero : J₁' (0 : ℝ) + J₃' 0 = -J₅' 0 := by
  have hI (z : ℝ → ℂ) (hz : ∀ t ∈ Icc (0 : ℝ) 1, ψT' (z t) = ψI' (z₅' t)) :
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z t)) =
        ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) :=
    intervalIntegral.integral_congr fun t ht => by
      simp [hz t (by simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)]
  have hJ1 : J₁' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₁'] using hI z₁' fun t => MagicFunction.b.PsiParamRelations.ψT'_z₁'_eq_ψI'_z₅' (t := t)
  have hJ3 : J₃' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    simpa [J₃'] using hI z₃' fun t => MagicFunction.b.PsiParamRelations.ψT'_z₃'_eq_ψI'_z₅' (t := t)
  simp [hJ1, hJ3, show J₅' (0 : ℝ) = (-2 : ℂ) *
    ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) by simp [J₅']]; ring

lemma ψT'_z₂'_eq_ψI'_add_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := by
  have hz2 : 0 < (z₂' t).im := im_z₂'_pos (t := t) (by simpa using ht)
  simpa [ψT', ψI', hz2, show ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩ : ℍ) = ⟨(t : ℂ) + Complex.I, by simp⟩ by
    ext1; simp [z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]] using
    (show ψT ⟨z₂' t, hz2⟩ = ψI ((1 : ℝ) +ᵥ ⟨z₂' t, hz2⟩) by simp [ψT, modular_slash_T_apply])

lemma ψS'_add_one (t : ℝ) (ht : 0 < t) :
    ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) := by
  have hz0 : 0 < (t * Complex.I).im := by simpa using ht
  have hz1 : 0 < ((1 : ℂ) + t * Complex.I).im := by simpa using ht
  let z0H : ℍ := ⟨t * Complex.I, hz0⟩
  simpa [ψS', hz0, hz1, ht, z0H, show ((1 : ℝ) +ᵥ z0H : ℍ) = ⟨(1 : ℂ) + t * Complex.I, hz1⟩ by
    ext1; simp [z0H, add_comm]] using show ψS ((1 : ℝ) +ᵥ z0H) = -ψS z0H by
      simpa [modular_slash_T_apply] using congrArg (fun F : ℍ → ℂ => F z0H) ψS_slash_T

lemma integrableOn_ψS'_vertical_left :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  have hC : ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) :=
    fun t ht => (hC0 t ht).trans (by gcongr; exact le_max_left _ _)
  have hEq : ∀ t : ℝ, 0 < t → ψS' (t * Complex.I) = ψS.resToImagAxis t := fun t ht0 => by
    simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
    (by simpa [mul_assoc] using
      ((exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := Real.pi) Real.pi_pos).const_mul C))
    ((((Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS)
          MagicFunction.b.PsiBounds.continuous_ψS).mono Set.Ioi_subset_Ici_self).congr
        fun t ht => hEq t (lt_trans (by norm_num) ht)).aestronglyMeasurable measurableSet_Ioi) <|
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      simpa [hEq t (lt_trans (by norm_num) ht)] using hC t ht.le

lemma J₂'_J₄_eq_neg_J₆'_zero : J₂' (0 : ℝ) + J₄' 0 = -J₆' 0 := by
  have hJ24 : J₂' (0 : ℝ) + J₄' 0 = ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
    have hJ2 : J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) := by
      simp only [J₂']; exact intervalIntegral.integral_congr fun t ht => by
        simp [ψT'_z₂'_eq_ψI'_add_one (t := t)
          (by simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht)]
    have hJ4 : J₄' (0 : ℝ) = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
      rw [show J₄' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) by simp [J₄']]
      have hEq :
          (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t)) =
            ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) :=
        intervalIntegral.integral_congr fun t ht => by
          have htIcc : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
          simp [show z₄' t = (1 - (t : ℂ)) + Complex.I by simpa using z₄'_eq_of_mem htIcc]
      let f : ℝ → ℂ := fun u => ψT' ((u : ℂ) + Complex.I)
      rw [hEq, intervalIntegral.integral_const_mul,
        (intervalIntegral.integral_congr fun t _ => by
          simp [f, show ((1 - t : ℝ) : ℂ) = (1 - t : ℂ) by push_cast; ring] :
            (∫ t in (0 : ℝ)..1, ψT' ((1 - t : ℂ) + Complex.I)) = ∫ t in (0 : ℝ)..1, f (1 - t)),
        (by simp : (∫ t in (0 : ℝ)..1, f (1 - t)) = ∫ t in (0 : ℝ)..1, f t), neg_one_mul]
    have hrel : ∀ t : ℝ, ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) := fun t =>
      sub_eq_of_eq_add' <| by
        have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
        simpa [ψI', ψT', ψS', hz] using
          congrArg (fun F : ℍ → ℂ => F ⟨(t : ℂ) + Complex.I, hz⟩) ψI_eq_add_ψT_ψS
    have hAddI : Continuous fun t : ℝ => (⟨(t : ℂ) + Complex.I, by simp⟩ : ℍ) :=
      Continuous.upperHalfPlaneMk (by fun_prop) (fun _ => by simp)
    simpa [hJ2, hJ4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := 0) (b := 1)
        ((by simpa [ψI'] using
            MagicFunction.b.PsiBounds.continuous_ψI.comp hAddI :
              Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I)).intervalIntegrable _ _)
        ((by simpa [ψT'] using
            MagicFunction.b.PsiBounds.continuous_ψT.comp hAddI :
              Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I)).intervalIntegrable _ _)).symm.trans
        (intervalIntegral.integral_congr fun t _ => hrel t)
  have hdiffψS :
      DifferentiableOn ℂ (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
    have hH2 := (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
    have hH3 := (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
    have hH4 := (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
    refine (DifferentiableOn.const_mul
        (((hH4.sub hH2).div (hH3.pow 2) (fun _ _ => pow_ne_zero 2 (H₃_ne_zero _))).sub
          ((hH2.add hH3).div (hH4.pow 2) (fun _ _ => pow_ne_zero 2 (H₄_ne_zero _))))
        (128 : ℂ)).congr fun z _ => ?_
    simpa [show (H₂_MF : ℍ → ℂ) = H₂ from rfl, show (H₃_MF : ℍ → ℂ) = H₃ from rfl,
      show (H₄_MF : ℍ → ℂ) = H₄ from rfl] using
      congrArg (fun f : ℍ → ℂ => f (UpperHalfPlane.ofComplex z)) ψS_eq'
  have hcont : ContinuousOn ψS' (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := by
    have hsubset : (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) ⊆ {z : ℂ | 0 < z.im} := fun z hz =>
      lt_of_lt_of_le (by norm_num) (by simpa [mem_Ici] using hz.2 : (1 : ℝ) ≤ z.im)
    refine (hdiffψS.continuousOn.mono hsubset).congr fun z hz => ?_
    have hz' : 0 < z.im := hsubset hz
    simp [ψS', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hdiff : ∀ z ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
      DifferentiableAt ℂ ψS' z := fun z hz => by
    have hzpos : 0 < z.im := lt_trans (by norm_num)
      (by simpa [mem_Ioi] using hz.1.2 : (1 : ℝ) < z.im)
    refine ((hdiffψS z hzpos).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hzpos)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hzpos] with w hw
    simp [ψS', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((0 : ℂ) + t * Complex.I)) = 0 := by
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using
    (Complex.integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := ψS') (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont (s := (∅ : Set ℂ))
        (by simp) hdiff (by simpa using integrableOn_ψS'_vertical_left)
        (by
          simpa [MeasureTheory.IntegrableOn] using (integrableOn_ψS'_vertical_left.neg).congr
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
              simp [ψS'_add_one t (lt_trans (by norm_num) ht)] :
              (fun t : ℝ => -ψS' (t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
                fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I))) (fun ε hε => by
          obtain ⟨M, hM⟩ := Filter.eventually_atImInfty.1 (show ∀ᶠ z in UpperHalfPlane.atImInfty,
            ‖ψS z‖ < ε by simpa [dist_eq_norm] using
              (Metric.tendsto_nhds.1 MagicFunction.b.PsiBounds.tendsto_ψS_atImInfty) ε hε)
          refine ⟨max M 1, fun z hz => ?_⟩
          have hzpos : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
          simpa [ψS', hzpos] using hM ⟨z, hzpos⟩ ((le_max_left _ _).trans hz)))
  have hright : (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
      -∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I) := by
    simpa [MeasureTheory.integral_neg] using MeasureTheory.integral_congr_ae
      (g := fun t : ℝ => -ψS' (t * Complex.I))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        simp [ψS'_add_one t (lt_trans (by norm_num) ht)])
  have hhor : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) -
      (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 := by
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg]
      using show (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
        (Complex.I • (-∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I))) -
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 by
        simpa [hright] using hrect
  have hJ6 : J₆' (0 : ℝ) =
      (-2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
    rw [show J₆' (0 : ℝ) = (-2 : ℂ) *
        ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) by simp [J₆'],
      MeasureTheory.integral_Ici_eq_integral_Ioi,
      MeasureTheory.integral_congr_ae (g := fun t : ℝ => (Complex.I : ℂ) * ψS' (t * Complex.I))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          simp [MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t)
            (le_of_lt (by simpa [Set.mem_Ioi] using ht)), mul_comm])]
    simp [MeasureTheory.integral_const_mul, smul_eq_mul]
  exact hJ24.trans (eq_neg_of_add_eq_zero_left (by
    simp [show (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) =
        (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) by
      simpa [sub_eq_zero] using hhor, hJ6]))

theorem b_zero : MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) = 0 := by
  rw [show MagicFunction.FourierEigenfunctions.b (0 : ℝ⁸) =
      J₁' (0 : ℝ) + J₂' 0 + J₃' 0 + J₄' 0 + J₅' 0 + J₆' 0 from by
    open MagicFunction.b.RadialFunctions in
    simpa [J₁, J₂, J₃, J₄, J₅, J₆] using congrArg (fun f : ℝ⁸ → ℂ => f (0 : ℝ⁸))
      MagicFunction.FourierEigenfunctions.b_eq_sum_integrals_RadialFunctions]
  linear_combination J₂'_J₄_eq_neg_J₆'_zero + J₁'_J₃_eq_neg_J₅'_zero

end MagicFunction.b.SpecialValuesProof

namespace MagicFunction.b.SpecialValues

open MagicFunction.FourierEigenfunctions

/-- The magic function `b` vanishes at the origin. -/
public theorem b_zero : b 0 = 0 := by
  simpa using MagicFunction.b.SpecialValuesProof.b_zero

end MagicFunction.b.SpecialValues


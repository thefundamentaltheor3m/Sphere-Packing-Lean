module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.ContDiffOnByDeriv
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.J6Integrable
import SpherePacking.Integration.SmoothIntegralIciOne
import SpherePacking.Integration.Measure


/-!
# Smoothness and decay for `J₆'` on `(-1, ∞)`

This file proves regularity of the primed radial integral `RealIntegrals.J₆'` on the open half-line
`Ioi (-1)`. The proofs differentiate under the integral sign using dominated differentiation, with
the exponential decay of `ψS` on the imaginary axis providing the integrable domination.

## Main statements
* `contDiffOn_J₆'_Ioi_neg1`
* `decay_J₆'`
-/


namespace MagicFunction.b.Schwartz.J6Smooth

noncomputable section

open scoped Topology ContDiff

open Complex Real Set MeasureTheory Filter

open MagicFunction.Parametrisations
open MagicFunction.b.RealIntegrals
open MagicFunction.b.PsiBounds
open MagicFunction.b.PsiBounds.PsiExpBounds
open SpherePacking.ForMathlib
open SpherePacking.Integration

def μ : Measure ℝ := μIciOne

-- The open set of parameters where the integral is dominated by an exponentially decaying bound.
def s : Set ℝ := Ioi (-1 : ℝ)

lemma isOpen_s : IsOpen s := isOpen_Ioi

abbrev coeff (t : ℝ) : ℂ := SmoothIntegralIciOne.coeff t

abbrev g (x t : ℝ) : ℂ := SmoothIntegralIciOne.g (hf := ψS.resToImagAxis) x t

abbrev gN (n : ℕ) (x t : ℝ) : ℂ := SmoothIntegralIciOne.gN (hf := ψS.resToImagAxis) n x t

lemma gN_measurable (n : ℕ) (x : ℝ) : AEStronglyMeasurable (gN n x) (μ) := by
  have hcoeff : Continuous coeff := by
    simpa [coeff] using (continuous_const.mul Complex.continuous_ofReal : Continuous fun t : ℝ =>
      (-Real.pi : ℂ) * (t : ℂ))
  have hψ : ContinuousOn (fun t : ℝ ↦ (ψS.resToImagAxis t)) (Ici (1 : ℝ)) :=
    Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) continuous_ψS
  have hexp : ContinuousOn (fun t : ℝ ↦ cexp ((x : ℂ) * coeff t)) (Ici (1 : ℝ)) :=
    ((continuous_const.mul hcoeff).cexp).continuousOn
  have hg : ContinuousOn (g x) (Ici (1 : ℝ)) := by
    simpa [g, mul_assoc] using (continuousOn_const.mul (hψ.mul hexp))
  refine (ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ))
    (s := Ici (1 : ℝ)) ?_ measurableSet_Ici).mono_measure (by simp [μ, μIciOne])
  simpa [gN] using (hcoeff.pow n).continuousOn.mul hg

lemma gN_integrable (n : ℕ) (x : ℝ) (hx : x ∈ s) : Integrable (gN n x) μ := by
  have hx' : -1 < x := hx
  have hmeas : AEStronglyMeasurable (gN_J6_integrand ψS.resToImagAxis n x)
      ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) :=
    gN_measurable (n := n) (x := x)
  simpa [μ, μIciOne] using
    (integrable_gN_J6 (f := ψS.resToImagAxis)
      (hBound := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
      (n := n) (x := x) hx' (hmeas := hmeas))

lemma coeff_norm (t : ℝ) (ht : t ∈ Ici (1 : ℝ)) : ‖coeff t‖ = π * t := by
  simpa [coeff] using SmoothIntegralIciOne.coeff_norm (t := t) ht

lemma g_norm_bound (x : ℝ) (t : ℝ) :
    ‖g x t‖ ≤ ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) := by
  simpa [g] using SmoothIntegralIciOne.g_norm_bound (hf := ψS.resToImagAxis) (x := x) (t := t)

def F (n : ℕ) (x : ℝ) : ℂ := ∫ t in Ici (1 : ℝ), gN n x t

-- Incorporate the outer constant factor from the definition of `J₆'`.
def G (n : ℕ) (x : ℝ) : ℂ := (-2 : ℂ) * F n x

lemma hasDerivAt_F (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => F n y) (F (n + 1) x) x := by
  have exists_bound :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤
        C * Real.exp (-(Real.pi * (1 : ℝ)) * t) := by
    simpa [one_mul, mul_assoc] using exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  simpa [F, μ] using
    (SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := ψS.resToImagAxis) (shift := (1 : ℝ))
      (exists_bound_norm_hf := exists_bound)
      (gN_measurable := fun n x => by simpa [μ] using gN_measurable (n := n) (x := x))
      (n := n) (x := x) hx (hF_int := by simpa [μ] using gN_integrable (n := n) (x := x) hx))

lemma hasDerivAt_G (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => G n y) (G (n + 1) x) x := by
  simpa [G] using (hasDerivAt_F (n := n) (x := x) hx).const_mul (-2 : ℂ)

lemma deriv_G (n : ℕ) (x : ℝ) (hx : x ∈ s) : deriv (G n) x = G (n + 1) x :=
  (hasDerivAt_G (n := n) (x := x) hx).deriv

lemma iteratedDeriv_G_eq :
    ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s :=
  SpherePacking.ForMathlib.eqOn_iteratedDeriv_eq_of_deriv_eq (hs := isOpen_s) (G := G)
    (hderiv := fun n x hx => deriv_G (n := n) (x := x) hx)

private lemma integral_J6_integrand_eq_integral_g (x : ℝ) :
    (∫ t in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' (z₆' t) * cexp (π * (Complex.I : ℂ) * x * (z₆' t))) =
      ∫ t in Ici (1 : ℝ), g x t := by
  refine integral_congr_ae <|
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
  have hψ : ψS' (z₆' t) = ψS.resToImagAxis t := by
    simp [ψS', Function.resToImagAxis, ResToImagAxis, hz, ht0, mul_comm]
  have hcexp :
      cexp ((π : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)) = cexp ((x : ℂ) * coeff t) := by
    refine congrArg cexp ?_
    simp [coeff, SmoothIntegralIciOne.coeff, hz]; ring_nf; simp
  dsimp
  rw [hψ, hcexp]
  simp [g, SmoothIntegralIciOne.g, Function.resToImagAxis, ResToImagAxis, mul_assoc]

private lemma J₆'_eq_G0 (x : ℝ) : RealIntegrals.J₆' x = G 0 x := by
  have hEq : RealIntegrals.J₆' x = (-2 : ℂ) * ∫ t in Ici (1 : ℝ), g x t := by
    simpa [RealIntegrals.J₆', mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun J : ℂ => (-2 : ℂ) * J) (integral_J6_integrand_eq_integral_g (x := x))
  simpa [G, F, gN, SmoothIntegralIciOne.gN, g] using hEq

/-- Smoothness of `RealIntegrals.J₆'` on the open half-line `Ioi (-1)`. -/
public theorem contDiffOn_J₆'_Ioi_neg1 :
    ContDiffOn ℝ ∞ RealIntegrals.J₆' (Ioi (-1 : ℝ)) := by
  have hF0 : ContDiffOn ℝ ∞ (F 0) s := by
    simpa using
      (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
        (fun n x hx => by simpa using (hasDerivAt_F (n := n) (x := x) hx)) 0)
  have hG0 : ContDiffOn ℝ ∞ (G 0) s := by simpa [G] using (contDiffOn_const.mul hF0)
  exact hG0.congr (fun x _ => J₆'_eq_G0 x)

/-- Schwartz-type decay bounds for `RealIntegrals.J₆'` and its iterated derivatives on `0 ≤ x`.

The prime in `decay_J₆'` refers to the function `RealIntegrals.J₆'`. -/
public theorem decay_J₆' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  rcases exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨Cψ, hCψ⟩
  have hCψ0 : 0 ≤ Cψ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity) ?_
    simpa using (hCψ 1 (le_rfl : (1 : ℝ) ≤ 1))
  -- A uniform bound for the integral defining `G n x` when `x ≥ 0`.
  let bound : ℝ → ℝ := fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) * Cψ
  have hbound_int : Integrable bound (μ) := by
    have hInt :
        IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-Real.pi * t)) (Ici (1 : ℝ)) volume :=
      SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi)
        (by simpa using Real.pi_pos)
    have : Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-Real.pi * t)) (μ) := by
      simpa [IntegrableOn, μIciOne] using hInt
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      this.const_mul ((Real.pi ^ n) * Cψ)
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    refine integral_nonneg_of_ae <|
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
    positivity
  refine ⟨2 * Kn * B, fun x hx => ?_⟩
  have hxabs : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hx_s : x ∈ s := lt_of_lt_of_le (by norm_num) hx
  have hiter : iteratedDeriv n RealIntegrals.J₆' x = G n x := by
    have hfun : RealIntegrals.J₆' = G 0 := funext J₆'_eq_G0
    simpa [hfun] using (iteratedDeriv_G_eq (n := n) (m := 0)) hx_s
  have hnorm_iter :
      ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ = ‖iteratedDeriv n RealIntegrals.J₆' x‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hGbound : ‖G n x‖ ≤ 2 * Kn * Real.exp (-Real.pi * x) := by
    have hFn : ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) := by
      have hnorm : ‖F n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := by
        have hEq : F n x = ∫ t, gN n x t ∂μ := by simp [F, μ, μIciOne]
        simpa [hEq] using (norm_integral_le_integral_norm (μ := μ) (f := gN n x))
      have hbound_ae :
          ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) := by
        refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
        intro t ht
        have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
        have hcoeff' : ‖coeff t‖ ^ n ≤ (Real.pi * t) ^ n := by simp [coeff_norm t ht]
        have hψ : ‖ψS.resToImagAxis t‖ ≤ Cψ * Real.exp (-Real.pi * t) := hCψ t ht
        have hg : ‖g x t‖ ≤ ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) :=
          g_norm_bound (x := x) (t := t)
        have hxexp : Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) :=
          SpherePacking.ForMathlib.exp_neg_mul_mul_le_exp_neg_mul_of_one_le
            (b := Real.pi) (x := x) (t := t) Real.pi_pos.le hx ht
        calc
          ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
                simp [gN, SmoothIntegralIciOne.gN, g, coeff, norm_pow]
          _ ≤ (Real.pi * t) ^ n * (‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by gcongr
          _ ≤ (Real.pi * t) ^ n * ((Cψ * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x)) := by
                gcongr
          _ = bound t * Real.exp (-Real.pi * x) := by ring
      have hbound_int' : Integrable (fun t ↦ bound t * Real.exp (-Real.pi * x)) μ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hbound_int.mul_const (Real.exp (-Real.pi * x))
      have hle : ∫ t, ‖gN n x t‖ ∂μ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg (gN n x t))
          hbound_int' hbound_ae
      calc ‖F n x‖
          ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ := hnorm.trans hle
        _ = Kn * Real.exp (-Real.pi * x) := by
            simpa [Kn] using
              (integral_mul_const (μ := μ) (r := Real.exp (-Real.pi * x)) (f := bound))
    calc ‖G n x‖
        ≤ 2 * (Kn * Real.exp (-Real.pi * x)) := by
          simpa [G, norm_mul, mul_assoc] using
            mul_le_mul_of_nonneg_left hFn (by positivity : (0 : ℝ) ≤ 2)
      _ = 2 * Kn * Real.exp (-Real.pi * x) := by ring_nf
  have hpoly : x ^ k * Real.exp (-Real.pi * x) ≤ B := hB x hx
  have hpow0 : 0 ≤ 2 * Kn := by positivity
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.J₆' x‖ := by simp [hxabs, hnorm_iter]
    _ = x ^ k * ‖G n x‖ := by simp [hiter]
    _ ≤ x ^ k * (2 * Kn * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-Real.pi * x)) := by ring_nf
    _ ≤ (2 * Kn) * B := by simpa using (mul_le_mul_of_nonneg_left hpoly hpow0)
    _ = 2 * Kn * B := by ring

end

end MagicFunction.b.Schwartz.J6Smooth

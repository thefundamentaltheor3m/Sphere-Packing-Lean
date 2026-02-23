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

lemma isOpen_s : IsOpen s := by
  simpa [s] using (isOpen_Ioi : IsOpen (Ioi (-1 : ℝ)))

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
  have hmeas :
      AEStronglyMeasurable (gN n x) ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) ?_ measurableSet_Ici
    simpa [gN] using (hcoeff.pow n).continuousOn.mul hg
  simpa [μ, μIciOne] using hmeas

lemma gN_integrable (n : ℕ) (x : ℝ) (hx : x ∈ s) : Integrable (gN n x) μ := by
  have hx' : -1 < x := by simpa [s] using hx
  let f : ℝ → ℂ := gN_J6_integrand ψS.resToImagAxis n x
  have hf : gN n x = f := by
    funext t
    simp [gN, SmoothIntegralIciOne.gN, SmoothIntegralIciOne.g, SmoothIntegralIciOne.coeff, f,
      gN_J6_integrand, mul_left_comm, mul_comm]
  have hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    simpa [hf, μ, μIciOne] using (gN_measurable (n := n) (x := x))
  have hInt : Integrable f ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    simpa [f] using
      (integrable_gN_J6 (f := ψS.resToImagAxis)
        (hBound := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
        (n := n) (x := x) hx' (hmeas := by simpa [f] using hmeas))
  simpa [hf, μ, μIciOne] using hInt

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
  have hx' : (-1 : ℝ) < x := by simpa [s] using hx
  have hInt : Integrable (gN n x) μ := gN_integrable (n := n) (x := x) hx
  simpa [F, μ] using
    (SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := ψS.resToImagAxis) (shift := (1 : ℝ)) (hshift := (by norm_num))
      (exists_bound_norm_hf := exists_bound)
      (gN_measurable := fun n x => by simpa [μ] using gN_measurable (n := n) (x := x))
      (n := n) (x := x) hx' (hF_int := by simpa [μ] using hInt))

lemma hasDerivAt_G (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => G n y) (G (n + 1) x) x := by
  simpa [G] using (hasDerivAt_F (n := n) (x := x) hx).const_mul (-2 : ℂ)

lemma deriv_G (n : ℕ) (x : ℝ) (hx : x ∈ s) : deriv (G n) x = G (n + 1) x :=
  (hasDerivAt_G (n := n) (x := x) hx).deriv

lemma iteratedDeriv_G_eq :
    ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  simpa using (SpherePacking.ForMathlib.eqOn_iteratedDeriv_eq_of_deriv_eq (hs := isOpen_s) (G := G)
    (hderiv := fun n x hx => deriv_G (n := n) (x := x) hx))

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
  have harg :
      (π : ℂ) * (Complex.I : ℂ) * (x : ℂ) * ((Complex.I : ℂ) * t) = (x : ℂ) * coeff t := by
    simp [coeff, SmoothIntegralIciOne.coeff]
    ring_nf
    simp
  have hcexp :
      cexp ((π : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)) = cexp ((x : ℂ) * coeff t) := by
    simpa [hz] using congrArg cexp harg
  -- reduce the β-redex introduced by `integral_congr_ae`
  dsimp
  rw [hψ, hcexp]
  simp [g, SmoothIntegralIciOne.g, Function.resToImagAxis, ResToImagAxis, mul_assoc]

/-- Smoothness of `RealIntegrals.J₆'` on the open half-line `Ioi (-1)`. -/
public theorem contDiffOn_J₆'_Ioi_neg1 :
    ContDiffOn ℝ ∞ RealIntegrals.J₆' (Ioi (-1 : ℝ)) := by
  have hJ : ContDiffOn ℝ ∞ RealIntegrals.J₆' s := by
    have hF0 : ContDiffOn ℝ ∞ (F 0) s := by
      simpa using
        (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
          (fun n x hx => by simpa using (hasDerivAt_F (n := n) (x := x) hx)) 0)
    have hG0 : ContDiffOn ℝ ∞ (G 0) s := by simpa [G] using (contDiffOn_const.mul hF0)
    refine hG0.congr ?_
    intro x hx
    have hEq :
        RealIntegrals.J₆' x = (-2 : ℂ) * ∫ t in Ici (1 : ℝ), g x t := by
      have hInt := integral_J6_integrand_eq_integral_g (x := x)
      have h' := congrArg (fun J : ℂ => (-2 : ℂ) * J) hInt
      simpa [RealIntegrals.J₆', mul_assoc, mul_left_comm, mul_comm] using h'
    have hInt0 : (∫ t in Ici (1 : ℝ), g x t) = ∫ t in Ici (1 : ℝ), gN 0 x t := by
      simp [gN, SmoothIntegralIciOne.gN, g]
    have hEq' :
        RealIntegrals.J₆' x = (-2 : ℂ) * ∫ t in Ici (1 : ℝ), gN 0 x t := by
      simpa [hInt0] using hEq
    simpa [G, F] using hEq'
  simpa [s] using hJ

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
    have hnonneg : 0 ≤ᵐ[μ] fun t ↦ bound t := by
      refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
      have : 0 ≤ (t ^ n * Real.exp (-Real.pi * t)) := by positivity
      have hpi : 0 ≤ (Real.pi ^ n : ℝ) := pow_nonneg Real.pi_pos.le n
      have : 0 ≤ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) := mul_nonneg hpi this
      have : 0 ≤ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) * Cψ := mul_nonneg this hCψ0
      simpa [bound] using this
    simpa [Kn] using (integral_nonneg_of_ae hnonneg)
  let C : ℝ := 2 * Kn * B
  refine ⟨C, ?_⟩
  intro x hx
  have hxabs : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hx_s : x ∈ s := by
    have : (-1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
    simpa [s] using this
  have hiter :
      iteratedDeriv n RealIntegrals.J₆' x = G n x := by
    -- `J₆' = G 0` as functions, then use the iterated-derivative recursion for `G`.
    have hfun : RealIntegrals.J₆' = G 0 := by
      funext y
      have hEq :
          RealIntegrals.J₆' y = (-2 : ℂ) * ∫ t in Ici (1 : ℝ), g y t := by
        simpa [RealIntegrals.J₆', mul_assoc, mul_left_comm, mul_comm] using
          congrArg (fun J : ℂ => (-2 : ℂ) * J) (integral_J6_integrand_eq_integral_g (x := y))
      have hInt0 : (∫ t in Ici (1 : ℝ), g y t) = ∫ t in Ici (1 : ℝ), gN 0 y t := by
        simp [gN, SmoothIntegralIciOne.gN, g]
      have hEq' :
          RealIntegrals.J₆' y = (-2 : ℂ) * ∫ t in Ici (1 : ℝ), gN 0 y t := by
        simpa [hInt0] using hEq
      simpa [G, F] using hEq'
    have hG : iteratedDeriv n (G 0) x = G (n + 0) x := (iteratedDeriv_G_eq (n := n) (m := 0)) hx_s
    simpa [hfun, Nat.add_zero] using (by simpa [hfun] using hG)
  -- Bound the iterated derivative via the integral representation and the exponential decay.
  have hnorm_iter :
      ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ = ‖iteratedDeriv n RealIntegrals.J₆' x‖ := by
    simpa using
      (norm_iteratedFDeriv_eq_norm_iteratedDeriv
        (𝕜 := ℝ) (n := n) (f := RealIntegrals.J₆') (x := x))
  have hGbound : ‖G n x‖ ≤ 2 * Kn * Real.exp (-Real.pi * x) := by
    -- First bound `‖F n x‖` using `‖gN n x t‖ ≤ bound t * exp(-π*x)` and integrate.
    have hx' : x ∈ s := hx_s
    have hx'' : -1 < x := by simpa [s] using hx'
    have hFn :
        ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) := by
      have hnorm :
          ‖F n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := by
        -- Rewrite the set integral as an integral over `μ`.
        have : F n x = ∫ t, gN n x t ∂μ := by
          simp [F, μ, μIciOne]
        -- Apply `‖∫ f‖ ≤ ∫ ‖f‖`.
        simpa [this] using (norm_integral_le_integral_norm (μ := μ) (f := gN n x))
      have hbound_ae :
          ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) := by
        refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
        intro t ht
        have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
        have hx0 : 0 ≤ x := hx
        have hcoeff' : ‖coeff t‖ ^ n ≤ (Real.pi * t) ^ n := by
          have : ‖coeff t‖ = Real.pi * t := coeff_norm t ht
          simp [this]
        have hψ : ‖ψS.resToImagAxis t‖ ≤ Cψ * Real.exp (-Real.pi * t) := hCψ t ht
        have hg : ‖g x t‖ ≤ ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) :=
          g_norm_bound (x := x) (t := t)
        have hxexp :
            Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) :=
          SpherePacking.ForMathlib.exp_neg_mul_mul_le_exp_neg_mul_of_one_le
            (b := Real.pi) (x := x) (t := t) Real.pi_pos.le hx0 (show (1 : ℝ) ≤ t from ht)
        calc
          ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
                simp [gN, SmoothIntegralIciOne.gN, g, coeff, norm_pow]
          _ ≤ (Real.pi * t) ^ n * (‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by
                gcongr
          _ ≤ (Real.pi * t) ^ n * ((Cψ * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x)) := by
                gcongr
          _ = bound t * Real.exp (-Real.pi * x) := by
                -- rearrange and fold `bound`
                have hp : (Real.pi * t) ^ n = (Real.pi ^ n) * (t ^ n) := by
                  simp [mul_pow, mul_comm]
                rw [hp]
                ring_nf
                simp [bound, mul_assoc, mul_left_comm, mul_comm]
      have hbound_int' : Integrable (fun t ↦ bound t * Real.exp (-Real.pi * x)) μ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hbound_int.mul_const (Real.exp (-Real.pi * x))
      have hle :
          ∫ t, ‖gN n x t‖ ∂μ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ := by
        refine integral_mono_of_nonneg ?_ hbound_int' hbound_ae
        exact (Eventually.of_forall fun t => norm_nonneg (gN n x t))
      have :
          ‖F n x‖ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ := hnorm.trans hle
      -- Evaluate the right-hand side as `Kn * exp(-π*x)`.
      have hconst :
          (∫ t, bound t * Real.exp (-Real.pi * x) ∂μ) = Kn * Real.exp (-Real.pi * x) := by
        simpa [Kn] using
          (integral_mul_const (μ := μ) (r := Real.exp (-Real.pi * x)) (f := bound))
      exact this.trans (le_of_eq hconst)
    -- Now go from `F` to `G`.
    calc
      ‖G n x‖ ≤ 2 * (Kn * Real.exp (-Real.pi * x)) := by
        simpa [G, mul_assoc] using
          (SpherePacking.ForMathlib.norm_neg_two_mul_le
            (z := F n x) (B := Kn * Real.exp (-Real.pi * x)) hFn)
      _ = 2 * Kn * Real.exp (-Real.pi * x) := by ring_nf
  have hpoly : x ^ k * Real.exp (-Real.pi * x) ≤ B := hB x hx
  have hpow0 : 0 ≤ 2 * Kn := by nlinarith [hKn_nonneg]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.J₆' x‖ := by simp [hxabs, hnorm_iter]
    _ = x ^ k * ‖G n x‖ := by simp [hiter]
    _ ≤ x ^ k * (2 * Kn * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-Real.pi * x)) := by ring_nf
    _ ≤ (2 * Kn) * B := by simpa using (mul_le_mul_of_nonneg_left hpoly hpow0)
    _ ≤ (2 * Kn * B) * 1 := by nlinarith
    _ = C := by simp [C, mul_assoc]

end

end MagicFunction.b.Schwartz.J6Smooth

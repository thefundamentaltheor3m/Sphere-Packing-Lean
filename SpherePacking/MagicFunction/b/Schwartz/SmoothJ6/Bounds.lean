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

Regularity of the primed radial integral `RealIntegrals.J₆'` on `Ioi (-1)`, proved by
differentiating under the integral sign with the exponential decay of `ψS` providing domination.
-/

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

lemma hasDerivAt_G (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => G n y) (G (n + 1) x) x := by
  simpa [G] using (hasDerivAt_F (n := n) (x := x) hx).const_mul (-2 : ℂ)

lemma iteratedDeriv_G_eq : ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  intro n
  induction n with
  | zero => intro m x _; simp [iteratedDeriv_zero]
  | succ n ih =>
      intro m x hx
      have hEq : iteratedDeriv n (G m) =ᶠ[𝓝 x] G (n + m) := by
        filter_upwards [isOpen_s.mem_nhds hx] with y hy using ih (m := m) hy
      simpa [iteratedDeriv_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Filter.EventuallyEq.deriv_eq hEq).trans
          ((hasDerivAt_G (n := n + m) (x := x) hx).deriv)

private lemma integral_J6_integrand_eq_integral_g (x : ℝ) :
    (∫ t in Ici (1 : ℝ),
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

private lemma J₆'_eq_G0 (x : ℝ) : RealIntegrals.J₆' x = G 0 x := by
  simpa [G, F, gN, SmoothIntegralIciOne.gN, g, RealIntegrals.J₆', mul_assoc, mul_left_comm,
    mul_comm] using
    congrArg (fun J : ℂ => (-2 : ℂ) * J) (integral_J6_integrand_eq_integral_g (x := x))

/-- Smoothness of `RealIntegrals.J₆'` on the open half-line `Ioi (-1)`. -/
public theorem contDiffOn_J₆'_Ioi_neg1 :
    ContDiffOn ℝ ∞ RealIntegrals.J₆' (Ioi (-1 : ℝ)) :=
  (by simpa [G] using contDiffOn_const.mul (by simpa using
      (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
        (fun n x hx => by simpa using (hasDerivAt_F (n := n) (x := x) hx)) 0)) :
    ContDiffOn ℝ ∞ (G 0) s).congr (fun x _ => J₆'_eq_G0 x)

/-- Schwartz-type decay bounds for `RealIntegrals.J₆'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₆' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := by
  intro k n
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
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) := by
      refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
      have hxexp : Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) :=
        SpherePacking.ForMathlib.exp_neg_mul_mul_le_exp_neg_mul_of_one_le
          (b := Real.pi) (x := x) (t := t) Real.pi_pos.le hx ht
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

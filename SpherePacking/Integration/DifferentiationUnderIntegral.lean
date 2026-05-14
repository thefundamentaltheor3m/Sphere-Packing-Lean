module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import SpherePacking.Integration.Measure
import Mathlib.Topology.Basic
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IteratedDeriv

/-!
# Differentiation under the integral sign on `(0, 1)`

Lemmas for differentiating `x ↦ ∫ t in Ioo (0 : ℝ) 1, hf t * exp (x * coeff t)`,
dimension-agnostic and used by the dimension-specific developments.
-/

namespace SpherePacking.Integration.DifferentiationUnderIntegral
noncomputable section

open scoped Topology Interval
open Complex Real Set MeasureTheory Filter intervalIntegral
open SpherePacking.Integration (μIoo01)

variable {coeff hf : ℝ → ℂ}

/-- The basic integrand `t ↦ hf t * exp (x * coeff t)` on `(0, 1)`. -/
@[expose] public def g (x t : ℝ) : ℂ := hf t * cexp ((x : ℂ) * coeff t)

/-- The auxiliary integrand `gN n`, corresponding to the `n`-th derivative in `x`. -/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ :=
  (coeff t) ^ n * g (coeff := coeff) (hf := hf) x t

private lemma aestronglyMeasurable_gN_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff) (n : ℕ) (x : ℝ) :
    AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) n x) μIoo01 := by
  simpa [μIoo01, gN, g] using (((continuous_coeff.pow n).continuousOn.mul (continuousOn_hf.mul
    ((continuous_const.mul continuous_coeff).cexp.continuousOn))).aestronglyMeasurable
      measurableSet_Ioo)

private lemma norm_gN_le_const
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    {M : ℝ} {t x x₀ : ℝ} (hx : x ∈ Metric.ball x₀ (1 : ℝ))
    (hh : ‖hf t‖ ≤ M) (n : ℕ) :
    ‖gN (coeff := coeff) (hf := hf) n x t‖ ≤
      (2 * Real.pi) ^ n * (M * Real.exp ((|x₀| + 1) * (2 * Real.pi))) := calc
  ‖gN (coeff := coeff) (hf := hf) n x t‖
      = ‖(coeff t) ^ n * (hf t * cexp ((x : ℂ) * coeff t))‖ := by simp [gN, g, mul_comm]
    _ ≤ ‖(coeff t) ^ n‖ * ‖hf t * cexp ((x : ℂ) * coeff t)‖ := norm_mul_le _ _
    _ ≤ (2 * Real.pi) ^ n * (M * Real.exp ((|x₀| + 1) * (2 * Real.pi))) := by
        gcongr
        · simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
        · refine norm_mul_le_of_le hh ?_
          have hre : ((x : ℂ) * coeff t).re ≤ (|x₀| + 1) * (2 * Real.pi) :=
            (Complex.re_le_norm _).trans <| by
            have : |x| * ‖coeff t‖ ≤ (|x₀| + 1) * (2 * Real.pi) := by
              gcongr
              · exact SpherePacking.ForMathlib.abs_le_abs_add_of_mem_ball hx
              · exact coeff_norm_le t
            simpa [norm_mul, Complex.norm_real, mul_assoc] using this
          simpa [Complex.norm_exp] using Real.exp_le_exp.2 hre

/-- Differentiate under the integral sign on `(0, 1)` for the integrand `gN n`. -/
public lemma hasDerivAt_integral_gN_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ t, gN (coeff := coeff) (hf := hf) n x t ∂μIoo01)
        (∫ t, gN (coeff := coeff) (hf := hf) (n + 1) x₀ t ∂μIoo01) x₀ := by
  have hμmem : ∀ᵐ t ∂μIoo01, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μIoo01] using ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_hf
  haveI : IsFiniteMeasure μIoo01 := ⟨by simp [μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μIoo01)
    (s := Metric.ball x₀ (1 : ℝ))
    (F := fun x t ↦ gN (coeff := coeff) (hf := hf) n x t)
    (F' := fun x t ↦ gN (coeff := coeff) (hf := hf) (n + 1) x t)
    (bound := fun _ : ℝ ↦
      (2 * Real.pi) ^ (n + 1) * (Mh * Real.exp ((|x₀| + 1) * (2 * Real.pi))))
    (x₀ := x₀) (Metric.ball_mem_nhds x₀ (by norm_num))
    (.of_forall fun x => aestronglyMeasurable_gN_Ioo continuousOn_hf continuous_coeff n x)
    (Integrable.of_bound (aestronglyMeasurable_gN_Ioo continuousOn_hf continuous_coeff n x₀) _
      (hμmem.mono fun t ht =>
        norm_gN_le_const coeff_norm_le (Metric.mem_ball_self (by norm_num)) (hMh t ht) n))
    (aestronglyMeasurable_gN_Ioo continuousOn_hf continuous_coeff (n + 1) x₀)
    (by filter_upwards [hμmem] with t ht x hx
        exact norm_gN_le_const coeff_norm_le hx (hMh t ht) (n + 1))
    (integrable_const _) (ae_of_all _ fun t x _ => by
      simpa [gN, g, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        (SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const
          (a := hf t) (c := coeff t) x).const_mul ((coeff t) ^ n))).2

/-- Smoothness of `x ↦ ∫_{(0,1)} g(x,t)` packaged from `hasDerivAt_integral_gN_Ioo`. -/
public theorem contDiff_integral_g_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1, g (coeff := coeff) (hf := hf) x t) := by
  let I : ℕ → ℝ → ℂ := fun n x => ∫ t, gN (coeff := coeff) (hf := hf) n x t ∂μIoo01
  have h0 : (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1, g (coeff := coeff) (hf := hf) x t) = I 0 := by
    funext x; simp [I, gN, g, μIoo01]
  simpa [h0] using SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I) fun n x => by
    simpa [I] using hasDerivAt_integral_gN_Ioo (coeff := coeff) (hf := hf) continuousOn_hf
      continuous_coeff exists_bound_norm_hf coeff_norm_le n x

/-- Differentiate under the integral sign for `∫ t in (0)..1, gN n x t`, assuming continuity. -/
public lemma hasDerivAt_integral_gN_of_continuous
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t)
      (∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) (n + 1) x₀ t) x₀ := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ι (0 : ℝ) 1)
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_h
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ι (0 : ℝ) 1 :=
    ae_restrict_mem (μ := (volume : Measure ℝ)) (by measurability)
  have continuous_gN (n : ℕ) (x : ℝ) :
      Continuous fun t : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t := by
    simpa [gN, g] using (continuous_coeff.pow n).mul
      (continuous_hf.mul ((continuous_const.mul continuous_coeff).cexp))
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Measure.restrict_apply, MeasurableSet.univ]⟩
  simpa [μ, intervalIntegral_eq_integral_uIoc, zero_le_one] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (s := Metric.ball x₀ (1 : ℝ)) (x₀ := x₀)
      (F := fun x t => gN (coeff := coeff) (hf := hf) n x t)
      (F' := fun x t => gN (coeff := coeff) (hf := hf) (n + 1) x t)
      (bound := fun _ : ℝ ↦ (2 * Real.pi) ^ (n + 1) * Mh * Real.exp ((|x₀| + 1) * (2 * Real.pi)))
      (Metric.ball_mem_nhds x₀ (by norm_num))
      (.of_forall fun x => (continuous_gN n x).aestronglyMeasurable)
      ((continuous_gN n x₀).integrableOn_uIoc (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
      (continuous_gN (n + 1) x₀).aestronglyMeasurable
      (by filter_upwards [hμmem] with t ht x hx
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            norm_gN_le_const coeff_norm_le hx (hMh t ht) (n + 1))
      (integrable_const _) (ae_of_all _ fun t x _ => by
        simpa [gN, g, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          (SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const (hf t) (coeff t)
            x).const_mul ((coeff t) ^ n))).2

/-! ## Auxiliary inequalities for smooth-integral bounds. -/

/-- Compute `‖exp (x * coeff t)‖` from the real part of `coeff t`. -/
public lemma norm_cexp_ofReal_mul_coeff_of_coeff_re {x t : ℝ}
    (hcoeff_re : (coeff t).re = -Real.pi * t) :
    ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
  simp [Complex.norm_exp, Complex.mul_re, hcoeff_re, mul_left_comm, mul_comm]

/-- Bound the norm of an integral by bounding the integrand almost everywhere. -/
public lemma norm_integral_le_integral_bound_mul_const {μ : MeasureTheory.Measure ℝ}
    {f : ℝ → ℂ} {bound : ℝ → ℝ} {E : ℝ}
    (hbound_int : MeasureTheory.Integrable bound μ)
    (h_ae : ∀ᵐ t ∂μ, ‖f t‖ ≤ bound t * E) :
    ‖∫ t, f t ∂μ‖ ≤ (∫ t, bound t ∂μ) * E := by
  calc
    ‖∫ t, f t ∂μ‖ ≤ ∫ t, ‖f t‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := f)
    _ ≤ ∫ t, bound t * E ∂μ :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun t => norm_nonneg (f t)) (hbound_int.mul_const E) h_ae
    _ = (∫ t, bound t ∂μ) * E := by
          simpa using MeasureTheory.integral_mul_const (μ := μ) (r := E) (f := bound)

/-- A pointwise bound for `gN` used in dominated differentiation arguments. -/
public lemma norm_gN_le_bound_mul_exp {ψ : ℂ → ℂ} {z : ℝ → ℂ}
    {n : ℕ} {Cψ x t : ℝ} (hCψ0 : 0 ≤ Cψ)
    (hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n)
    (hψ : ‖ψ (z t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ))
    (hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t)) :
    ‖gN (coeff := coeff) (hf := fun s ↦ (Complex.I : ℂ) * ψ (z s)) n x t‖ ≤
      (((2 * Real.pi) ^ n) * Cψ * t ^ (2 : ℕ)) *
        (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)) := by
  have hfactor0 :
      0 ≤ (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) * Real.exp (-Real.pi * x * t) := by
    positivity
  calc
    ‖gN (coeff := coeff) (hf := fun s ↦ (Complex.I : ℂ) * ψ (z s)) n x t‖ =
        ‖coeff t‖ ^ n * ‖ψ (z t)‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by
          simp [gN, g, mul_assoc, norm_pow]
    _ = ‖coeff t‖ ^ n * (‖ψ (z t)‖ * Real.exp (-Real.pi * x * t)) := by
          simp [hcexp, mul_assoc]
    _ ≤ ‖coeff t‖ ^ n * ((Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) *
          Real.exp (-Real.pi * x * t)) := by gcongr
    _ ≤ (2 * Real.pi) ^ n * ((Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (2 : ℕ)) *
          Real.exp (-Real.pi * x * t)) := mul_le_mul_of_nonneg_right hcoeff hfactor0
    _ = (((2 * Real.pi) ^ n) * Cψ * t ^ (2 : ℕ)) *
          (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

end

end SpherePacking.Integration.DifferentiationUnderIntegral

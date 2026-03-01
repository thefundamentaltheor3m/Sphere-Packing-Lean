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

This file provides lemmas for differentiating functions of the form
`x ↦ ∫ t in Ioo (0 : ℝ) 1, hf t * exp (x * coeff t)`.

It is dimension-agnostic and is used by the dimension-specific developments.
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

/-- Continuity of `g x` on `(0, 1)` assuming continuity of `hf` there and continuity of `coeff`. -/
public lemma continuousOn_g_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff) (x : ℝ) :
    ContinuousOn (g (coeff := coeff) (hf := hf) x) (Ioo (0 : ℝ) 1) := by
  simpa [g] using
    continuousOn_hf.mul (Continuous.continuousOn ((continuous_const.mul continuous_coeff).cexp))

/-- Continuity of `gN n x` on `(0, 1)`.

Assumes continuity of `hf` on `(0, 1)` and continuity of `coeff`.
-/
public lemma continuousOn_gN_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff) (n : ℕ) (x : ℝ) :
    ContinuousOn (gN (coeff := coeff) (hf := hf) n x) (Ioo (0 : ℝ) 1) := by
  simpa [gN] using
    ((continuous_coeff.pow n).continuousOn.mul
      (continuousOn_g_Ioo (coeff := coeff) (hf := hf) continuousOn_hf continuous_coeff x))

private lemma aestronglyMeasurable_gN_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff) (n : ℕ) (x : ℝ) :
    AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) n x)
      μIoo01 := by
  have hcont :=
    continuousOn_gN_Ioo (coeff := coeff) (hf := hf) continuousOn_hf continuous_coeff n x
  simpa [μIoo01] using
    hcont.aestronglyMeasurable (μ := (volume : Measure ℝ)) measurableSet_Ioo

lemma norm_cexp_mul_coeff_le
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    {x x₀ : ℝ} (t : ℝ) (hx : x ∈ Metric.ball x₀ (1 : ℝ)) :
    ‖cexp ((x : ℂ) * coeff t)‖ ≤ Real.exp ((|x₀| + 1) * (2 * Real.pi)) :=
  SpherePacking.ForMathlib.norm_cexp_ofReal_mul_le_exp_mul_of_norm_le (c := coeff t)
    (B := (2 * Real.pi)) (coeff_norm_le t) hx

private lemma norm_gN_le_const
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    {M : ℝ} {t x x₀ : ℝ} (hx : x ∈ Metric.ball x₀ (1 : ℝ))
    (hh : ‖hf t‖ ≤ M) (n : ℕ) :
    ‖gN (coeff := coeff) (hf := hf) n x t‖ ≤
      (2 * Real.pi) ^ n * (M * Real.exp ((|x₀| + 1) * (2 * Real.pi))) := by
  have hpow : ‖(coeff t) ^ n‖ ≤ (2 * Real.pi) ^ n := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
  have hexp : ‖cexp ((x : ℂ) * coeff t)‖ ≤ Real.exp ((|x₀| + 1) * (2 * Real.pi)) :=
    norm_cexp_mul_coeff_le (coeff := coeff) (coeff_norm_le := coeff_norm_le) (t := t) hx
  have hhexp :
      ‖hf t * cexp ((x : ℂ) * coeff t)‖ ≤ M * Real.exp ((|x₀| + 1) * (2 * Real.pi)) :=
    norm_mul_le_of_le hh hexp
  calc
    ‖gN (coeff := coeff) (hf := hf) n x t‖ =
        ‖(coeff t) ^ n * (hf t * cexp ((x : ℂ) * coeff t))‖ := by
          simp [gN, g, mul_comm]
    _ ≤ ‖(coeff t) ^ n‖ * ‖hf t * cexp ((x : ℂ) * coeff t)‖ :=
          norm_mul_le _ _
    _ ≤ (2 * Real.pi) ^ n * (M * Real.exp ((|x₀| + 1) * (2 * Real.pi))) := by gcongr

/-- Provide an a.e. bound for `gN (n+1)` on a neighborhood of `x₀`, with an integrable constant
dominating function. -/
public lemma ae_bound_gN_succ_Ioo
    (exists_bound_norm_h : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    ∃ K,
      (∀ᵐ t ∂μIoo01,
          ∀ x ∈ Metric.ball x₀ (1 : ℝ),
            ‖gN (coeff := coeff) (hf := hf) (n + 1) x t‖ ≤ K) ∧
        Integrable (fun _ : ℝ ↦ K) μIoo01 := by
  let μ : Measure ℝ := μIoo01
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μ, μIoo01] using
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_h
  let K : ℝ := (2 * Real.pi) ^ (n + 1) * (Mh * Real.exp ((|x₀| + 1) * (2 * Real.pi)))
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩
  refine ⟨K, ?_, ?_⟩
  · filter_upwards [hμmem] with t ht
    intro x hx
    exact norm_gN_le_const coeff_norm_le hx (hMh t ht) (n + 1)
  · simpa [K, μ] using (integrable_const (c := K) (μ := μ))

/-- Integrability of `gN n x` over `(0, 1)`.

This uses boundedness assumptions on `hf` and `coeff`.
-/
public lemma integrable_gN_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x : ℝ) :
    Integrable (gN (coeff := coeff) (hf := hf) n x)
      μIoo01 := by
  let μ : Measure ℝ := μIoo01
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μ, μIoo01] using
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)
  have hmeas : AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) n x) μ := by
    simpa [μ, μIoo01] using
      aestronglyMeasurable_gN_Ioo (coeff := coeff) (hf := hf) continuousOn_hf continuous_coeff n x
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_hf
  let K : ℝ := (2 * Real.pi) ^ n * (Mh * Real.exp ((|x| + 1) * (2 * Real.pi)))
  have hbound : ∀ᵐ t ∂μ, ‖gN (coeff := coeff) (hf := hf) n x t‖ ≤ K := by
    refine hμmem.mono ?_
    intro t ht
    have hh : ‖hf t‖ ≤ Mh := hMh t ht
    have hx : x ∈ Metric.ball x (1 : ℝ) := Metric.mem_ball_self (by norm_num)
    exact norm_gN_le_const coeff_norm_le hx (hMh t ht) n
  exact Integrable.of_bound hmeas K hbound

/-- Differentiate under the integral sign on `(0, 1)` for the integrand `gN n`. -/
public lemma hasDerivAt_integral_gN_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    HasDerivAt
        (fun x : ℝ =>
          ∫ t, gN (coeff := coeff) (hf := hf) n x t ∂μIoo01)
        (∫ t, gN (coeff := coeff) (hf := hf) (n + 1) x₀ t ∂μIoo01)
        x₀ := by
  let μ : Measure ℝ := μIoo01
  have hF_meas :
      ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) n x) μ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    simpa [μ, μIoo01] using
      aestronglyMeasurable_gN_Ioo (coeff := coeff) (hf := hf) continuousOn_hf continuous_coeff n x
  have hF_int : Integrable (gN (coeff := coeff) (hf := hf) n x₀) μ :=
    integrable_gN_Ioo continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le n x₀
  have hF'_meas : AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) (n + 1) x₀) μ :=
    aestronglyMeasurable_gN_Ioo continuousOn_hf continuous_coeff (n + 1) x₀
  rcases
      ae_bound_gN_succ_Ioo (coeff := coeff) (hf := hf) (exists_bound_norm_h := exists_bound_norm_hf)
        (coeff_norm_le := coeff_norm_le) (n := n) (x₀ := x₀) with
    ⟨K, h_bound0, hK_int0⟩
  have h_bound :
      (∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ),
          ‖gN (coeff := coeff) (hf := hf) (n + 1) x t‖ ≤ K) := by
    simpa [μ] using h_bound0
  have hK_int : Integrable (fun _ : ℝ => K) μ := by
    simp [μ]
  have h_diff :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ (1 : ℝ),
        HasDerivAt (fun x : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t)
          (gN (coeff := coeff) (hf := hf) (n + 1) x t) x := by
    refine ae_of_all _ ?_
    intro t x _
    have hg : HasDerivAt (fun x : ℝ ↦ g (coeff := coeff) (hf := hf) x t)
        (coeff t * g (coeff := coeff) (hf := hf) x t) x := by
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using
        (SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const (a := hf t) (c := coeff t) x)
    have h := hg.const_mul ((coeff t) ^ n)
    simpa [gN, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
  simpa [μ] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (s := Metric.ball x₀ (1 : ℝ))
        (F := fun x t ↦ gN (coeff := coeff) (hf := hf) n x t)
        (F' := fun x t ↦ gN (coeff := coeff) (hf := hf) (n + 1) x t)
        (bound := fun _ : ℝ ↦ K)
        (x₀ := x₀) (Metric.ball_mem_nhds x₀ (by norm_num))
        (hF_meas := hF_meas) (hF_int := hF_int) (hF'_meas := hF'_meas)
        (h_bound := h_bound) (bound_integrable := hK_int) (h_diff := h_diff)).2

/-- Smoothness of `x ↦ ∫_{(0,1)} g(x,t)` packaged from `hasDerivAt_integral_gN_Ioo`. -/
public theorem contDiff_integral_g_Ioo
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1, g (coeff := coeff) (hf := hf) x t) := by
  let I : ℕ → ℝ → ℂ := fun n x => ∫ t, gN (coeff := coeff) (hf := hf) n x t ∂μIoo01
  have hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x := fun n x => by
    simpa [I] using
      hasDerivAt_integral_gN_Ioo (coeff := coeff) (hf := hf) continuousOn_hf continuous_coeff
        exists_bound_norm_hf coeff_norm_le n x
  have h0 : (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1, g (coeff := coeff) (hf := hf) x t) = I 0 := by
    funext x; simp [I, gN, g, μIoo01]
  simpa [h0] using SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I) hI

/-- A wrapper around `contDiff_integral_g_Ioo` using a pointwise equality. -/
public theorem contDiff_of_eq_integral_g_Ioo
    (I' : ℝ → ℂ)
    (hI : ∀ x : ℝ, I' x = ∫ t in Ioo (0 : ℝ) 1, g (coeff := coeff) (hf := hf) x t)
    (continuousOn_hf : ContinuousOn hf (Ioo (0 : ℝ) 1))
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi) :
    ContDiff ℝ (⊤ : ℕ∞) I' := by
  simpa [funext hI] using
    (contDiff_integral_g_Ioo (coeff := coeff) (hf := hf) continuousOn_hf continuous_coeff
      exists_bound_norm_hf coeff_norm_le)

/-- Differentiate under the integral sign for the interval integral `∫ t in (0)..1, gN n x t`. -/
public lemma hasDerivAt_integral_gN
    (continuous_gN : ∀ n : ℕ, ∀ x : ℝ, Continuous fun t : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t)
    (hasDerivAt_gN :
      ∀ n : ℕ, ∀ x t : ℝ,
        HasDerivAt (fun x : ℝ ↦ gN (coeff := coeff) (hf := hf) n x t)
          (gN (coeff := coeff) (hf := hf) (n + 1) x t) x)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t)
      (∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) (n + 1) x₀ t) x₀ := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ι (0 : ℝ) 1)
  obtain ⟨Mh, hMh⟩ := exists_bound_norm_h
  let bound : ℝ → ℝ :=
    fun _ => (2 * Real.pi) ^ (n + 1) * Mh * Real.exp ((|x₀| + 1) * (2 * Real.pi))
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ι (0 : ℝ) 1 := by
    simpa [μ] using
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := (Ι (0 : ℝ) 1)) (by measurability))
  have hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) n x) μ :=
    Filter.Eventually.of_forall fun x => (continuous_gN n x).aestronglyMeasurable
  have hint : Integrable (gN (coeff := coeff) (hf := hf) n x₀) μ := by
    simpa [μ] using (continuous_gN n x₀).integrableOn_uIoc
      (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
  have hmeas' : AEStronglyMeasurable (gN (coeff := coeff) (hf := hf) (n + 1) x₀) μ :=
    (continuous_gN (n + 1) x₀).aestronglyMeasurable
  have hbound :
      ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ 1,
        ‖gN (coeff := coeff) (hf := hf) (n + 1) x t‖ ≤ bound t := by
    filter_upwards [hμmem] with t ht
    intro x hx
    have hh : ‖hf t‖ ≤ Mh := hMh t ht
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (norm_gN_le_const (coeff := coeff) (hf := hf) (coeff_norm_le := coeff_norm_le)
        (M := Mh) (t := t) (x := x) (x₀ := x₀) hx hh
        (n := n + 1))
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Measure.restrict_apply, MeasurableSet.univ]⟩
  simpa [μ, intervalIntegral_eq_integral_uIoc, zero_le_one] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := μ) (s := Metric.ball x₀ (1 : ℝ)) (x₀ := x₀)
        (F := fun x t => gN (coeff := coeff) (hf := hf) n x t)
        (F' := fun x t => gN (coeff := coeff) (hf := hf) (n + 1) x t)
        (bound := bound) (Metric.ball_mem_nhds x₀ (by norm_num))
        hmeas hint hmeas' hbound
        (integrable_const _)
        (ae_of_all _ fun t x _ => hasDerivAt_gN n x t)).2

/-- Specialize `hasDerivAt_integral_gN` assuming `hf` and `coeff` are continuous. -/
public lemma hasDerivAt_integral_gN_of_continuous
    (continuous_hf : Continuous hf)
    (continuous_coeff : Continuous coeff)
    (exists_bound_norm_h : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M)
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t)
      (∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) (n + 1) x₀ t) x₀ := by
  refine
    hasDerivAt_integral_gN (coeff := coeff) (hf := hf)
      (continuous_gN := ?_) (hasDerivAt_gN := ?_)
      (exists_bound_norm_h := exists_bound_norm_h) (coeff_norm_le := coeff_norm_le)
      (n := n) (x₀ := x₀)
  · intro n x
    simpa [gN, g] using
      (continuous_coeff.pow n).mul
        (continuous_hf.mul ((continuous_const.mul continuous_coeff).cexp))
  · intro n x t
    simpa [gN, g, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      ((SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const (hf t) (coeff t) x).const_mul
        ((coeff t) ^ n))

end

end SpherePacking.Integration.DifferentiationUnderIntegral

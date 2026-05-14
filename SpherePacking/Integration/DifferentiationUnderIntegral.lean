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

/-! # Differentiation under the integral sign on `Ici 1`

Reusable dominated-differentiation lemma for integrals over `Ici 1`, used in the `I₆'` and `J₆'`
smoothness proofs. -/

namespace SpherePacking.Integration.SmoothIntegralIciOne
noncomputable section

open scoped Topology
open Complex Real Set MeasureTheory Filter
open SpherePacking.Integration (μIciOne)

/-- The coefficient function used in the exponential weight. -/
@[expose] public def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

/-- The basic integrand `t ↦ I * (hf t * exp (x * coeff t))`. -/
@[expose] public def g (hf : ℝ → ℂ) (x t : ℝ) : ℂ :=
  (Complex.I : ℂ) * (hf t * cexp ((x : ℂ) * coeff t))

/-- The auxiliary integrand `gN n`, corresponding to the `n`-th derivative in `x`. -/
@[expose] public def gN (hf : ℝ → ℂ) (n : ℕ) (x t : ℝ) : ℂ :=
  (coeff t) ^ n * g (hf := hf) x t

/-- Norm of `coeff t` on `Ici 1`. -/
public lemma coeff_norm (t : ℝ) (ht : t ∈ Set.Ici (1 : ℝ)) : ‖coeff t‖ = Real.pi * t := by
  simp [coeff, Complex.norm_real, abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (zero_le_one.trans (by simpa [Set.mem_Ici] using ht))]

/-- Crude bound on `g` in terms of `‖hf t‖` and `exp (-π * x * t)`. -/
public lemma g_norm_bound (hf : ℝ → ℂ) (x t : ℝ) :
    ‖g (hf := hf) x t‖ ≤ ‖hf t‖ * Real.exp (-Real.pi * x * t) := by
  simp [g, coeff, Complex.norm_exp, mul_left_comm, mul_comm]

/-- Differentiate under the integral sign for `∫ t ∈ Ici 1, gN n x t`, under standard bounds.

The `shift` is the decay exponent of `hf` on `Ici 1`; differentiability at `x` only requires
`-shift < x` so that `x + shift > 0`. -/
public lemma hasDerivAt_integral_gN
    {hf : ℝ → ℂ} {shift : ℝ}
    (exists_bound_norm_hf :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖hf t‖ ≤ C * Real.exp (-(Real.pi * shift) * t))
    (gN_measurable :
      ∀ n : ℕ, ∀ x : ℝ, AEStronglyMeasurable (gN (hf := hf) n x) μIciOne)
    (n : ℕ) (x : ℝ) (hx : -shift < x)
    (hF_int : Integrable (gN (hf := hf) n x) μIciOne) :
    HasDerivAt (fun y : ℝ ↦ ∫ t in Set.Ici (1 : ℝ), gN (hf := hf) n y t)
      (∫ t in Set.Ici (1 : ℝ), gN (hf := hf) (n + 1) x t) x := by
  have hxshift : 0 < x + shift := by linarith
  -- Shrink the neighborhood so that `x + shift` stays uniformly positive.
  let ε : ℝ := (x + shift) / 2
  have ε_pos : 0 < ε := by simpa [ε] using half_pos hxshift
  obtain ⟨C, hC⟩ := exists_bound_norm_hf
  have hC0 : 0 ≤ C :=
    SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖hf 1‖)
      (b := Real.exp (-(Real.pi * shift) * (1 : ℝ))) (C := C) (norm_nonneg _) (by positivity)
      (by simpa using hC 1 le_rfl)
  have hb : 0 < Real.pi * ε := mul_pos Real.pi_pos ε_pos
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ (n + 1)) * (t ^ (n + 1) * Real.exp (-(Real.pi * ε) * t)) * C
  have hbound_int : Integrable bound μIciOne := by
    have hInt : Integrable (fun t : ℝ ↦ t ^ (n + 1) * Real.exp (-(Real.pi * ε) * t)) μIciOne := by
      simpa [IntegrableOn, μIciOne, mul_assoc] using
        SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1)
          (b := Real.pi * ε) (by simpa [mul_assoc] using hb)
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using hInt.const_mul ((Real.pi ^ (n + 1)) * C)
  have h_bound :
      ∀ᵐ t ∂μIciOne, ∀ y ∈ Metric.ball x ε, ‖gN (hf := hf) (n + 1) y t‖ ≤ bound t := by
    refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
    intro t ht y hy
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
    have hy0 : ε ≤ y + shift := by
      have hdist : |y - x| < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      grind only [= abs.eq_1, = max_def]
    have hg : ‖g (hf := hf) y t‖ ≤ C * Real.exp (-(Real.pi * (y + shift)) * t) := by
      calc ‖g (hf := hf) y t‖ ≤ ‖hf t‖ * Real.exp (-Real.pi * y * t) := g_norm_bound _ _ _
        _ ≤ (C * Real.exp (-(Real.pi * shift) * t)) * Real.exp (-Real.pi * y * t) := by
              gcongr; exact hC t ht
        _ = C * Real.exp (-(Real.pi * (y + shift)) * t) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf
    calc ‖gN (hf := hf) (n + 1) y t‖ = ‖coeff t‖ ^ (n + 1) * ‖g (hf := hf) y t‖ := by
            simp [gN, norm_pow]
      _ ≤ (Real.pi * t) ^ (n + 1) * (C * Real.exp (-(Real.pi * ε) * t)) := by
            gcongr
            · simp [coeff_norm (t := t) ht]
            · exact hg.trans (by gcongr)
      _ = bound t := by simp [bound, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  simpa [μIciOne, ε] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μIciOne)
      (s := Metric.ball x ε) (F := fun y t ↦ gN (hf := hf) n y t) (x₀ := x)
      (Metric.ball_mem_nhds x ε_pos)
      (hF_meas := .of_forall fun y ↦ gN_measurable n y) (hF_int := hF_int)
      (hF'_meas := gN_measurable (n + 1) x)
      (h_bound := h_bound) (bound_integrable := hbound_int)
      (h_diff := ae_of_all _ fun t y _ => by
        have hg : HasDerivAt (fun y : ℝ ↦ g (hf := hf) y t) (coeff t * g (hf := hf) y t) y := by
          simpa [g, mul_assoc, mul_left_comm, mul_comm] using
            SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const
              (a := (Complex.I : ℂ) * (hf t)) (c := coeff t) y
        simpa [gN, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          hg.const_mul ((coeff t) ^ n))).2

end

end SpherePacking.Integration.SmoothIntegralIciOne

namespace SpherePacking.ForMathlib

open scoped ContDiff

/-- If `F n` satisfies `HasDerivAt (F n) (F (n + 1) x) x` on an open set `s`, then each `F n` is
`ContDiffOn ℝ ∞` on `s`. -/
public theorem contDiffOn_family_infty_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E} {s : Set ℝ} (hs : IsOpen s)
    (hF : ∀ n : ℕ, ∀ x : ℝ, x ∈ s → HasDerivAt (F n) (F (n + 1) x) x) (n : ℕ) :
    ContDiffOn ℝ ∞ (F n) s := by
  have hdiff k : DifferentiableOn ℝ (F k) s :=
    fun _ hx => (hF k _ hx).differentiableAt.differentiableWithinAt
  have hnat : ∀ m : ℕ, ∀ k : ℕ, ContDiffOn ℝ m (F k) s := by
    intro m
    induction m with
    | zero => intro k; exact contDiffOn_zero.2 (hdiff k).continuousOn
    | succ m ih =>
        intro k
        refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := F k) (s := s) (n := m) hs).2
          ⟨hdiff k, by simp, (ih (k + 1)).congr fun x hx => by simpa using (hF k x hx).deriv⟩
  simpa [contDiffOn_infty] using fun m => hnat m n

end SpherePacking.ForMathlib

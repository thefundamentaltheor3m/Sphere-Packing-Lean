module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

import SpherePacking.ForMathlib.DerivHelpers

/-! # Scalar one-form utilities, convenience measures on standard intervals (Lebesgue
restrictions), and inversion change-of-variables on `Ioc (0, 1]`.

Also includes differentiation-under-the-integral lemmas on `(0, 1)` and `Ici 1` (originally
in `Integration.DifferentiationUnderIntegral`), and the helper
`SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt`. -/

namespace MagicFunction

/-- Interpret a scalar function `F : ℂ → ℂ` as the `ℂ`-linear one-form `v ↦ v * F z`. -/
@[expose] public def scalarOneForm (F : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ (ContinuousLinearMap.id ℂ ℂ).smulRight (F z)

/-- Evaluate `scalarOneForm` as multiplication by `F z`. -/
@[simp] public lemma scalarOneForm_apply (F : ℂ → ℂ) (z v : ℂ) :
    scalarOneForm F z v = v * F z := rfl

end MagicFunction

namespace SpherePacking.ForMathlib

/-- If `F` is `DiffContOnCl` on `s`, then so is the associated scalar one-form. -/
public lemma diffContOnCl_scalarOneForm {F : ℂ → ℂ} {s : Set ℂ} (hF : DiffContOnCl ℝ F s) :
    DiffContOnCl ℝ (MagicFunction.scalarOneForm F) s := by
  let L : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ
  simpa [MagicFunction.scalarOneForm, L] using
    L.differentiable.comp_diffContOnCl (g := F) (t := s) hF

open MagicFunction

/-- `fderivWithin`-version of `fderiv_scalarOneForm_symm` on an open set. -/
public lemma fderivWithin_scalarOneForm_symm_of_isOpen
    {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    {u v : ℂ} (hfdiff : DifferentiableAt ℂ f x) :
    fderivWithin ℝ (scalarOneForm f) s x u v = fderivWithin ℝ (scalarOneForm f) s x v u := by
  rw [fderivWithin_of_mem_nhds (f := scalarOneForm f) (hs.mem_nhds hx)]
  let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) := (ContinuousLinearMap.mul ℂ ℂ).flip
  rw [(show HasFDerivAt (𝕜 := ℝ) (scalarOneForm f)
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L (deriv f x))).restrictScalars ℝ) x from by
    simpa [show scalarOneForm f = fun z => L (f z) from rfl] using
      ((hasDerivAt_const x L).clm_apply hfdiff.hasDerivAt).hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [L, mul_left_comm, mul_comm]

end SpherePacking.ForMathlib

namespace SpherePacking.Integration

noncomputable section

open scoped Interval
open MeasureTheory Set intervalIntegral
open MagicFunction

/-- The restriction of Lebesgue measure to `Ioc (0, 1]`. -/
@[expose] public def μIoc01 : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)

/-- `μIoc01` is `SFinite`. -/
public instance : MeasureTheory.SFinite μIoc01 := by unfold μIoc01; infer_instance

/-- `μIoc01` is finite. -/
public instance : MeasureTheory.IsFiniteMeasure μIoc01 := ⟨by simp [μIoc01]⟩

/-- The restriction of Lebesgue measure to `Ioo (0, 1)`. -/
@[expose] public def μIoo01 : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)

attribute [irreducible] μIoo01

/-- `μIoo01` is `SFinite`. -/
public instance : MeasureTheory.SFinite μIoo01 := by unfold μIoo01; infer_instance

/-- `μIoo01` is finite. -/
public instance : MeasureTheory.IsFiniteMeasure μIoo01 := ⟨by simp [μIoo01]⟩

/-- The restriction of Lebesgue measure to `Ici 1`. -/
@[expose] public def μIciOne : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))

/-! `μIciOne` is `SFinite`. -/
public instance : MeasureTheory.SFinite μIciOne := by unfold μIciOne; infer_instance

/-- The restriction of Lebesgue measure to `Ioi 0`. -/
@[expose] public def μIoi0 : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))

/-! #### `μIoo01` helper lemmas -/

/-- Almost everywhere with respect to `μIoo01`, the variable lies in `Ioo (0, 1)`. -/
public lemma ae_mem_Ioo01_muIoo01 : ∀ᵐ t ∂μIoo01, t ∈ Ioo (0 : ℝ) 1 := by
  simpa [μIoo01] using (ae_restrict_mem (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)

/-- The function `t ↦ A * t ^ p` is integrable with respect to `μIoo01` when `0 ≤ A`. -/
public lemma integrable_const_mul_pow_muIoo01 (A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    Integrable (fun t : ℝ ↦ A * t ^ p) μIoo01 :=
  MeasureTheory.Integrable.of_mem_Icc (μ := μIoo01) (a := (0 : ℝ)) (b := A)
    (hX := by fun_prop) <| by
    filter_upwards [ae_mem_Ioo01_muIoo01] with t ht
    refine ⟨mul_nonneg hA (pow_nonneg ht.1.le _), ?_⟩
    simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1.le ht.2.le) hA

/-! #### `μIoc01` helper lemmas (downstream uses are curve-integral arguments). -/

/-- Product with `μIoc01` agrees with restricting the product measure. -/
public lemma prod_muIoc01_eq_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] :
    μ.prod μIoc01 = (μ.prod (volume : Measure ℝ)).restrict ((univ : Set α) ×ˢ (Ioc (0 : ℝ) 1)) := by
  simpa [μIoc01] using
    (Measure.prod_restrict (μ := μ) (ν := volume) (s := (univ : Set α)) (t := Ioc (0 : ℝ) 1))

/-- Rewrite a `μIoc01`-integral as a curve integral over a segment, for the scalar one-form. -/
public lemma integral_dir_mul_muIoc01_eq_curveIntegral_segment (F : ℂ → ℂ) (a b : ℂ)
    (zline : ℝ → ℂ) (hzline : ∀ t : ℝ, AffineMap.lineMap a b t = zline t) :
    (∫ t : ℝ, (b - a) * F (zline t) ∂μIoc01) = (∫ᶜ z in Path.segment a b, scalarOneForm F z) := by
  rw [show (∫ t : ℝ, (b - a) * F (zline t) ∂μIoc01) =
      ∫ t in (0 : ℝ)..1, (b - a) * F (zline t) from by
    simpa [μIoc01] using (intervalIntegral.integral_of_le (μ := volume)
      (f := fun t => (b - a) * F (zline t)) (by norm_num)).symm,
    curveIntegral_segment (ω := scalarOneForm F) a b]
  exact intervalIntegral.integral_congr fun t _ => by simp [scalarOneForm_apply, hzline t]

namespace InvChangeOfVariables

open Complex Real

/-- Simplify the Jacobian factor and an inverse power after substituting `t ↦ 1 / t`:
`(1 / t ^ 2) * (1 / t) ^ (-k) = t ^ (k - 2)` for `2 ≤ k` and `t ≠ 0`. -/
public lemma one_div_pow_two_mul_one_div_zpow (k : ℕ) (t : ℝ) (hk : 2 ≤ k) (ht : t ≠ 0) :
    (1 / t ^ 2) * ((1 / t : ℝ) ^ (-(k : ℤ))) = t ^ (k - 2) := by
  have hzpow : (1 / t : ℝ) ^ (-(k : ℤ)) = t ^ k := by rw [one_div]; simp [zpow_natCast]
  simpa [one_div, hzpow, mul_assoc, mul_left_comm, mul_comm] using (pow_sub₀ t ht hk).symm

/-- The image of `t ↦ 1 / t` on `Ioc (0, 1]` is `Ici 1`. -/
public lemma Ici_one_eq_image_inv_Ioc :
    Ici (1 : ℝ) = (fun t : ℝ ↦ 1 / t) '' (Ioc (0 : ℝ) (1 : ℝ)) := by
  refine Set.eq_of_subset_of_subset (fun x hx ↦ ?_) ?_
  · have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    exact ⟨x⁻¹, ⟨by simpa [one_div] using inv_pos.2 hx0,
      by simpa [one_div] using (inv_le_one₀ hx0).2 hx⟩, by simp⟩
  · rintro _ ⟨y, hy, rfl⟩
    simpa [one_div, mem_Ici] using one_le_inv_iff₀.2 hy

/-- Change-of-variables formula for `t ↦ 1 / t` from `Ici 1` back to `Ioc (0, 1]`. -/
public lemma integral_Ici_one_eq_integral_abs_deriv_smul (g : ℝ → ℂ) :
    ∫ s in Ici (1 : ℝ), g s = ∫ t in Ioc (0 : ℝ) 1, |(-1 / t ^ 2)| • g (1 / t) := by
  rw [Ici_one_eq_image_inv_Ioc]
  refine integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x hx ↦ by
      simpa [one_div, div_eq_mul_inv] using
        hasDerivWithinAt_inv (x := x) (ne_of_gt hx.1) (Ioc 0 1))
    (fun x _ y _ hxy ↦ inv_inj.1 (by simpa [one_div] using hxy)) g

end InvChangeOfVariables

/-- Integrability of the endpoint weight `(1 / t ^ 2) * exp (-c / t)` on `Ioc (0, 1]` for `c > 0`.
-/
public lemma integrableOn_one_div_sq_mul_exp_neg_div (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ (1 / t ^ 2) * Real.exp (-c / t)) (Set.Ioc (0 : ℝ) 1) volume := by
  let s : Set ℝ := Set.Ioc (0 : ℝ) 1; let f : ℝ → ℝ := fun t ↦ (1 : ℝ) / t
  let f' : ℝ → ℝ := fun t ↦ -(1 : ℝ) / t ^ 2
  have hs : MeasurableSet s := measurableSet_Ioc
  have hf' : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t := fun t ht => by
    simpa [f, f', one_div, div_eq_mul_inv, pow_two, ne_of_gt ht.1] using
      (hasDerivAt_inv (ne_of_gt ht.1)).hasDerivWithinAt
  have hfinj : Set.InjOn f s := fun a _ b _ hab =>
    inv_injective (by simpa [f, one_div] using hab)
  have himage : f '' s = Set.Ici (1 : ℝ) := by
    simpa [f, s] using (InvChangeOfVariables.Ici_one_eq_image_inv_Ioc).symm
  have hmain : IntegrableOn (fun t : ℝ ↦ |f' t| * Real.exp (-(c * f t))) s volume := by
    have : IntegrableOn (fun y : ℝ ↦ Real.exp (-(c * y))) (f '' s) volume := by
      simpa [himage, pow_zero, one_mul] using
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := c) hc)
    simpa [smul_eq_mul] using
      (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (hs := hs) (hf' := hf')
        (hf := hfinj) (g := fun y : ℝ ↦ Real.exp (-(c * y)))).1 this
  refine hmain.congr_fun (hs := hs) fun t _ => ?_
  simp [f', f, abs_of_nonneg (pow_two_nonneg t), div_eq_mul_inv]

end

end SpherePacking.Integration

/-! ## Helpers for real parametrisations in `ℍ`

Continuity and boundedness helpers for functions on `ℍ` along real parametrisations. -/

namespace SpherePacking.Integration

open scoped Interval
open Set

/-- Imaginary part of `-1 / (t + i)` as a real function of `t`. -/
public lemma im_neg_one_div_ofReal_add_I (t : ℝ) :
    (-1 / ((t : ℂ) + Complex.I)).im = 1 / (t ^ 2 + 1) := by
  simp [div_eq_mul_inv, Complex.normSq, pow_two]

/-- Imaginary part of `-1 / (-t + i)` as a real function of `t`. -/
public lemma im_neg_one_div_neg_ofReal_add_I (t : ℝ) :
    (-1 / (-(t : ℂ) + Complex.I)).im = 1 / (t ^ 2 + 1) := by
  simpa using im_neg_one_div_ofReal_add_I (t := -t)

/-- For `t ∈ (0,1)`, we have `1/2 < 1 / (t^2 + 1)`. -/
public lemma one_half_lt_one_div_sq_add_one_of_mem_Ioo01 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) < 1 / (t ^ 2 + 1) := by
  simpa using one_div_lt_one_div_of_lt (by positivity)
    (by linarith [(sq_lt_one_iff₀ ht.1.le).2 ht.2] : t ^ 2 + 1 < 2)

/-- Continuity helper for expressions that pass through `UpperHalfPlane.mk`, when a function on
`ℍ` is computed on `ℂ` with an explicit proof of positivity of the imaginary part. -/
public lemma continuous_comp_upperHalfPlane_mk {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {ψT : UpperHalfPlane → β} (hψT : Continuous ψT) {z : α → ℂ}
    (hz : Continuous z) (him : ∀ a : α, 0 < (z a).im) {ψT' : ℂ → β}
    (hEq : ∀ a : α, ψT' (z a) = ψT (⟨z a, him a⟩ : UpperHalfPlane)) :
    Continuous fun a : α => ψT' (z a) := by
  simpa [hEq] using hψT.comp (hz.upperHalfPlaneMk him)

/-- A continuous function on `[0,1]` is bounded on `Ι (0,1)`. -/
public lemma exists_bound_norm_uIoc_zero_one_of_continuous (f : ℝ → ℂ) (hf : Continuous f) :
    ∃ M : ℝ, ∀ t ∈ (Ι (0 : ℝ) 1), ‖f t‖ ≤ M :=
  let ⟨C, hC⟩ := SpherePacking.ForMathlib.exists_upper_bound_on_Icc (g := fun t : ℝ => ‖f t‖)
    (a := (0 : ℝ)) (b := 1) zero_le_one hf.norm.continuousOn
  ⟨C, fun x hx => hC x (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le zero_le_one] using hx))⟩

end SpherePacking.Integration

/-! # Differentiation under the integral sign on `(0, 1)`

Lemmas for differentiating `x ↦ ∫ t in Ioo (0 : ℝ) 1, hf t * exp (x * coeff t)`,
dimension-agnostic and used by the dimension-specific developments. -/

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
    unfold gN g; fun_prop
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
  -- Shrink the neighborhood so that `x + shift` stays uniformly positive.
  let ε : ℝ := (x + shift) / 2
  have ε_pos : 0 < ε := by simpa [ε] using half_pos (by linarith : 0 < x + shift)
  obtain ⟨C, hC⟩ := exists_bound_norm_hf
  have hC0 : 0 ≤ C :=
    SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖hf 1‖)
      (b := Real.exp (-(Real.pi * shift) * (1 : ℝ))) (C := C) (norm_nonneg _) (by positivity)
      (by simpa using hC 1 le_rfl)
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ (n + 1)) * (t ^ (n + 1) * Real.exp (-(Real.pi * ε) * t)) * C
  have hbound_int : Integrable bound μIciOne := by
    have hInt : Integrable (fun t : ℝ ↦ t ^ (n + 1) * Real.exp (-(Real.pi * ε) * t)) μIciOne := by
      simpa [IntegrableOn, μIciOne, mul_assoc] using
        SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n + 1)
          (b := Real.pi * ε) (mul_pos Real.pi_pos ε_pos)
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using hInt.const_mul ((Real.pi ^ (n + 1)) * C)
  have h_bound :
      ∀ᵐ t ∂μIciOne, ∀ y ∈ Metric.ball x ε, ‖gN (hf := hf) (n + 1) y t‖ ≤ bound t :=
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall fun t ht y hy => by
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
        simpa [gN, g, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          (SpherePacking.ForMathlib.hasDerivAt_mul_cexp_ofReal_mul_const
            (a := (Complex.I : ℂ) * (hf t)) (c := coeff t) y).const_mul ((coeff t) ^ n))).2

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
  have hnat : ∀ m : ℕ, ∀ k : ℕ, ContDiffOn ℝ m (F k) s := fun m => by
    induction m with
    | zero => intro k; exact contDiffOn_zero.2 (hdiff k).continuousOn
    | succ m ih =>
        intro k
        refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := F k) (s := s) (n := m) hs).2
          ⟨hdiff k, by simp, (ih (k + 1)).congr fun x hx => by simpa using (hF k x hx).deriv⟩
  simpa [contDiffOn_infty] using fun m => hnat m n

end SpherePacking.ForMathlib

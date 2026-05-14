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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

import SpherePacking.ForMathlib.DerivHelpers

/-! # Scalar one-form utilities, convenience measures on standard intervals (Lebesgue
restrictions), and inversion change-of-variables on `Ioc (0, 1]`. -/

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
    (hX := (measurable_const.mul (measurable_id.pow_const p)).aemeasurable) <| by
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
  let s : Set ℝ := Set.Ioc (0 : ℝ) 1
  let f : ℝ → ℝ := fun t ↦ (1 : ℝ) / t
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
  simp [f', f, abs_div, abs_of_nonneg (pow_two_nonneg t), div_eq_mul_inv]

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

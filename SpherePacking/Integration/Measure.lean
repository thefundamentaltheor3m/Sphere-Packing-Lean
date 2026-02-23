module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict

public import SpherePacking.ForMathlib.ScalarOneForm

/-!
# Convenience measures on standard intervals

This file defines repo-local convenience measures on standard intervals, used pervasively in the
sphere packing development (but too specialized for Mathlib).
-/

namespace SpherePacking.Integration

noncomputable section

open scoped Interval
open MeasureTheory Set intervalIntegral
open MagicFunction

/-- The restriction of Lebesgue measure to `Ioc (0, 1]`. -/
@[expose] public def μIoc01 : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)

/-- `μIoc01` is `SFinite`. -/
public instance : MeasureTheory.SFinite μIoc01 := by
  simpa [μIoc01] using (by infer_instance : SFinite (volume.restrict (Ioc (0 : ℝ) 1)))

/-- `μIoc01` is finite. -/
public instance : MeasureTheory.IsFiniteMeasure μIoc01 := by
  refine ⟨by simp [μIoc01]⟩

/-- The restriction of Lebesgue measure to `Ioo (0, 1)`. -/
@[expose] public def μIoo01 : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)

attribute [irreducible] μIoo01

/-- `μIoo01` is `SFinite`. -/
public instance : MeasureTheory.SFinite μIoo01 := by
  simpa [μIoo01] using (by infer_instance : SFinite (volume.restrict (Ioo (0 : ℝ) 1)))

/-- `μIoo01` is finite. -/
public instance : MeasureTheory.IsFiniteMeasure μIoo01 := by
  refine ⟨by simp [μIoo01]⟩

/-- The restriction of Lebesgue measure to `Ici 1`. -/
@[expose] public def μIciOne : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ici (1 : ℝ))

/-! `μIciOne` is `SFinite`. -/
public instance : MeasureTheory.SFinite μIciOne := by
  simpa [μIciOne] using (by infer_instance : SFinite (volume.restrict (Ici (1 : ℝ))))

/-- The restriction of Lebesgue measure to `Ioi 0`. -/
@[expose] public def μIoi0 : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioi (0 : ℝ))

/-!
#### `μIoo01` helper lemmas

These are small, reusable facts for the frequently used measure `μIoo01`.
-/

/-- Almost everywhere with respect to `μIoo01`, the variable lies in `Ioo (0, 1)`. -/
public lemma ae_mem_Ioo01_muIoo01 : ∀ᵐ t ∂μIoo01, t ∈ Ioo (0 : ℝ) 1 := by
  simpa [μIoo01] using
    (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)

/-- The function `t ↦ A * t ^ p` is integrable with respect to `μIoo01` when `0 ≤ A`. -/
public lemma integrable_const_mul_pow_muIoo01 (A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    Integrable (fun t : ℝ ↦ A * t ^ p) μIoo01 := by
  have haemeas : AEMeasurable (fun t : ℝ ↦ A * t ^ p) μIoo01 :=
    (measurable_const.mul (measurable_id.pow_const p)).aemeasurable
  have hμmem : ∀ᵐ t ∂μIoo01, t ∈ Ioo (0 : ℝ) 1 := ae_mem_Ioo01_muIoo01
  have hmem : ∀ᵐ t ∂μIoo01, (A * t ^ p) ∈ Set.Icc 0 A := by
    filter_upwards [hμmem] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    refine ⟨mul_nonneg hA (pow_nonneg ht0 _), ?_⟩
    have : A * t ^ p ≤ A * (1 : ℝ) := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1) hA
    simpa using this
  exact
    MeasureTheory.Integrable.of_mem_Icc (μ := μIoo01) (a := (0 : ℝ)) (b := A) (hX := haemeas) hmem

/-- The integral of `t ↦ A * t ^ p` with respect to `μIoo01` is nonnegative when `0 ≤ A`. -/
public lemma integral_nonneg_const_mul_pow_muIoo01 (A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    0 ≤ (∫ t : ℝ, A * t ^ p ∂μIoo01) := by
  refine integral_nonneg_of_ae ?_
  have hμmem : ∀ᵐ t ∂μIoo01, t ∈ Ioo (0 : ℝ) 1 := ae_mem_Ioo01_muIoo01
  filter_upwards [hμmem] with t ht
  exact mul_nonneg hA (pow_nonneg (le_of_lt ht.1) _)

/-!
#### `μIoc01` helper lemmas

We keep the segment/interval-integral conversion lemma here because most downstream uses of
`μIoc01` are in curve-integral arguments.
-/

/-- The integral against `μIoc01` equals the interval integral on `(0, 1]`. -/
public lemma integral_restrict_Ioc01_eq_intervalIntegral (f : ℝ → ℂ) :
    (∫ t : ℝ, f t ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) = ∫ t in (0 : ℝ)..1, f t := by
  simpa using
    (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) (f := f) (by norm_num)).symm

/-- Product with the restricted measure agrees with restricting the product measure. -/
public lemma prod_restrict_Ioc01_eq_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] :
    μ.prod ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) =
      (μ.prod (volume : Measure ℝ)).restrict ((univ : Set α) ×ˢ (Ioc (0 : ℝ) 1)) := by
  simpa using
    (Measure.prod_restrict (μ := μ) (ν := (volume : Measure ℝ)) (s := (univ : Set α))
      (t := Ioc (0 : ℝ) 1))

/-- Specialized version of `prod_restrict_Ioc01_eq_restrict` for `μIoc01`. -/
public lemma prod_muIoc01_eq_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] :
    μ.prod μIoc01 = (μ.prod (volume : Measure ℝ)).restrict ((univ : Set α) ×ˢ (Ioc (0 : ℝ) 1)) := by
  simpa [μIoc01] using prod_restrict_Ioc01_eq_restrict (μ := μ)

/-- Rewrite a restricted integral as a curve integral over a segment, for the scalar one-form. -/
public lemma integral_dir_mul_restrict_Ioc01_eq_curveIntegral_segment (F : ℂ → ℂ) (a b : ℂ)
    (zline : ℝ → ℂ) (hzline : ∀ t : ℝ, AffineMap.lineMap a b t = zline t) :
    (∫ t : ℝ, (b - a) * F (zline t) ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) =
      (∫ᶜ z in Path.segment a b, scalarOneForm F z) := by
  rw [integral_restrict_Ioc01_eq_intervalIntegral (f := fun t => (b - a) * F (zline t))]
  rw [curveIntegral_segment (ω := scalarOneForm F) a b]
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp [scalarOneForm_apply, hzline t]

/-- Version of `integral_dir_mul_restrict_Ioc01_eq_curveIntegral_segment` for `μIoc01`. -/
public lemma integral_dir_mul_muIoc01_eq_curveIntegral_segment (F : ℂ → ℂ) (a b : ℂ)
    (zline : ℝ → ℂ) (hzline : ∀ t : ℝ, AffineMap.lineMap a b t = zline t) :
    (∫ t : ℝ, (b - a) * F (zline t) ∂μIoc01) = (∫ᶜ z in Path.segment a b, scalarOneForm F z) := by
  simpa [μIoc01] using integral_dir_mul_restrict_Ioc01_eq_curveIntegral_segment F a b zline hzline

end

end SpherePacking.Integration

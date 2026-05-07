module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict

public import SpherePacking.ForMathlib.ScalarOneForm

/-! # Convenience measures on standard intervals (Lebesgue restrictions). -/

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

/-- The integral of `t ↦ A * t ^ p` with respect to `μIoo01` is nonnegative when `0 ≤ A`. -/
public lemma integral_nonneg_const_mul_pow_muIoo01 (A : ℝ) (p : ℕ) (hA : 0 ≤ A) :
    0 ≤ (∫ t : ℝ, A * t ^ p ∂μIoo01) :=
  integral_nonneg_of_ae <| by
    filter_upwards [ae_mem_Ioo01_muIoo01] with t ht
    exact mul_nonneg hA (pow_nonneg ht.1.le _)

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

end

end SpherePacking.Integration

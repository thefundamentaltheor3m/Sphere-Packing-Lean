module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Contour.Segments

/-!
Shared "curve integral = interval integral" lemmas for the four standard J12 segments.

These are used to present the real integrals `J₁'` to `J₄'` as curve integrals of the scalar 1-form
`scalarOneForm f` along the segments

* `-1 → -1 + I`
* `-1 + I → I`
* `1 → 1 + I`
* `1 + I → I`.

They are dimension-agnostic: callers instantiate `f` with the appropriate integrand (typically
`Ψ₁' r`).
-/

open scoped Interval
open MeasureTheory
open MagicFunction.Parametrisations MagicFunction

namespace SpherePacking.Contour

noncomputable section

private lemma curveIntegral_segment_eq_intervalIntegral (a b : ℂ) (f : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → AffineMap.lineMap a b t = g t) :
    (∫ᶜ z in Path.segment a b, scalarOneForm f z) = ∫ t in (0 : ℝ)..1, (b - a) * f (g t) := by
  rw [curveIntegral_segment (ω := scalarOneForm f) a b]
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) fun t ht => ?_
  simp [scalarOneForm_apply, hg t (by simpa [Set.uIcc_of_le zero_le_one] using ht)]

/-- Rewrite the segment integral on `1 → 1 + I` as an interval integral in the parameter `t`. -/
public lemma curveIntegral_segment_z₃ (f : ℂ → ℂ) :
    (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I), scalarOneForm f z) =
      ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * f (z₃' t) := by
    simpa using curveIntegral_segment_eq_intervalIntegral (1 : ℂ) ((1 : ℂ) + Complex.I) f z₃'
      lineMap_z₃_eq_z₃'

/-- Rewrite the segment integral on `1 + I → I` as an interval integral in the parameter `t`. -/
public lemma curveIntegral_segment_z₄ (f : ℂ → ℂ) :
    (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I, scalarOneForm f z) =
      ∫ t in (0 : ℝ)..1, (-1 : ℂ) * f (z₄' t) := by
    simpa using curveIntegral_segment_eq_intervalIntegral ((1 : ℂ) + Complex.I) Complex.I f z₄'
      lineMap_z₄_eq_z₄'

end

end SpherePacking.Contour

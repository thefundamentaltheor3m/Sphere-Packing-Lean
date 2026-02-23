module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import SpherePacking.ForMathlib.ScalarOneForm

/-!
# `DiffContOnCl` for scalar one-forms

This file packages a common step in contour deformation arguments: the construction
`F ↦ MagicFunction.scalarOneForm F` preserves `DiffContOnCl`.
-/

namespace SpherePacking.ForMathlib

noncomputable section

lemma diffContOnCl_smulRight_one {F : ℂ → ℂ} {s : Set ℂ} (hF : DiffContOnCl ℝ F s) :
    DiffContOnCl ℝ (fun z : ℂ => (ContinuousLinearMap.id ℂ ℂ).smulRight (F z)) s := by
  let L : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ
  simpa [L] using (L.differentiable.comp_diffContOnCl (g := F) (t := s) hF)

/-- If `F` is `DiffContOnCl` on `s`, then the associated scalar one-form is `DiffContOnCl` on `s`.
-/
public lemma diffContOnCl_scalarOneForm {F : ℂ → ℂ} {s : Set ℂ} (hF : DiffContOnCl ℝ F s) :
    DiffContOnCl ℝ (MagicFunction.scalarOneForm F) s := by
  simpa [MagicFunction.scalarOneForm] using diffContOnCl_smulRight_one hF

end

end SpherePacking.ForMathlib

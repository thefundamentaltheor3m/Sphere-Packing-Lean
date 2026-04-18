module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Scalar one-form utilities

This file is meant to be independent of the rest of the project so it can be upstreamed to Mathlib.
It provides the definition of `scalarOneForm`, its `DiffContOnCl` preservation, and
symmetry of its `fderiv`/`fderivWithin`.
-/

namespace MagicFunction

/-- Interpret a scalar function `F : ℂ → ℂ` as the `ℂ`-linear one-form `v ↦ v * F z`. -/
@[expose] public def scalarOneForm (F : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ (ContinuousLinearMap.id ℂ ℂ).smulRight (F z)

/-- Evaluate `scalarOneForm` as multiplication by `F z`. -/
@[simp] public lemma scalarOneForm_apply (F : ℂ → ℂ) (z v : ℂ) :
    scalarOneForm F z v = v * F z := by simp [scalarOneForm]

end MagicFunction

namespace SpherePacking.ForMathlib

noncomputable section

/-- If `F` is `DiffContOnCl` on `s`, then the associated scalar one-form is `DiffContOnCl` on `s`.
-/
public lemma diffContOnCl_scalarOneForm {F : ℂ → ℂ} {s : Set ℂ} (hF : DiffContOnCl ℝ F s) :
    DiffContOnCl ℝ (MagicFunction.scalarOneForm F) s := by
  let L : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ
  simpa [MagicFunction.scalarOneForm, L] using
    L.differentiable.comp_diffContOnCl (g := F) (t := s) hF

open MagicFunction

/-- The `fderiv` of `scalarOneForm f` is symmetric in its two tangent arguments. -/
public lemma fderiv_scalarOneForm_symm {f : ℂ → ℂ} {x u v : ℂ}
    (hfdiff : DifferentiableAt ℂ f x) :
    fderiv ℝ (scalarOneForm f) x u v = fderiv ℝ (scalarOneForm f) x v u := by
  let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) := (ContinuousLinearMap.mul ℂ ℂ).flip
  have hEq : scalarOneForm f = fun z => L (f z) := rfl
  have hωF :
      HasFDerivAt (𝕜 := ℝ) (scalarOneForm f)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L (deriv f x))).restrictScalars ℝ) x := by
    simpa [hEq] using
      ((hasDerivAt_const x L).clm_apply hfdiff.hasDerivAt).hasFDerivAt.restrictScalars ℝ
  rw [hωF.fderiv]
  simp [L, mul_left_comm, mul_comm]

/-- `fderivWithin`-version of `fderiv_scalarOneForm_symm` on an open set. -/
public lemma fderivWithin_scalarOneForm_symm_of_isOpen
    {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    {u v : ℂ} (hfdiff : DifferentiableAt ℂ f x) :
    fderivWithin ℝ (scalarOneForm f) s x u v = fderivWithin ℝ (scalarOneForm f) s x v u := by
  simpa [fderivWithin_of_mem_nhds (f := scalarOneForm f) (hs.mem_nhds hx)] using
    (fderiv_scalarOneForm_symm (f := f) (x := x) (u := u) (v := v) hfdiff)

end

end SpherePacking.ForMathlib

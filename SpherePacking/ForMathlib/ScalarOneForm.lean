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

Independent of the rest of the project so it can be upstreamed to Mathlib. Provides
`scalarOneForm`, its `DiffContOnCl` preservation, and symmetry of its `fderiv`/`fderivWithin`.
-/

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

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Scalar one-form utilities

This file is meant to be independent of the rest of the project so it can be upstreamed to Mathlib.
-/

namespace MagicFunction

/-- Interpret a scalar function `F : ℂ → ℂ` as the `ℂ`-linear one-form `v ↦ v * F z`. -/
@[expose] public def scalarOneForm (F : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z ↦ (ContinuousLinearMap.id ℂ ℂ).smulRight (F z)

/-- Evaluate `scalarOneForm` as multiplication by `F z`. -/
@[simp] public lemma scalarOneForm_apply (F : ℂ → ℂ) (z v : ℂ) :
    scalarOneForm F z v = v * F z := by simp [scalarOneForm]

end MagicFunction

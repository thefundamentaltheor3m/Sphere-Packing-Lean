module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Mobius inversion: basic API for `z ↦ -z⁻¹`. -/

namespace SpherePacking

noncomputable section

/-- The Mobius inversion map `z ↦ -z⁻¹`. -/
@[expose] public def mobiusInv (z : ℂ) : ℂ := -z⁻¹

/-- Complex derivative of `mobiusInv`. -/
public lemma deriv_mobiusInv (z : ℂ) : deriv mobiusInv z = (1 : ℂ) / z ^ (2 : ℕ) := by
  simp [show mobiusInv = (fun z : ℂ => -z⁻¹) from rfl, deriv_inv, div_eq_mul_inv]

end

end SpherePacking

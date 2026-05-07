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

/-- Derivative of `mobiusInv` composed with a line segment `AffineMap.lineMap a b`. -/
public lemma hasDerivAt_mobiusInv_comp_lineMap (a b : ℂ) (t : ℝ)
    (h0 : AffineMap.lineMap a b t ≠ 0) :
    HasDerivAt (fun s : ℝ => mobiusInv (AffineMap.lineMap a b s))
      ((b - a) / (AffineMap.lineMap a b t) ^ (2 : ℕ)) t := by
  simpa [mobiusInv, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using
    ((by simpa [mobiusInv] using (hasFDerivAt_inv' (𝕜 := ℝ) (R := ℂ) h0).neg :
      HasFDerivAt (𝕜 := ℝ) mobiusInv
        (ContinuousLinearMap.mulLeftRight ℝ ℂ (AffineMap.lineMap a b t)⁻¹
          (AffineMap.lineMap a b t)⁻¹) (AffineMap.lineMap a b t)).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t)))

end

end SpherePacking

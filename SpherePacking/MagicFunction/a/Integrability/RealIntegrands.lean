/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

/-! # Smoothness

We prove smoothness of the integrands of all of the REAL integrals making up `a`, by translating
complex holomorphicity results via smoothness of the parametrisations.
-/

open Real ContDiff Filter Set Complex

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands MagicFunction.Parametrisations

variable {r : ℝ}

namespace MagicFunction.a.RealIntegrands

/-- Smoothness of the real integrand `Φ₂ r` on `Icc (0, 1)`. -/
public theorem Φ₂_contDiffOn : ContDiffOn ℝ ∞ (Φ₂ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₂_def, Φ₂'] using ((Φ₁'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ).comp
    (((contDiffOn_const.add ofRealCLM.contDiff.contDiffOn).add contDiffOn_const).congr
      fun y hy ↦ by simpa [add_assoc] using z₂'_eq_of_mem (t := y) hy) z₂'_mapsto

/-- Smoothness of the real integrand `Φ₄ r` on `Icc (0, 1)`. -/
public theorem Φ₄_contDiffOn : ContDiffOn ℝ ∞ (Φ₄ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₄_def, Φ₄', smul_eq_mul] using ContDiffOn.const_smul (c := (-1 : ℂ))
    ((Φ₃'_contDiffOn (r := r)).comp
      (((contDiffOn_const.sub ofRealCLM.contDiff.contDiffOn).add contDiffOn_const).congr
        fun y hy ↦ by simpa [sub_eq_add_neg, add_assoc] using z₄'_eq_of_mem (t := y) hy)
      z₄'_mapsto)

/-- Smoothness of the real integrand `Φ₆ r` on `Ici 1`. -/
public theorem Φ₆_contDiffOn : ContDiffOn ℝ ∞ (Φ₆ r) (Ici (1 : ℝ)) := by
  simpa [Φ₆_def, smul_eq_mul] using ContDiffOn.const_smul (c := I)
    (((Φ₆'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ).comp
      ((contDiffOn_const.mul ofRealCLM.contDiff.contDiffOn).congr
        fun y hy ↦ by simpa using z₆'_eq_of_mem (t := y) hy)
      z₆'_mapsto)

end MagicFunction.a.RealIntegrands

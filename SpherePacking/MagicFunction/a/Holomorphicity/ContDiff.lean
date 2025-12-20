/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.Holomorphicity.I1

/-! # Smoothness

In this file, we prove that the integrands of all of the REAL integrals making up a are smooth. That
is, we translate the complex holomorphicity results into smoothness results by showing first that
the parametrisations are smooth and then composing them with the holomorphicity proofs to conclude
that the composition of the complex integrands with the parametrisations are smooth real functions.
-/

open Real ContDiff Filter Set Complex

section Parametrisations

namespace MagicFunction.Parametrisations

theorem z₁'_contDiffOn : ContDiffOn ℝ ∞ z₁' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₁' y = _ :=
    fun _ hy => z₁'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.add (contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt)

theorem z₂'_contDiffOn : ContDiffOn ℝ ∞ z₂' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₂' y = _ :=
    fun _ hy => z₂'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact (contDiffWithinAt_const.add ofRealCLM.contDiff.contDiffWithinAt).add contDiffWithinAt_const

theorem z₃'_contDiffOn : ContDiffOn ℝ ∞ z₃' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₃' y = _ :=
    fun _ hy => z₃'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.add (contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt)

theorem z₄'_contDiffOn : ContDiffOn ℝ ∞ z₄' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₄' y = _ :=
    fun _ hy => z₄'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact (contDiffWithinAt_const.sub ofRealCLM.contDiff.contDiffWithinAt).add contDiffWithinAt_const

theorem z₅'_contDiffOn : ContDiffOn ℝ ∞ z₅' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₅' y = _ :=
    fun _ hy => z₅'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt

theorem z₆'_contDiffOn : ContDiffOn ℝ ∞ z₆' (Ioi (1 : ℝ)) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioi (1 : ℝ), z₆' y = _ :=
    fun _ hy => z₆'_eq_of_mem <| mem_Ici_of_Ioi hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt

end Parametrisations

section ContDiff

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

variable {r : ℝ} (hr : r ≥ 0)

namespace MagicFunction.a.RealIntegrands

theorem Φ₁_contDiffOn : ContDiffOn ℝ ∞ (Φ₁ r) (Ioc (0 : ℝ) 1) := by
  sorry

end MagicFunction.a.RealIntegrands

end ContDiff

/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.Holomorphicity.I1
import SpherePacking.MagicFunction.a.Holomorphicity.I2
import SpherePacking.MagicFunction.a.Holomorphicity.I3
import SpherePacking.MagicFunction.a.Holomorphicity.I4
import SpherePacking.MagicFunction.a.Holomorphicity.I5
import SpherePacking.MagicFunction.a.Holomorphicity.I6

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
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₁' y = _ := fun _ hy => z₁'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.add (contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt)

theorem z₂'_contDiffOn : ContDiffOn ℝ ∞ z₂' (Icc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Icc (0 : ℝ) 1, z₂' y = _ := fun _ hy => z₂'_eq_of_mem hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact (contDiffWithinAt_const.add ofRealCLM.contDiff.contDiffWithinAt).add contDiffWithinAt_const

theorem z₃'_contDiffOn : ContDiffOn ℝ ∞ z₃' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₃' y = _ := fun _ hy => z₃'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.add (contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt)

theorem z₄'_contDiffOn : ContDiffOn ℝ ∞ z₄' (Icc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Icc (0 : ℝ) 1, z₄' y = _ := fun _ hy => z₄'_eq_of_mem hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact (contDiffWithinAt_const.sub ofRealCLM.contDiff.contDiffWithinAt).add contDiffWithinAt_const

theorem z₅'_contDiffOn : ContDiffOn ℝ ∞ z₅' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₅' y = _ := fun _ hy => z₅'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt

theorem z₆'_contDiffOn : ContDiffOn ℝ ∞ z₆' (Ici (1 : ℝ)) := by
  intro x hx
  have h_eq : ∀ y ∈ Ici (1 : ℝ), z₆' y = _ := fun _ hy => z₆'_eq_of_mem hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt

end MagicFunction.Parametrisations

end Parametrisations

section ContDiff

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

variable {r : ℝ} (hr : r ≥ 0)

namespace MagicFunction.a.RealIntegrands

include hr in
theorem Φ₁_contDiffOn : ContDiffOn ℝ ∞ (Φ₁ r) (Ioc (0 : ℝ) 1) := by
  simp only [Φ₁_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₁' r) ∘ z₁') (Ioc (0 : ℝ) 1)
  refine (Φ₁'_contDiffOn hr).comp z₁'_contDiffOn ?_
  exact z₁'_mapsto

include hr in
theorem Φ₂_contDiffOn : ContDiffOn ℝ ∞ (Φ₂ r) (Icc (0 : ℝ) 1) := by
  simp only [Φ₂_def]
  change ContDiffOn ℝ ∞ ((Φ₂' r) ∘ z₂') (Icc (0 : ℝ) 1)
  refine (Φ₂'_contDiffOn hr).comp z₂'_contDiffOn ?_
  exact z₂'_mapsto

include hr in
theorem Φ₃_contDiffOn : ContDiffOn ℝ ∞ (Φ₃ r) (Ioc (0 : ℝ) 1) := by
  simp only [Φ₃_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₃' r) ∘ z₃') (Ioc (0 : ℝ) 1)
  refine (Φ₃'_contDiffOn hr).comp z₃'_contDiffOn ?_
  exact z₃'_mapsto

include hr in
theorem Φ₄_contDiffOn : ContDiffOn ℝ ∞ (Φ₄ r) (Icc (0 : ℝ) 1) := by
  simp only [Φ₄_def, ← smul_eq_mul (-1 : ℂ) _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₄' r) ∘ z₄') (Icc (0 : ℝ) 1)
  refine (Φ₄'_contDiffOn hr).comp z₄'_contDiffOn ?_
  exact z₄'_mapsto

include hr in
theorem Φ₅_contDiffOn : ContDiffOn ℝ ∞ (Φ₅ r) (Ioc (0 : ℝ) 1) := by
  simp only [Φ₅_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₅' r) ∘ z₅') (Ioc (0 : ℝ) 1)
  refine (Φ₅'_contDiffOn hr).comp z₅'_contDiffOn ?_
  exact z₅'_mapsto

include hr in
theorem Φ₆_contDiffOn : ContDiffOn ℝ ∞ (Φ₆ r) (Ici (1 : ℝ)) := by
  simp only [Φ₆_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₆' r) ∘ z₆') (Ici (1 : ℝ))
  refine (Φ₆'_contDiffOn hr).comp z₆'_contDiffOn ?_
  exact z₆'_mapsto

end MagicFunction.a.RealIntegrands

end ContDiff

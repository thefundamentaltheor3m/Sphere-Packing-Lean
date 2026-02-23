/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands

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

private lemma z₂'_rhs_contDiffOn :
    ContDiffOn ℝ ∞ (fun y : ℝ => (-1 : ℂ) + y + I) (Icc (0 : ℝ) 1) := by
  simpa [add_assoc] using
    ((contDiffOn_const.add ofRealCLM.contDiff.contDiffOn).add contDiffOn_const)

/-- Smoothness of the parametrisation `z₂'` on `Icc (0, 1)`. -/
public theorem z₂'_contDiffOn : ContDiffOn ℝ ∞ z₂' (Icc (0 : ℝ) 1) := by
  refine z₂'_rhs_contDiffOn.congr fun y hy => by simpa using z₂'_eq_of_mem (t := y) hy

theorem z₃'_contDiffOn : ContDiffOn ℝ ∞ z₃' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₃' y = _ := fun _ hy => z₃'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.add (contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt)

private lemma z₄'_rhs_contDiffOn :
    ContDiffOn ℝ ∞ (fun y : ℝ => (1 : ℂ) - y + I) (Icc (0 : ℝ) 1) := by
  simpa [sub_eq_add_neg, add_assoc] using
    ((contDiffOn_const.sub ofRealCLM.contDiff.contDiffOn).add contDiffOn_const)

/-- Smoothness of the parametrisation `z₄'` on `Icc (0, 1)`. -/
public theorem z₄'_contDiffOn : ContDiffOn ℝ ∞ z₄' (Icc (0 : ℝ) 1) := by
  refine z₄'_rhs_contDiffOn.congr fun y hy => by simpa using z₄'_eq_of_mem (t := y) hy

theorem z₅'_contDiffOn : ContDiffOn ℝ ∞ z₅' (Ioc (0 : ℝ) 1) := by
  intro x hx
  have h_eq : ∀ y ∈ Ioc (0 : ℝ) 1, z₅' y = _ := fun _ hy => z₅'_eq_of_mem <| mem_Icc_of_Ioc hy
  refine ContDiffWithinAt.congr ?_ h_eq <| h_eq x hx
  exact contDiffWithinAt_const.mul ofRealCLM.contDiff.contDiffWithinAt

private lemma z₆'_rhs_contDiffOn : ContDiffOn ℝ ∞ (fun y : ℝ => I * y) (Ici (1 : ℝ)) := by
  simpa using (contDiffOn_const.mul ofRealCLM.contDiff.contDiffOn)

/-- Smoothness of the parametrisation `z₆'` on `Ici 1`. -/
public theorem z₆'_contDiffOn : ContDiffOn ℝ ∞ z₆' (Ici (1 : ℝ)) := by
  refine z₆'_rhs_contDiffOn.congr fun y hy => by simpa using z₆'_eq_of_mem (t := y) hy

end MagicFunction.Parametrisations

end Parametrisations
section Integrands

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

variable {r : ℝ} (hr : r ≥ 0)

namespace MagicFunction.a.RealIntegrands

public theorem Φ₁_contDiffOn : ContDiffOn ℝ ∞ (Φ₁ r) (Ioc (0 : ℝ) 1) := by
  simp only [Φ₁_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₁' r) ∘ z₁') (Ioc (0 : ℝ) 1)
  refine Φ₁'_contDiffOn.comp z₁'_contDiffOn ?_
  exact z₁'_mapsto

/-- Smoothness of the real integrand `Φ₂ r` on `Icc (0, 1)`. -/
public theorem Φ₂_contDiffOn : ContDiffOn ℝ ∞ (Φ₂ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₂_def, Φ₂'] using (Φ₁'_contDiffOn (r := r)).comp z₂'_contDiffOn z₂'_mapsto

public theorem Φ₃_contDiffOn : ContDiffOn ℝ ∞ (Φ₃ r) (Ioc (0 : ℝ) 1) := by
  simp only [Φ₃_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₃' r) ∘ z₃') (Ioc (0 : ℝ) 1)
  refine Φ₃'_contDiffOn.comp z₃'_contDiffOn ?_
  exact z₃'_mapsto


/-- Smoothness of the real integrand `Φ₄ r` on `Icc (0, 1)`. -/
private lemma Φ₄_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (-1 : ℂ) • Φ₃' r (z₄' t)) (Icc (0 : ℝ) 1) := by
  simpa using
    ContDiffOn.const_smul (c := (-1 : ℂ))
      ((Φ₃'_contDiffOn (r := r)).comp z₄'_contDiffOn z₄'_mapsto)

public theorem Φ₄_contDiffOn : ContDiffOn ℝ ∞ (Φ₄ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₄_def, Φ₄', smul_eq_mul] using Φ₄_contDiffOn_core (r := r)

public theorem Φ₅_contDiffOn : ContDiffOn ℝ ∞ (Φ₅ r) (Ioc (0 : ℝ) 1) := by
  simp only [Φ₅_def, ← smul_eq_mul I _]
  apply ContDiffOn.const_smul
  change ContDiffOn ℝ ∞ ((Φ₅' r) ∘ z₅') (Ioc (0 : ℝ) 1)
  refine Φ₅'_contDiffOn.comp z₅'_contDiffOn ?_
  exact z₅'_mapsto

/-- Smoothness of the real integrand `Φ₆ r` on `Ici 1`. -/
private lemma Φ₆_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (I : ℂ) • Φ₆' r (z₆' t)) (Ici (1 : ℝ)) := by
  simpa using
    ContDiffOn.const_smul (c := I) ((Φ₆'_contDiffOn (r := r)).comp z₆'_contDiffOn z₆'_mapsto)

public theorem Φ₆_contDiffOn : ContDiffOn ℝ ∞ (Φ₆ r) (Ici (1 : ℝ)) := by
  simpa [Φ₆_def, smul_eq_mul] using Φ₆_contDiffOn_core (r := r)

end MagicFunction.a.RealIntegrands

end Integrands

/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
import Mathlib
import SpherePacking.Basic.SpherePacking

/-!
# Density of Periodic Packings

In this file, we prove the following important results on periodic sphere packings:
-/

open scoped ENNReal
open Metric BigOperators Pointwise Filter MeasureTheory

variable {d : ℕ} (S : PeriodicSpherePacking d)

section Quotient

def PeriodicSpherePacking.AddActionQuotient : Type := Quotient (AddAction.orbitRel S.Λ S.centers)

def PeriodicSpherePacking.AddActionQuotient_coe : PeriodicSpherePacking.AddActionQuotient S →
  EuclideanSpace ℝ (Fin d) := sorry

lemma PeriodicSpherePacking.AddActionQuotient_coe_injective :
  Function.Injective S.AddActionQuotient_coe := sorry

instance PeriodicSpherePacking.instFintypeOrbits :
  Fintype (PeriodicSpherePacking.AddActionQuotient S) := sorry

end Quotient

noncomputable section Density_Formula

@[simp]
def PeriodicSpherePacking.density : ℝ :=
  (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toNNReal *
  (Fintype.card (S.AddActionQuotient) : ℝ) / ((Zlattice.covolume S.Λ volume) : ℝ)

theorem PeriodicSpherePacking.density_eq :
  S.density = (S.toSpherePacking).density.toReal := by
  rw [density, SpherePacking.density]
  sorry

end Density_Formula

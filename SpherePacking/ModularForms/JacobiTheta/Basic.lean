/-
Copyright (c) 2025 Sphere Packing Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.Power
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Order.CompletePartialOrder

public import SpherePacking.ForMathlib.ModularFormsHelpers

/-!
# Jacobi theta functions: definitions and basic identifications

This file defines the Jacobi theta functions `Θ₂`, `Θ₃`, `Θ₄` on the upper half-plane and their
fourth powers `H₂`, `H₃`, `H₄`. It also records their identification with the two-variable Jacobi
theta function `jacobiTheta₂` from Mathlib, as well as summability helpers used throughout the
rest of the `JacobiTheta` development.

## Main declarations
* `Θ₂`, `Θ₃`, `Θ₄`
* `H₂`, `H₃`, `H₄`
* `Θ₂_as_jacobiTheta₂`, `Θ₃_as_jacobiTheta₂`, `Θ₄_as_jacobiTheta₂`
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-- The term in the series defining `Θ₂`. -/
@[expose] public noncomputable def Θ₂_term (n : ℤ) (τ : ℍ) : ℂ :=
  cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)
/-- The term in the series defining `Θ₃`. -/
@[expose] public noncomputable def Θ₃_term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- The term in the series defining `Θ₄`. -/
@[expose] public noncomputable def Θ₄_term (n : ℤ) (τ : ℍ) : ℂ :=
  (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- The Jacobi theta function `Θ₂` on the upper half-plane. -/
@[expose] public noncomputable def Θ₂ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₂_term n τ
/-- The Jacobi theta function `Θ₃` on the upper half-plane. -/
@[expose] public noncomputable def Θ₃ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₃_term n τ
/-- The Jacobi theta function `Θ₄` on the upper half-plane. -/
@[expose] public noncomputable def Θ₄ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₄_term n τ
/-- The fourth power of `Θ₂`. -/
@[expose] public noncomputable def H₂ (τ : ℍ) : ℂ := (Θ₂ τ) ^ 4
/-- The fourth power of `Θ₃`. -/
@[expose] public noncomputable def H₃ (τ : ℍ) : ℂ := (Θ₃ τ) ^ 4
/-- The fourth power of `Θ₄`. -/
@[expose] public noncomputable def H₄ (τ : ℍ) : ℂ := (Θ₄ τ) ^ 4

/-!
## Connection with `jacobiTheta₂`
-/

/-- Identify `Θ₂_term` with a specialization of `jacobiTheta₂_term`. -/
public theorem Θ₂_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₂_term n τ = cexp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [Θ₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

/-- Identify `Θ₂` with a specialization of `jacobiTheta₂`. -/
public theorem Θ₂_as_jacobiTheta₂ (τ : ℍ) :
    Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  simp_rw [Θ₂, Θ₂_term_as_jacobiTheta₂_term, tsum_mul_left, jacobiTheta₂]

/-- Identify `Θ₃_term` with a specialization of `jacobiTheta₂_term`. -/
public theorem Θ₃_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₃_term n τ = jacobiTheta₂_term n 0 τ := by
  simp [Θ₃_term, jacobiTheta₂_term]

/-- Identify `Θ₃` with a specialization of `jacobiTheta₂`. -/
public theorem Θ₃_as_jacobiTheta₂ (τ : ℍ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, Θ₃_term_as_jacobiTheta₂_term, jacobiTheta₂]

/-- Identify `Θ₄_term` with a specialization of `jacobiTheta₂_term`. -/
public theorem Θ₄_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₄_term n τ = jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [Θ₄_term, jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
  ring_nf

/-- Identify `Θ₄` with a specialization of `jacobiTheta₂`. -/
public theorem Θ₄_as_jacobiTheta₂ (τ : ℍ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, Θ₄_term_as_jacobiTheta₂_term, jacobiTheta₂]

/-!
## Shared helpers
-/

@[grind =] public lemma I_mul_mul_I (x y : ℂ) : I * (x * (I * y)) = -(x * y) := by
  simp [mul_left_comm, mul_comm]

public lemma summable_Θ₂_term (τ : ℍ) : Summable (fun n : ℤ => Θ₂_term n τ) := by
  simpa [Θ₂_term_as_jacobiTheta₂_term (τ := τ)] using
    ((summable_jacobiTheta₂_term_iff (z := (τ : ℂ) / 2) (τ := (τ : ℂ))).2
          (by simpa using τ.im_pos)).mul_left (cexp (π * Complex.I * (τ : ℂ) / 4))

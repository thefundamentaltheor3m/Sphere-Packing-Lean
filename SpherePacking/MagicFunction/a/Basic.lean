/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.IntegralParametrisations

/-!
# Integral representation of the magic function `a`

Complex integrands and real reparametrizations for the scalar integrals `I₁'`, ..., `I₆'` and
their radial versions on `V = EuclideanSpace ℝ (Fin 8)`. Primed names take a scalar; unprimed
names are radial: `‖x‖^2 ↦ Iᵢ' (‖x‖^2)`.
-/

local notation "V" => EuclideanSpace ℝ (Fin 8)

open scoped UpperHalfPlane
open Set Complex Real MagicFunction.Parametrisations

noncomputable section

variable (r : ℝ)

namespace MagicFunction.a.ComplexIntegrands

/-- First complex integrand for `a`. -/
@[expose] public def Φ₁' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))

/-- A copy of `Φ₁'` used for uniform indexing. -/
@[expose] public def Φ₂' : ℂ → ℂ := Φ₁' r

/-- Third complex integrand for `a`. -/
@[expose] public def Φ₃' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))

/-- A copy of `Φ₃'` used for uniform indexing. -/
@[expose] public def Φ₄' : ℂ → ℂ := Φ₃' r

/-- Fifth complex integrand for `a`. -/
@[expose] public def Φ₅' : ℂ → ℂ :=
  fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))

/-- Sixth complex integrand for `a`. -/
@[expose] public def Φ₆' : ℂ → ℂ := fun z ↦ φ₀'' z * cexp (π * I * r * (z : ℂ))

end MagicFunction.a.ComplexIntegrands

namespace MagicFunction.a.RealIntegrands

open MagicFunction.a.ComplexIntegrands

/-- Real-variable integrand from `Φ₁'` via `z₁'`. -/
@[expose] public def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' r (z₁' t)
/-- Real-variable integrand from `Φ₂'` via `z₂'`. -/
@[expose] public def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' r (z₂' t)
/-- Real-variable integrand from `Φ₃'` via `z₃'`. -/
@[expose] public def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' r (z₃' t)
/-- Real-variable integrand from `Φ₄'` via `z₄'`. -/
@[expose] public def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' r (z₄' t)
/-- Real-variable integrand from `Φ₅'` via `z₅'`. -/
@[expose] public def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' r (z₅' t)
/-- Real-variable integrand from `Φ₆'` via `z₆'`. -/
@[expose] public def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' r (z₆' t)

@[simp] public lemma Φ₁_def : Φ₁ r = fun t ↦ I * Φ₁' r (z₁' t) := rfl
@[simp] public lemma Φ₂_def : Φ₂ r = fun t ↦ Φ₂' r (z₂' t) := rfl
@[simp] public lemma Φ₃_def : Φ₃ r = fun t ↦ I * Φ₃' r (z₃' t) := rfl
@[simp] public lemma Φ₄_def : Φ₄ r = fun t ↦ -1 * Φ₄' r (z₄' t) := rfl
@[simp] public lemma Φ₅_def : Φ₅ r = fun t ↦ I * Φ₅' r (z₅' t) := rfl
@[simp] public lemma Φ₆_def : Φ₆ r = fun t ↦ I * Φ₆' r (z₆' t) := rfl

end MagicFunction.a.RealIntegrands

namespace MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrands

/-- First scalar integral for `a'`. -/
@[expose] public def I₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₁ x t
/-- Second scalar integral for `a'`. -/
@[expose] public def I₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₂ x t
/-- Third scalar integral for `a'`. -/
@[expose] public def I₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₃ x t
/-- Fourth scalar integral for `a'`. -/
@[expose] public def I₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₄ x t
/-- Fifth scalar integral for `a'`. -/
@[expose] public def I₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ x t
/-- Sixth scalar integral for `a'`. -/
@[expose] public def I₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ x t

/-- Scalar `a'` as the sum of `I₁'`, ..., `I₆'`. -/
@[expose] public def a' : ℝ → ℂ := fun x ↦ I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x

end MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrals

namespace MagicFunction.a.RadialFunctions

/-- Radial function on `V` from `I₁'` via `r = ‖x‖^2`. -/
@[expose] public def I₁ : V → ℂ := fun x ↦ I₁' (‖x‖ ^ 2)
/-- Radial function on `V` from `I₂'` via `r = ‖x‖^2`. -/
@[expose] public def I₂ : V → ℂ := fun x ↦ I₂' (‖x‖ ^ 2)
/-- Radial function on `V` from `I₃'` via `r = ‖x‖^2`. -/
@[expose] public def I₃ : V → ℂ := fun x ↦ I₃' (‖x‖ ^ 2)
/-- Radial function on `V` from `I₄'` via `r = ‖x‖^2`. -/
@[expose] public def I₄ : V → ℂ := fun x ↦ I₄' (‖x‖ ^ 2)
/-- Radial function on `V` from `I₅'` via `r = ‖x‖^2`. -/
@[expose] public def I₅ : V → ℂ := fun x ↦ I₅' (‖x‖ ^ 2)
/-- Radial function on `V` from `I₆'` via `r = ‖x‖^2`. -/
@[expose] public def I₆ : V → ℂ := fun x ↦ I₆' (‖x‖ ^ 2)

/-- Magic function `a` as a radial function on `V`. -/
@[expose] public def a : V → ℂ := fun x ↦ a' (‖x‖ ^ 2)

open intervalIntegral

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

@[simp] public lemma a_eq (x : V) : a x = I₁ x + I₂ x + I₃ x + I₄ x + I₅ x + I₆ x := rfl
@[simp] public lemma I₁_eq (x : V) : I₁ x = I₁' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₂_eq (x : V) : I₂ x = I₂' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₃_eq (x : V) : I₃ x = I₃' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₄_eq (x : V) : I₄ x = I₄' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₅_eq (x : V) : I₅ x = I₅' (‖x‖ ^ 2) := rfl
@[simp] public lemma I₆_eq (x : V) : I₆ x = I₆' (‖x‖ ^ 2) := rfl

/-- Explicit integral expression for `I₁'`. -/
public lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₁, Φ₁', z₁'_eq_of_mem ht, show ((-1 : ℂ) + I * t + 1) = I * t by ring, mul_pow, I_sq,
    show ((π : ℂ) * I * r * (-1 + I * t)) = -π * I * r + -π * r * t by
      linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- `I₁'` as an integral over `Ioc 0 1`. -/
public lemma I₁'_eq_Ioc (r : ℝ) : I₁' r = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
  simp [I₁'_eq, intervalIntegral_eq_integral_uIoc]

/-- Explicit integral expression for `I₂'`. -/
public lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1, φ₀'' (-1 / (t + I))
    * (t + I) ^ 2 * cexp (-π * I * r) * cexp (π * I * r * t) * cexp (-π * r) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₂, Φ₂', Φ₁', z₂'_eq_of_mem ht, show (-1 + (t : ℂ) + I + 1) = t + I from by ring,
    show ((π : ℂ) * I * r * (-1 + t + I)) = -π * I * r + π * I * r * t + -π * r by
      linear_combination ↑π * r * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- Explicit integral expression for `I₃'`. -/
public lemma I₃'_eq (r : ℝ) : I₃' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (π * I * r) * cexp (-π * r * t) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₃, Φ₃', z₃'_eq_of_mem ht, show (1 + I * (t : ℂ) - 1) = I * t from by ring, mul_pow,
    I_sq, show ((π : ℂ) * I * r * (1 + I * t)) = π * I * r + -π * r * t by
      linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- Explicit integral expression for `I₄'`. -/
public lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1, -1 * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2 * cexp (π * I * r) * cexp (-π * I * r * t) * cexp (-π * r) := by
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Φ₄, Φ₄', Φ₃', z₄'_eq_of_mem ht, show ((1 : ℂ) - t + I - 1) = -t + I from by ring,
    show ((π : ℂ) * I * r * (1 - t + I)) = π * I * r + -π * I * r * t + -π * r by
      linear_combination ↑π * r * (I_sq : (I : ℂ) ^ 2 = -1), Complex.exp_add]; ring

/-- Explicit integral expression for `I₅'`. -/
public lemma I₅'_eq (r : ℝ) : I₅' r = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * r * t) := by
  simp only [I₅', Φ₅, Φ₅']; congr 1
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [z₅'_eq_of_mem ht, mul_pow, I_sq, show ((π : ℂ) * I * r * (I * t)) = -π * r * t by
    linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1)]; ring

/-- `I₅'` as an integral over `Ioc 0 1`. -/
public lemma I₅'_eq_Ioc (r : ℝ) : I₅' r = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t)) * t ^ 2 * cexp (-π * r * t) := by
  simp [I₅'_eq, intervalIntegral_eq_integral_uIoc]

/-- Explicit integral expression for `I₆'`. -/
public lemma I₆'_eq (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t) * cexp (-π * r * t) := by
  simp only [I₆', Φ₆, Φ₆']; congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
  rw [z₆'_eq_of_mem ht, show ((π : ℂ) * I * r * (I * t)) = -π * r * t by
      linear_combination ↑π * r * t * (I_sq : (I : ℂ) ^ 2 = -1)]; ring

end MagicFunction.a.RadialFunctions

end

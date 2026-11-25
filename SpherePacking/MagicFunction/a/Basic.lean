/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.MagicFunction.a.Defs

import SpherePacking.ForMathlib.IntegralCongr
import SpherePacking.Tactic.ExpRing

/-!
# The Function `a`: explicit integral formulas

This file rewrites the integrals `Iⱼ'` defining Viazovska's function `a` (see
`SpherePacking.MagicFunction.a.Defs`) as explicit integrals in the real variable `t`.
-/

@[expose] public section

open Set Complex Real MagicFunction.Parametrisations MagicFunction.a.RealIntegrals intervalIntegral

namespace MagicFunction.a.RadialFunctions

section Eq

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  simp (disch := grind) only [I₁', Φ₁, Φ₁', z₁'_eq_of_mem]
  congr! 1 with t
  exp_ring

lemma I₁'_eq' (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  rw [I₁'_eq r, ← intervalIntegral.integral_const_mul]
  congr! 1 with t
  ring

lemma I₁'_eq_Ioc (r : ℝ) : I₁' r = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  rw [I₁'_eq, integral_of_le zero_le_one]

lemma I₁'_eq'_Ioc (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
      φ₀'' (-1 / (I * t))
      * t ^ 2
      * cexp (-π * I * r)
      * cexp (-π * r * t) := by
    simp [I₁'_eq', intervalIntegral_eq_integral_uIoc]

lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * r)
    * cexp (π * I * r * t)
    * cexp (-π * r) := by
  simp (disch := grind) only [I₂', Φ₂, Φ₂', z₂'_eq_of_mem]
  congr! 1 with t
  exp_ring

lemma I₃'_eq (r : ℝ) : I₃' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  simp (disch := grind) only [I₃', Φ₃, Φ₃', z₃'_eq_of_mem]
  congr! 1 with t
  exp_ring

lemma I₃'_eq' (r : ℝ) : I₃' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  rw [I₃'_eq r, ← intervalIntegral.integral_const_mul]
  congr! 1 with t
  ring

lemma I₃'_eq_Ioc (r : ℝ) : I₃' r = ∫ (t : ℝ) in Ioc 0 1, -I
  * φ₀'' (-1 / (I * t))
  * t ^ 2
  * cexp (π * I * r)
  * cexp (-π * r * t) := by
    rw [I₃'_eq, integral_of_le zero_le_one]

lemma I₃'_eq'_Ioc (r : ℝ) : I₃' r = -I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  rw [I₃'_eq', integral_of_le zero_le_one]

lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1, -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r) := by
  simp (disch := grind) only [I₄', Φ₄, Φ₄', z₄'_eq_of_mem]
  congr! 1 with t
  exp_ring

lemma I₅'_eq (r : ℝ) : I₅' r = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  simp (disch := grind) only [I₅', Φ₅, Φ₅', z₅'_eq_of_mem]
  congr! 2 with t
  exp_ring

lemma I₅'_eq' (r : ℝ) : I₅' r = 2 * I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq r, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  congr! 1 with t
  ring

lemma I₅'_eq_Ioc (r : ℝ) : I₅' r = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq, integral_of_le zero_le_one]

lemma I₅'_eq'_Ioc (r : ℝ) : I₅' r = 2 * I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq', integral_of_le zero_le_one]

lemma I₆'_eq (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t)
    * cexp (-π * r * t) := by
  simp (disch := grind) only [I₆', Φ₆, Φ₆', z₆'_eq_of_mem]
  congr! 2 with t
  exp_ring

lemma I₆'_eq' (r : ℝ) : I₆' r = 2 * I * ∫ t in Ici (1 : ℝ),
  φ₀'' (I * t)
  * cexp (-π * r * t) := by
  rw [I₆'_eq r, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  congr! 1 with t
  ring

end Eq

end MagicFunction.a.RadialFunctions

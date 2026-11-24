/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import SpherePacking.ForMathlib.IntegralCongr

/-!
# Tests for the `@[congr]` lemmas for integrals

These check that `simp` and `congr!` can use membership in the domain of integration when
rewriting an integrand.
-/

public section

open MeasureTheory Set

/-- A function that is only "nice" on the positive reals. -/
noncomputable def testFn (t : ℝ) : ℝ := if 0 < t then t else 37

theorem testFn_of_pos {t : ℝ} (ht : 0 < t) : testFn t = t := by simp [testFn, ht]

theorem testFn_of_mem_Ioc {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : testFn t = t := testFn_of_pos ht.1

/-! ### `simp` with a discharger: the membership hypothesis is in the local context -/

example : ∫ t in Ioc (0 : ℝ) 1, testFn t = ∫ t in Ioc (0 : ℝ) 1, t := by
  simp (disch := grind) only [testFn_of_pos]

example : ∫ t in Ioi (0 : ℝ), testFn t = ∫ t in Ioi (0 : ℝ), t := by
  simp (disch := grind) only [testFn_of_pos]

example : ∫ t in Ici (1 : ℝ), testFn t = ∫ t in Ici (1 : ℝ), t := by
  simp (disch := grind) only [testFn_of_pos]

example : ∫ t in Icc (1 : ℝ) 2, testFn t = ∫ t in Icc (1 : ℝ) 2, t := by
  simp (disch := grind) only [testFn_of_pos]

example : ∫ t in (0 : ℝ)..1, testFn t = ∫ t in (0 : ℝ)..1, t := by
  simp (disch := grind) only [testFn_of_pos]

-- The integral may sit anywhere inside the goal.
example : 2 * ∫ t in (0 : ℝ)..1, testFn t + 1 = 2 * ∫ t in (0 : ℝ)..1, t + 1 := by
  simp (disch := grind) only [testFn_of_pos]

-- With the bounds the other way around, `Set.uIoc 1 0` is still `Set.Ioc 0 1`.
example : ∫ t in (1 : ℝ)..0, testFn t = ∫ t in (1 : ℝ)..0, t := by
  simp (disch := grind) only [testFn_of_pos]

/-! ### `simp +contextual`: the membership hypothesis is a rewrite rule -/

example : ∫ t in Ioc (0 : ℝ) 1, testFn t = ∫ t in Ioc (0 : ℝ) 1, t := by
  simp +contextual only [testFn_of_mem_Ioc]

-- An arbitrary measurable set: the default discharger proves `MeasurableSet s`.
example (s : Set ℝ) (hs : MeasurableSet s) (h : ∀ t ∈ s, 0 < t) :
    ∫ t in s, testFn t = ∫ t in s, t := by
  simp +contextual only [testFn_of_pos, h, hs]

example (s : Set ℝ) (hs : MeasurableSet s) (h : ∀ t ∈ s, 0 < t) :
    ∫⁻ t in s, ENNReal.ofReal (testFn t) = ∫⁻ t in s, ENNReal.ofReal t := by
  simp +contextual only [testFn_of_pos, h, hs]

/-! ### `congr!` -/

example : ∫ t in Ioc (0 : ℝ) 1, testFn t = ∫ t in Ioc (0 : ℝ) 1, t := by
  congr! 1 with t ht
  exact testFn_of_mem_Ioc ht

example : -2 * ∫ t in Ici (1 : ℝ), testFn t = -2 * ∫ t in Ici (1 : ℝ), t := by
  congr! 2 with t ht
  exact testFn_of_pos (by grind)

example : ∫ t in (0 : ℝ)..1, testFn t = ∫ t in (0 : ℝ)..1, t := by
  congr! 1 with t ht
  exact testFn_of_pos (by grind)

/-! ### Nothing changes when there is no domain -/

example (f : ℝ → ℝ) : ∫ t, (f t + 0) = ∫ t, f t := by simp only [add_zero]
example (f : ℝ → ℝ) (s : Set ℝ) : ∫ t in s, (f t + 0) = ∫ t in s, f t := by simp only [add_zero]
example (f : ℝ → ℝ) (a b : ℝ) : ∫ t in a..b, (f t + 0) = ∫ t in a..b, f t := by
  simp only [add_zero]

/-! ### `Set.uIcc` and `grind` -/

example (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : t ∈ Icc (0 : ℝ) 1 := by grind
example (t : ℝ) (ht : t ∈ uIcc (1 : ℝ) 0) : 0 ≤ t := by grind

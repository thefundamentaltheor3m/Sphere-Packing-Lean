/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic

/-!
# Tests for the `Complex.re` / `Complex.im` positivity extensions
-/

@[expose] public section

open Complex
open UpperHalfPlane hiding I

section re

example {t : ℝ} (ht : 0 < t) : 0 < (t : ℂ).re := by positivity
example {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (t : ℂ).re := by positivity
example {t : ℝ} (ht : t ≠ 0) : (t : ℂ).re ≠ 0 := by positivity
example {t : ℝ} : 0 < ((t ^ 2 + 1 : ℝ) : ℂ).re := by positivity

end re

section im

-- The key goal shape: the membership proof of imaginary-axis points of ℍ
example {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ)).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < ((t : ℂ) * I).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 ≤ (I * (t : ℂ)).im := by positivity
example {t : ℝ} (ht : t ≠ 0) : (I * (t : ℂ)).im ≠ 0 := by positivity
example : 0 < I.im := by positivity
example {t : ℝ} : 0 ≤ ((t : ℂ)).im := by positivity

-- Recursion into the real factor
example {t : ℝ} (ht : 0 < t) : 0 < (I * ((1 / t : ℝ) : ℂ)).im := by positivity
example {t : ℝ} : 0 < (I * ((t ^ 2 + 1 : ℝ) : ℂ)).im := by positivity
example {t : ℝ} (ht : 1 ≤ t) : 0 < (I * ((t : ℝ) : ℂ)).im := by positivity

-- Coercions from the upper half-plane
example (z : ℍ) : 0 < ((z : ℂ)).im := by positivity

-- Constructing imaginary-axis points of ℍ with `positivity`
example {t : ℝ} (ht : 0 < t) : ((⟨I * t, by positivity⟩ : ℍ) : ℂ) = I * t := rfl
example {t : ℝ} (ht : 0 < t) : ((⟨I * (1 / t : ℝ), by positivity⟩ : ℍ) : ℂ) = I * (1 / t : ℝ) :=
  rfl

end im

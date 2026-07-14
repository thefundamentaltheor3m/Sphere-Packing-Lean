/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.ModularForms.ResToImagAxis

/-!
# Tests for the `res_simp` tactic
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex

variable {F : ℍ → ℂ} {t : ℝ}

-- Basic rewrite, on both spellings
example (ht : 0 < t) : F.resToImagAxis t = F ⟨I * t, by positivity⟩ := by res_simp
example (ht : 0 < t) : ResToImagAxis F t = F ⟨I * t, by positivity⟩ := by res_simp

-- The positivity hypothesis may be derivable rather than literal
example (ht : 1 ≤ t) : F.resToImagAxis t = F ⟨I * t, by positivity⟩ := by res_simp
example {t₀ : ℝ} (ht : 0 < t₀) : F.resToImagAxis (t₀ ^ 2 + 1) =
    F ⟨I * (t₀ ^ 2 + 1 : ℝ), by positivity⟩ := by res_simp

-- Extra simp lemmas ride along
example (ht : 0 < t) (c : ℝ) : ((fun _ => (c : ℂ)).resToImagAxis t).im = 0 := by
  res_simp [ofReal_im]

-- Rewriting at a hypothesis
example (ht : 0 < t) (h : F.resToImagAxis t = 0) : F ⟨I * t, by positivity⟩ = 0 := by
  res_simp at h
  exact h

-- The nonpositive branch
example (ht : t ≤ 0) : ResToImagAxis F t = 0 := ResToImagAxis_apply_of_nonpos ht

-- `res_simp` fails (rather than silently succeeding) when positivity of the
-- argument is not derivable
example (h : ResToImagAxis F t = 0) : ResToImagAxis F t = 0 := by
  fail_if_success res_simp
  exact h

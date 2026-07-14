/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.Summability
public import Mathlib.Analysis.Complex.Basic

/-!
# Tests for the `summability` tactic
-/

@[expose] public section

open Complex

section closure

variable {f g : ℕ → ℂ} (hf : Summable f) (hg : Summable g)

include hf hg in
example : Summable (fun n => f n + g n) := by summability

include hf in
example : Summable (fun n => -f n) := by summability

include hf hg in
example : Summable (fun n => f n - g n) := by summability

include hf in
example : Summable (fun n => (3 : ℂ) * f n) := by summability

include hf in
example : Summable (fun n => f n * (3 : ℂ)) := by summability

include hf in
example : Summable (fun n => f n / (2 : ℂ)) := by summability

include hf in
example (c : ℂ) : Summable (fun n => c • f n) := by summability

include hf hg in
example : Summable (fun n => (2 : ℂ) * f n - g n / 3) := by summability

end closure

section leaves

-- Geometric series and polynomial × geometric
example {r : ℂ} (hr : ‖r‖ < 1) : Summable (fun n : ℕ => r ^ n) := by summability
example {r : ℂ} (hr : ‖r‖ < 1) : Summable (fun n : ℕ => (n : ℂ) ^ 3 * r ^ n) := by summability
example {r : ℂ} (hr : ‖r‖ < 1) : Summable (fun n : ℕ => ‖(n : ℂ) ^ 2 * r ^ n‖) := by
  summability
example : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) := by
  summability (disch := norm_num [abs_of_pos])

-- q-expansion-shaped series with an abstract `q`
example {q : ℂ} (hq : ‖q‖ < 1) {a : ℕ → ℂ} (ha : Summable a) :
    Summable fun n => a n + (2 : ℂ) * ((n : ℂ) ^ 2 * q ^ n) := by summability

-- Finite index types
example (f : Fin 37 → ℂ) : Summable f := by summability

end leaves

section combined

example {r : ℂ} (hr : ‖r‖ < 1) {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n => f n + (n : ℂ) ^ 3 * r ^ n) := by summability

-- Bare `↑n * r ^ n` (no `^ k`) is out of `summability`'s reach (see the note in
-- `SpherePacking.Tactic.Summability`); use the specialized lemma directly
example {r : ℂ} (hr : ‖r‖ < 1) : Summable (fun n : ℕ => (n : ℂ) * r ^ n) :=
  summable_cast_mul_geometric_of_norm_lt_one hr

end combined

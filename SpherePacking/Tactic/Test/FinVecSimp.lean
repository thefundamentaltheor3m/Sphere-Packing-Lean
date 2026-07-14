/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.FinVecSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Real.Basic

/-!
# Tests for the `fin_vec_simp` tactic
-/

@[expose] public section

open Matrix

section literal

-- Matrix products of literals
example : !![1, 2; 3, 4] * !![(1 : ℚ), 0; 0, 1] = !![1, 2; 3, 4] := by fin_vec_simp
example : !![(0 : ℚ), 1; 1, 0] * !![0, 1; 1, 0] = 1 := by fin_vec_simp
example : !![(2 : ℚ)⁻¹, 0; 0, 2⁻¹] * !![2, 0; 0, 2] = 1 := by fin_vec_simp

-- Entry access
example : !![(1 : ℤ), 2; 3, 4] 1 0 = 3 := by fin_vec_simp
example : ![(5 : ℚ), 7] 1 = 7 := by fin_vec_simp

end literal

section vecMul

-- `vecMul` and `mulVec` against literals, including symbolic vectors
example : ![(1 : ℚ), 2] ᵥ* !![1, 0; 0, 1] = ![1, 2] := by fin_vec_simp
example (a b : ℚ) : ![a, b] ᵥ* !![0, 1; 1, 0] = ![b, a] := by fin_vec_simp
example (a b : ℚ) : !![0, 1; 1, 0] *ᵥ ![a, b] = ![b, a] := by fin_vec_simp

-- `dotProduct`
example (v : Fin 2 → ℚ) : v ⬝ᵥ ![1, 0] = v 0 := by fin_vec_simp
example (a b : ℚ) : ![a, b] ⬝ᵥ ![b, a] = 2 * (a * b) := by
  fin_vec_simp
  ring

end vecMul

section forall_sum

-- `∀ i : Fin n` and `∑ i : Fin n` over literals
example : ∀ i : Fin 3, ![(1 : ℚ), 1, 1] i = 1 := by fin_vec_simp
example : ∑ i : Fin 4, ![(1 : ℚ), 2, 3, 4] i = 10 := by fin_vec_simp

end forall_sum

section cast

-- The `E8Matrix_eq_cast` shape: entrywise equality after `Matrix.map`
example : !![(2 : ℚ), 1; 0, 2⁻¹].map (Rat.cast (K := ℝ)) = !![(2 : ℝ), 1; 0, 2⁻¹] := by
  fin_vec_simp

end cast

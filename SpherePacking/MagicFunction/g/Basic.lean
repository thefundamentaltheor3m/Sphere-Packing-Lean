/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.Schwartz
import SpherePacking.MagicFunction.b.Schwartz

/-! # Viazovska's Magic Function

In this file, we define Viazovska's magic funtction `g`.
-/

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions

/-- The Magic Function, `g`. -/
noncomputable def g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a + (I / (240 * π)) • b

-- Note that in the proof, we need `g` to be Real-valued. We need to decide how we want to state
-- this: either `g ∘ Complex.im = 0` or we actually construct an element of `𝓢(ℝ⁸, ℝ)`...

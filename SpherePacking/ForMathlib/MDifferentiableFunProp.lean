import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Tactic.FunProp

import SpherePacking.ModularForms.Eisenstein

open scoped Manifold UpperHalfPlane EisensteinSeries

/--
To be upstreamed in mathlib PR [#33830](https://github.com/leanprover-community/mathlib4/pull/33830)
-/
lemma MDifferentiable.pow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (n : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ^ n) := by
  induction n with
  | zero => exact fun _ => mdifferentiableAt_const
  | succ n ih => exact ih.mul hf

theorem E₄_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₄.toFun := E₄.holo'

theorem E₆_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₆.toFun := E₆.holo'

/-
Register `MDifferentiable` as a `fun_prop` so that we can use it in `fun_prop`-based proofs.
To be upstreamed in mathlib PR [#33808](https://github.com/leanprover-community/mathlib4/pull/33808)
-/
attribute [fun_prop] MDifferentiable

attribute [fun_prop]
  MDifferentiable.add
  MDifferentiable.sub
  MDifferentiable.neg
  MDifferentiable.mul
  MDifferentiable.pow
  MDifferentiable.const_smul
  mdifferentiable_const
  E₄_MDifferentiable
  E₆_MDifferentiable

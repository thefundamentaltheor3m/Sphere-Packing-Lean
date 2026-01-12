import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

import Mathlib.Tactic.FunProp

open scoped Manifold UpperHalfPlane

/--
To be upstreamed in mathlib PR [#33830](https://github.com/leanprover-community/mathlib4/pull/33830)
-/
lemma MDifferentiable.pow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (n : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ^ n) := by
  induction n with
  | zero => exact fun _ => mdifferentiableAt_const
  | succ n ih => exact ih.mul hf

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
  EisensteinSeries.eisensteinSeries_SIF_MDifferentiable

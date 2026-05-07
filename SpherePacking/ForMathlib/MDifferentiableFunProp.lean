module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.Tactic.FunProp

public import SpherePacking.ModularForms.Eisenstein

/-!
# `fun_prop` registrations for manifold-differentiable Eisenstein series

Wrap `E₄.holo'` / `E₆.holo'` / `Δ.holo'` as `MDifferentiable` lemmas so that `fun_prop` can
close goals of the form `MDiff (fun z => E₄ z * …)` automatically.

To be upstreamed in mathlib PR [#33808](https://github.com/leanprover-community/mathlib4/pull/33808).
-/

@[expose] public section

open scoped Manifold UpperHalfPlane EisensteinSeries

theorem E₄_MDifferentiable : MDiff E₄.toFun := E₄.holo'

theorem E₆_MDifferentiable : MDiff E₆.toFun := E₆.holo'

attribute [fun_prop] MDifferentiable MDifferentiable.add MDifferentiable.sub MDifferentiable.neg
  MDifferentiable.mul MDifferentiable.pow MDifferentiable.const_smul mdifferentiable_const
  E₄_MDifferentiable E₆_MDifferentiable

module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.Tactic.FunProp

public import SpherePacking.ModularForms.Eisenstein

@[expose] public section

open scoped Manifold UpperHalfPlane EisensteinSeries

theorem E₄_MDifferentiable : MDiff E₄.toFun := E₄.holo'

theorem E₆_MDifferentiable : MDiff E₆.toFun := E₆.holo'

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

-- Lambda forms of MDifferentiable lemmas: fun_prop needs these to match value-level operations
-- inside lambdas, since the base lemmas use function-level operators (Pi instances).
section MDifferentiableLambda

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F']

@[fun_prop]
theorem MDifferentiable.hMul {f g : M → F'}
    (hf : MDifferentiable I 𝓘(𝕜, F') f) (hg : MDifferentiable I 𝓘(𝕜, F') g) :
    MDifferentiable I 𝓘(𝕜, F') (fun x => f x * g x) := hf.mul hg

@[fun_prop]
theorem MDifferentiable.hPow {f : M → F'}
    (hf : MDifferentiable I 𝓘(𝕜, F') f) (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, F') (fun x => f x ^ n) := hf.pow n

end MDifferentiableLambda

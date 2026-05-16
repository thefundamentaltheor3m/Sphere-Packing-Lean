module
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Tactic.FunProp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# `fun_prop` extensions

Extends Mathlib's `fun_prop` lemma database with closure lemmas for `MDifferentiable`
(incl. a `pow` rule and a numeral leaf-rule), `Summable`, `HasSum`, and `Integrable`.
-/

open scoped Manifold

attribute [fun_prop] MDifferentiable mdifferentiable_id mdifferentiable_const MDifferentiable.comp
  MDifferentiable.add MDifferentiable.sub MDifferentiable.neg MDifferentiable.mul
  MDifferentiable.const_smul

section MDifferentiablePow

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedRing E'] [NormedAlgebra 𝕜 E']

/-- `fun_prop` leaf-rule: numerals (as constant functions) are `MDifferentiable`. Without this,
`fun_prop` can get stuck on goals like `MDifferentiable ... fun x => 3 x`, whose head symbol is
`OfNat.ofNat` (for the `OfNat (M → E') 3` instance). -/
public theorem mdifferentiable_ofNat (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, E') (OfNat.ofNat (α := M → E') n) :=
  mdifferentiable_const (c := (OfNat.ofNat (α := E') n))

attribute [fun_prop] mdifferentiable_ofNat MDifferentiable.pow

end MDifferentiablePow

attribute [fun_prop] Summable Summable.add Summable.sub Summable.neg Summable.const_smul
  Summable.smul_const Summable.mul_left Summable.mul_right

attribute [fun_prop] HasSum HasSum.add HasSum.sub HasSum.neg HasSum.const_smul HasSum.smul_const
  HasSum.mul_left HasSum.mul_right

attribute [fun_prop] MeasureTheory.Integrable MeasureTheory.Integrable.add
  MeasureTheory.Integrable.sub MeasureTheory.Integrable.neg MeasureTheory.Integrable.smul
  MeasureTheory.Integrable.smul_const MeasureTheory.Integrable.const_mul
  MeasureTheory.Integrable.mul_const MeasureTheory.Integrable.norm
  MeasureTheory.Integrable.comp_measurable

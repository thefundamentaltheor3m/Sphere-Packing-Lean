module
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.CohnElkies.LPBoundAux


/-!
# Summability lemmas for the LP bound

For a Schwartz function `f` on `ℝᵈ`, the restriction of `f` to any translate of a discrete
`ℤ`-lattice is absolutely summable, by Schwartz decay.

We use this to justify exchanging lattice `tsum`s with other operations in the Cohn-Elkies
argument.
-/

open scoped BigOperators
open scoped SchwartzMap

namespace SpherePacking.CohnElkies

variable {d : ℕ}

namespace LPBoundSummability

open SpherePacking.CohnElkies.LPBoundAux

section ZLattice

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))

/-- A Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate :
    Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) :=
  Summable.of_norm (summable_norm_comp_add_zlattice (Λ := Λ) f a)

/-- The real part of a Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate_re :
    Summable (fun ℓ : Λ => (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
  Complex.reCLM.summable (summable_lattice_translate (Λ := Λ) f a)

end SpherePacking.CohnElkies.LPBoundSummability.ZLattice

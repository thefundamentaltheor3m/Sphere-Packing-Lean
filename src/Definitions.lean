import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

variable (n : ℕ)
-- The following (copied from Mathlib/MeasureTheory/Integral/TorusIntegral.lean)
-- allows the local notation ℝⁿ = Fin n → ℝ
local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n → $t)

open Euclidean

namespace SpherePacking

/-
# We define a Sphere Packing as a 5-tuple consisting of
1. `centres`: A subset of ℝⁿ consisting of the centres of the spheres
2. `hcc`: The `h`ypothesis that the set of `c`entres is `c`ountable
3. `radius`: The (common) radius of each sphere in the packing
4. `hrad`: The hypothesis that `radius` is positive
5. `hpacking`: The hypothesis that no two spheres centred at points in `centres` with common
    radius `c` intersect---ie, that the spheres do, indeed, form a packing.
Remark. We define packings to be extensional: two packings are equal iff they have the same set of
centres and the same common radius.
-/

@[ext]
structure SpherePacking where
  centres : Set ℝⁿ
  hcc : Countable centres
  radius : ℝ
  hrad : radius > 0
  hpacking : ∀ p₁ p₂ : ℝⁿ, p₁ ∈ centres → p₂ ∈ centres → p₁ ≠ p₂ →
    Euclidean.dist p₁ p₂ > 2 * radius

#check SpherePacking.ext_iff

-- Below, we give a few examples of sphere packings.

def EgPacking2 : SpherePacking 2 where -- An example of a sphere packing in two dimensions
  centres := ∅
  hcc := Encodable.countable
  radius := 1
  hrad := by linarith
  hpacking := by
    intros p₁ p₂ hp₁ hp₂ hp₁p₂
    exfalso
    assumption

def EgPacking1 : SpherePacking 1 where -- An example of a sphere packing in one dimension
  centres := {2, 4, 6, 8, 10}
  hcc := Finite.to_countable
  radius := 1
  hrad := by linarith
  hpacking := sorry

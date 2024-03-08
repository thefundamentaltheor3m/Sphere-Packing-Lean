import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

-- variable (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (n : ℕ)
-- Below copied from Mathlib/MeasureTheory/Integral/TorusIntegral.lean
-- The following allows the local notation ℝⁿ = Fin n → ℝ
local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n → $t)

open Euclidean

namespace SpherePacking

-- The following definition is NOT good: it means we'd need to supply each of those ingredients
-- explicitly every time we want to move forward.

-- def SpherePacking {P : Set V} (hP : Countable P) {r : ℝ} (hr : r > 0)
--   (hPr : ∀ p₁ p₂ : V, p₁ ∈ P → p₂ ∈ P → p₁ ≠ p₂ → Euclidean.dist p₁ p₂ > 2 * r) : Set V :=
--   {y | ∃ p : V, p ∈ P ∧ y ∈ ball p r}

-- Maybe we will also get an idea once we do packing density...

@[ext]
structure SpherePacking where
  centres : Set ℝⁿ -- A subset of ℝⁿ
  hcc : Countable centres -- Hypothesis that there are countably many centres
  radius : ℝ -- The radius of each sphere in the packing
  hrad : radius > 0 -- Hypothesis that the common radius is positive
  -- Now, the hypothesis that the spheres form a valid packing
  hpacking : ∀ p₁ p₂ : ℝⁿ, p₁ ∈ centres → p₂ ∈ centres → p₁ ≠ p₂ → Euclidean.dist p₁ p₂ > 2 * radius

#check SpherePacking.ext_iff

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
  hpacking := sorry -- Annoying to prove...

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Sphere.Basic

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

open Euclidean

namespace SpherePacking

def SpherePacking {P : Set V} (hP : Countable P) {r : ℝ} (hr : r > 0)
  (hPr : ∀ p₁ p₂ : V, p₁ ∈ P → p₂ ∈ P → p₁ ≠ p₂ → Euclidean.dist p₁ p₂ > 2 * r) : Set V :=
  {y | ∃ p : V, p ∈ P ∧ y ∈ ball p r}

-- I will aim to check which of these is a better way of going about it.
-- Maybe we will also get an idea once we do packing density...

@[ext]
structure SpherePacking' where
  centres : Set V
  hcc : Countable centres -- Hypothesis that centres are countable
  radius : ℝ
  hrad : radius > 0 -- Hypothesis that the common radius is positive
  -- Now, the hypothesis that the spheres form a valid packing
  hpacking : ∀ p₁ p₂ : V, p₁ ∈ centres → p₂ ∈ centres → p₁ ≠ p₂ → Euclidean.dist p₁ p₂ > 2 * radius

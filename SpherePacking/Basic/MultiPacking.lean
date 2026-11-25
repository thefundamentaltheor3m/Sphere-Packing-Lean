/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.MetricSpace.IsometricSMul
public import SpherePacking.Basic.SpherePacking

/-!
# Multi-packings

A `MultiPacking S` packs isometric copies of a family of prototiles `prototile k` into a set
`S`, such that all the copies are pairwise disjoint (they need not cover `S`).

Every sphere packing
gives a multi-packing of the whole space with a single prototile, see
`SpherePacking.toMultiPacking`.
-/

@[expose] public section

open Metric

structure MultiPacking {X : Type*} [PseudoEMetricSpace X] /- or `[MeasureSpace X]` -/
    {κ : Type*} (S : Set X) where
  /-- The prototiles: the shapes whose isometric copies make up the packing. -/
  prototile : κ → Set X
  /-- For each `k`, the index type of the copies of `prototile k` in the packing. -/
  ι : κ → Type*
  /-- The isometric equivalences that represent the transformations of the base shape to
    their locations in the packing. -/
  embeddings k : (ι k) → (X ≃ᵢ X)
  /-- The images of the embeddings of the same shape are pairwise disjoint. -/
  disjoint₁ k : Pairwise fun i j ↦
    Disjoint (embeddings k i '' prototile k) (embeddings k j '' prototile k)
  /-- The images of the embeddings of different shapes are pairwise disjoint. -/
  disjoint₂ : Pairwise fun k l ↦
    ∀ i j, Disjoint (embeddings k i '' prototile k) (embeddings l j '' prototile l)
  /-- The images of the embeddings are all inside the larger set `S`. -/
  inside k i : embeddings k i '' prototile k ⊆ S

variable {d : ℕ}

/-- A sphere packing viewed as a `MultiPacking` of `Set.univ` with a single prototile, the open
ball of radius `SP.separation / 2` around the origin, translated to each of the centers. -/
noncomputable def SpherePacking.toMultiPacking (SP : SpherePacking d) :
    MultiPacking (κ := Unit) (Set.univ : Set (EuclideanSpace ℝ (Fin d))) where
  prototile _ := ball (0 : EuclideanSpace ℝ (Fin d)) (SP.separation / 2)
  ι _ := SP.centers
  embeddings _ x := IsometryEquiv.addLeft (x : EuclideanSpace ℝ (Fin d))
  disjoint₁ _ x y hxy := by
    beta_reduce
    simp_rw [IsometryEquiv.image_ball, IsometryEquiv.addLeft_apply, add_zero]
    apply ball_disjoint_ball
    rw [add_halves]
    exact SP.centers_dist hxy
  disjoint₂ k l hkl := (hkl (Subsingleton.elim k l)).elim
  inside _ _ := Set.subset_univ _

namespace SpherePacking

variable (SP : SpherePacking d)

@[simp]
theorem toMultiPacking_prototile (k : Unit) :
    SP.toMultiPacking.prototile k = ball 0 (SP.separation / 2) := rfl

@[simp]
theorem toMultiPacking_ι (k : Unit) : SP.toMultiPacking.ι k = SP.centers := rfl

@[simp]
theorem toMultiPacking_embeddings_apply (k : Unit) (x : SP.centers)
    (y : EuclideanSpace ℝ (Fin d)) :
    SP.toMultiPacking.embeddings k x y = (x : EuclideanSpace ℝ (Fin d)) + y := rfl

/-- The image of the prototile under the embedding indexed by a center `x` is the ball around
`x`. -/
theorem toMultiPacking_image (k : Unit) (x : SP.centers) :
    SP.toMultiPacking.embeddings k x '' SP.toMultiPacking.prototile k =
      ball (x : EuclideanSpace ℝ (Fin d)) (SP.separation / 2) := by
  simp [IsometryEquiv.image_ball]

/-- The union of all the pieces of `SP.toMultiPacking` is `SP.balls`. -/
theorem iUnion_toMultiPacking_image :
    ⋃ (k : Unit) (x : SP.centers),
      SP.toMultiPacking.embeddings k x '' SP.toMultiPacking.prototile k = SP.balls := by
  simp only [toMultiPacking_image, Set.iUnion_const]

end SpherePacking

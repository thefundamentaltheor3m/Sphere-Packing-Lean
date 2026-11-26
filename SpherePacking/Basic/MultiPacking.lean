/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Combinatorics.Tiling.Tile
public import SpherePacking.Basic.SpherePacking

/-!
# Multi-packings

Given an action of a group `G` on `X` and a protoset `ps : Protoset G X ι` of prototiles, a
`MultiPacking ps S` is a set of placed copies of the prototiles inside a set `S`, such that the
copies have pairwise disjoint interiors (they need not cover `S`). As usual for packings of convex
bodies, copies are allowed to touch along their boundaries, e.g. closed pentagons sharing an edge.

Prototiles and placed tiles are those of mathlib's tiling theory, `DiscreteTiling.Protoset` and
`DiscreteTiling.PlacedTile`, which make sense for any group action. A placed tile is an index `i`
with a coset `g • symmetries` of the chosen symmetry subgroup of the prototile `ps i`, standing for
the set `g • ps i`. Taking the whole stabiliser as the symmetries (as `Protoset.single` does)
identifies copies that are equal as sets, while `⊥` keeps the copies by different `g` distinct.
Distinct placed tiles that are equal as sets cannot both be in a packing unless that set has empty
interior, so prototiles are expected to have nonempty interior.

As for `PlacedTile ps`, the protoset is a parameter, so the type of a packing records its shapes. To
range over packings by all families of shapes, quantify over `ι` and `ps`.

Two multi-packings, possibly with different protosets, are `MultiPacking.Congruent` when a single
`g : G` moves all the tiles of one onto the tiles of the other, i.e. one is the other moved as a
whole (`MultiPacking.move`).
-/

@[expose] public section

open DiscreteTiling
open scoped Pointwise

variable {G X ι ι₁ ι₂ ι₃ : Type*} [Group G] [MulAction G X]

namespace DiscreteTiling.Protoset

variable (G) in
/-- The protoset with the single prototile `K`, all of whose stabiliser counts as symmetries, so
that copies of `K` which are equal as sets are the same placed tile. -/
def single (K : Set X) : Protoset G X Unit :=
  ⟨fun _ ↦ ⟨K, ⊤⟩⟩

@[simp]
lemma coe_single (K : Set X) (i : Unit) : (single G K i : Set X) = K :=
  rfl

@[simp]
lemma coe_single_mk (K : Set X) (g : G) : ((⟨(), g⟩ : PlacedTile (single G K)) : Set X) = g • K :=
  rfl

end DiscreteTiling.Protoset

variable [TopologicalSpace X]

/-- A packing of copies of the prototiles of `ps` into `S`: the placed tiles have pairwise disjoint
interiors, so they may touch along their boundaries. -/
structure MultiPacking (ps : Protoset G X ι) (S : Set X) where
  /-- The placed tiles, i.e. the copies of prototiles in the packing. -/
  placed : Set (PlacedTile ps)
  /-- Distinct placed tiles have disjoint interiors. -/
  disjoint : placed.PairwiseDisjoint fun pt ↦ interior (pt : Set X)
  /-- Every placed tile lies inside `S`. -/
  subset : ∀ pt ∈ placed, (pt : Set X) ⊆ S

namespace MultiPacking

variable {ps : Protoset G X ι} {ps₁ : Protoset G X ι₁} {ps₂ : Protoset G X ι₂}
  {ps₃ : Protoset G X ι₃} {S S₁ S₂ S₃ : Set X}

/-- The tiles of `M`: its placed tiles, as subsets of `X`. -/
def tiles (M : MultiPacking ps S) : Set (Set X) :=
  (↑) '' M.placed

/-! ### Congruence -/

/-- `M₁` and `M₂` are congruent if moving all of `M₁` by a single `g : G` gives `M₂`, i.e. `g`
carries the tiles of `M₁` onto the tiles of `M₂`. Only the tiles are compared, not the protosets,
nor the ambient sets `S₁` and `S₂`. -/
def Congruent (M₁ : MultiPacking ps₁ S₁) (M₂ : MultiPacking ps₂ S₂) : Prop :=
  ∃ g : G, g • M₁.tiles = M₂.tiles

@[refl]
theorem Congruent.refl (M : MultiPacking ps S) : M.Congruent M :=
  ⟨1, one_smul _ _⟩

theorem Congruent.rfl {M : MultiPacking ps S} : M.Congruent M :=
  .refl M

@[symm]
theorem Congruent.symm {M₁ : MultiPacking ps₁ S₁} {M₂ : MultiPacking ps₂ S₂} :
    M₁.Congruent M₂ → M₂.Congruent M₁
  | ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

theorem congruent_comm {M₁ : MultiPacking ps₁ S₁} {M₂ : MultiPacking ps₂ S₂} :
    M₁.Congruent M₂ ↔ M₂.Congruent M₁ :=
  ⟨.symm, .symm⟩

@[trans]
theorem Congruent.trans {M₁ : MultiPacking ps₁ S₁} {M₂ : MultiPacking ps₂ S₂}
    {M₃ : MultiPacking ps₃ S₃} : M₁.Congruent M₂ → M₂.Congruent M₃ → M₁.Congruent M₃
  | ⟨g, hg⟩, ⟨g', hg'⟩ => ⟨g' * g, by rw [mul_smul, hg, hg']⟩

theorem congruent_equivalence :
    Equivalence (Congruent : MultiPacking ps S → MultiPacking ps S → Prop) :=
  ⟨.refl, .symm, .trans⟩

/-! ### Moving a packing -/

variable [ContinuousConstSMul G X]

/-- Move the whole packing `M` by `g`, using the action of `G` on placed tiles: a packing of `S`
becomes a packing of `g • S`. -/
@[simps]
def move (M : MultiPacking ps S) (g : G) : MultiPacking ps (g • S) where
  placed := g • M.placed
  disjoint := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := by rintro rfl; exact hne rfl
    simpa only [Function.onFun, PlacedTile.coe_smul, interior_smul, Set.disjoint_smul_set] using
      M.disjoint hp hq hpq
  subset := by
    rintro _ ⟨p, hp, rfl⟩
    rw [PlacedTile.coe_smul]
    exact Set.smul_set_mono (M.subset p hp)

@[simp]
theorem tiles_move (M : MultiPacking ps S) (g : G) : (M.move g).tiles = g • M.tiles := by
  simp only [tiles, move_placed, ← Set.image_smul, Set.image_image, PlacedTile.coe_smul]

theorem congruent_move (M : MultiPacking ps S) (g : G) : M.Congruent (M.move g) :=
  ⟨g, (tiles_move M g).symm⟩

/-- Two multi-packings are congruent iff one has the same tiles as a moved copy of the other. -/
theorem congruent_iff_exists_tiles_move {M₁ : MultiPacking ps₁ S₁} {M₂ : MultiPacking ps₂ S₂} :
    M₁.Congruent M₂ ↔ ∃ g : G, (M₁.move g).tiles = M₂.tiles := by
  simp [Congruent]

end MultiPacking

/-! ### Rigid motions

To pack rotated (and reflected) copies of a shape we take `G` to be the group `P ≃ᵃⁱ[𝕜] P` of
affine isometric equivalences, acting on `P` by evaluation. -/

/-- Affine isometric equivalences of `P` act on `P` by evaluation. -/
instance AffineIsometryEquiv.applyMulAction {𝕜 V P : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P] :
    MulAction (P ≃ᵃⁱ[𝕜] P) P where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance AffineIsometryEquiv.continuousConstSMul {𝕜 V P : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P] :
    ContinuousConstSMul (P ≃ᵃⁱ[𝕜] P) P :=
  ⟨fun g ↦ g.continuous⟩

@[simp]
lemma AffineIsometryEquiv.smul_def {𝕜 V P : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
    (g : P ≃ᵃⁱ[𝕜] P) (x : P) : g • x = g x :=
  rfl

/-! ### Example: a sphere packing as a multi-packing -/

namespace SpherePacking

variable {d : ℕ}

/-- A sphere packing gives a multi-packing of the whole space by translates of the single prototile
`closedBall 0 (separation / 2)`, one centred at each centre. Balls whose centres are exactly
`separation` apart touch. -/
noncomputable def toMultiPacking (P : SpherePacking d) :
    MultiPacking (Protoset.single (Multiplicative (EuclideanSpace ℝ (Fin d)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (P.separation / 2))) Set.univ where
  placed := (fun x : EuclideanSpace ℝ (Fin d) ↦ ⟨(), ↑(Multiplicative.ofAdd x)⟩) '' P.centers
  disjoint := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have hxy : x ≠ y := by rintro rfl; exact hne rfl
    have hr : P.separation / 2 ≠ 0 := by linarith [P.separation_pos]
    simp only [Function.onFun, Protoset.coe_single_mk, ofAdd_smul, vadd_closedBall_zero,
      interior_closedBall _ hr]
    exact Metric.ball_disjoint_ball (by linarith [P.centers_dist' x y hx hy hxy])
  subset _ _ := Set.subset_univ _

/-- The rigid motion `z ↦ x + ρ z`: rotate (or reflect) about the origin by `ρ`, then translate
the origin to `x`. -/
noncomputable def motion (ρ : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  AffineIsometryEquiv.constVAdd ℝ _ x * ρ.toAffineIsometryEquiv

@[simp]
lemma motion_apply (ρ : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x z : EuclideanSpace ℝ (Fin d)) : motion ρ x z = x + ρ z :=
  rfl

/-- If `K` lies in `closedBall 0 r` and the centres of a sphere packing are at least `2 * r`
apart, then placing a copy of `K` at each centre `x`, rotated by its own `ρ x`, gives a packing of
congruent copies of `K`. -/
noncomputable def toCongruentMultiPacking (P : SpherePacking d)
    {K : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} (hK : K ⊆ Metric.closedBall 0 r) (hr₀ : 0 < r)
    (hr : 2 * r ≤ P.separation)
    (ρ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    MultiPacking (Protoset.single (EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) K)
      Set.univ where
  placed := (fun x : EuclideanSpace ℝ (Fin d) ↦ ⟨(), ↑(motion (ρ x) x)⟩) '' P.centers
  disjoint := by
    have hsub (x) : interior (motion (ρ x) x • K) ⊆ Metric.ball x r := by
      rw [← interior_closedBall x hr₀.ne']
      refine interior_mono ?_
      rintro _ ⟨z, hz, rfl⟩
      simpa [dist_eq_norm] using hK hz
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have hxy : x ≠ y := by rintro rfl; exact hne rfl
    exact (Metric.ball_disjoint_ball
      (by linarith [P.centers_dist' x y hx hy hxy])).mono (hsub x) (hsub y)
  subset _ _ := Set.subset_univ _

end SpherePacking

/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib

/-! # The scaled integer lattice `L • ℤ^d` and its coordinate cube

For `d : ℕ` and `L : ℝ`, this file packages:

* `coordCube d L = [0, L)^d` and the closed inner cube `coordCubeInner d L r = [r, L-r]^d` in
  `EuclideanSpace ℝ (Fin d)`, with their membership API;
* the scaled standard basis `cubeBasis d L hL` and the cubic lattice `cubeLattice d L hL = L • ℤ^d`
  it spans, with `DiscreteTopology`/`IsZLattice` instances;
* the basic geometry and measure of these objects: `coordCube` is the fundamental domain of
  `cubeBasis` (`fundamentalDomain_cubeBasis_eq_coordCube`), every point has a unique lattice
  translate in it (`coordCube_unique_covers`), it is bounded, and the volumes are `L^d` and
  `(L - 2r)^d`. Only finitely many lattice points lie in a ball (`finite_lattice_in_ball`).

Everything is placed in the `EuclideanSpace` namespace, its natural home.

Upstream target: `Mathlib/Algebra/Module/ZLattice/` (scaled integer lattice) together with the
measure-theoretic facts. Imports here are left as `public import Mathlib`; they are narrowed at
upstreaming time.
-/

open MeasureTheory Metric ZSpan Module Bornology

namespace EuclideanSpace

variable {d : ℕ}

/-- The half-open coordinate cube `[0, L)^d`. Used pervasively as the fundamental domain of
`cubeLattice`; its membership API is `mem_coordCube`. -/
@[expose] public def coordCube (d : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}

@[simp] public lemma mem_coordCube {L : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ coordCube d L ↔ ∀ i, x i ∈ Set.Ico (0 : ℝ) L := Iff.rfl

/-- The closed inner cube `[r, L-r]^d`, the locus where a radius-`r` ball stays inside
`coordCube L`. Membership API: `mem_coordCubeInner`. -/
@[expose] public def coordCubeInner (d : ℕ) (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}

@[simp] public lemma mem_coordCubeInner {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ coordCubeInner d L r ↔ ∀ i, x i ∈ Set.Icc r (L - r) := Iff.rfl

/-- The standard basis of `EuclideanSpace ℝ (Fin d)` scaled by `L`; its span is `cubeLattice` and
its fundamental domain is `coordCube d L` (`fundamentalDomain_cubeBasis_eq_coordCube`). -/
@[expose] public noncomputable def cubeBasis (d : ℕ) (L : ℝ) (hL : 0 < L) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.isUnitSMul fun _ : Fin d ↦ IsUnit.mk0 L hL.ne'

/-- The cubic lattice `L • ℤ^d`, spanned by `cubeBasis d L hL`. Standalone so it can carry
`ZLattice`/`DiscreteTopology` instances and act as the period lattice of the cube packing. -/
@[expose] public noncomputable def cubeLattice (d : ℕ) (L : ℝ) (hL : 0 < L) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (cubeBasis d L hL))

public instance instDiscreteTopology_cubeLattice (L : ℝ) (hL : 0 < L) :
    DiscreteTopology (cubeLattice d L hL) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (cubeBasis d L hL))))

public instance instIsZLattice_cubeLattice (L : ℝ) (hL : 0 < L) :
    IsZLattice ℝ (cubeLattice d L hL) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (cubeBasis d L hL))))

/-- The fundamental domain of the scaled basis `cubeBasis d L hL` is the cube `[0, L)^d`. -/
public lemma fundamentalDomain_cubeBasis_eq_coordCube (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (cubeBasis d L hL) = coordCube d L := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, coordCube, cubeBasis, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, smul_eq_mul,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, Set.mem_setOf_eq,
    Set.mem_Ico]
  exact forall_congr' fun i =>
    and_congr (mul_nonneg_iff_of_pos_left (inv_pos.2 hL)) (inv_mul_lt_one₀ hL)

/-- Every point has a unique `cubeLattice` translate lying in the cube `coordCube d L`. -/
public lemma coordCube_unique_covers (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : cubeLattice d L hL, g +ᵥ x ∈ coordCube d L := fun x => by
  simpa [cubeLattice, fundamentalDomain_cubeBasis_eq_coordCube L hL] using
    exist_unique_vadd_mem_fundamentalDomain (cubeBasis d L hL) x

/-- The cube `coordCube d L` is a bounded set. -/
public lemma isBounded_coordCube (L : ℝ) (hL : 0 < L) : IsBounded (coordCube d L) := by
  simpa [fundamentalDomain_cubeBasis_eq_coordCube L hL] using
    fundamentalDomain_isBounded (cubeBasis d L hL)

private lemma volume_preimage_ofLp (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s :=
  (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hs.nullMeasurableSet

/-- The volume of the cube `[0, L)^d` is `L ^ d`. -/
public lemma volume_coordCube (L : ℝ) : volume (coordCube d L) = (ENNReal.ofReal L) ^ d := by
  have hcube : coordCube d L = (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
      (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    ext x; simp [mem_coordCube, Set.mem_pi]
  rw [hcube, volume_preimage_ofLp _ (.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico),
    volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico, sub_zero]

/-- `coordCubeInner d L r` is the `ofLp`-preimage of the product set `[r, L - r]^d`. -/
public lemma coordCubeInner_eq_preimage_ofLp (L r : ℝ) :
    coordCubeInner d L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x; simp [mem_coordCubeInner, Pi.le_def, forall_and]

/-- The volume of the closed inner cube `[r, L - r]^d` is `(L - 2r) ^ d`. -/
public lemma volume_coordCubeInner (L r : ℝ) :
    volume (coordCubeInner d L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  rw [coordCubeInner_eq_preimage_ofLp, volume_preimage_ofLp _
    (.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc), volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, show L - r - r = L - 2 * r by ring]

/-- Only finitely many `cubeLattice` points lie in a ball of radius `R`. -/
public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice d L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine (Set.Finite.preimage_embedding (f := ⟨fun g : cubeLattice d L hL =>
    (g : EuclideanSpace ℝ (Fin d)), Subtype.val_injective⟩) (by
      simpa [cubeLattice] using ZSpan.setFinite_inter (b := cubeBasis d L hL)
        (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)).subset fun g hg => ?_
  exact ⟨hg, g.property⟩

end EuclideanSpace

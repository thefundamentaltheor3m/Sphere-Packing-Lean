/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The scaled integer lattice `L • ℤ^d` and its coordinate boxes

For `d : ℕ` and `L : ℝ`, this file packages:

* the coordinate box `cubeBox d I = {x | ∀ i, x i ∈ I}` in `EuclideanSpace ℝ (Fin d)`. This is a
  reducible `abbrev`, not a standalone definition: membership is definitionally `∀ i, x i ∈ I`
  (`hx i` and `fun i => …` work with no unfolding lemma), so it behaves like notation for the
  set-builder while keeping call sites readable. Its real API is the cross-structure content:
  `cubeBox_eq_preimage_ofLp`, `measurableSet_cubeBox`, and `volume_cubeBox`
  (`volume (cubeBox d I) = volume I ^ d`). The cubes of the LP bound are written inline as
  `cubeBox d (Set.Ico 0 L) = [0, L)^d` and `cubeBox d (Set.Icc r (L - r)) = [r, L-r]^d` — there are
  deliberately no named specialisations (and hence no per-cube API to maintain);
* the scaled standard basis `cubeBasis d L hL` (also a reducible `abbrev`) and the cubic lattice
  `cubeLattice d L hL = L • ℤ^d` it spans, with `DiscreteTopology`/`IsZLattice` instances.
  `cubeLattice` is the one standalone definition, kept so it can carry those instances;
* the basic geometry: `cubeBox d (Set.Ico 0 L)` is the fundamental domain of `cubeBasis`
  (`fundamentalDomain_cubeBasis`), every point has a unique lattice translate in it
  (`cubeLattice_unique_covers`), it is bounded (`isBounded_cubeBox_Ico`), and only finitely many
  lattice points lie in a ball (`finite_lattice_in_ball`).

Everything is placed in the `EuclideanSpace` namespace, its natural home.

## Why a cube, and not an arbitrary lattice basis?

The cube `L • ℤ^d` enters the Cohn–Elkies density argument (`LPBound.lean`) only through its
*boundary geometry*. The lattice/fundamental-domain *counting* layer is already basis-generic and
delegates to Mathlib's `ZSpan`: a translate of a fundamental domain is again a fundamental domain
(`vadd_unique_covers`), the cell-assignment map exists for any basis
(`fundamentalDomainCover`), the domain is bounded (`ZSpan.fundamentalDomain_isBounded`), meets a
ball finitely (`ZSpan.setFinite_inter`), tiles space
(`ZSpan.exist_unique_vadd_mem_fundamentalDomain`), and has covolume `volume (fundamentalDomain b)`
(`ZLattice.covolume_eq_measure_fundamentalDomain`).

What genuinely needs the cube — and is *not* available for a general `ZSpan.fundamentalDomain b` —
is the boundary control of the LP bound, which rests on two facts with no current Mathlib analogue:

* an **inradius / boundary-safe inner core**: a ball of radius `r` about a point of the inner cube
  `cubeBox d (Set.Icc r (L - r))` stays inside `cubeBox d (Set.Ico 0 L)`
  (`ball_subset_cubeBox_of_mem_inner`). For a sheared parallelepiped the safe inner region is not a
  coordinate-box shrink; it depends on the dual-basis norms / the parallelepiped inradius.
  *Upstream TODO:* `ZSpan.ball_subset_fundamentalDomain_of_mem_inner`.
* a **boundary-shell volume asymptotic** under homothety: the relative volume of the
  `r`-neighbourhood of the cell boundary vanishes as the lattice is scaled (here the explicit
  `((L+1)^d - (L-2)^d)/L^d → 0`, `tendsto_volume_cubeShell_div_volume_cubeBox_zero`). For a general
  fundamental domain this is a Minkowski-content statement.  *Upstream TODO:*
  `ZSpan.tendsto_volume_boundaryThickening_div_volume_fundamentalDomain_zero`.

So the answer to "why so much for `L • ℤ^d`?" is: the counting is generic (and is written that
way), while the cube is the one fundamental domain whose inradius and boundary-shell volume are
elementary.

Upstream target: `Mathlib/Algebra/Module/ZLattice/` (scaled integer lattice) together with the
measure-theoretic facts and the two general boundary lemmas above. Imports here are left as
`public import Mathlib`; they are narrowed at upstreaming time.
-/

open MeasureTheory Metric ZSpan Module Bornology

namespace EuclideanSpace

variable {d : ℕ}

/-- The coordinate box `{x | ∀ i, x i ∈ I}` in `EuclideanSpace ℝ (Fin d)`: the points all of whose
coordinates lie in `I ⊆ ℝ`. A reducible `abbrev`, so membership is definitionally `∀ i, x i ∈ I`
and no membership/unfolding API is needed; the substantive API is `cubeBox_eq_preimage_ofLp`,
`measurableSet_cubeBox`, and `volume_cubeBox`. -/
@[expose] public abbrev cubeBox (d : ℕ) (I : Set ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ I}

/-- The standard basis of `EuclideanSpace ℝ (Fin d)` scaled by `L`; its span is `cubeLattice` and
its fundamental domain is `cubeBox d (Set.Ico 0 L)` (`fundamentalDomain_cubeBasis`).

This is a reducible *abbreviation*, not a standalone definition: it is a one-line shorthand for
`Basis.isUnitSMul`, carries no API of its own, and is only ever passed straight to Mathlib's `ZSpan`
basis lemmas. Keeping it `abbrev` (rather than `def`) means it unfolds definitionally — no unfolding
lemmas, no `cubeBasis_apply`-style API — so it behaves like notation while still accepting the
positivity proof `hL` that a syntactic `notation` could not supply to `IsUnit.mk0`. -/
@[expose] public noncomputable abbrev cubeBasis (d : ℕ) (L : ℝ) (hL : 0 < L) :
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
public lemma fundamentalDomain_cubeBasis (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (cubeBasis d L hL) = cubeBox d (Set.Ico 0 L) := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, cubeBasis, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, smul_eq_mul,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, Set.mem_setOf_eq,
    Set.mem_Ico]
  exact forall_congr' fun i =>
    and_congr (mul_nonneg_iff_of_pos_left (inv_pos.2 hL)) (inv_mul_lt_one₀ hL)

/-- Every point has a unique `cubeLattice` translate lying in the cube `[0, L)^d`. -/
public lemma cubeLattice_unique_covers (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : cubeLattice d L hL, g +ᵥ x ∈ cubeBox d (Set.Ico 0 L) := fun x => by
  simpa [cubeLattice, fundamentalDomain_cubeBasis L hL] using
    exist_unique_vadd_mem_fundamentalDomain (cubeBasis d L hL) x

/-- The cube `[0, L)^d` is a bounded set. -/
public lemma isBounded_cubeBox_Ico (L : ℝ) (hL : 0 < L) :
    IsBounded (cubeBox d (Set.Ico 0 L)) := by
  simpa [fundamentalDomain_cubeBasis L hL] using
    fundamentalDomain_isBounded (cubeBasis d L hL)

/-- A coordinate box is the `ofLp`-preimage of the product box `∏ i, I`. This is the single
preimage identity from which the boxes' measurability and volume are read off. -/
public lemma cubeBox_eq_preimage_ofLp (I : Set ℝ) :
    cubeBox d I =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' (Set.pi Set.univ fun _ : Fin d ↦ I) := by
  ext x; simp [Set.mem_pi]

/-- A coordinate box over a measurable interval is measurable. -/
public lemma measurableSet_cubeBox {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet (cubeBox d I) := by
  rw [cubeBox_eq_preimage_ofLp]
  exact (MeasurableSet.pi Set.countable_univ fun _ _ => hI).preimage
    (PiLp.volume_preserving_ofLp (ι := Fin d)).measurable

/-- The volume of a coordinate box `cubeBox d I` is `volume I ^ d`. -/
public lemma volume_cubeBox (I : Set ℝ) (hI : MeasurableSet I) :
    volume (cubeBox d I) = volume I ^ d := by
  rw [cubeBox_eq_preimage_ofLp,
    (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage
      (MeasurableSet.pi Set.countable_univ fun _ _ ↦ hI).nullMeasurableSet,
    volume_pi, Measure.pi_pi]
  simp

/-- Only finitely many `cubeLattice` points lie in a ball of radius `R`. -/
public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice d L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine (Set.Finite.preimage_embedding (f := ⟨fun g : cubeLattice d L hL =>
    (g : EuclideanSpace ℝ (Fin d)), Subtype.val_injective⟩) (by
      simpa [cubeLattice] using ZSpan.setFinite_inter (b := cubeBasis d L hL)
        (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)).subset fun g hg => ?_
  exact ⟨hg, g.property⟩

end EuclideanSpace

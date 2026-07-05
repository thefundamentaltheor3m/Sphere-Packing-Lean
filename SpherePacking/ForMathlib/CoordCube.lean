/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The scaled integer lattice `L • ℤ^d` and its coordinate cubes

For `d : ℕ` and `L : ℝ`, this file packages:

* the measure theory of coordinate cubes `{x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ I}`.
  There is deliberately **no definition** for this set: the set-builder is written inline
  (membership is judgementally `∀ i, x i ∈ I`, so no membership or unfolding API exists at all).
  The lemmas record the genuine content: such a cube is the `ofLp`-preimage of a product box
  (`cube_eq_preimage_ofLp`), is measurable (`measurableSet_cube`), and has volume `volume I ^ d`
  (`volume_cube`, with endpoint corollaries `volume_cube_Ico`/`volume_cube_Icc`);
* the basic geometry of the scaled standard lattice: `[0, L)^d` is the fundamental domain of the
  scaled standard basis (`fundamentalDomain_cubeBasis`), every point has a unique lattice
  translate in it (`cubeLattice_unique_covers`), it is bounded (`isBounded_cube_Ico`), and only
  finitely many lattice points lie in a ball (`finite_lattice_in_ball`).

This file contains **no definitions at all** — only lemmas. The scaled standard basis and the
cubic lattice `L • ℤ^d` it spans are *notation* (`cubeBasis d L hL`, `cubeLattice d L hL`),
expanding literally to `Basis.isUnitSMul` on the standard basis and to
`Submodule.span ℤ (Set.range …)` of it. Consequently:

* there is no API and nothing to unfold — Mathlib's `ZSpan`/`ZLattice` lemmas apply directly to
  the expansions, and the `DiscreteTopology`/`IsZLattice` instances are found by Mathlib's own
  instance synthesis on the span spelling (no local instances needed);
* the notations are declared `local`ly here and re-declared at their point of use in
  `LPBound.lean`, following this project's existing pattern for cross-file notation (cf. `ℝ⁸`).
  Exported lemma *types* contain only the expanded Mathlib terms.

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
  `[r, L-r]^d` stays inside `[0, L)^d` (`ball_subset_cube_of_mem_inner` in `LPBound.lean`). For a
  sheared parallelepiped the safe inner region is not a coordinate-box shrink; it depends on the
  dual-basis norms / the parallelepiped inradius.
  *Upstream TODO:* `ZSpan.ball_subset_fundamentalDomain_of_mem_inner`.
* a **boundary-shell volume asymptotic** under homothety: the relative volume of the
  `r`-neighbourhood of the cell boundary vanishes as the lattice is scaled (here the explicit
  `((L+1)^d - (L-2)^d)/L^d → 0`, `tendsto_volume_cubeShell_div_volume_cube_zero` in
  `LPBound.lean`). For a general fundamental domain this is a Minkowski-content statement.
  *Upstream TODO:* `ZSpan.tendsto_volume_boundaryThickening_div_volume_fundamentalDomain_zero`.

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

/-- The standard basis of `EuclideanSpace ℝ (Fin d)` scaled by `L`, given `hL : 0 < L`. This is
*notation*, not a definition: it elaborates literally to `Basis.isUnitSMul` on the standard basis,
so Mathlib's `ZSpan` lemmas apply to it directly and there is nothing to unfold. (The right-hand
side is written projection-free because the notation precheck does not support `.foo` syntax.) -/
local notation:max "cubeBasis " d:max L:max hL:max =>
  Module.Basis.isUnitSMul (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin d) ℝ))
    fun _ : Fin d ↦ IsUnit.mk0 L (LT.lt.ne' hL)

/-- The cubic lattice `L • ℤ^d`, the span of `cubeBasis d L hL`. This is *notation*, not a
definition: it elaborates literally to `Submodule.span ℤ (Set.range …)`, so Mathlib's
`DiscreteTopology`/`IsZLattice` instances for spans of basis ranges apply to it directly. -/
local notation:max "cubeLattice " d:max L:max hL:max =>
  Submodule.span ℤ (Set.range (cubeBasis d L hL))

/-- The fundamental domain of the scaled standard basis is the cube `[0, L)^d`. -/
public lemma fundamentalDomain_cubeBasis (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (cubeBasis d L hL) =
      {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Ico 0 L} := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, smul_eq_mul,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, Set.mem_setOf_eq,
    Set.mem_Ico]
  exact forall_congr' fun i =>
    and_congr (mul_nonneg_iff_of_pos_left (inv_pos.2 hL)) (inv_mul_lt_one₀ hL)

/-- Every point has a unique translate along the lattice `L • ℤ^d` lying in the cube
`[0, L)^d`. -/
public lemma cubeLattice_unique_covers (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : cubeLattice d L hL,
      g +ᵥ x ∈ {y : EuclideanSpace ℝ (Fin d) | ∀ i, y i ∈ Set.Ico 0 L} := fun x => by
  simpa [fundamentalDomain_cubeBasis L hL] using
    exist_unique_vadd_mem_fundamentalDomain (cubeBasis d L hL) x

/-- The cube `[0, L)^d` is a bounded set. -/
public lemma isBounded_cube_Ico (L : ℝ) (hL : 0 < L) :
    IsBounded {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Ico 0 L} := by
  simpa [fundamentalDomain_cubeBasis L hL] using
    fundamentalDomain_isBounded (cubeBasis d L hL)

/-- A coordinate cube is the `ofLp`-preimage of the product box `∏ i, I`. This is the single
preimage identity from which the cubes' measurability and volume are read off. -/
public lemma cube_eq_preimage_ofLp (I : Set ℝ) :
    {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ I} =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' (Set.pi Set.univ fun _ : Fin d ↦ I) := by
  ext x; simp [Set.mem_pi]

/-- A coordinate cube over a measurable set of reals is measurable. -/
public lemma measurableSet_cube {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ I} := by
  rw [cube_eq_preimage_ofLp]
  exact (MeasurableSet.pi Set.countable_univ fun _ _ => hI).preimage
    (PiLp.volume_preserving_ofLp (ι := Fin d)).measurable

/-- The volume of a coordinate cube is `volume I ^ d`. -/
public lemma volume_cube (I : Set ℝ) (hI : MeasurableSet I) :
    volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ I} = volume I ^ d := by
  rw [cube_eq_preimage_ofLp,
    (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage
      (MeasurableSet.pi Set.countable_univ fun _ _ ↦ hI).nullMeasurableSet,
    volume_pi, Measure.pi_pi]
  simp

/-- The volume of the half-open cube `[a, b)^d` is `(b - a) ^ d`. -/
public lemma volume_cube_Ico (a b : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Ico a b} =
      ENNReal.ofReal (b - a) ^ d := by
  rw [volume_cube _ measurableSet_Ico, Real.volume_Ico]

/-- The volume of the closed cube `[a, b]^d` is `(b - a) ^ d`. -/
public lemma volume_cube_Icc (a b : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc a b} =
      ENNReal.ofReal (b - a) ^ d := by
  rw [volume_cube _ measurableSet_Icc, Real.volume_Icc]

/-- Only finitely many points of the lattice `L • ℤ^d` lie in a ball of radius `R`. -/
public lemma finite_lattice_in_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : cubeLattice d L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine (Set.Finite.preimage_embedding (f := ⟨fun g : cubeLattice d L hL =>
    (g : EuclideanSpace ℝ (Fin d)), Subtype.val_injective⟩)
    (ZSpan.setFinite_inter (b := cubeBasis d L hL)
      (s := ball (0 : EuclideanSpace ℝ (Fin d)) R) Metric.isBounded_ball)).subset fun g hg => ?_
  exact ⟨hg, g.property⟩

end EuclideanSpace

/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Gareth Ma
-/
import Architect
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.EMetricSpace.Paracompact

import SpherePacking.ForMathlib.VolumeOfBalls

open BigOperators MeasureTheory Metric

/-!
# Density of Sphere Packings

Let `X ⊆ ℝ^d` be a set of points such that distinct points are at least distance `r` apart. Putting
a ball of radius `r / 2` around each point, we have a configuration of *sphere packing*. We call `X`
the sphere packing centers.

We also define the *density* of the configuration.
-/

open scoped ENNReal
open BigOperators Pointwise Filter Module

section Definitions

@[blueprint
  (statement := /--
  A \emph{sphere packing} is a set $X \subset \R^d$ and a real number $r > 0$ (known as the
  \emph{separation radius}) such that $\|x - y\| \geq r$ for all distinct $x, y \in X$.

  Note that a sphere packing is uniquely defined from a given set of centres (which, in order to be
  a valid set of centres, must admit a corresponding separation radius). Therefore, as a conscious
  choice during the formalisation process, we will define everything that depends on sphere packings
  in terms of \verb|SpherePacking|, a \verb|structure| that bundles all the identifying information
  of a packing, but not the actual balls themselves. For the purposes of this blueprint, however, we
  will refrain from making this distinction.
  -/)]
structure SpherePacking (d : ℕ) where
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

attribute [blueprint
  (statement := /--
  We say that an additive subgroup $\Lambda \leq \R^d$ is a \emph{lattice} if it is discrete and its
  $\R$-span contains all the elements of $\R^d$.
  -/)]
  IsZLattice

@[blueprint
  (statement := /--
  We say that a sphere packing $\Pa(X)$ is ($\Lambda$-)\emph{periodic} if there exists a lattice
  $\Lambda \subset \R^d$ such that for all $x \in X$ and $y \in \Lambda$, $x + y \in X$ (ie, $X$ is
  $\Lambda$-periodic).
  -/)]
structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {d : ℕ}

theorem SpherePacking.centers_dist' (S : SpherePacking d) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ S.centers) (hy : y ∈ S.centers) (hxy : x ≠ y) :
    S.separation ≤ dist x y := by
  have : (⟨x, hx⟩ : S.centers) ≠ ⟨y, hy⟩ := Subtype.coe_ne_coe.mp hxy
  -- The following fails. Reason unknown.
  -- exact S.centers_dist this
  have := S.centers_dist this
  simp only at this
  exact this

instance PeriodicSpherePacking.instLatticeDiscrete (S : PeriodicSpherePacking d) :
    DiscreteTopology S.lattice :=
  S.lattice_discrete

instance PeriodicSpherePacking.instIsZLattice (S : PeriodicSpherePacking d) :
    IsZLattice ℝ S.lattice :=
  S.lattice_isZLattice

instance SpherePacking.instCentersDiscrete (S : SpherePacking d) :
    DiscreteTopology S.centers := by
  simp_rw [discreteTopology_iff_isOpen_singleton, Metric.isOpen_iff]
  intro ⟨u, hu⟩ ⟨v, hv⟩ huv
  simp_rw [Set.subset_singleton_iff, mem_ball, Subtype.forall, Subtype.mk.injEq]
  rw [Set.mem_singleton_iff, Subtype.mk.injEq] at huv
  subst huv
  use S.separation, S.separation_pos
  intro a ha h_dist
  contrapose! h_dist
  exact S.centers_dist <| Subtype.coe_ne_coe.mp h_dist

noncomputable instance PeriodicSpherePacking.addAction (S : PeriodicSpherePacking d) :
    AddAction S.lattice S.centers where
  vadd x y := ⟨↑x + ↑y, S.lattice_action x.prop y.prop⟩
  zero_vadd := by
    intro ⟨v, hv⟩
    apply Subtype.ext
    exact zero_add v
  add_vadd := by
    intro ⟨u, hu⟩ ⟨v, hv⟩ ⟨p, hp⟩
    apply Subtype.ext
    exact add_assoc u v p

alias PeriodicSpherePacking.instAddAction := PeriodicSpherePacking.addAction

theorem PeriodicSpherePacking.addAction_vadd (S : PeriodicSpherePacking d)
    {x : S.lattice} {y : S.centers} :
      x +ᵥ y = ⟨x.val + y.val, S.lattice_action x.prop y.prop⟩ :=
  rfl

@[blueprint
  (statement := /--
  % Do we want to replace the notation \mathcal{P} with \mathcal{P}_X or \mathcal{P}(X)?
  Given a set $X \subset \R^d$ and a real number $r > 0$ (known as the \emph{separation radius})
  such that $\|x - y\| \geq r$ for all distinct $x, y \in X$, we define the \emph{sphere packing}
  $\Pa(X)$ with centres at $X$ to be the union of all open balls of radius $r$ centred at points in
  $X$:
  \[
    \Pa(X) := \bigcup_{x \in X} B_d(x, r)
  \]
  -/)]
abbrev SpherePacking.balls (S : SpherePacking d) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x : S.centers, ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)

@[blueprint
  (statement := /--
  The \emph{finite density} of a packing $\mathcal{P}$ is defined as
  \[
    \Delta_{\mathcal{P}}(R):=\frac{\mathrm{Vol}(\mathcal{P}\cap
    B_d(0,R))}{\mathrm{Vol}(B_d(0,R))},\quad R>0.
  \]
  -/)]
noncomputable def SpherePacking.finiteDensity (S : SpherePacking d) (R : ℝ) : ℝ≥0∞ :=
  volume (S.balls ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))

@[blueprint
  (statement := /--
  We define the \emph{density} of a packing $\mathcal{P}$ as the limit superior
  \[
    \Delta_{\mathcal{P}}:=\limsup\limits_{R\to\infty}\Delta_{\mathcal{P}}(R).
  \]
  -/)]
noncomputable def SpherePacking.density (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.finiteDensity atTop

-- Here is one way to choose a basis, but I think for our purpose we can just supply one.
-- /-- Returns a ℝ-basis of ℝ^d such that the its ℤ-span is `S.lattice`. -/
-- noncomputable def PeriodicSpherePacking.lattice_basis (S : PeriodicSpherePacking d) :
-- Basis (Module.Free.ChooseBasisIndex ℤ S.lattice) ℝ (EuclideanSpace ℝ (Fin d)) :=
-- ((ZLattice.module_free ℝ S.lattice).chooseBasis).ofZLatticeBasis _ _

-- Rendered unnecessary by bump to 4.13.0-rc3
-- theorem Submodule.toIntSubmodule_eq_iff_eq_toAddSubgroup {G : Type*} [AddCommGroup G]
-- {A : AddSubgroup G} {B : Submodule ℤ G} :
-- AddSubgroup.toIntSubmodule A = B ↔ A = B.toAddSubgroup := by
-- constructor <;> rintro rfl <;> rfl

theorem PeriodicSpherePacking.basis_Z_span
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) :
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) = S.lattice :=
  Basis.ofZLatticeBasis_span ℝ S.lattice b

theorem PeriodicSpherePacking.mem_basis_Z_span
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) (v) :
    v ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) ↔ v ∈ S.lattice :=
  SetLike.ext_iff.mp (S.basis_Z_span b) v

theorem PeriodicSpherePacking.basis_R_span
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) :
    Submodule.span ℝ (Set.range (b.ofZLatticeBasis ℝ _)) = ⊤ :=
  Basis.span_eq _

end Definitions

section Scaling
variable {d : ℕ}
open Real

-- Unfortunately I can't define a SMul ℝ (SpherePacking d) because we require 0 < c
-- Perhaps we can define a monoid action instead - Sid
@[blueprint
  (statement := /--
  Given a sphere packing $\Pa(X)$ with separation radius $r$, we defined the \emph{scaled packing}
  with respect to a real number $c > 0$ to be the packing $\Pa(cX)$, where $cX = \setof{cx \in V}{x
  \in X}$ has separation radius $cr$.
  -/)]
def SpherePacking.scale (S : SpherePacking d) {c : ℝ} (hc : 0 < c) : SpherePacking d where
  centers := c • S.centers
  separation := c * S.separation
  separation_pos := mul_pos hc S.separation_pos
  centers_dist := fun ⟨x, hx⟩ ⟨y, hy⟩ _ ↦ by
    change c * S.separation ≤ ‖x - y‖
    obtain ⟨x', ⟨hx', rfl⟩⟩ := Set.mem_smul_set.mp hx
    obtain ⟨y', ⟨hy', rfl⟩⟩ := Set.mem_smul_set.mp hy
    rw [← smul_sub, norm_smul, norm_eq_abs, abs_eq_self.mpr hc.le]
    rw [ne_eq, Subtype.mk.injEq] at *
    have : x' ≠ y' := by rintro rfl; tauto
    have : (⟨x', hx'⟩ : S.centers) ≠ ⟨y', hy'⟩ := by simp [this]
    have := S.centers_dist this
    exact (mul_le_mul_iff_right₀ hc).mpr this


noncomputable def PeriodicSpherePacking.scale (S : PeriodicSpherePacking d) {c : ℝ} (hc : 0 < c) :
  PeriodicSpherePacking d := {
  S.toSpherePacking.scale hc with
  lattice := c • S.lattice
  lattice_action := fun x y hx hy ↦ by
    simp_all only [SpherePacking.scale, Set.mem_smul_set]
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    use x + y, S.lattice_action hx hy, smul_add ..
  lattice_discrete := by
    have := S.lattice_discrete
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at this ⊢
    obtain ⟨ε, hε, hε'⟩ := this
    use c * ε, mul_pos hc hε
    simp_rw [dist_zero_right, Subtype.forall] at hε' ⊢
    rintro x ⟨x, hx, rfl⟩ hx'
    -- rw [mul_lt_mul_left hc] at hx'
    -- rw [hε' x hx hx', smul_zero]
    simp only [DistribSMul.toLinearMap_apply, Submodule.mk_eq_zero, smul_eq_zero]
    right
    specialize hε' x hx
    simp only [DistribSMul.toLinearMap_apply, AddSubgroupClass.coe_norm,
      Submodule.mk_eq_zero] at hx' hε'
    rw [norm_smul, norm_eq_abs, abs_eq_self.mpr hc.le, mul_lt_mul_iff_right₀ hc] at hx'
    exact hε' hx'
  lattice_isZLattice := by
    use ?_
    rw [← S.lattice_isZLattice.span_top]
    ext v
    simp_rw [Submodule.mem_span]
    constructor <;> intro h p hp
    · specialize h (c • p) ?_
      · rw [Submodule.coe_pointwise_smul]
        exact Set.smul_set_mono hp
      · have : c • v ∈ c • p := Submodule.smul_mem _ _ h
        have := Submodule.smul_mem_pointwise_smul _ c⁻¹ _ this
        simpa [smul_smul, inv_mul_cancel₀ hc.ne.symm, one_smul]
    · specialize h (c⁻¹ • p) ?_
      · rw [Submodule.coe_pointwise_smul] at *
        have := Set.smul_set_mono (a := c⁻¹) hp
        rwa [smul_smul, inv_mul_cancel₀ hc.ne.symm, one_smul] at this
      · have : c⁻¹ • v ∈ c⁻¹ • p := Submodule.smul_mem _ _ h
        have := Submodule.smul_mem_pointwise_smul _ c _ this
        simpa [smul_smul, mul_inv_cancel₀ hc.ne.symm, one_smul]
}

lemma PeriodicSpherePacking.scale_toSpherePacking
    {S : PeriodicSpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).toSpherePacking = S.toSpherePacking.scale hc :=
  rfl

lemma SpherePacking.scale_balls {S : SpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).balls = c • S.balls := by
  ext x
  simp only [scale, Set.mem_iUnion, Set.iUnion_coe_set]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have := Set.smul_mem_smul_set (a := c⁻¹) hy
    rw [smul_smul, inv_mul_cancel₀ hc.ne.symm, one_smul] at this
    simp only [mem_ball, Set.mem_smul_set, Set.mem_iUnion] at hxy ⊢
    use c⁻¹ • x, ?_, ?_
    · use c⁻¹ • y, this
      have : 0 ≤ c⁻¹ := by positivity
      have h : 0 < c⁻¹ := by positivity
      rw [dist_eq_norm] at hxy ⊢
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_eq_self.mpr this]
      apply lt_of_lt_of_le (b := c⁻¹ * (c * S.separation / 2))
      · exact (mul_lt_mul_iff_right₀ h).mpr hxy
      · rw [mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hc.ne.symm, one_mul]
    · rw [smul_smul, mul_inv_cancel₀ hc.ne.symm, one_smul]
  · intro h
    simp only [mem_ball, Set.mem_smul_set, Set.mem_iUnion] at h ⊢
    obtain ⟨x, ⟨⟨y, hy₁, hy₂⟩, rfl⟩⟩ := h
    use c • y, ⟨y, hy₁, rfl⟩
    rw [dist_eq_norm] at hy₂ ⊢
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_eq_self.mpr hc.le, mul_div_assoc]
    gcongr

lemma PeriodicSpherePacking.scale_balls {S : PeriodicSpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.scale hc).balls = c • S.balls :=
  SpherePacking.scale_balls hc

end Scaling

noncomputable section Density

variable {d : ℕ} (S : SpherePacking d)

/-- The `PeriodicSpherePackingConstant` in dimension d is the supremum of the density of all
periodic packings. See also `<TODO>` for specifying the separation radius of the packings. -/
@[blueprint
  "def:Periodic-sphere-packing-constant"
  (statement := /--
  The periodic sphere packing constant is defined to be
  $$ \Delta_{d}^{\text{periodic}} := \sup_{\substack{P \subset \R^d \\ \text{periodic packing}}}
  \Delta_P$$
  -/)]
def PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : PeriodicSpherePacking d, S.density

/-- The `SpherePackingConstant` in dimension d is the supremum of the density of all packings. See
also `<TODO>` for specifying the separation radius of the packings. -/
@[blueprint
  (statement := /--
  The \emph{sphere packing constant} is defined as supremum of packing densities over all possible
  packings:
  \[
    \Delta_d:=\sup\limits_{\substack{\mathcal{P}\subset\R^d\\
    \scriptscriptstyle\mathrm{sphere}\;\mathrm{packing}}}\Delta_{\mathcal{P}}.
  \]
  -/)]
def SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : SpherePacking d, S.density

end Density

section DensityLemmas
namespace SpherePacking

lemma finiteDensity_le_one {d : ℕ} (S : SpherePacking d) (R : ℝ) : S.finiteDensity R ≤ 1 := by
  rw [finiteDensity]
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact volume.mono Set.inter_subset_right

lemma density_le_one {d : ℕ} (S : SpherePacking d) : S.density ≤ 1 := by
  rw [density]
  apply limsup_le_iSup.trans
  apply iSup_le
  intro
  exact finiteDensity_le_one _ _

/-- Finite density of a scaled packing. -/
@[simp, blueprint
  (statement := /--
  Let $\Pa(X)$ be a sphere packing and $c$ a positive real number. Then, for all $R > 0$,
  \[
    \Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R).
  \]
  -/)
  (proof := /--
  The proof follows by direct computation:
  \[
    \Delta_{\Pa(cX)}(cR) = \frac{\Vol{\Pa(cX) \cap B_d(0, cR)}}{\Vol{B_d(0, cR)}} = \frac{c^d \cdot
    \Vol{\Pa(X) \cap B_d(0, R)}}{c^d \cdot \Vol{B_d(0, R)}}
    % = \frac{\Vol{\Pa(X) \cap B_d(0, R)}}{\Vol{B_d(0, R)}}
    = \Delta_{\Pa(X)}(R)
  \]
  where the second equality follows from applying the fact that scaling a (measurable) set by a
  factor of $c$ scales its volume by a factor of $c^d$ to the fact that $\Pa(cX) \cap B_d(0, cR) = c
  \cdot (\Pa(X) \cap B_d(0, cR))$.
  -/)
  (latexEnv := "lemma")]
lemma scale_finiteDensity {d : ℕ} (_ : 0 < d) (S : SpherePacking d) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (S.scale hc).finiteDensity (c * R) = S.finiteDensity R := by
  -- haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd -- (_ : 0 < d) unnecessary
  have : ball (0 : EuclideanSpace ℝ (Fin d)) (c * R) = c • ball 0 R := by
    convert (_root_.smul_ball hc.ne.symm (0 : EuclideanSpace ℝ (Fin d)) R).symm
    · exact Eq.symm (DistribMulAction.smul_zero c)
    · rw [Real.norm_eq_abs, abs_eq_self.mpr hc.le]
  rw [finiteDensity, scale_balls, this, ← Set.smul_set_inter₀ hc.ne.symm]
  repeat rw [Measure.addHaar_smul_of_nonneg _ hc.le]
  rw [ENNReal.mul_div_mul_left, finiteDensity]
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, finrank_euclideanSpace_fin]
    positivity
  · apply ENNReal.ofReal_ne_top

@[simp]
lemma scale_finiteDensity' {d : ℕ} (hd : 0 < d) (S : SpherePacking d) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (S.scale hc).finiteDensity R = S.finiteDensity (R / c) := by
  rw [div_eq_mul_inv, ← scale_finiteDensity hd S hc, ← mul_assoc, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hc.ne.symm, one_mul]

/-- Density of a scaled packing. -/
@[blueprint
  (statement := /--
  Let $\Pa(X)$ be a sphere packing and $c$ a positive real number. Then, the density of the scaled
  packing $\Pa(cX)$ is equal to the density of the original packing $\Pa(X)$.
  -/)
  (proof := /--
  One can show, using relatively unsophisticated real analysis, that
  \[
    \limsup_{R \to \infty} \Delta_{\Pa(cX)}(R) = \limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR)
  \]
  Lemma~\ref{SpherePacking.scale_finiteDensity} tells us that $\Delta_{\Pa(cX)}(cR) =
  \Delta_{\Pa(X)}(R)$ for every $R > 0$. Therefore,
  \[
    \limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR) = \limsup_{cR \to \infty} \Delta_{\Pa(X)}(R) =
    \limsup_{R \to \infty} \Delta_{\Pa(X)}(R)
  \]
  where the second equality is the result of a similar change of variables to the one done above.
  -/)
  (latexEnv := "lemma")]
lemma scale_density {d : ℕ} (hd : 0 < d) (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.scale hc).density = S.density := by
  simp only [density, limsup, limsSup, eventually_map, eventually_atTop]
  apply le_antisymm
  -- The following are almost identical. Can we condense the proof?
  · simp only [sInf_le_iff, le_sInf_iff, Set.mem_setOf_eq, lowerBounds]
    intro x hx y hy
    rcases hx with ⟨a, ha⟩
    apply hy
    use c * a
    intro b' hb'
    rw [scale_finiteDensity' hd S hc]
    apply ha
    exact (le_div_iff₀' hc).mpr hb'
  · simp only [sInf_le_iff, le_sInf_iff, Set.mem_setOf_eq, lowerBounds]
    intro x hx y hy
    rcases hx with ⟨a, ha⟩
    apply hy
    use a / c
    intro b' hb'
    rw [← scale_finiteDensity hd S hc]
    apply ha
    exact (div_le_iff₀' hc).mp hb'

@[blueprint
  (statement := /--
  \[
    \Delta_d = \sup\limits_{\substack{\Pa \subset \R^d \\ \text{sphere packing} \\ \text{sep.~rad.}
    = 1}} \Delta_{\Pa}
  \]
  -/)
  (proof := /--
  That the supremum over packings of unit density is at most the sphere packing constant is obvious.
  For the reverse inequality, let $\Pa(X)$ be any sphere packing with separation radius $r$. We
  know, from Lemma~\ref{SpherePacking.scale_density}, that the density of $\Pa(X)$ is equal to that
  of the scaled packing $\Pa\!\left(\frac{X}{r}\right)$. Since the scaled packing has separation
  radius $1$, its density is naturally at most the supremum over all packings of unit density,
  meaning that the same is true of $\Pa(X)$.
  -/)
  (latexEnv := "lemma")]
theorem constant_eq_constant_normalized {d : ℕ} (hd : 0 < d) :
    SpherePackingConstant d = ⨆ (S : SpherePacking d) (_ : S.separation = 1), S.density := by
  rw [iSup_subtype', SpherePackingConstant]
  apply le_antisymm
  · apply iSup_le
    intro S
    have h := inv_mul_cancel₀ S.separation_pos.ne.symm
    have := le_iSup (fun S : { S : SpherePacking d // S.separation = 1 } ↦ S.val.density)
        ⟨S.scale (inv_pos.mpr S.separation_pos), h⟩
    simpa only [scale_density hd]
  · apply iSup_le
    intro ⟨S, _⟩
    exact le_iSup density S

end SpherePacking
end DensityLemmas

section PeriodicDensity

/- In this subsection, we prove that PeriodicDensity is equivalent to Density. This would allow us
to compute density of a periodic sphere packing easier. -/

-- TODO: state the theorem lol (first need to define PeriodicDensity in PeriodicPacking.lean
-- Probably also using dot notation under PeriodicSpherePacking namespace

end PeriodicDensity

section BasicResults
open scoped ENNReal
open EuclideanSpace

variable {d : ℕ} (S : SpherePacking d)

/- In this section we establish basic results about FiniteDensity and Density of different types of
packings. -/

lemma biUnion_inter_balls_subset_biUnion_balls_inter
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := by
  intro x hx
  simp at hx ⊢
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
  use ⟨y, ⟨hy₁.left, hy₂⟩⟩
  apply lt_of_le_of_lt <| norm_le_norm_add_norm_sub' x y
  gcongr <;> tauto

lemma biUnion_balls_inter_subset_biUnion_inter_balls
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := by
  intro x hx
  simp at hx ⊢
  obtain ⟨⟨y, ⟨hy₁, hy₂⟩⟩, hx⟩ := hx
  use y, ⟨hy₁, ?_⟩, hy₂
  calc
    ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_norm_add_norm_sub' y x
    _ = ‖x‖ + dist x y := by rw [dist_comm]; rfl
    _ < R - r + r := by gcongr
    _ = R := by ring

theorem SpherePacking.volume_iUnion_balls_eq_tsum
    (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') := by
  have : Countable S.centers := countable_of_Lindelof_of_discrete
  have : Countable ↑(S.centers ∩ ball 0 R) := Set.Countable.mono (Set.inter_subset_left) this
  apply measure_iUnion ?_ (fun _ ↦ measurableSet_ball)
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply ball_disjoint_ball
  simp_rw [ne_eq, Subtype.mk.injEq] at h ⊢
  linarith [S.centers_dist' x y hx.left hy.left h]

/-- This gives an upper bound on the number of points in the sphere packing X with norm less than R.
-/
theorem SpherePacking.inter_ball_encard_le (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤
      volume (S.balls ∩ ball 0 (R + S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    biUnion_inter_balls_subset_biUnion_balls_inter S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum R (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.le_div_iff_mul_le] at h <;> left
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

/-- This gives an upper bound on the number of points in the sphere packing X with norm less than R.
-/
theorem SpherePacking.inter_ball_encard_ge (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≥
      volume (S.balls ∩ ball 0 (R - S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    biUnion_balls_inter_subset_biUnion_inter_balls S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_iUnion_balls_eq_tsum _ (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.div_le_iff_le_mul] at h <;> left
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

theorem aux6 (R : ℝ) : Finite ↑(S.centers ∩ ball 0 R) := by
  apply Set.encard_lt_top_iff.mp
  by_cases hd : 0 < d
  · haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    apply ENat.toENNReal_lt.mp
    apply lt_of_le_of_lt (S.inter_ball_encard_le hd R)
    apply ENNReal.div_lt_top ?_ (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
    rw [← lt_top_iff_ne_top]
    calc
      _ ≤ volume (ball 0 (R + S.separation / 2)) := volume.mono Set.inter_subset_right
      _ < ⊤ := EuclideanSpace.volume_ball_lt_top _
  · rw [not_lt, nonpos_iff_eq_zero] at hd
    have : (ball (0 : EuclideanSpace ℝ (Fin 0)) R).encard ≤ 1 := by
      rw [← Set.Finite.cast_ncard_eq (Set.toFinite _), Nat.cast_le_one]
      exact Set.ncard_le_one_of_subsingleton _
    subst hd
    apply lt_of_le_of_lt (Set.encard_mono inf_le_right)
    apply lt_of_le_of_lt this (by decide)

@[blueprint
  "lemma:sp-finite-density-bound"
  (statement := /--
  For any $R > 0$,
  \[
    \left|X \cap \mathcal{B}_d\left(R - \frac{r}{2}\right)\right| \cdot
    \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
    \leq \Delta_{\mathcal{P}}(R)
    \leq \left|X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)\right| \cdot
    \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
  \]
  -/)
  (proof := /--
  The high level idea is to prove that $\mathcal{P} \cap \mathcal{B}_d(R) = \left(\bigcup_{x \in X}
  \mathcal{B}_d\left(x, \frac{r}{2}\right)\right) \subseteq \bigcup_{x \in X \cap
  \mathcal{B}_d\left(R + \frac{r}{2}\right)} \mathcal{B}_d\left(x, \frac{r}{2}\right)$, and a
  similar inequality for the upper bound. The rest follows by rearranging and using the fact that
  the balls are pairwise disjoint.
  -/)
  (latexEnv := "lemma")]
theorem SpherePacking.finiteDensity_ge (hd : 0 < d) (R : ℝ) :
    S.finiteDensity R
      ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [finiteDensity, balls]
  apply ENNReal.div_le_div_right
  rw [← ENNReal.le_div_iff_mul_le] <;> try left
  · have := S.inter_ball_encard_le hd (R - S.separation / 2)
    rwa [sub_add_cancel] at this
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

@[blueprint
  "lemma:sp-finite-density-bound"
  (statement := /--
  For any $R > 0$,
  \[
    \left|X \cap \mathcal{B}_d\left(R - \frac{r}{2}\right)\right| \cdot
    \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
    \leq \Delta_{\mathcal{P}}(R)
    \leq \left|X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)\right| \cdot
    \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
  \]
  -/)
  (proof := /--
  The high level idea is to prove that $\mathcal{P} \cap \mathcal{B}_d(R) = \left(\bigcup_{x \in X}
  \mathcal{B}_d\left(x, \frac{r}{2}\right)\right) \subseteq \bigcup_{x \in X \cap
  \mathcal{B}_d\left(R + \frac{r}{2}\right)} \mathcal{B}_d\left(x, \frac{r}{2}\right)$, and a
  similar inequality for the upper bound. The rest follows by rearranging and using the fact that
  the balls are pairwise disjoint.
  -/)
  (latexEnv := "lemma")]
theorem SpherePacking.finiteDensity_le (hd : 0 < d) (R : ℝ) :
    S.finiteDensity R
      ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [finiteDensity, balls]
  apply ENNReal.div_le_div_right
  rw [← ENNReal.div_le_iff_le_mul] <;> try left
  · have := S.inter_ball_encard_ge hd (R + S.separation / 2)
    rwa [add_sub_cancel_right] at this
  · exact (volume_ball_pos _ (by linarith [S.separation_pos])).ne.symm
  · exact (volume_ball_lt_top _).ne

end BasicResults

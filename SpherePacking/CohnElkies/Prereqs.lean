/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
/-
## THIS FILE SHOULD EVENTUALLY BE REMOVED AND THE REFERENCES IN COHN-ELKIES MUST BE REPLACED WITH
## THE RIGHT ONES (NOT THE ONES FROM HERE). THIS FILE IS JUST A TEMPORARY SOLUTION TO MAKE THE
## COHN-ELKIES FILE WORK.
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.RCLike.Inner
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Compactness.PseudometrizableLindelof
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order

import SpherePacking.ForMathlib.VolumeOfBalls
import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.ForMathlib.InvPowSummability

open BigOperators Bornology

variable {d : ℕ} --[Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]


-- noncomputable section Dual_Lattice

-- /-
-- This section defines the Dual Lattice of a Lattice. Taken from
-- `SpherePacking/ForMathlib/Dual.lean`.
-- -/

-- def bilinFormOfRealInner.dualSubmodule : AddSubgroup (EuclideanSpace ℝ (Fin d)) where
-- carrier := { x | ∀ l : Λ, ∃ n : ℤ, ⟪x, l⟫_[ℝ] = ↑n }
-- zero_mem' := by
-- simp only [Subtype.forall, Set.mem_setOf_eq, inner_zero_left]
-- intro a _
-- use 0
-- rw [Int.cast_zero]
-- add_mem' := by
-- intros x y hx hy l
-- obtain ⟨n, hn⟩ := hx l
-- obtain ⟨m, hm⟩ := hy l
-- use n + m
-- simp only [inner_add_left, hn, hm, Int.cast_add]
-- neg_mem' := by
-- intros x hx l
-- obtain ⟨n, hn⟩ := hx l
-- use -n
-- simp only [inner_neg_left, hn, Int.cast_neg]

-- end Dual_Lattice

section Euclidean_Space
/-
instance instNonemptyFin : Nonempty (Fin d) := ⟨0, Fact.out⟩
  -- rw [← Fintype.card_pos_iff, Fintype.card_fin]
  -- exact Fact.out
-/

-- noncomputable instance : DivisionCommMonoid ENNReal where
-- inv_inv := inv_inv
-- mul_inv_rev := sorry
-- inv_eq_of_mul := sorry
-- mul_comm := sorry


end Euclidean_Space

open scoped FourierTransform

open Complex Real
open LinearMap (BilinForm)

noncomputable section PSF_L

-- instance inst₁ : IsScalarTower ℤ ℝ (EuclideanSpace ℝ (Fin d)) := AddCommGroup.intIsScalarTower

/-
This section defines the Poisson Summation Formual, Lattice Version (`PSF_L`). This is a direct
dependency of the Cohn-Elkies proof.
-/

-- Could this maybe become a `structure` with each field being a different condition?
def PSF_Conditions (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  /-
    Mention here all the conditions we decide to impose functions on which to define the PSF-L.
    For example, this could be that they must be Schwartz (cf. blueprint) or admissible (cf. Cohn-
    Elkies). This is a placeholder for now, as is almost everything in this file.

    I think Schwartz is a good choice, because we can use the results in
    `Mathlib.Analysis.Distribution.FourierSchwartz` to conclude various things about the function.
  -/
  Summable f ∧
  sorry

theorem PSF_L {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : bilinFormOfRealInner.dualSubmodule Λ,
  (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) :=
  sorry

-- The version below is on the blueprint. I'm pretty sure it can be removed.
theorem PSF_L' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f) :
    ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) * ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 f m)
    := by
  simpa using PSF_L Λ hf 0

namespace SchwartzMap

theorem PoissonSummation_Lattices (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
  ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 ⇑f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) := by
  sorry

-- theorem PoissonSummation_Lattices' (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
-- ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) * ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 f m)
--   := by
-- sorry

end SchwartzMap

end PSF_L

open scoped FourierTransform

section FourierSchwartz

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
    [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

include 𝕜 in
@[simp]
theorem fourierInversion : 𝓕⁻ (𝓕 ⇑f) = f := by
  rw [← fourier_coe, ← fourierInv_coe]
  congr 1
  rw [← fourierTransformCLE_apply 𝕜 f,
      ← fourierTransformCLE_symm_apply 𝕜 _,
      ContinuousLinearEquiv.symm_apply_apply]

end SchwartzMap

end FourierSchwartz

section Positivity_on_Nhd

-- TODO: PR this to Mathlib (very useful!)
-- Or was I just not able to find it...

variable {E : Type*} [TopologicalSpace E]

theorem Continuous.pos_iff_exists_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hx
    suffices ∀ᶠ y in nhds x, 0 < f y by
      rw [Filter.eventually_iff] at this
      refine ⟨_, this, by simp⟩
    exact hf₁.tendsto x (eventually_gt_nhds hx)
  · intro hexistsnhd
    obtain ⟨U, hU₁, hU₂⟩ := hexistsnhd
    specialize hU₂ x (mem_of_mem_nhds hU₁)
    exact hU₂

open MeasureTheory

variable [MeasureSpace E] [BorelSpace E]

theorem Continuous.pos_iff_exists_measurable_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), MeasurableSet U ∧ ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hposatx
    have h₁ : ContinuousAt f x := continuousAt hf₁
    rw [continuousAt_def] at h₁
    have h₁' : Set.Ioo (f x / 2) (3 * f x / 2) ∈ nhds (f x) := by
      apply Ioo_mem_nhds (div_two_lt_of_pos hposatx) ?_
      linarith
    specialize h₁ (Set.Ioo (f x / 2) (3 * f x / 2)) h₁'
    use (f ⁻¹' Set.Ioo (f x / 2) (3 * f x / 2))
    constructor
    · exact h₁
    · constructor
      · exact hf₁.measurable measurableSet_Ioo
      · intro y hy
        have h₂ : f y ∈ Set.Ioo (f x / 2) (3 * f x / 2) := hy
        rw [Set.mem_Ioo] at h₂
        linarith
  · intro hnhx
    obtain ⟨U, hU₁, _, hU₃⟩ := hnhx
    exact (hf₁.pos_iff_exists_nhd_pos x).mpr ⟨U, hU₁, hU₃⟩

end Positivity_on_Nhd

section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)] -- More Generality Possible?

instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular

theorem Continuous.integral_zero_iff_zero_of_nonneg {f : E → ℝ} (hf₁ : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  /- Informal proof:
  ← is obvious. Now, assume the integral is zero. Suppose, for contradiction, that f ≠ 0.
  Then, there is a point x at which 0 < f x. So, there is a neighbourhood of x at which
  0 < f. The integral over this neighbourhood has to be positive, but less than that over
  the entire space. This is a contradiction.
  -/
  constructor
  · intro hintf
    by_contra hne
    -- Get an x at which f x ≠ 0
    obtain ⟨x, hneatx⟩ := Function.ne_iff.mp fun a ↦ hne (id (Eq.symm a))
    have hposatx : 0 < f x := lt_of_le_of_ne (hnn x) hneatx
    -- Get a neighbourhood of x at which f is positive
    obtain ⟨U, hU₁, hU₃⟩ := (hf₁.pos_iff_exists_nhd_pos x).mp hposatx
    -- Compare the integral over this neighbourhood to the integral over the entire space
    have hintgleintf : ∫ (v : E) in U, f v ≤ ∫ (v : E), f v := by
      refine integral_mono_measure Measure.restrict_le_self ?_ hf₂
      simp only [EventuallyLE, Pi.zero_apply, hnn, eventually_true]
    have hintgpos : 0 < ∫ (v : E) in U, f v := by
      refine (integral_pos_iff_support_of_nonneg hnn (Integrable.restrict hf₂)).mpr ?_
      suffices hUpos : 0 < (volume.restrict U) U by
        dsimp [Function.support]
        suffices hInclusion : U ⊆ {x | f x ≠ 0} by
          have : (volume.restrict U) U ≤ (volume.restrict U) {x | f x ≠ 0} := by
            rw [Measure.restrict_apply_self, Measure.restrict_apply_superset hInclusion]
          exact lt_of_lt_of_le hUpos this
        intro y hy
        rw [Set.mem_setOf_eq]
        specialize hU₃ y hy
        exact Ne.symm (ne_of_lt hU₃)
      rw [Measure.restrict_apply_self]
      exact MeasureTheory.Measure.measure_pos_of_mem_nhds volume hU₁
    linarith
  · intro hf
    simp only [hf, Pi.zero_apply]
    exact integral_zero E ℝ

example {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf₁ : Continuous f) (hf₂ : Integrable f)
  (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 :=
  hf₁.integral_zero_iff_zero_of_nonneg hf₂ hnn

namespace SchwartzMap

theorem toFun_eq_zero_iff_zero {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : 𝓢(E, F)) : (f : E → F) = 0 ↔ f = 0 := by
  constructor
  · exact fun a ↦ SchwartzMap.ext (congrFun a)
  · intro hf
    rw [hf]
    exact coeFn_zero

theorem integral_zero_iff_zero_of_nonneg {f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)}
  (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 := by
  simp [← f.toFun_eq_zero_iff_zero]
  exact f.continuous.integral_zero_iff_zero_of_nonneg f.integrable hnn

end SchwartzMap

end Integration

noncomputable section Misc

-- For some reason the following two instances seem to need restating...
instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

-- Now a small theorem from Complex analysis:
local notation "conj" => starRingEnd ℂ
theorem Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
  cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) :=
  calc cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
  _ = Circle.exp (-2 * π * ⟪x, m⟫_[ℝ])
      := by
          rw [Circle.coe_exp]
          push_cast
          ring_nf
  _ = conj (Circle.exp (2 * π * ⟪x, m⟫_[ℝ]))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
  _= conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
      := by
          rw [Circle.coe_exp]
          apply congrArg conj
          push_cast
          ring_nf

end Misc







section prerequisites

open scoped Finset
open Filter MeasureTheory ZSpan

variable (d) in
/-- The ball of radius r around x in d-dimensional Euclidean space. -/
def B (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball x r

/-- The volume of a set in d-dimensional Euclidean space as a real number. -/
noncomputable def vol (S : Set (EuclideanSpace ℝ (Fin d))) : ℝ := volume.real S

/-- The covolume of a lattice in d-dimensional Euclidean space as a real number. -/
noncomputable def covol (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) : ℝ := ZLattice.covolume Λ

section sphere_packing

/-- This structure is already being defined by Sid and Gareth in `SpherePacking.lean`.
Here I just used `X` instead of `centers` to respect the blueprint notation and changed everything
else accordingly. -/
structure SpherePacking' (d : ℕ) where
  X : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  X_dist : Pairwise (separation ≤ ‖·.val - ·.val‖ : X → X → Prop)

namespace SpherePacking'

variable {S : SpherePacking' d}

/-- New -/
instance : DiscreteTopology S.X := by sorry

variable (S) in
/-- Identical Sid and Gareth's for SpherePacking' -/
noncomputable def finiteBallDensity (R : ℝ) : ℝ :=
  vol (⋃ x : S.X, B d x (S.separation / 2) ∩ B d 0 R) / vol (B d 0 R)

variable (S) in
/-- Identical Sid and Gareth's for SpherePacking' -/
noncomputable def density : ℝ :=
  limsup S.finiteBallDensity atTop

/-- Identical Sid and Gareth's for SpherePacking' -/
protected noncomputable def constant (d : ℕ) : ℝ :=
  ⨆ S : SpherePacking' d, S.density

/-- New : If the set of centers of a sphere packing is empty then its density is 0. -/
lemma density_eq_zero_of_empty_centers (h : S.X = ∅) :
    S.density = 0 := by
  sorry

end SpherePacking'

structure PeriodicSpherePacking' (d : ℕ) extends SpherePacking' d where
  b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))
  inst_b := instIsZLatticeRealSpan b
  Λ := Submodule.span ℤ (Set.range b)
  hvadd : ∀ ⦃x y⦄, x ∈ Λ → y ∈ X → x +ᵥ y ∈ X
  hfintype : Fintype <| ↑(X ∩ fundamentalDomain b) := by apply Fintype.ofFinite
  X_Λ := (X ∩ fundamentalDomain b).toFinset
  inst_Discrete : DiscreteTopology Λ := by infer_instance
  inst_IsZLattice : IsZLattice ℝ Λ := by infer_instance

def Subtype.toX {P : PeriodicSpherePacking' d} (y : P.X_Λ) : P.X :=
  ⟨y.val, by sorry⟩

/-- The equivalence Λ × X⧸Λ ≃ X, via (λ, x) ↦ λ +ᵥ x. -/
noncomputable def e (P : PeriodicSpherePacking' d) : P.Λ × P.X_Λ → P.X :=
  fun p ↦ ⟨p.1.val +ᵥ p.2.val, P.hvadd p.1.prop p.2.toX.prop⟩

lemma e_bijective (P : PeriodicSpherePacking' d) : Function.Bijective (e P) := by sorry
/-
  have η_bij : Function.Bijective η := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp [η] at hxy

      sorry
    · intro z
      simp only [η]
      use
        ⟨⟨fract P.b z.val, by
          simp only [P.X_Λ_def, Set.mem_toFinset]
          exact Set.mem_inter
            (PeriodicSpherePacking'.fract_mem_centers z) (fract_mem_fundamentalDomain _ _)⟩,
        ⟨floor P.b z.val, by rw [P.Λ_def]; exact (floor P.b z.val).prop⟩⟩
      simp [fract]
-/

namespace PeriodicSpherePacking'

variable {P : PeriodicSpherePacking' d}

/-- New -/
def Λ_def : P.Λ = Submodule.span ℤ (Set.range P.b) := by sorry

/-- New -/
instance : Fintype ↑(P.X ∩ fundamentalDomain P.b) := by sorry

/-- New -/
def X_Λ_def : P.X_Λ = (P.X ∩ fundamentalDomain P.b).toFinset := by sorry

/-- Identical Sid and Gareth's for PeriodicSpherePacking' -/
instance instDiscrete_Λ :
    DiscreteTopology P.Λ := P.inst_Discrete

/-- Identical Sid and Gareth's for PeriodicSpherePacking' -/
instance instIsZLattice_Λ :
    IsZLattice ℝ P.Λ := P.inst_IsZLattice

/-- New -/
instance instFinite_X_Λ : Finite P.X_Λ := sorry

/-- New -/
lemma fract_mem_centers (z : P.X) : fract P.b z ∈ P.X := by sorry

/-- I believe one needs to ask as an axiom of the structure of periodic sphere packing that,
if X is nonempty, than X ∩ fundamentalDomain Λ must be nonempty,
otherwise the packing is not periodic. This proves the lemma below -/
lemma empty_centers_iff_card_X_Λ_eq_zero : P.X = ∅ ↔ P.X_Λ.card = 0 := by sorry

/-- Identical Sid and Gareth's for PeriodicSpherePacking' -/
protected noncomputable def constant (d : ℕ) : ℝ :=
  ⨆ S : PeriodicSpherePacking' d, S.density

/-- Identical Sid and Gareth's for PeriodicSpherePacking' -/
protected noncomputable def normalConstant (d : ℕ) : ℝ :=
  ⨆ S : {S : PeriodicSpherePacking' d // S.separation = 1}, S.val.density

theorem density_eq : P.density = #P.X_Λ * vol (B d 0 (P.separation / 2)) / covol P.Λ := by sorry

end PeriodicSpherePacking'

section cast

protected lemma PeriodicSpherePacking'.cast_normalConstant (d : ℕ) :
    PeriodicSpherePacking'.normalConstant d = PeriodicSpherePacking'.constant d := by
  sorry

lemma SpherePacking'.cast_constant (d : ℕ) :
    PeriodicSpherePacking'.constant d = SpherePacking'.constant d := by
  sorry

protected lemma SpherePacking'.cast_normalConstant (d : ℕ) :
    PeriodicSpherePacking'.normalConstant d = SpherePacking'.constant d := by
  rw [PeriodicSpherePacking'.cast_normalConstant d, SpherePacking'.cast_constant d]

end cast

end sphere_packing

section for_mathlib

section poisson

/- Poisson Summation fomula is taken care of within a separate PR and there is a dedicated folder
`ForMathlib\PoissonSummation`. Here you can find the statement needed in `LPBound.lean`. -/

open scoped FourierTransform SchwartzMap RealInnerProductSpace MeasureTheory ZSpan ZLattice
open LinearMap (BilinForm)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {Λ : Submodule ℤ V} [hdiscrete : DiscreteTopology Λ] [hlattice : IsZLattice ℝ Λ]
variable {L : BilinForm ℝ V}

--notation Λ"*["B"]" => LinearMap.BilinForm.dualSubmodule Λ B
notation Λ"*" => bilinFormOfRealInner.dualSubmodule Λ
--notation "𝓕v" => VectorFourier.fourierIntegral

/-- Identical to -/
instance instDiscreteTopology_dual : DiscreteTopology (L.dualSubmodule Λ) :=
  sorry

/-- New -/
instance instDiscreteTopology_dual_set :
    DiscreteTopology ((L.dualSubmodule Λ) : Set V) := by
  sorry

/--  -/
instance instIsZLattice_dual : IsZLattice ℝ (L.dualSubmodule Λ) :=
  sorry

/-lemma general_poisson_summation (e : AddChar ℝ Circle) (μ : Measure V)
    (f : C(V, E)) (h_sum : Summable (𝓕v e μ L f)) (x : V) :
    ∑' (ℓ : Λ), f (x + ℓ) = (1 / covolume Λ μ) • ∑' (m : Λ*[L]), e (L m x) • 𝓕v e μ L f m.val := by
  sorry
-/

protected lemma SchwartzMap.general_poisson_summation (f : 𝓢(V, E)) (x : V) :
    ∑' (ℓ : Λ), f (x + ℓ) =
      (1 / ZLattice.covolume Λ) • ∑' (m : Λ*), (𝐞 ⟪m.val, x⟫).val • 𝓕 f m := by
  sorry

end poisson

namespace Multipliable

variable {α β γ : Type*} {f : β → α}
variable [CommMonoid α] [TopologicalSpace α] [Finite γ]

--todo : extend to the summation filter version of the following lemmas
variable {L : SummationFilter β}

@[to_additive]
lemma fst_of_finite (hf : Multipliable f) :
    Multipliable (fun (x : β × γ) ↦ f x.1) := by
  sorry

@[to_additive]
lemma snd_of_finite (hf : Multipliable f) :
    Multipliable (fun (x : γ × β) ↦ f x.2) := by sorry

end Multipliable

namespace Complex

open scoped ComplexOrder

variable {a b c : ℂ}

protected lemma le_div_iff₀ (hc : 0 < c) :
    a ≤ b / c ↔ a * c ≤ b := by
  simp [le_def]
  constructor
  all_goals intro h; simp [div_re, div_im, (le_def.1 <| le_of_lt hc).2.symm] at h ⊢
  · sorry
  · sorry

protected lemma mul_le_mul_iff_of_pos_right (hc : 0 < c) :
    a * c ≤ b * c ↔ a ≤ b := by
  simp [le_def, ← (lt_def.1 hc).2]
  constructor
  all_goals intro h;
  · refine ⟨(mul_le_mul_iff_of_pos_right (lt_def.1 hc).1).mp h.1, ?_⟩
    obtain ⟨h₁, h_re | h_im⟩ := h
    · exact h_re
    · exfalso; rw [lt_def] at hc; simp [h_im] at hc
  · exact ⟨(mul_le_mul_iff_of_pos_right (lt_def.1 hc).1).mpr h.1, by simp [h.2]⟩

protected lemma mul_le_mul_iff_of_pos_left (hc : 0 < c) :
    c * a ≤ c * b ↔ a ≤ b := by
  simp [mul_comm c _]
  exact Complex.mul_le_mul_iff_of_pos_right hc

end Complex

namespace SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def translation (f : 𝓢(V, E)) (c : V) : 𝓢(V, E) :=
  { toFun := fun x ↦ f (x - c),
    smooth' := by sorry,
    decay' := by sorry }

@[simp]
theorem translation_def {f : 𝓢(V, E)} {c : V} :
    f.translation c = fun x ↦ f (x - c) := by rfl

--to do : see if this works for "multipliable" and for maps more general then Schwartz maps
protected lemma summable_on_discrete (f : 𝓢(V, E))
  (S : Set V) [hdiscrete : DiscreteTopology S] : Summable (fun (x : S) ↦ f x) := by sorry

end SchwartzMap

end for_mathlib

end prerequisites

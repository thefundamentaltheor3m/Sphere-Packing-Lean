module
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.ContinuousMap.Compact

public import SpherePacking.CohnElkies.PoissonSummationLattices.UnitAddTorus
public import SpherePacking.ForMathlib.FourierLinearEquiv

/-!
# Poisson summation for `ℤ`-lattices

Poisson summation for full-rank `ℤ`-lattices in Euclidean space, in the form needed by the
Cohn-Elkies argument.
-/

open scoped BigOperators
open MeasureTheory

namespace SchwartzMap

variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

local notation "E" => EuclideanSpace ℝ (Fin d)

-- This file is intentionally minimal; its purpose is to provide a reusable proof of Poisson
-- summation for `ℤ`-lattices, used by `SpherePacking/CohnElkies/Prereqs.lean`.

section StandardLattice

/-- The standard `ℤ`-lattice in `E = ℝ^d`, i.e. the span of the standard basis over `ℤ`. -/
@[expose] public noncomputable def standardLattice (d : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))

namespace standardLattice

/-- The standard lattice has the discrete topology. -/
public instance instDiscreteTopology : DiscreteTopology (standardLattice d) := by
  simpa [standardLattice] using
    (inferInstance :
      DiscreteTopology
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

/-- The standard lattice is a full-rank `ℤ`-lattice in `ℝ^d`. -/
public instance instIsZLattice : IsZLattice ℝ (standardLattice d) := by
  simpa [standardLattice] using
    (inferInstance :
      IsZLattice ℝ
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

end StandardLattice.standardLattice
/-!
## Poisson summation for lattices

We prove a Poisson summation formula for Schwartz functions on `E = ℝ^d`, for any full-rank
`ℤ`-lattice `Λ ⊆ E`.

The proof follows the standard Fourier-series-on-the-torus argument:
- periodize a Schwartz function along the lattice;
- descend it to the quotient torus;
- compute Fourier coefficients by pulling back to a fundamental domain and using the
  fundamental-domain tiling lemma;
- sum the Fourier series using absolute summability of Fourier coefficients (Schwartz decay).
-/

section PoissonSummation

namespace PoissonSummation

/-! ### The standard lattice `ℤ^d` -/

namespace Standard

/-- Embed an integer vector `k : ℤ^d` into `E = ℝ^d`. -/
@[expose] public noncomputable def intVec (k : Fin d → ℤ) : E :=
  WithLp.toLp (2 : ENNReal) (fun i : Fin d => (k i : ℝ))

/-- Coordinatewise evaluation of `intVec`. -/
@[simp]
public lemma intVec_apply (k : Fin d → ℤ) (i : Fin d) :
    intVec (d := d) k i = (k i : ℝ) := by
  simp [intVec]

/-- The image of `intVec` lies in the standard lattice. -/
public lemma intVec_mem_standardLattice (k : Fin d → ℤ) :
    intVec (d := d) k ∈ SchwartzMap.standardLattice d := by
  have hsum :
      intVec (d := d) k =
        ∑ i : Fin d, (k i) • ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i) := by
    ext j
    simp [intVec, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [hsum]
  refine (SchwartzMap.standardLattice d).sum_mem ?_
  intro i hi
  refine (SchwartzMap.standardLattice d).smul_mem (k i) ?_
  exact Submodule.subset_span ⟨i, rfl⟩

end SchwartzMap.PoissonSummation.PoissonSummation.Standard
/-!
### Poisson summation for the standard lattice

We specialize to the standard lattice in `E = ℝ^d` and use Fourier series on the torus
`(ℝ/ℤ)^d`. The proof is a multi-dimensional analogue of `Mathlib.Analysis.Fourier.PoissonSummation`
and follows the usual steps:
- periodize a Schwartz function along the integer lattice;
- descend to a continuous function on the torus;
- compute Fourier coefficients as Fourier transforms by swapping `tsum` and `integral` and using a
  fundamental domain;
- apply uniform convergence of the Fourier series (summable Fourier coefficients).
-/

namespace SchwartzMap

open TopologicalSpace MeasureTheory

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace PoissonSummation.Standard
open UnitAddTorus

/-! #### The integer cube as a fundamental domain -/

/-- The half-open cube `(0,1]^d`, used as a fundamental domain for the action of `ℤ^d` on `ℝ^d`. -/
@[expose] public def iocCube : Set E := {x | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- Measurability of the fundamental cube `iocCube`. -/
public lemma measurableSet_iocCube : MeasurableSet (iocCube (d := d)) := by
  -- `iocCube` is an intersection of coordinate preimages of a measurable interval.
  have hset :
      iocCube (d := d) = ⋂ i : Fin d, {x : E | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    ext x
    simp [iocCube]
  -- Coordinate projections are measurable, and `Ioc` is measurable.
  have hcoord :
      ∀ i : Fin d, MeasurableSet {x : E | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    intro i
    have hproj : Measurable fun x : E => x i := by
      simpa using
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ) i).measurable
    exact hproj measurableSet_Ioc
  simpa [hset] using MeasurableSet.iInter (ι := Fin d) hcoord

/-- `iocCube` is null-measurable (useful for integrals over its indicator). -/
public lemma nullMeasurableSet_iocCube : NullMeasurableSet (iocCube (d := d)) :=
  (measurableSet_iocCube (d := d)).nullMeasurableSet

/--
Every point `x : ℝ^d` has a unique translate by an integer vector that lies in `iocCube`.

This is the usual "fractional part" decomposition used to identify `ℝ^d / ℤ^d` with a cube.
-/
public lemma existsUnique_add_intVec_mem_iocCube (x : E) :
    ∃! n : Fin d → ℤ, x + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n ∈
      iocCube (d := d) := by
  -- Choose the unique `n i` sending `x i` into `(0,1]`.
  have hxcoord :
      ∀ i : Fin d, ∃! m : ℤ, (x i : ℝ) + m • (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    simpa [one_smul, add_assoc] using
      (existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ))
        (c := (0 : ℝ)))
  choose n hn hn_unique using hxcoord
  refine ⟨n, ?_, ?_⟩
  · -- membership
    intro i
    simpa [SchwartzMap.PoissonSummation.Standard.intVec_apply, iocCube, zsmul_one] using hn i
  · -- uniqueness
    intro n' hn'
    funext i
    have hn'i : (x i : ℝ) + n' i ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [SchwartzMap.PoissonSummation.Standard.intVec_apply] using
        (show ∀ i : Fin d,
            (x + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n') i ∈ Set.Ioc (0 : ℝ) 1 by
            simpa [iocCube] using hn') i
    exact hn_unique i (n' i) (by simpa [zsmul_one] using hn'i)

/-! #### Elements of the standard lattice are integer vectors -/

/-- Every element of the standard lattice comes from an integer vector via `intVec`. -/
public lemma exists_intVec_eq_of_mem_standardLattice (x : E)
    (hx : x ∈ SchwartzMap.standardLattice d) :
    ∃ n : Fin d → ℤ, x = SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
  let b : OrthonormalBasis (Fin d) ℝ E := EuclideanSpace.basisFun (Fin d) ℝ
  have hx_span :
      x ∈ Submodule.span ℤ (Set.range fun j : Fin d => (b.toBasis j : E)) := by
    -- Avoid rewriting `basisFun` into `single` (this can confuse `simp` through `Set.range`).
    simpa [SchwartzMap.standardLattice, standardLattice] using hx
  have hx_repr :=
    (Module.Basis.mem_span_iff_repr_mem (R := ℤ) (b := b.toBasis) x).1 hx_span
  choose n hn using hx_repr
  have hn' : ∀ i : Fin d, (n i : ℝ) = x i := by
    intro i
    simpa [b] using hn i
  refine ⟨n, ?_⟩
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec_apply, hn' i]

/-! #### Dual lattice of the standard lattice -/

/-- The dual of the standard lattice (for the Euclidean inner product) is the standard lattice. -/
public lemma dualSubmodule_standardLattice_eq :
    LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E))
        (SchwartzMap.standardLattice d) =
      SchwartzMap.standardLattice d := by
  ext x
  constructor
  · intro hx
    have hxcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      have hinner :
          inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∈ (1 : Submodule ℤ ℝ) := by
        simpa [innerₗ_apply_apply] using
          hx _ (Submodule.subset_span ⟨i, by simp⟩)
      rcases Submodule.mem_one.mp hinner with ⟨n, hn⟩
      exact ⟨n, by simpa [-EuclideanSpace.basisFun_apply] using hn⟩
    choose n hn using hxcoord
    have hx' : x = SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
      ext i
      simp [SchwartzMap.PoissonSummation.Standard.intVec_apply, hn i]
    simpa [hx'] using
      SchwartzMap.PoissonSummation.Standard.intVec_mem_standardLattice (d := d) n
  · intro hx y hy
    rcases exists_intVec_eq_of_mem_standardLattice (d := d) x hx with ⟨n, rfl⟩
    rcases exists_intVec_eq_of_mem_standardLattice (d := d) y hy with ⟨m, rfl⟩
    refine Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i, ?_⟩
    simp [innerₗ_apply_apply, SchwartzMap.PoissonSummation.Standard.intVec,
      PiLp.inner_apply, map_sum, Int.cast_mul, mul_comm]

end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace PoissonSummation.Standard
open UnitAddTorus

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`. -/
@[expose] public def coeFunE : E → UnitAddTorus (Fin d) :=
  fun x => UnitAddTorus.coeFun d ((WithLp.ofLp : E → (Fin d → ℝ)) x)

/-- Continuity of the quotient map `coeFunE`. -/
@[continuity]
public theorem continuous_coeFunE : Continuous (coeFunE (d := d)) := by
  simpa [coeFunE] using (UnitAddTorus.continuous_coeFun (n := d)).comp
    (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ))

/-- `coeFunE` is an open quotient map (so `UnitAddTorus` is the quotient `ℝ^d/ℤ^d`). -/
public theorem isOpenQuotientMap_coeFunE : IsOpenQuotientMap (coeFunE (d := d)) := by
  simpa [coeFunE] using
    IsOpenQuotientMap.comp (UnitAddTorus.isOpenQuotientMap_coeFun d) (by
      simpa using
        (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ)).isOpenQuotientMap)

/-- Adding an integer vector does not change the image in `(ℝ/ℤ)^d`. -/
@[simp]
public theorem coeFunE_add_intVec (x : E) (n : Fin d → ℤ) :
    coeFunE (d := d) (x + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) =
      coeFunE (d := d) x := by
  ext i
  simp [coeFunE, UnitAddTorus.coeFun]

/-- If two points map to the same torus point, their difference is an integer vector. -/
public theorem exists_intVec_eq_sub_of_coeFunE_eq {x y : E}
    (h : coeFunE (d := d) x = coeFunE (d := d) y) :
    ∃ n : Fin d → ℤ, x - y = SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
  have hcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = (x i - y i : ℝ) := by
    intro i
    have hsub : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      simpa [UnitAddCircle, AddCircle.coe_sub, coeFunE, UnitAddTorus.coeFun] using
        sub_eq_zero.2 (congrArg (fun t => t i) h)
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (x i - y i : ℝ))).1 hsub with ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩
  choose n hn using hcoord
  refine ⟨n, ?_⟩
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec, hn i]

/-- The cube `iocCube` is a fundamental domain for translation by the standard lattice. -/
public theorem isAddFundamentalDomain_iocCube :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.standardLattice d)
      (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) (volume : Measure E) := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'
      (SchwartzMap.PoissonSummation.Standard.nullMeasurableSet_iocCube (d := d)) ?_
  intro x
  rcases SchwartzMap.PoissonSummation.Standard.existsUnique_add_intVec_mem_iocCube (d := d) x with
    ⟨n, hn, hn_unique⟩
  refine
    ⟨(⟨SchwartzMap.PoissonSummation.Standard.intVec (d := d) n,
        SchwartzMap.PoissonSummation.Standard.intVec_mem_standardLattice (d := d) n⟩), ?_, ?_⟩
  · -- membership
    simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc] using hn
  · -- uniqueness
    intro ℓ hℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.exists_intVec_eq_of_mem_standardLattice (d := d)
          (ℓ : E) ℓ.property with
      ⟨n', hn'⟩
    have : n' = n := hn_unique n' (by
      simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc, hn'] using hℓ)
    apply Subtype.ext
    simp [hn', this]

/-- Pull back Haar integration on `(ℝ/ℤ)^d` to `iocCube` in `E = ℝ^d`. -/
public theorem integral_eq_integral_preimage_coeFunE (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (coeFunE (d := d) x) ∂(volume : Measure E).restrict
        (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) := by
  have h1 :
      (∫ y : UnitAddTorus (Fin d), g y) =
        ∫ x, g (UnitAddTorus.coeFun d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1)) := by
    simpa using
      (UnitAddTorus.integral_eq_integral_preimage_coeFun (n := d) (t := (0 : ℝ)) g hg)
  let f : (Fin d → ℝ) ≃ᵐ E := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (⇑f) (volume : Measure (Fin d → ℝ)) (volume : Measure E) := by
    simpa [f, MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (ι := Fin d))
  have hpre :
      f ⁻¹' (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) =
        Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1) := by
    ext x
    simp [f, SchwartzMap.PoissonSummation.Standard.iocCube, MeasurableEquiv.coe_toLp]
  have hmpR :
      MeasurePreserving (⇑f)
        ((volume : Measure (Fin d → ℝ)).restrict
          (f ⁻¹' SchwartzMap.PoissonSummation.Standard.iocCube (d := d)))
        ((volume : Measure E).restrict
          (SchwartzMap.PoissonSummation.Standard.iocCube (d := d))) :=
    MeasurePreserving.restrict_preimage hmp
      (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d))
  have h2 :
      (∫ x, g (UnitAddTorus.coeFun d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1))) =
        ∫ y, g (coeFunE (d := d) y) ∂(volume : Measure E).restrict
          (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) := by
    simpa [hpre, coeFunE, f] using
      (MeasurePreserving.integral_comp' hmpR
        (g := fun y : E => g (UnitAddTorus.coeFun d (WithLp.ofLp y))))
  exact h1.trans h2

end SchwartzMap.PoissonSummation.Standard

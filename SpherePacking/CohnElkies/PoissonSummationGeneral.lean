module
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.ContinuousMap.Compact

public import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Poisson summation for Schwartz functions

Three layers:

* `SchwartzMap.PoissonSummation.Standard` — periodization, descent to the torus, Schwartz decay
  bounds, and Poisson summation over the standard `ℤ^d` lattice.
* `SchwartzMap.PoissonSummationLattices` — Poisson summation over a full-rank `ℤ`-lattice
  `L ⊆ ℝ^d`, obtained from the standard case via a linear equivalence sending `ℤ^d` to `L`.
-/

open scoped BigOperators FourierTransform Real
open MeasureTheory

namespace SpherePacking.ForMathlib.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Change-of-variables for the Fourier transform under an invertible linear map. For
`A : V ≃ₗ[ℝ] V`, `𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A.symm).adjoint w)`. -/
public theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
        𝓕 f (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) := by
  simp only [Real.fourier_eq]
  let g : V → ℂ := fun y ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y
  let e : V ≃ᵐ V := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  calc (∫ x : V, Real.fourierChar (-(inner ℝ x w)) • f (A x)) =
        ∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V) := by
          simpa [g, e] using (MeasureTheory.integral_map_equiv (μ := (volume : Measure V)) e g).symm
    _ = (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ • ∫ y : V, g y := by
          rw [show Measure.map (⇑A) (volume : Measure V) =
              ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) by
            simpa using Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure V))
              (LinearEquiv.isUnit_det' A).ne_zero, MeasureTheory.integral_smul_measure]
          simp [abs_inv]
    _ = _ := by simp [g, show (fun y : V ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y) =
                    fun y : V ↦
                      Real.fourierChar (-(inner ℝ y
                        (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w))) • f y by
                  funext y; simp [LinearMap.adjoint_inner_right]]

end SpherePacking.ForMathlib.Fourier

namespace SchwartzMap.UnitAddTorus

/-- The coordinatewise quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n`. -/
@[expose] public def coeFun (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

/-- Continuity of the coordinatewise quotient map `coeFun`. -/
@[continuity]
public theorem continuous_coeFun {n : ℕ} : Continuous (coeFun n) := by
  simpa [coeFun, UnitAddCircle] using
    (continuous_pi fun i => (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i))

/-- A homeomorphism `α × (Fin n → α) ≃ (Fin (n+1) → α)`, specialized to constant families. -/
def finSuccPiHomeomorph (α : Type*) [TopologicalSpace α] (n : ℕ) :
    (α × (Fin n → α)) ≃ₜ (Fin n.succ → α) where
  toEquiv := Fin.consEquiv (fun _ ↦ α)
  continuous_toFun := by
    simpa [Fin.consEquiv] using Continuous.finCons (by fun_prop) (by fun_prop)
  continuous_invFun := by fun_prop

/-- `coeFun` is an open quotient map, so it presents `(ℝ/ℤ)^n` as a quotient of `ℝ^n`. -/
public theorem isOpenQuotientMap_coeFun (n : ℕ) : IsOpenQuotientMap (coeFun n) := by
  induction n with
  | zero =>
      have h : coeFun 0 =
          (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0)) : _ → _) :=
        funext fun _ => Subsingleton.elim _ _
      simpa [h] using
        (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0))).isOpenQuotientMap
  | succ n ih =>
      have h₁ : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
        simpa using
          (QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))
      let eX := (finSuccPiHomeomorph (α := ℝ) n).symm
      let eY := finSuccPiHomeomorph (α := UnitAddCircle) n
      have hconj : coeFun n.succ =
          (fun x => eY (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coeFun n) (eX x))) := by
        funext x; ext i
        cases i using Fin.cases with
        | zero => simp [coeFun, eY, finSuccPiHomeomorph, eX, Prod.map]
        | succ i => simp [coeFun, eY, finSuccPiHomeomorph, eX, Prod.map, Fin.tail]
      simpa [hconj] using
        (IsOpenQuotientMap.comp eY.isOpenQuotientMap
          (IsOpenQuotientMap.comp (IsOpenQuotientMap.prodMap h₁ ih) eX.isOpenQuotientMap))

/-- Evaluate the additive character `mFourier k` on a point `x : ℝ^n` viewed in the torus
via `coeFun`. -/
public theorem mFourier_apply_coeFun_ofLp (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coeFun n (WithLp.ofLp x)) =
      Complex.exp (2 * π * Complex.I * (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, coeFun, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * (WithLp.ofLp x i)))).symm

/-- Pull back Haar integration on `(ℝ/ℤ)^n` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^n`. -/
public theorem integral_eq_integral_preimage_coeFun (n : ℕ) (t : ℝ) (g : UnitAddTorus (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coeFun n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp : MeasurePreserving (coeFun n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) := by
    simpa [coeFun] using
      (MeasureTheory.measurePreserving_pi
        (μ := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
        (ν := fun _ : Fin n => (volume : Measure UnitAddCircle))
        (hf := fun _ => UnitAddCircle.measurePreserving_mk t))
  have h1 : (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coeFun n x) ∂(Measure.pi fun _ : Fin n =>
        (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) := by
    rw [← hmp.map_eq]
    simpa using MeasureTheory.integral_map (hφ := hmp.aemeasurable) (f := g)
      (hfm := by simpa [hmp.map_eq] using hg)
  simpa [(by simpa using (Measure.restrict_pi_pi
    (μ := fun _ : Fin n => (volume : Measure ℝ)) (s := fun _ : Fin n => Set.Ioc t (t + 1))) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
    Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))).symm] using h1

end SchwartzMap.UnitAddTorus

namespace SchwartzMap

variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

local notation "E" => EuclideanSpace ℝ (Fin d)

section StandardLattice

/-- The standard `ℤ`-lattice in `E = ℝ^d`, i.e. the span of the standard basis over `ℤ`. -/
@[expose] public noncomputable def standardLattice (d : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))

namespace standardLattice

public instance instDiscreteTopology : DiscreteTopology (standardLattice d) := by
  unfold standardLattice; infer_instance

public instance instIsZLattice : IsZLattice ℝ (standardLattice d) := by
  unfold standardLattice; infer_instance

end StandardLattice.standardLattice

namespace PoissonSummation

namespace Standard

/-- Embed an integer vector `k : ℤ^d` into `E = ℝ^d`. -/
@[expose] public noncomputable def intVec (k : Fin d → ℤ) : E :=
  WithLp.toLp (2 : ENNReal) (fun i : Fin d => (k i : ℝ))

@[simp] public lemma intVec_apply (k : Fin d → ℤ) (i : Fin d) :
    intVec (d := d) k i = (k i : ℝ) := by simp [intVec]

public lemma intVec_mem_standardLattice (k : Fin d → ℤ) :
    intVec (d := d) k ∈ SchwartzMap.standardLattice d := by
  rw [show intVec (d := d) k =
      ∑ i : Fin d, (k i) • ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i) by
    ext j; simp [intVec, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      Pi.single_apply]]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

open TopologicalSpace UnitAddTorus

/-- The half-open cube `(0,1]^d`, used as a fundamental domain for the action of `ℤ^d` on `ℝ^d`. -/
@[expose] public def iocCube : Set E := {x | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}

public lemma measurableSet_iocCube : MeasurableSet (iocCube (d := d)) := by
  rw [show iocCube (d := d) = ⋂ i : Fin d, {x : E | x i ∈ Set.Ioc (0 : ℝ) 1} by
    ext x; simp [iocCube]]
  exact .iInter fun i ↦ ((PiLp.continuous_apply (p := (2 : ENNReal))
    (β := fun _ : Fin d ↦ ℝ) i).measurable) measurableSet_Ioc

/-- Every element of the standard lattice comes from an integer vector via `intVec`. -/
public lemma exists_intVec_eq_of_mem_standardLattice (x : E)
    (hx : x ∈ SchwartzMap.standardLattice d) : ∃ n : Fin d → ℤ, x = intVec (d := d) n := by
  choose n hn using (Module.Basis.mem_span_iff_repr_mem (R := ℤ)
    (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) x).1
    (by simpa [SchwartzMap.standardLattice, standardLattice] using hx)
  exact ⟨n, by ext i; simpa [intVec_apply] using (hn i).symm⟩

/-- The dual of the standard lattice (for the Euclidean inner product) is the standard lattice. -/
public lemma dualSubmodule_standardLattice_eq :
    LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E))
        (SchwartzMap.standardLattice d) = SchwartzMap.standardLattice d := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx y hy ↦ ?_⟩
  · choose n hn using show ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = x i from fun i ↦ by
      rcases Submodule.mem_one.mp (show inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∈
          (1 : Submodule ℤ ℝ) by
        simpa [innerₗ_apply_apply] using hx _ (Submodule.subset_span ⟨i, by simp⟩)) with ⟨n, hn⟩
      exact ⟨n, by simpa [-EuclideanSpace.basisFun_apply] using hn⟩
    exact (show x = intVec (d := d) n by ext i; simp [intVec_apply, hn i]) ▸
      intVec_mem_standardLattice (d := d) n
  · rcases exists_intVec_eq_of_mem_standardLattice (d := d) x hx with ⟨n, rfl⟩
    rcases exists_intVec_eq_of_mem_standardLattice (d := d) y hy with ⟨m, rfl⟩
    exact Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i, by
      simp [innerₗ_apply_apply, intVec, PiLp.inner_apply, map_sum, Int.cast_mul, mul_comm]⟩

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`. -/
@[expose] public def coeFunE : E → UnitAddTorus (Fin d) :=
  fun x ↦ UnitAddTorus.coeFun d ((WithLp.ofLp : E → (Fin d → ℝ)) x)

@[continuity] public theorem continuous_coeFunE : Continuous (coeFunE (d := d)) := by
  simpa [coeFunE] using (UnitAddTorus.continuous_coeFun (n := d)).comp
    (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin d ↦ ℝ))

@[simp] public theorem coeFunE_add_intVec (x : E) (n : Fin d → ℤ) :
    coeFunE (d := d) (x + intVec (d := d) n) = coeFunE (d := d) x := by
  ext i; simp [coeFunE, UnitAddTorus.coeFun]

/-- If two points map to the same torus point, their difference is an integer vector. -/
public theorem exists_intVec_eq_sub_of_coeFunE_eq {x y : E}
    (h : coeFunE (d := d) x = coeFunE (d := d) y) :
    ∃ n : Fin d → ℤ, x - y = intVec (d := d) n := by
  choose n hn using show ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = (x i - y i : ℝ) from fun i ↦ by
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (x i - y i : ℝ))).1 (by
      simpa [UnitAddCircle, AddCircle.coe_sub, coeFunE, UnitAddTorus.coeFun] using
        sub_eq_zero.2 (congrArg (fun t ↦ t i) h)) with ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩
  exact ⟨n, by ext i; simp [intVec, hn i]⟩

/-- The cube `iocCube` is a fundamental domain for translation by the standard lattice. -/
public theorem isAddFundamentalDomain_iocCube :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.standardLattice d)
      (iocCube (d := d)) (volume : Measure E) := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'
    (measurableSet_iocCube (d := d)).nullMeasurableSet fun x ↦ ?_
  choose n hn hn_unique using fun i : Fin d ↦ by
    simpa [one_smul, add_assoc] using
      existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ)) (c := (0 : ℝ))
  have hn : x + intVec (d := d) n ∈ iocCube (d := d) := fun i ↦ by
    simpa [intVec_apply, iocCube, zsmul_one] using hn i
  have hn_unique : ∀ n' : Fin d → ℤ, x + intVec (d := d) n' ∈ iocCube (d := d) → n' = n :=
    fun n' hn' ↦ funext fun i ↦ hn_unique i (n' i) (by
      simpa [intVec_apply, zsmul_one] using
        (show ∀ j : Fin d, (x + intVec (d := d) n') j ∈
          Set.Ioc (0:ℝ) 1 by simpa [iocCube] using hn') i)
  refine ⟨⟨intVec (d := d) n, intVec_mem_standardLattice (d := d) n⟩,
    by simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc] using hn,
    fun ℓ hℓ ↦ ?_⟩
  rcases exists_intVec_eq_of_mem_standardLattice (d := d) (ℓ : E) ℓ.property with ⟨n', hn'⟩
  exact Subtype.ext (by simp [hn', hn_unique n' (by
    simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc, hn'] using hℓ)])

/-- Pull back Haar integration on `(ℝ/ℤ)^d` to `iocCube` in `E = ℝ^d`. -/
public theorem integral_eq_integral_preimage_coeFunE (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (coeFunE (d := d) x) ∂(volume : Measure E).restrict (iocCube (d := d)) := by
  let f : (Fin d → ℝ) ≃ᵐ E := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (⇑f) (volume : Measure (Fin d → ℝ)) (volume : Measure E) := by
    simpa [f, MeasurableEquiv.coe_toLp] using PiLp.volume_preserving_toLp (ι := Fin d)
  calc
    (∫ y : UnitAddTorus (Fin d), g y)
        = ∫ x, g (UnitAddTorus.coeFun d x) ∂(volume : Measure (Fin d → ℝ)).restrict
            (Set.univ.pi fun _ : Fin d ↦ Set.Ioc (0 : ℝ) (0 + 1)) := by
          simpa using UnitAddTorus.integral_eq_integral_preimage_coeFun
            (n := d) (t := (0 : ℝ)) g hg
    _ = ∫ y, g (coeFunE (d := d) y) ∂(volume : Measure E).restrict (iocCube (d := d)) := by
          simpa [show f ⁻¹' (iocCube (d := d)) =
              Set.univ.pi fun _ : Fin d ↦ Set.Ioc (0 : ℝ) (0 + 1) by
            ext x; simp [f, iocCube, MeasurableEquiv.coe_toLp], coeFunE, f] using
            MeasurePreserving.integral_comp'
              (MeasurePreserving.restrict_preimage hmp (measurableSet_iocCube (d := d)))
              (g := fun y : E ↦ g (UnitAddTorus.coeFun d (WithLp.ofLp y)))

end SchwartzMap.PoissonSummation.Standard

open Module UnitAddTorus

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

/-! ## Basic infrastructure (merged from `PoissonSummationSchwartz.Basic`) -/

/-- Equivalence between integer vectors `Fin d → ℤ` and the standard lattice `Λ = ℤ^d ⊆ ℝ^d`. -/
@[expose] public noncomputable def equivIntVec : (Fin d → ℤ) ≃ Λ :=
  Equiv.ofBijective
    (fun n : Fin d → ℤ => ⟨intVec (d := d) n, intVec_mem_standardLattice (d := d) n⟩)
    ⟨fun a b hab => funext fun i => by
      simpa [intVec_apply] using congrArg (fun x : E => x i) (congrArg Subtype.val hab),
    fun ℓ =>
      let ⟨n, hn⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (x := (ℓ : E)) ℓ.property
      ⟨n, Subtype.ext hn.symm⟩⟩

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

public instance instMeasurableVAdd_standardLattice : MeasurableVAdd Λ E where
  measurable_const_vadd c := by
    simpa [Submodule.vadd_def, vadd_eq_add] using (continuous_const.add continuous_id).measurable
  measurable_vadd_const x := by simpa [Submodule.vadd_def, vadd_eq_add] using
    (continuous_subtype_val.add continuous_const).measurable

public instance instVAddInvariantMeasure_standardLattice :
    MeasureTheory.VAddInvariantMeasure Λ E (volume : Measure E) where
  measure_preimage_vadd c s hs := by
    simp [Submodule.vadd_def, vadd_eq_add, MeasureTheory.measure_preimage_add]

/-- Translate the Schwartz function `f` by a lattice vector, as a continuous map. -/
@[expose] public noncomputable def translate (ℓ : Λ) : C(E, ℂ) :=
  (⟨f, f.continuous⟩ : C(E, ℂ)).comp (ContinuousMap.addRight (ℓ : E))

@[simp] public lemma translate_apply (ℓ : Λ) (x : E) :
    translate (d := d) f ℓ x = f (x + (ℓ : E)) := rfl

/-- Only finitely many standard lattice points lie in a closed ball of radius `r`. -/
public lemma finite_norm_le_lattice (r : ℝ) :
    ( {ℓ : Λ | ‖(ℓ : E)‖ ≤ r} : Set _ ).Finite := by
  haveI : DiscreteTopology ((Λ).toAddSubgroup) := (inferInstance : DiscreteTopology Λ)
  have hfinE : Set.Finite (Metric.closedBall (0 : E) r ∩ ((Λ).toAddSubgroup : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  let e : Λ ↪ E := ⟨fun ℓ => (ℓ : E), Subtype.coe_injective⟩
  refine (Set.Finite.preimage_embedding e
    (by simpa [Submodule.coe_toAddSubgroup] using hfinE)).subset fun ℓ hℓ => by
      simpa [e, Metric.mem_closedBall, dist_eq_norm] using hℓ

/-- Schwartz decay: sup norms of translates restricted to a compact `K` are summable. -/
public lemma summable_norm_translate_restrict (K : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : Λ => ‖(translate (d := d) f ℓ).restrict K‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  simp_rw [norm_iteratedFDeriv_zero] at hC
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  let r0 : ℝ := max r 0
  have hrK0 : (K : Set E) ⊆ Metric.closedBall (0 : E) r0 :=
    fun x hx => Metric.closedBall_subset_closedBall (le_max_left r 0) (hrK hx)
  have h_event : ∀ᶠ ℓ : Λ in Filter.cofinite,
      ‖(translate (d := d) f ℓ).restrict K‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) := by
    filter_upwards [(finite_norm_le_lattice (d := d) (r := max (2 * r0) 1)
      ).eventually_cofinite_notMem] with ℓ hℓ
    have hRlt : max (2 * r0) 1 < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
    have hnorm_lt : 2 * r0 < ‖(ℓ : E)‖ := lt_of_le_of_lt (le_max_left _ _) hRlt
    have hnorm_pos : 0 < ‖(ℓ : E)‖ := lt_trans (by positivity) hRlt
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun ⟨x, hxK⟩ => ?_
    have hxnorm : ‖(x : E)‖ ≤ r0 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hrK0 hxK
    have hnorm_ge : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(x + (ℓ : E))‖ := by
      have hsub : ‖(ℓ : E)‖ - ‖(x : E)‖ ≤ ‖(ℓ : E) + x‖ := by
        simpa [add_comm] using norm_sub_norm_le (ℓ : E) (-x)
      simpa [add_comm] using (by nlinarith : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(ℓ : E) + x‖)
    have hpow_pos : 0 < ‖(x + (ℓ : E))‖ ^ k :=
      pow_pos ((by positivity : 0 < (1 / 2 : ℝ) * ‖(ℓ : E)‖).trans_le hnorm_ge) _
    have hinv : (‖(x + (ℓ : E))‖ ^ k)⁻¹ ≤ (2 ^ k : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k) := by
      simpa [one_div, mul_pow, inv_pow, mul_inv_rev, mul_comm] using
        one_div_le_one_div_of_le (pow_pos (mul_pos (by positivity) hnorm_pos) _)
          (pow_le_pow_left₀ (by positivity) hnorm_ge k)
    calc ‖(translate (d := d) f ℓ) (⟨x, hxK⟩ : K)‖
        = ‖f (x + (ℓ : E))‖ := by simp [translate]
      _ ≤ C / (‖(x + (ℓ : E))‖ ^ k) := (le_div_iff₀' hpow_pos).2 (hC (x + (ℓ : E)))
      _ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) := by
        simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hinv hCpos.le
  refine Summable.of_norm_bounded_eventually
    (((by simpa [k] using ZLattice.summable_norm_pow_inv (L := Λ) (n := k) (Nat.lt_succ_self _)
        : Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ))).mul_left (C * (2 ^ k : ℝ)))) ?_
  filter_upwards [h_event] with ℓ hℓ
  simpa [Real.norm_of_nonneg (by positivity)] using hℓ

/-- Periodization of a Schwartz function along the standard lattice. -/
@[expose] public noncomputable def periodized : C(E, ℂ) :=
  ∑' ℓ : Λ, translate (d := d) f ℓ

public lemma periodized_apply (x : E) :
    periodized (d := d) f x = ∑' ℓ : Λ, f (x + (ℓ : E)) := by
  simpa [periodized, translate_apply] using
    (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
      (summable_norm_translate_restrict (d := d) f)) x).symm

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`, bundled as a continuous map. -/
@[expose] public noncomputable def coeFunEC : C(E, UnitAddTorus (Fin d)) :=
  ⟨coeFunE (d := d), continuous_coeFunE⟩

/-- The periodization is invariant under lattice translates, so it factors through the torus. -/
public lemma periodized_factorsThrough :
    Function.FactorsThrough (periodized (d := d) f) (coeFunEC (d := d)) := fun x y hxy => by
  obtain ⟨n, hn⟩ := exists_intVec_eq_sub_of_coeFunE_eq (d := d) (x := x) (y := y)
    (by simpa [coeFunEC] using hxy)
  simpa [show x = y + intVec (d := d) n by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun t => t + y) hn] using
    show periodized (d := d) f (y + (⟨_, intVec_mem_standardLattice (d := d) n⟩ : Λ)) =
        periodized (d := d) f y by
      simpa [periodized_apply (d := d) f, add_assoc] using
        (Equiv.addLeft (⟨_, intVec_mem_standardLattice (d := d) n⟩ : Λ)).tsum_eq
          fun ℓ => f (y + (ℓ : E))

/-- Descend the periodization to the torus `(ℝ/ℤ)^d` via the quotient. -/
@[expose] public noncomputable def descended : C(UnitAddTorus (Fin d), ℂ) :=
  Topology.IsQuotientMap.lift (hf := (show IsOpenQuotientMap (coeFunE (d := d)) by
      simpa [coeFunE] using IsOpenQuotientMap.comp (UnitAddTorus.isOpenQuotientMap_coeFun d)
        (PiLp.homeomorph (p := (2 : ENNReal))
          (β := fun _ : Fin d ↦ ℝ)).isOpenQuotientMap).isQuotientMap)
    (g := periodized (d := d) f) (periodized_factorsThrough (d := d) (f := f))

/-- Compatibility of `descended` with `coeFunE`: pulling back gives `periodized`. -/
public lemma descended_comp (x : E) :
    descended (d := d) f (coeFunE (d := d) x) = periodized (d := d) f x :=
  congrArg (fun g : C(E, ℂ) => g x)
    (by simp [descended] : (descended (d := d) f).comp (coeFunEC (d := d)) = periodized (d := d) f)

public lemma mFourier_neg_apply_coeFunE (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) =
      (𝐞 (-(inner ℝ x (intVec (d := d) n))) : ℂ) := by
  simp [coeFunE, UnitAddTorus.mFourier_apply_coeFun_ofLp,
    Real.fourierChar_apply, intVec, PiLp.inner_apply,
    Finset.sum_neg_distrib, mul_assoc, mul_comm]

@[simp] lemma intVec_neg (n : Fin d → ℤ) :
    intVec (d := d) (-n) = -intVec (d := d) n := by ext i; simp [intVec_apply]

public lemma mFourier_apply_coeFunE_exp (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier n (coeFunE (d := d) x) =
      Complex.exp (2 * Real.pi * Complex.I * ⟪x, intVec (d := d) n⟫_[ℝ]) := by
  simpa [Real.fourierChar_apply, mul_assoc, mul_comm, inner_neg_right,
    RCLike.inner_eq_wInner_one x (intVec n)] using
    mFourier_neg_apply_coeFunE (d := d) (n := -n) (x := x)

public lemma mFourier_neg_apply_coeFunE_add_standardLattice (n : Fin d → ℤ) (ℓ : Λ) (x : E) :
    UnitAddTorus.mFourier (-n) (coeFunE (d := d) (x + (ℓ : E))) =
      UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) :=
  let ⟨m, hm⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (x := (ℓ : E)) ℓ.property
  by simp [hm]

public lemma iocCube_subset_closedBall :
    iocCube (d := d) ⊆ Metric.closedBall (0 : E) (Real.sqrt d) := fun x hx => by
  simpa [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq] using
    Real.sqrt_le_sqrt (show (∑ i : Fin d, ‖x i‖ ^ 2) ≤ (d : ℝ) by
      simpa using (Finset.sum_le_sum fun i _ => show ‖x i‖ ^ 2 ≤ (1 : ℝ) by
        nlinarith [norm_nonneg (x i), show ‖x i‖ ≤ (1 : ℝ) by
          simpa [Real.norm_eq_abs, abs_of_nonneg (hx i).1.le] using (hx i).2]).trans_eq (by simp))

public lemma volume_iocCube_lt_top : (volume : Measure E) (iocCube (d := d)) < ⊤ :=
  ((Metric.isBounded_closedBall (x := (0 : E)) (r := Real.sqrt d)).subset
    (iocCube_subset_closedBall (d := d))).measure_lt_top

public lemma integrableOn_mFourier_mul_translate_iocCube (n : Fin d → ℤ) (ℓ : Λ) :
    IntegrableOn
        (fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E)))
        (iocCube (d := d)) (volume : Measure E) := by
  let K : TopologicalSpace.Compacts E :=
    ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩
  refine Measure.integrableOn_of_bounded (μ := (volume : Measure E))
    (s := iocCube (d := d)) (s_finite := (volume_iocCube_lt_top (d := d)).ne)
    (M := ‖(translate (d := d) f ℓ).restrict K‖)
    (((UnitAddTorus.mFourier (-n)).continuous.comp (continuous_coeFunE (d := d))).mul
        (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x hx => ?_)
  calc ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E))‖
      ≤ 1 * ‖f (x + (ℓ : E))‖ := by
        rw [norm_mul]; gcongr
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) _
    _ ≤ ‖(translate (d := d) f ℓ).restrict K‖ := by
      simpa [translate_apply, ContinuousMap.restrict_apply] using
        ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict K)
          ⟨x, iocCube_subset_closedBall (d := d) hx⟩

/-! ## Standard Poisson summation (merged from `PoissonSummationSchwartz.PoissonSummation`) -/

section StandardPoissonSummation

open UnitAddTorus PoissonSummation.Standard

noncomputable def ball : TopologicalSpace.Compacts E :=
  ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩

lemma summable_integral_norm_mFourier_mul_translate_iocCube (n : Fin d → ℤ) :
    Summable
        (fun ℓ : Λ =>
          ∫ x in iocCube (d := d),
            ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂(volume : Measure E)) := by
  let s : Set E := iocCube (d := d); let μ : Measure E := (volume : Measure E).restrict s
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ, s] using volume_iocCube_lt_top (d := d)⟩
  have hsum_norm : Summable (fun ℓ : Λ =>
      μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (summable_norm_translate_restrict (d := d) f (ball (d := d))).mul_left (μ.real Set.univ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hsum_norm
  simpa [μ, s, MeasureTheory.integral_const (μ := μ), smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
      (integrable_const ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖)
      (ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x hx => by
        have hmFourier : ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x)‖ ≤ 1 := by
          simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
            ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) (coeFunE (d := d) x)
        simpa using (mul_le_mul hmFourier
          (by simpa [translate_apply, ContinuousMap.restrict_apply] using
              ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict (ball (d := d)))
                ⟨x, iocCube_subset_closedBall (d := d) hx⟩ :
            ‖f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖)
          (norm_nonneg _) (by norm_num)).trans (one_mul _).le)

lemma mFourierCoeff_descended (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n =
      𝓕 (fun x : E => f x) (intVec (d := d) n) := by
  have hpull : (∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y) =
        ∫ x in iocCube (d := d), UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) •
            descended (d := d) f (coeFunE (d := d) x) ∂(volume : Measure E) :=
    integral_eq_integral_preimage_coeFunE
      (fun y => UnitAddTorus.mFourier (-n) y • descended f y)
      ((UnitAddTorus.mFourier (-n)).continuous.smul
        (descended (d := d) f).continuous).aestronglyMeasurable
  have hsum_int :
      (∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E)) =
        ∑' ℓ : Λ,
          ∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
    let s : Set E := iocCube (d := d)
    simpa [s, tsum_mul_left, mul_assoc] using
      (MeasureTheory.integral_tsum_of_summable_integral_norm
          (μ := (volume : Measure E).restrict s)
          (F := fun ℓ : Λ => fun x : E =>
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E)))
          (fun ℓ => by
            simpa [IntegrableOn, s] using
              (integrableOn_mFourier_mul_translate_iocCube (d := d) (f := f) n ℓ))
          (by simpa [s] using
            (summable_integral_norm_mFourier_mul_translate_iocCube (d := d) (f := f) n))).symm
  have hint : Integrable
      (fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x)
      (volume : Measure E) := by
    simpa using Integrable.bdd_mul (μ := (volume : Measure E))
      (SchwartzMap.integrable (μ := (volume : Measure E)) f)
      (((UnitAddTorus.mFourier (-n)).continuous.comp
        (continuous_coeFunE (d := d))).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) (coeFunE (d := d) x)))
  have hFD' : ∑' ℓ : Λ,
        ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
            f (x + (ℓ : E)) ∂(volume : Measure E) =
        ∫ x : E, UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
          ∂(volume : Measure E) := by
    let g : E → ℂ := fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
    have hterm : ∀ ℓ : Λ,
        (∫ x in iocCube (d := d), g (ℓ +ᵥ x) ∂(volume : Measure E)) =
            ∫ x in iocCube (d := d),
              UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
                f (x + (ℓ : E)) ∂(volume : Measure E) := fun ℓ =>
      integral_congr_ae <| ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x _ => by
        simp [g, Submodule.vadd_def, vadd_eq_add, add_comm,
          mFourier_neg_apply_coeFunE_add_standardLattice (d := d) (n := n) (ℓ := ℓ) (x := x)]
    simpa [g, hterm] using
      (MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'' (μ := (volume : Measure E))
        (isAddFundamentalDomain_iocCube (d := d)) (f := g) hint).symm
  calc
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n
        = ∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y := by
            simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
            haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
            simp [show (@volume (UnitAddTorus (Fin d))
                  (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                    (fun _ => instMeasureSpaceUnitAddCircle))) =
                (@volume (UnitAddTorus (Fin d))
                  (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                    (fun _ => AddCircle.measureSpace (1 : ℝ)))) from
              congrArg Measure.pi (funext fun _ => by
                change (AddCircle.haarAddCircle (T := (1 : ℝ)) : Measure UnitAddCircle) =
                  (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ)))
                simp [UnitAddCircle, AddCircle.volume_eq_smul_haarAddCircle])]
    _ = ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) •
            descended (d := d) f (coeFunE (d := d) x)
            ∂(volume : Measure E) := by
          simpa using hpull
    _ = ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
            (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E) :=
          integral_congr_ae <| ae_restrict_of_forall_mem (measurableSet_iocCube (d := d))
            fun _ _ => by simp [descended_comp (d := d) (f := f),
              periodized_apply (d := d) (f := f), smul_eq_mul]
    _ = ∑' ℓ : Λ,
          ∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
          simpa using hsum_int
    _ = ∫ x : E,
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
            ∂(volume : Measure E) := by
          simpa using hFD'
    _ = 𝓕 (fun x : E => f x) (intVec (d := d) n) := by
          simp [Real.fourier_eq, Circle.smul_def, smul_eq_mul,
            mFourier_neg_apply_coeFunE (d := d) (n := n)]

lemma summable_mFourierCoeff_descended :
    Summable (UnitAddTorus.mFourierCoeff (descended (d := d) f)) := by
  have hsum_norm : Summable (fun n : Fin d → ℤ =>
      ‖𝓕 (fun x : E => f x) (intVec (d := d) n)‖) := by
    let k : ℕ := d + 1
    have hk : Module.finrank ℤ Λ < k := by
      simp [show Module.finrank ℤ Λ = d from by
        simpa using (ZLattice.rank (K := ℝ) (L := Λ)).trans (by simp), k]
    obtain ⟨C, _, hC⟩ := (FourierTransform.fourierCLE ℂ (SchwartzMap E ℂ) f).decay k 0
    have hC' : ∀ x : E, ‖x‖ ^ k * ‖𝓕 (fun y : E => f y) x‖ ≤ C := by
      simpa [FourierTransform.fourierCLE_apply, fourier_coe, norm_iteratedFDeriv_zero] using hC
    have hsum_lattice : Summable (fun ℓ : Λ => ‖𝓕 (fun y : E => f y) (ℓ : E)‖) := by
      refine Summable.of_norm_bounded_eventually
        ((by simpa [k] using ZLattice.summable_norm_pow_inv (L := Λ) (n := k) hk :
          Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ))).mul_left C) ?_
      filter_upwards [(finite_norm_le_lattice (d := d) 1).compl_mem_cofinite] with ℓ hℓ
      simpa [Real.norm_of_nonneg (norm_nonneg _), div_eq_mul_inv, inv_pow, one_div] using
        (le_div_iff₀' (pow_pos (lt_trans (by positivity)
          (lt_of_not_ge (by simpa using hℓ) : (1 : ℝ) < ‖(ℓ : E)‖)) _)).2 (hC' (ℓ : E))
    simpa [equivIntVec] using
      hsum_lattice.comp_injective (equivIntVec (d := d)).injective
  exact Summable.of_norm (by simpa [mFourierCoeff_descended (d := d) (f := f)] using hsum_norm)

/-- Poisson summation for Schwartz functions over the standard lattice `ℤ^d`. -/
public theorem poissonSummation_standard (v : E) :
    (∑' ℓ : Λ, f (v + (ℓ : E))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : E => f x) (intVec (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, intVec (d := d) n⟫_[ℝ]) := by
  simpa [descended_comp (d := d) (f := f) v, periodized_apply (d := d) (f := f), smul_eq_mul,
    mFourierCoeff_descended (d := d) (f := f), mFourier_apply_coeFunE_exp (d := d), mul_assoc,
    mul_left_comm, mul_comm] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := descended (d := d) f)
        (summable_mFourierCoeff_descended (d := d) (f := f))
        (coeFunE (d := d) v)).tsum_eq.symm

end StandardPoissonSummation

end SchwartzMap.PoissonSummation.Standard

namespace SchwartzMap

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dual `ℤ`-lattice with respect to the Euclidean inner product. -/
public noncomputable abbrev dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E)) L

noncomputable def zBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℤ L :=
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  (Module.Free.chooseBasis ℤ L).reindex <| Fintype.equivOfCardEq <| by
    simpa [(ZLattice.rank (K := ℝ) (L := L)).trans (by simp : _ = d)] using
      (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm

noncomputable def rBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℝ E := (zBasis (d := d) L).ofZLatticeBasis ℝ L

noncomputable def stdBasis : Basis (Fin d) ℝ E := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

noncomputable def A (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] : E ≃ₗ[ℝ] E :=
  (stdBasis (d := d)).equiv (rBasis (d := d) L) (Equiv.refl (Fin d))

@[simp] lemma A_apply_stdBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin d) : (A (d := d) L) ((stdBasis (d := d)) i) = (rBasis (d := d) L) i := by
  simpa [A, stdBasis, rBasis] using Basis.equiv_apply
    (b := stdBasis (d := d)) (b' := rBasis (d := d) L) (e := Equiv.refl _) (i := i)

lemma map_standardLattice_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.map ((A (d := d) L).toLinearMap.restrictScalars ℤ)
        (SchwartzMap.standardLattice d) = L := calc
    Submodule.map ((A (d := d) L).toLinearMap.restrictScalars ℤ) (SchwartzMap.standardLattice d) =
        Submodule.span ℤ ((fun a : E => (A (d := d) L) a) '' Set.range (stdBasis (d := d))) := by
          simp [SchwartzMap.standardLattice, stdBasis, Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (rBasis (d := d) L)) := by
        rw [show (fun a : E => (A (d := d) L) a) '' (Set.range (stdBasis (d := d))) =
            Set.range (rBasis (d := d) L) from by
          simpa [show (fun a : E => (A (d := d) L) a) ∘ stdBasis (d := d) = rBasis (d := d) L from
            by funext i; simp [Function.comp]] using
            (Set.range_comp (g := fun a : E => (A (d := d) L) a) (f := stdBasis (d := d))).symm]
    _ = L := by simpa [rBasis] using
        Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := zBasis (d := d) L)

section CovolumeDet

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

lemma covolume_eq_abs_det_A :
    ZLattice.covolume L =
      abs ((LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) ((A L).toLinearMap)) := by
  have hvol : (volume : Measure E).real
      (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
    let f : E ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ
    simpa [show f ⁻¹' (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) =
        ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) by
      rw [show ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)) =
          f.toLinearEquiv '' ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
        from by simpa [show ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).map f.toLinearEquiv =
            Pi.basisFun ℝ (Fin d) from rfl] using
          (ZSpan.map_fundamentalDomain
            (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) f.toLinearEquiv).symm]
      exact Set.preimage_image_eq _ f.injective, ZSpan.volume_real_fundamentalDomain,
      show (Matrix.of (Pi.basisFun ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ) = 1 by
        ext; simp [Matrix.of_apply, Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]]
      using (show MeasurePreserving (fun x : E => (f x)) volume volume by
        simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
          PiLp.volume_preserving_ofLp (ι := Fin d)).measureReal_preimage
      (ZSpan.fundamentalDomain_measurableSet (b := (Pi.basisFun ℝ (Fin d)))).nullMeasurableSet
  have hr : rBasis (d := d) L = fun i : Fin d => (zBasis (d := d) L i : E) :=
    funext fun i => by simp [rBasis]
  have hcovol : ZLattice.covolume L =
      |(stdBasis (d := d)).det (fun i : Fin d => (zBasis (d := d) L i : E))| := by
    simpa [stdBasis, hvol] using
      ZLattice.covolume_eq_det_mul_measureReal (L := L) (b := zBasis (d := d) L)
        (b₀ := stdBasis (d := d)) (μ := (volume : Measure E))
  rw [hcovol, ← hr]; simp [A, stdBasis]

end CovolumeDet

section PoissonSummationLattices

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

noncomputable def Aₗ : E ≃ₗ[ℝ] E := A L
noncomputable def Bₗ : E →ₗ[ℝ] E := (Aₗ L).symm.toLinearMap.adjoint
noncomputable def Aadjₗ : E →ₗ[ℝ] E := (Aₗ L).toLinearMap.adjoint

noncomputable def equivStandardLattice : SchwartzMap.standardLattice d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (Aₗ L)).ofSubmodules (SchwartzMap.standardLattice d) L
    (by simpa [LinearEquiv.restrictScalars_apply] using map_standardLattice_eq (d := d) L)

@[simp] lemma equivStandardLattice_apply (x : SchwartzMap.standardLattice d) :
    ((equivStandardLattice (d := d) L x : L) : E) = (Aₗ L) x := by simp [equivStandardLattice]

lemma Bₗ_comp_Aadjₗ : (Bₗ L ∘ₗ Aadjₗ L) = (LinearMap.id : E →ₗ[ℝ] E) := by
  simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp,
    show (Aₗ L).toLinearMap ∘ₗ (Aₗ L).symm.toLinearMap = LinearMap.id from by ext x; simp]

noncomputable def adjointSymmEquiv : E ≃ₗ[ℝ] E where
  toLinearMap := Bₗ L
  invFun := Aadjₗ L
  left_inv x := by
    simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (show Aadjₗ L ∘ₗ Bₗ L = LinearMap.id by
      simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp,
        show (Aₗ L).symm.toLinearMap ∘ₗ (Aₗ L).toLinearMap = LinearMap.id from by ext x; simp])
  right_inv x := by simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Bₗ_comp_Aadjₗ L)

lemma map_standardLattice_adjointSymm_eq_dualSubmodule :
    Submodule.map ((Bₗ L).restrictScalars ℤ) (standardLattice d) = dualLattice (d := d) L := by
  ext x
  have hdualStd : dualLattice (d := d) (standardLattice d) = standardLattice d := by
    simpa [dualLattice] using PoissonSummation.Standard.dualSubmodule_standardLattice_eq (d := d)
  refine ⟨?_, fun hx => ⟨(Aadjₗ L) x, ?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ : (z : E) ∈
        Submodule.map ((Aₗ L).toLinearMap.restrictScalars ℤ) (standardLattice d) := by
      simpa [Aₗ, map_standardLattice_eq (d := d) L] using hz
    simpa [dualLattice, innerₗ_apply_apply,
      show inner ℝ ((Bₗ L) y) ((Aₗ L) w) = inner ℝ y w from by
        simpa [Bₗ, Aₗ] using LinearMap.adjoint_inner_left
          ((Aₗ L).symm.toLinearMap) ((Aₗ L) w) y] using
      (by simpa [hdualStd] using hy : y ∈ dualLattice (d := d) (standardLattice d)) w hw
  · suffices hydual : (Aadjₗ L) x ∈ dualLattice (d := d) (standardLattice d) by
      simpa [hdualStd] using hydual
    intro w hw
    have hwL : (Aₗ L) w ∈ L := by
      have : (Aₗ L) w ∈ Submodule.map ((Aₗ L).toLinearMap.restrictScalars ℤ)
          (standardLattice d) := ⟨w, hw, rfl⟩
      simpa [Aₗ, map_standardLattice_eq (d := d) L] using this
    simpa [dualLattice, innerₗ_apply_apply,
      show inner ℝ ((Aadjₗ L) x) w = inner ℝ x ((Aₗ L) w) from by
        simpa [Aadjₗ, Aₗ] using LinearMap.adjoint_inner_left ((Aₗ L).toLinearMap) w x] using
      hx ((Aₗ L) w) hwL
  · simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Bₗ_comp_Aadjₗ L)

/-- Poisson summation over a full-rank `ℤ`-lattice `L`. -/
public theorem poissonSummation_lattice (f : SchwartzMap E ℂ) (v : E) :
    (∑' ℓ : L, f (v + (ℓ : E))) =
      (1 / ZLattice.covolume L) *
        ∑' m : dualLattice (d := d) L,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
  let A : E ≃ₗ[ℝ] E := Aₗ L
  let g : SchwartzMap E ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hlhs :
      (∑' ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E))) =
        ∑' ℓ : L, f (v + (ℓ : E)) := by
    rw [tsum_congr (fun ℓ : SchwartzMap.standardLattice d => by simp [g, map_add] :
      ∀ ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E)) = f (v + A (ℓ : E)))]
    simpa [equivStandardLattice_apply] using
      (equivStandardLattice (d := d) L).toEquiv.tsum_eq (f := fun ℓ : L => f (v + (ℓ : E)))
  have hrhs :
      (∑' n : Fin d → ℤ,
          (𝓕 (fun x : E => g x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)) *
            Complex.exp
              (2 * π * Complex.I *
                ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.intVec (d := d) n⟫_[ℝ])) =
        (1 / ZLattice.covolume L) *
          ∑' m : dualLattice (d := d) L,
            (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
    let F : dualLattice (d := d) L → ℂ :=
      fun m => (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ])
    let detA : ℝ := (LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) (A : E →ₗ[ℝ] E)
    let cC : ℂ := ((abs detA)⁻¹ : ℝ)
    let iv : (Fin d → ℤ) → E := SchwartzMap.PoissonSummation.Standard.intVec (d := d)
    have hfourier (w : E) : 𝓕 (fun x : E => g x) w =
        cC * 𝓕 (fun x : E => f x) ((Bₗ L) w) := by
      simpa [g, A, Bₗ, detA, cC, Complex.real_smul] using
        SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
          (A := A) (f := fun x : E => f x) w
    have hexp (w : E) :
        Complex.exp (2 * π * Complex.I * ⟪A.symm v, w⟫_[ℝ]) =
          Complex.exp (2 * π * Complex.I * ⟪v, (Bₗ L) w⟫_[ℝ]) := by
      simp [show ⟪A.symm v, w⟫_[ℝ] = ⟪v, (Bₗ L) w⟫_[ℝ] by
        simpa [RCLike.inner_eq_wInner_one, A, Bₗ] using
          (LinearMap.adjoint_inner_right ((A.symm : E ≃ₗ[ℝ] E).toLinearMap) v w).symm]
    rw [show (∑' n : Fin d → ℤ, (𝓕 (fun x : E => g x) (iv n)) *
            Complex.exp (2 * π * Complex.I * ⟪A.symm v, iv n⟫_[ℝ])) =
          cC * ∑' m : dualLattice (d := d) L, F m from by
      rw [← (PoissonSummation.Standard.equivIntVec.trans
        ((LinearEquiv.restrictScalars ℤ (adjointSymmEquiv L)).ofSubmodules _ _ <| by
            simpa [LinearEquiv.restrictScalars_apply] using
              map_standardLattice_adjointSymm_eq_dualSubmodule (d := d)
                (L := L)).toEquiv).tsum_eq (f := F), ← tsum_mul_left]
      exact tsum_congr fun n ↦ by
        simpa [F, mul_assoc] using congrArg₂ (· * ·) (hfourier (w := iv n)) (hexp (w := iv n))]
    simp [F, cC, show ZLattice.covolume L = abs detA from by
      simpa [A, Aₗ, detA] using covolume_eq_abs_det_A (d := d) (L := L), one_div]
  simpa [hlhs, hrhs] using SchwartzMap.PoissonSummation.Standard.poissonSummation_standard
    (d := d) (f := g) (v := A.symm v)

end SchwartzMap.PoissonSummationLattices

module
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

/-! Poisson summation for full-rank `ℤ`-lattices in Euclidean space (Cohn-Elkies). -/

open scoped BigOperators Real
open MeasureTheory

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

/-
Copyright (c) 2026 Auguste Poiroux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Auguste Poiroux
-/
module
public import Mathlib

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
  have hmap : Measure.map (⇑A) (volume : Measure V) =
      ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (LinearEquiv.isUnit_det' A).ne_zero
  have hinner (y : V) :
      inner ℝ (A.symm y) w = inner ℝ y (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) :=
    (LinearMap.adjoint_inner_right _ y w).symm
  calc 𝓕 (fun x ↦ f (A x)) w
      = ∫ y, Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y
          ∂Measure.map (⇑A) (volume : Measure V) := by
        simpa [Real.fourier_eq] using
          (integral_map_equiv (μ := (volume : Measure V))
            A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
            fun y ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y).symm
    _ = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ •
          ∫ y, Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
    _ = _ := by simp only [Real.fourier_eq, hinner]

end SpherePacking.ForMathlib.Fourier

namespace SchwartzMap.UnitAddTorus

/-- The coordinatewise quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n`. Kept as a named definition: it is the
fundamental projection presenting the torus as a quotient of `ℝ^n`, with its own continuity, open-
quotient, and integral-pullback API. -/
public def coeFun (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

/-- The coordinatewise quotient map `coeFun` is continuous. -/
@[continuity, fun_prop]
public theorem continuous_coeFun {n : ℕ} : Continuous (coeFun n) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

/-- `coeFun` is an open quotient map, so it presents `(ℝ/ℤ)^n` as a quotient of `ℝ^n`. -/
public theorem isOpenQuotientMap_coeFun (n : ℕ) : IsOpenQuotientMap (coeFun n) :=
  .piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

/-- Evaluate the additive character `mFourier k` on a point `x : ℝ^n` viewed in the torus
via `coeFun`. -/
public theorem mFourier_apply_coeFun_ofLp (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coeFun n (WithLp.ofLp x)) =
      Complex.exp (2 * π * Complex.I * (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simp [UnitAddTorus.mFourier, coeFun, ← Complex.exp_sum, Finset.mul_sum, mul_assoc]

/-- Pull back Haar integration on `(ℝ/ℤ)^n` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^n`. -/
public theorem integral_eq_integral_preimage_coeFun (n : ℕ) (t : ℝ) (g : UnitAddTorus (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coeFun n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp : MeasurePreserving (coeFun n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) :=
    measurePreserving_pi _ _ fun _ => UnitAddCircle.measurePreserving_mk t
  have hrestrict : (volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) :=
    Measure.restrict_pi_pi _ _
  rw [hrestrict, ← hmp.map_eq]
  exact integral_map hmp.aemeasurable (hmp.map_eq.symm ▸ hg)

end SchwartzMap.UnitAddTorus

namespace SchwartzMap

variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

local notation "E" => EuclideanSpace ℝ (Fin d)

section StandardLattice

/-- The standard `ℤ`-lattice in `E = ℝ^d`, i.e. the span of the standard basis over `ℤ`. Kept as a
named definition: it is the base lattice to which every full-rank lattice is reduced, and the
domain of all the periodization/descent machinery. -/
@[expose] public def standardLattice (d : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))

namespace standardLattice

public instance instDiscreteTopology : DiscreteTopology (standardLattice d) :=
  inferInstanceAs <| DiscreteTopology (Submodule.span ℤ (Set.range _))

public instance instIsZLattice : IsZLattice ℝ (standardLattice d) :=
  inferInstanceAs <| IsZLattice ℝ (Submodule.span ℤ (Set.range _))

end StandardLattice.standardLattice

namespace PoissonSummation

namespace Standard

/-- Embed an integer vector `k : ℤ^d` into `E = ℝ^d`. Kept as a named definition: it is the
concrete parametrization of the standard lattice (`equivIntVec`) used pervasively to index lattice
sums and Fourier coefficients. -/
@[expose] public noncomputable def intVec (k : Fin d → ℤ) : E :=
  WithLp.toLp 2 fun i ↦ (k i : ℝ)

/-- The `i`-th coordinate of `intVec k` is `(k i : ℝ)`. -/
@[simp] public lemma intVec_apply (k : Fin d → ℤ) (i : Fin d) :
    intVec (d := d) k i = (k i : ℝ) := rfl

@[simp] lemma intVec_neg (k : Fin d → ℤ) : intVec (d := d) (-k) = -intVec (d := d) k := by
  ext i; simp [intVec_apply]

/-- Every integer vector lies in the standard lattice. -/
public lemma intVec_mem_standardLattice (k : Fin d → ℤ) :
    intVec (d := d) k ∈ SchwartzMap.standardLattice d :=
  (Module.Basis.mem_span_iff_repr_mem ℤ _ _).2 fun i ↦ ⟨k i, rfl⟩

open TopologicalSpace UnitAddTorus

/-- The half-open cube `(0,1]^d`. Kept as a named definition: it is the explicit fundamental domain
for `ℤ^d` (`isAddFundamentalDomain_iocCube`) over which every torus integral is unfolded. -/
public def iocCube : Set E := {x | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- The half-open cube `(0,1]^d` is measurable. -/
public lemma measurableSet_iocCube : MeasurableSet (iocCube (d := d)) := by
  unfold iocCube
  measurability

/-- Every element of the standard lattice comes from an integer vector via `intVec`. -/
public lemma exists_intVec_eq_of_mem_standardLattice (x : E)
    (hx : x ∈ SchwartzMap.standardLattice d) : ∃ n : Fin d → ℤ, x = intVec (d := d) n := by
  choose n hn using ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.mem_span_iff_repr_mem ℤ x).1 hx
  exact ⟨n, PiLp.ext fun i => (hn i).symm⟩

/-- The dual of the standard lattice (for the Euclidean inner product) is the standard lattice. -/
public lemma dualSubmodule_standardLattice_eq :
    LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E))
        (SchwartzMap.standardLattice d) = SchwartzMap.standardLattice d := by
  ext x
  constructor
  · intro hx
    have hcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = x i := fun i ↦ by
      have hmem : x i ∈ (1 : Submodule ℤ ℝ) := by
        simpa [innerₗ_apply_apply, EuclideanSpace.inner_single_right] using
          hx (EuclideanSpace.basisFun (Fin d) ℝ i) (Submodule.subset_span ⟨i, by simp⟩)
      obtain ⟨n, hn⟩ := Submodule.mem_one.mp hmem
      exact ⟨n, by simpa using hn⟩
    choose n hn using hcoord
    have hx_eq : x = intVec (d := d) n := by ext i; simp [hn i]
    exact hx_eq ▸ intVec_mem_standardLattice (d := d) n
  · intro hx y hy
    obtain ⟨n, rfl⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) x hx
    obtain ⟨m, rfl⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) y hy
    exact Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i,
      by simp [innerₗ_apply_apply, PiLp.inner_apply, mul_comm]⟩

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d` (the `EuclideanSpace`/`WithLp` form of `coeFun`). Kept as
a named definition: it is the quotient map through which the periodization descends to the torus,
with its own continuity and open-quotient API. -/
@[expose] public def coeFunE : E → UnitAddTorus (Fin d) :=
  fun x ↦ UnitAddTorus.coeFun d (WithLp.ofLp x)

/-- Continuity of the quotient map `coeFunE`. -/
@[continuity] public theorem continuous_coeFunE : Continuous (coeFunE (d := d)) :=
  UnitAddTorus.continuous_coeFun.comp (PiLp.continuous_ofLp _ _)

/-- `coeFunE` is invariant under translation by integer vectors. -/
@[simp] public theorem coeFunE_add_intVec (x : E) (n : Fin d → ℤ) :
    coeFunE (d := d) (x + intVec (d := d) n) = coeFunE (d := d) x := by
  ext i; simp [coeFunE, UnitAddTorus.coeFun]

/-- If two points map to the same torus point, their difference is an integer vector. -/
public theorem exists_intVec_eq_sub_of_coeFunE_eq {x y : E}
    (h : coeFunE (d := d) x = coeFunE (d := d) y) :
    ∃ n : Fin d → ℤ, x - y = intVec (d := d) n := by
  have key (i : Fin d) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
    have h0 : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      simpa [UnitAddCircle, AddCircle.coe_sub, coeFunE, UnitAddTorus.coeFun] using
        sub_eq_zero.2 (congrFun h i)
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
    exact ⟨n, by simpa using hn⟩
  choose n hn using key
  exact ⟨n, by ext i; simp [intVec, hn i]⟩

/-- The cube `iocCube` is a fundamental domain for translation by the standard lattice. -/
public theorem isAddFundamentalDomain_iocCube :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.standardLattice d)
      (iocCube (d := d)) (volume : Measure E) := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'
    (measurableSet_iocCube (d := d)).nullMeasurableSet fun x ↦ ?_
  choose n hn huniq using fun i : Fin d ↦ by
    simpa [one_smul, add_assoc] using
      existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ)) (c := (0 : ℝ))
  have hmem : x + intVec (d := d) n ∈ iocCube (d := d) := fun i ↦ by
    simpa [intVec_apply, zsmul_one] using hn i
  have hmem_unique : ∀ n' : Fin d → ℤ, x + intVec (d := d) n' ∈ iocCube (d := d) → n' = n :=
    fun n' hn' ↦ funext fun i ↦ huniq i (n' i) (by simpa [intVec_apply, zsmul_one] using hn' i)
  refine ⟨⟨intVec (d := d) n, intVec_mem_standardLattice (d := d) n⟩, ?_, fun ℓ hℓ ↦ ?_⟩
  · change (⟨intVec n, _⟩ : ↥(standardLattice d)) +ᵥ x ∈ iocCube
    rwa [Submodule.vadd_def, vadd_eq_add, add_comm]
  · obtain ⟨n', hn'⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (ℓ : E) ℓ.property
    have hℓ' : x + intVec (d := d) n' ∈ iocCube (d := d) := by rw [add_comm, ← hn']; exact hℓ
    exact Subtype.ext (hn'.trans (congrArg (intVec (d := d)) (hmem_unique n' hℓ')))

/-- Pull back Haar integration on `(ℝ/ℤ)^d` to `iocCube` in `E = ℝ^d`. -/
public theorem integral_eq_integral_preimage_coeFunE (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (coeFunE (d := d) x) ∂(volume : Measure E).restrict (iocCube (d := d)) := by
  -- `f` is the measure-preserving identification `ℝ^d ≃ᵐ E`, used to transport the cube integral.
  let f : (Fin d → ℝ) ≃ᵐ E := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (⇑f) (volume : Measure (Fin d → ℝ)) (volume : Measure E) := by
    simpa [f] using PiLp.volume_preserving_toLp (ι := Fin d)
  have hpre : f ⁻¹' iocCube (d := d) = Set.univ.pi fun _ : Fin d ↦ Set.Ioc (0 : ℝ) 1 := by
    ext x; simp [f, iocCube]
  calc
    (∫ y : UnitAddTorus (Fin d), g y)
        = ∫ x, g (UnitAddTorus.coeFun d x) ∂(volume : Measure (Fin d → ℝ)).restrict
            (Set.univ.pi fun _ : Fin d ↦ Set.Ioc (0 : ℝ) 1) := by
          simpa using UnitAddTorus.integral_eq_integral_preimage_coeFun d 0 g hg
    _ = ∫ y, g (coeFunE (d := d) y) ∂(volume : Measure E).restrict (iocCube (d := d)) := by
          simpa [hpre, coeFunE] using
            (hmp.restrict_preimage (measurableSet_iocCube (d := d))).integral_comp'
              (g := fun y : E ↦ g (UnitAddTorus.coeFun d (WithLp.ofLp y)))

end SchwartzMap.PoissonSummation.Standard

open Module UnitAddTorus

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

/-- The canonical equivalence between integer vectors `Fin d → ℤ` and the standard lattice
`Λ = ℤ^d ⊆ ℝ^d`. Kept as a named definition: it reindexes sums over the lattice as sums over
`ℤ^d`, both for Schwartz-decay summability and for the dual-lattice change of variables. -/
@[expose] public noncomputable def equivIntVec : (Fin d → ℤ) ≃ Λ :=
  Equiv.ofBijective
    (fun n : Fin d → ℤ => ⟨intVec (d := d) n, intVec_mem_standardLattice (d := d) n⟩) <| by
    refine ⟨fun a b hab => funext fun i => ?_, fun ℓ => ?_⟩
    · simpa using congrArg (fun x : E => x i) (congrArg Subtype.val hab)
    · obtain ⟨n, hn⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (ℓ : E) ℓ.property
      exact ⟨n, Subtype.ext hn.symm⟩

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

public instance instMeasurableVAdd_standardLattice : MeasurableVAdd Λ E where
  measurable_const_vadd _ := by simp only [Submodule.vadd_def, vadd_eq_add]; fun_prop
  measurable_vadd_const _ := by simp only [Submodule.vadd_def, vadd_eq_add]; fun_prop

public instance instVAddInvariantMeasure_standardLattice :
    MeasureTheory.VAddInvariantMeasure Λ E (volume : Measure E) where
  measure_preimage_vadd _ _ _ := by
    simp [Submodule.vadd_def, vadd_eq_add, MeasureTheory.measure_preimage_add]

/-- Translate the Schwartz function `f` by a lattice vector, as a continuous map. Kept as a named
map: it carries the `ContinuousMap` structure used to take sup-norms over compacts and to assemble
`periodization` as a `tsum` of continuous maps. -/
@[expose] public noncomputable def translate (ℓ : Λ) : C(E, ℂ) :=
  (f : C(E, ℂ)).comp (ContinuousMap.addRight (ℓ : E))

@[simp] public lemma translate_apply (ℓ : Λ) (x : E) :
    translate (d := d) f ℓ x = f (x + (ℓ : E)) := rfl

/-- Only finitely many standard lattice points lie in a closed ball of radius `r`. -/
public lemma finite_norm_le_lattice (r : ℝ) :
    ({ℓ : Λ | ‖(ℓ : E)‖ ≤ r} : Set _).Finite := by
  have : DiscreteTopology (Λ).toAddSubgroup := inferInstanceAs (DiscreteTopology Λ)
  have hfin : (Metric.closedBall (0 : E) r ∩ ((Λ).toAddSubgroup : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  refine .of_finite_image (hfin.subset ?_) Subtype.coe_injective.injOn
  rintro _ ⟨ℓ, hℓ, rfl⟩
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hℓ, ℓ.2⟩

private lemma half_norm_le_norm_add {G : Type*} [SeminormedAddCommGroup G] {x ℓ : G} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hℓ : 2 * r < ‖ℓ‖) : 1 / 2 * ‖ℓ‖ ≤ ‖x + ℓ‖ := by
  have h : ‖ℓ‖ - ‖x‖ ≤ ‖x + ℓ‖ := by simpa [add_comm] using norm_sub_norm_le ℓ (-x)
  linarith

/-- Schwartz decay: sup norms of translates restricted to a compact `K` are summable. -/
public lemma summable_norm_translate_restrict (K : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : Λ => ‖(translate (d := d) f ℓ).restrict K‖) := by
  -- `k` is a decay order exceeding the lattice rank, so that `‖·‖⁻¹ ^ k` is summable over `Λ`.
  let k : ℕ := Module.finrank ℤ Λ + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  simp_rw [norm_iteratedFDeriv_zero] at hC
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  have hsum : Summable fun ℓ : Λ => ‖(ℓ : E)‖⁻¹ ^ k := by
    simpa [k] using ZLattice.summable_norm_pow_inv (L := Λ) k (Nat.lt_succ_self _)
  refine (hsum.mul_left (C * 2 ^ k)).of_norm_bounded_eventually ?_
  filter_upwards [(finite_norm_le_lattice (d := d) (max (2 * r) 1)).eventually_cofinite_notMem]
    with ℓ hℓ
  have hRlt : max (2 * r) 1 < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
  have hnorm_pos : 0 < ‖(ℓ : E)‖ := one_pos.trans_le ((le_max_right _ _).trans hRlt.le)
  rw [norm_norm]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun ⟨x, hxK⟩ => ?_
  have hxr : ‖x‖ ≤ r := by simpa using hrK hxK
  have hge : 1 / 2 * ‖(ℓ : E)‖ ≤ ‖x + (ℓ : E)‖ :=
    half_norm_le_norm_add hxr ((le_max_left _ _).trans_lt hRlt)
  have hpos : 0 < ‖x + (ℓ : E)‖ := (by positivity : (0 : ℝ) < 1 / 2 * ‖(ℓ : E)‖).trans_le hge
  have hinv : ‖x + (ℓ : E)‖⁻¹ ≤ 2 * ‖(ℓ : E)‖⁻¹ := by
    have h := inv_anti₀ (by positivity) hge
    rwa [mul_inv, one_div, inv_inv] at h
  calc ‖(translate (d := d) f ℓ) (⟨x, hxK⟩ : K)‖
      = ‖f (x + (ℓ : E))‖ := rfl
    _ ≤ C / ‖x + (ℓ : E)‖ ^ k := (le_div_iff₀' (pow_pos hpos k)).2 (hC _)
    _ = C * ‖x + (ℓ : E)‖⁻¹ ^ k := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ C * (2 * ‖(ℓ : E)‖⁻¹) ^ k := by gcongr
    _ = C * 2 ^ k * ‖(ℓ : E)‖⁻¹ ^ k := by rw [mul_pow, mul_assoc]

/-- The quotient map `coeFunE`, bundled as a continuous map. This packaging is what the
`IsQuotientMap.lift`/`FactorsThrough` API consumes when descending periodic maps to the torus. -/
@[expose] public noncomputable def coeFunEC : C(E, UnitAddTorus (Fin d)) :=
  ⟨coeFunE (d := d), continuous_coeFunE⟩

section Periodization

/-- The **periodization** of a Schwartz function `f` along the standard lattice `ℤ^d`, as a
continuous map `x ↦ ∑' n : ℤ^d, f (x + n)`. It is `ℤ^d`-periodic (`periodization_add_lattice`), so
it descends to the torus `(ℝ/ℤ)^d` (`descended`); its torus Fourier coefficients are the values of
`𝓕 f` on `ℤ^d`, which is the content of Poisson summation. -/
@[expose] public noncomputable def periodization : C(E, ℂ) :=
  ∑' ℓ : Λ, translate (d := d) f ℓ

public lemma periodization_apply (x : E) :
    periodization (d := d) f x = ∑' ℓ : Λ, f (x + (ℓ : E)) := by
  simpa [periodization, translate_apply] using
    (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
      (summable_norm_translate_restrict (d := d) f)) x).symm

/-- The periodization is invariant under translation by a lattice vector. -/
public lemma periodization_add_lattice (x : E) (ℓ : Λ) :
    periodization (d := d) f (x + (ℓ : E)) = periodization (d := d) f x := by
  rw [periodization_apply, periodization_apply]
  simpa [add_assoc] using (Equiv.addLeft ℓ).tsum_eq fun m : Λ ↦ f (x + (m : E))

/-- The periodization factors through the quotient `(ℝ/ℤ)^d`. -/
public lemma periodization_factorsThrough :
    Function.FactorsThrough (periodization (d := d) f) (coeFunEC (d := d)) := by
  intro x y hxy
  obtain ⟨n, hn⟩ := exists_intVec_eq_sub_of_coeFunE_eq (d := d) (by simpa [coeFunEC] using hxy)
  have hx : x = y + intVec (d := d) n := by rw [← hn]; abel
  rw [hx]
  exact periodization_add_lattice (d := d) f y ⟨_, intVec_mem_standardLattice (d := d) n⟩

end Periodization

/-- The quotient map `coeFunE : E → (ℝ/ℤ)^d` presents the torus as an open quotient of `E`. -/
public theorem isOpenQuotientMap_coeFunE : IsOpenQuotientMap (coeFunE (d := d)) := by
  simpa [coeFunE] using (UnitAddTorus.isOpenQuotientMap_coeFun d).comp
    (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin d ↦ ℝ)).isOpenQuotientMap

/-- Descend the periodization to a continuous function on the torus `(ℝ/ℤ)^d`. This bridges to the
torus Fourier theory: the Fourier coefficients of `descended f` are the values of `𝓕 f` on the
lattice. -/
@[expose] public noncomputable def descended : C(UnitAddTorus (Fin d), ℂ) :=
  isOpenQuotientMap_coeFunE.isQuotientMap.lift (periodization (d := d) f)
    (periodization_factorsThrough (d := d) (f := f))

/-- Compatibility of `descended` with `coeFunE`: pulling back along the quotient gives back the
periodization. -/
public lemma descended_comp (x : E) :
    descended (d := d) f (coeFunE (d := d) x) = periodization (d := d) f x :=
  congrArg (fun g : C(E, ℂ) => g x)
    (by simp [descended] :
      (descended (d := d) f).comp (coeFunEC (d := d)) = periodization (d := d) f)

public lemma mFourier_neg_apply_coeFunE (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) =
      (𝐞 (-(inner ℝ x (intVec (d := d) n))) : ℂ) := by
  have hinner : inner ℝ x (intVec (d := d) n) = ∑ i, (n i : ℝ) * (x.ofLp i : ℝ) := by
    simp [intVec, PiLp.inner_apply]
  rw [hinner]
  simp [coeFunE, UnitAddTorus.mFourier_apply_coeFun_ofLp, Real.fourierChar_apply,
    Finset.sum_neg_distrib, mul_assoc, mul_comm]

public lemma mFourier_apply_coeFunE_exp (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier n (coeFunE (d := d) x) =
      Complex.exp (2 * Real.pi * Complex.I * ⟪x, intVec (d := d) n⟫_[ℝ]) := by
  have h := mFourier_neg_apply_coeFunE (d := d) (n := -n) (x := x)
  simp only [neg_neg, intVec_neg, inner_neg_right] at h
  rw [h, ← RCLike.inner_eq_wInner_one]
  simp [Real.fourierChar_apply, mul_assoc, mul_comm]

public lemma mFourier_neg_apply_coeFunE_add_standardLattice (n : Fin d → ℤ) (ℓ : Λ) (x : E) :
    UnitAddTorus.mFourier (-n) (coeFunE (d := d) (x + (ℓ : E))) =
      UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) := by
  obtain ⟨m, hm⟩ := exists_intVec_eq_of_mem_standardLattice (d := d) (ℓ : E) ℓ.property
  rw [hm, coeFunE_add_intVec]

public lemma iocCube_subset_closedBall :
    iocCube (d := d) ⊆ Metric.closedBall (0 : E) (Real.sqrt d) := fun x hx => by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i : Fin d, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => pow_le_one₀ (norm_nonneg _) ?_
        rw [Real.norm_eq_abs, abs_of_pos (hx i).1]; exact (hx i).2
    _ = d := by simp

public lemma volume_iocCube_lt_top : (volume : Measure E) (iocCube (d := d)) < ⊤ :=
  ((Metric.isBounded_closedBall (x := (0 : E)) (r := Real.sqrt d)).subset
    (iocCube_subset_closedBall (d := d))).measure_lt_top

/-- The closed ball of radius `√d`, packaged as `Compacts E`; it contains the fundamental cube
`iocCube`. Kept as a named definition: it is the single compact on which the Schwartz-decay
summability `summable_norm_translate_restrict` is instantiated to bound the cube integrals. -/
def sqrtdBall : TopologicalSpace.Compacts E :=
  ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩

/-- On `iocCube`, the integrand `mFourier (-n) (coeFunE ·) * f (· + ℓ)` is bounded by the sup norm
of the translate `f (· + ℓ)` restricted to `sqrtdBall`. -/
lemma norm_mFourier_mul_translate_le (n : Fin d → ℤ) (ℓ : Λ) {x : E}
    (hx : x ∈ iocCube (d := d)) :
    ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E))‖ ≤
      ‖(translate (d := d) f ℓ).restrict (sqrtdBall (d := d))‖ := by
  rw [norm_mul]
  calc ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x)‖ * ‖f (x + (ℓ : E))‖
      ≤ 1 * ‖f (x + (ℓ : E))‖ := by
        gcongr
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n)) _
    _ = ‖f (x + (ℓ : E))‖ := one_mul _
    _ ≤ ‖(translate (d := d) f ℓ).restrict (sqrtdBall (d := d))‖ := by
        simpa [translate_apply, ContinuousMap.restrict_apply] using
          ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict (sqrtdBall (d := d)))
            ⟨x, iocCube_subset_closedBall (d := d) hx⟩

public lemma integrableOn_mFourier_mul_translate_iocCube (n : Fin d → ℤ) (ℓ : Λ) :
    IntegrableOn
        (fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E)))
        (iocCube (d := d)) (volume : Measure E) :=
  Measure.integrableOn_of_bounded (volume_iocCube_lt_top (d := d)).ne
    (((UnitAddTorus.mFourier (-n)).continuous.comp (continuous_coeFunE (d := d))).mul
        (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun _ hx =>
      norm_mFourier_mul_translate_le (d := d) f n ℓ hx)

section StandardPoissonSummation

open UnitAddTorus PoissonSummation.Standard

lemma summable_integral_norm_mFourier_mul_translate_iocCube (n : Fin d → ℤ) :
    Summable (fun ℓ : Λ => ∫ x in iocCube (d := d),
        ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E))‖
        ∂(volume : Measure E)) := by
  -- `μ` is the (finite) restriction of Lebesgue measure to the fundamental cube.
  set μ : Measure E := (volume : Measure E).restrict (iocCube (d := d)) with hμ
  have : IsFiniteMeasure μ := ⟨by simpa [hμ] using volume_iocCube_lt_top (d := d)⟩
  refine ((summable_norm_translate_restrict (d := d) f (sqrtdBall (d := d))).mul_left
    (μ.real Set.univ)).of_nonneg_of_le (fun _ => by positivity) fun ℓ => ?_
  calc ∫ x, ‖UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E))‖ ∂μ
      ≤ ∫ _, ‖(translate (d := d) f ℓ).restrict (sqrtdBall (d := d))‖ ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
          (ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x hx =>
            norm_mFourier_mul_translate_le (d := d) f n ℓ hx)
    _ = μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (sqrtdBall (d := d))‖ := by
        rw [integral_const, smul_eq_mul]

/-- The `n`-th torus Fourier coefficient of `descended f` is the integral over the unit cube
of `mFourier(-n)(coeFunE x)` times the periodization `∑' ℓ, f (x + ℓ)`. -/
private lemma mFourierCoeff_descended_eq_iocCube_integral (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n =
      ∫ x in iocCube (d := d),
        UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
          (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E) := by
  have hpull : (∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y) =
        ∫ x in iocCube (d := d), UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) •
            descended (d := d) f (coeFunE (d := d) x) ∂(volume : Measure E) :=
    integral_eq_integral_preimage_coeFunE
      (fun y => UnitAddTorus.mFourier (-n) y • descended f y)
      ((UnitAddTorus.mFourier (-n)).continuous.smul
        (descended (d := d) f).continuous).aestronglyMeasurable
  calc
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n
        = ∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y := by
            have hvol : (@volume (UnitAddTorus (Fin d))
                  (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                    (fun _ => instMeasureSpaceUnitAddCircle))) =
                @volume (UnitAddTorus (Fin d))
                  (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                    (fun _ => AddCircle.measureSpace (1 : ℝ))) :=
              congrArg Measure.pi (funext fun _ => by
                change (AddCircle.haarAddCircle (T := (1 : ℝ)) : Measure UnitAddCircle) =
                  @volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ))
                simp [UnitAddCircle, AddCircle.volume_eq_smul_haarAddCircle])
            simp [UnitAddTorus.mFourierCoeff, smul_eq_mul, hvol]
    _ = ∫ x in iocCube (d := d),
          UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) •
            descended (d := d) f (coeFunE (d := d) x)
            ∂(volume : Measure E) := by simpa using hpull
    _ = _ :=
          integral_congr_ae <| ae_restrict_of_forall_mem (measurableSet_iocCube (d := d))
            fun _ _ => by simp [descended_comp (d := d) (f := f),
              periodization_apply (d := d) (f := f), smul_eq_mul]

/-- The integral over the unit cube of `mFourier(-n)(coeFunE x)` times the periodization of `f`
equals the integral of `mFourier(-n)(coeFunE x) * f x` over the whole space, by swapping the
integral with the lattice sum and applying the fundamental-domain property of `iocCube`. -/
private lemma integral_iocCube_mFourier_periodization_eq_integral (n : Fin d → ℤ) :
    (∫ x in iocCube (d := d),
        UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
          (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E)) =
      ∫ x : E, UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x ∂(volume : Measure E) := by
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
  have hsum_int :
      (∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E)) =
        ∑' ℓ : Λ,
          ∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
    simpa [tsum_mul_left, mul_assoc] using
      (MeasureTheory.integral_tsum_of_summable_integral_norm
          (μ := (volume : Measure E).restrict (iocCube (d := d)))
          (F := fun ℓ : Λ => fun x : E =>
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f (x + (ℓ : E)))
          (fun ℓ => by
            simpa [IntegrableOn] using
              (integrableOn_mFourier_mul_translate_iocCube (d := d) (f := f) n ℓ))
          (summable_integral_norm_mFourier_mul_translate_iocCube (d := d) (f := f) n)).symm
  -- `g` is the full integrand, abbreviated for the fundamental-domain unfolding below.
  let g : E → ℂ := fun x : E => UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) * f x
  have hterm : ∀ ℓ : Λ,
      (∫ x in iocCube (d := d), g (ℓ +ᵥ x) ∂(volume : Measure E)) =
          ∫ x in iocCube (d := d),
            UnitAddTorus.mFourier (-n) (coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := fun ℓ =>
    integral_congr_ae <| ae_restrict_of_forall_mem (measurableSet_iocCube (d := d)) fun x _ => by
      simp [g, Submodule.vadd_def, vadd_eq_add, add_comm,
        mFourier_neg_apply_coeFunE_add_standardLattice (d := d) (n := n) (ℓ := ℓ) (x := x)]
  rw [hsum_int]
  simpa [g, hterm] using
    ((isAddFundamentalDomain_iocCube (d := d)).integral_eq_tsum'' g hint).symm

lemma mFourierCoeff_descended (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n =
      𝓕 (fun x : E => f x) (intVec (d := d) n) := by
  rw [mFourierCoeff_descended_eq_iocCube_integral (d := d) (f := f) (n := n),
      integral_iocCube_mFourier_periodization_eq_integral (d := d) (f := f) (n := n)]
  simp [Real.fourier_eq, Circle.smul_def, smul_eq_mul,
    mFourier_neg_apply_coeFunE (d := d) (n := n)]

lemma summable_mFourierCoeff_descended :
    Summable (UnitAddTorus.mFourierCoeff (descended (d := d) f)) := by
  have hsum_norm : Summable (fun n : Fin d → ℤ =>
      ‖𝓕 (fun x : E => f x) (intVec (d := d) n)‖) := by
    -- `k` is a decay order exceeding the lattice rank, so that `‖·‖⁻¹ ^ k` is summable.
    let k : ℕ := d + 1
    have hrank : Module.finrank ℤ Λ = d := by
      simpa using (ZLattice.rank (K := ℝ) (L := Λ)).trans (by simp)
    have hk : Module.finrank ℤ Λ < k := by simp [hrank, k]
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
    (∑' ℓ : Λ, f (v + (ℓ : E))) = ∑' n : Fin d → ℤ, 𝓕 (fun x : E => f x) (intVec (d := d) n) *
        Complex.exp (2 * Real.pi * Complex.I * ⟪v, intVec (d := d) n⟫_[ℝ]) := by
  simpa [descended_comp (d := d) (f := f) v, periodization_apply (d := d) (f := f), smul_eq_mul,
    mFourierCoeff_descended (d := d) (f := f), mFourier_apply_coeFunE_exp (d := d), mul_assoc,
    mul_left_comm, mul_comm] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := descended (d := d) f)
        (summable_mFourierCoeff_descended (d := d) (f := f))
        (coeFunE (d := d) v)).tsum_eq.symm

end StandardPoissonSummation

end SchwartzMap.PoissonSummation.Standard

namespace SchwartzMap

open SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dual `ℤ`-lattice with respect to the Euclidean inner product. Kept as a named abbreviation:
it is the index set of the spectral side of Poisson summation and is part of this file's public
API (used downstream in the linear-programming bound). -/
public noncomputable abbrev dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E)) L

/-- A `Fin d`-indexed integral basis of the `ℤ`-lattice `L` (Mathlib's `chooseBasis` reindexed
along `finrank ℤ L = d`). Kept as a named definition: a fixed integral frame for `L` whose
determinant against `stdBasis` computes the covolume. -/
noncomputable def zBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℤ L :=
  (Module.Free.chooseBasis ℤ L).reindex <| Fintype.equivOfCardEq <| by
    simpa [(ZLattice.rank (K := ℝ) (L := L)).trans (by simp : _ = d)] using
      (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm

/-- The `ℝ`-basis of `E` spanned by `zBasis L` (Mathlib's `Basis.ofZLatticeBasis`). Kept as a named
definition: the real frame realizing `L`, namely the image of `stdBasis` under `latticeEquiv L`. -/
noncomputable def rBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℝ E := (zBasis (d := d) L).ofZLatticeBasis ℝ L

/-- The standard basis of `E = ℝ^d` as an `ℝ`-basis, i.e. `(EuclideanSpace.basisFun _ _).toBasis`.
Kept as a named definition: the orthonormal reference frame (and `ℤ`-basis of the standard lattice)
against which the lattice determinant and covolume are measured. -/
noncomputable def stdBasis : Basis (Fin d) ℝ E := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-- The `ℝ`-linear automorphism of `E` sending the standard basis to `rBasis L`, hence the standard
lattice `ℤ^d` onto `L`. Kept as a named definition: it is the change-of-variables map underlying
the reduction of lattice Poisson summation to the standard-lattice case, used throughout this
section and reused via its adjoints `Bₗ`/`Aadjₗ`. -/
noncomputable def latticeEquiv (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    E ≃ₗ[ℝ] E := (stdBasis (d := d)).equiv (rBasis (d := d) L) (Equiv.refl (Fin d))

@[simp] lemma latticeEquiv_apply_stdBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin d) : latticeEquiv (d := d) L ((stdBasis (d := d)) i) = (rBasis (d := d) L) i :=
  Basis.equiv_apply (b := stdBasis (d := d)) (b' := rBasis (d := d) L) (e := Equiv.refl _) (i := i)

lemma map_standardLattice_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.map ((latticeEquiv (d := d) L).toLinearMap.restrictScalars ℤ)
        (SchwartzMap.standardLattice d) = L := by
  have hrange : (fun a : E => latticeEquiv (d := d) L a) '' Set.range (stdBasis (d := d)) =
      Set.range (rBasis (d := d) L) := by
    rw [← Set.range_comp]; simp [Function.comp_def]
  calc Submodule.map ((latticeEquiv (d := d) L).toLinearMap.restrictScalars ℤ)
          (SchwartzMap.standardLattice d)
      = Submodule.span ℤ ((fun a : E => latticeEquiv (d := d) L a) '' Set.range (stdBasis (d := d)))
        := by simp [SchwartzMap.standardLattice, stdBasis, Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (rBasis (d := d) L)) := by rw [hrange]
    _ = L := by
        simpa [rBasis] using Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := zBasis L)

/-- The standard fundamental domain in `E = ℝ^d` (the unit cube of the orthonormal standard
basis) has volume `1`. -/
private lemma volume_real_fundamentalDomain_basisFun :
    (volume : Measure E).real
      (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
  rw [measureReal_def, measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped
    (μ := (volume : Measure E)) ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))]
  simp [(EuclideanSpace.basisFun (Fin d) ℝ).volume_parallelepiped]

section CovolumeDet

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The covolume of `L` equals `|det (latticeEquiv L)|`: the map carrying the standard lattice
onto `L` scales the unit-covolume standard lattice by exactly its determinant. -/
lemma covolume_eq_abs_det_latticeEquiv :
    ZLattice.covolume L = |(LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) ((latticeEquiv L).toLinearMap)| := by
  have hr : rBasis (d := d) L = fun i : Fin d => (zBasis (d := d) L i : E) :=
    funext fun i => by simp [rBasis]
  have hcovol : ZLattice.covolume L =
      |(stdBasis (d := d)).det (fun i : Fin d => (zBasis (d := d) L i : E))| := by
    simpa [stdBasis, volume_real_fundamentalDomain_basisFun] using
      ZLattice.covolume_eq_det_mul_measureReal (L := L) (b := zBasis (d := d) L)
        (b₀ := stdBasis (d := d)) (μ := (volume : Measure E))
  rw [hcovol, ← hr]; simp [latticeEquiv, stdBasis]

end CovolumeDet

section PoissonSummationLattices

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The adjoint of `(latticeEquiv L)⁻¹`; it carries the standard lattice onto the dual lattice
`L*`, and is the engine of the change of variables on the spectral side of Poisson summation. -/
noncomputable def Bₗ : E →ₗ[ℝ] E := (latticeEquiv L).symm.toLinearMap.adjoint

/-- The adjoint of `latticeEquiv L`. Kept as a named definition: it is the two-sided inverse of
`Bₗ L`, supplying `adjointSymmEquiv` with its inverse map. -/
noncomputable def Aadjₗ : E →ₗ[ℝ] E := (latticeEquiv L).toLinearMap.adjoint

/-- `latticeEquiv L` restricted to a `ℤ`-linear equivalence from the standard lattice `ℤ^d` onto
`L`. Kept as a named definition: it transports lattice sums between `ℤ^d` and `L`. -/
noncomputable def equivStandardLattice : SchwartzMap.standardLattice d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (latticeEquiv L)).ofSubmodules (SchwartzMap.standardLattice d) L
    (by simpa [LinearEquiv.restrictScalars_apply] using map_standardLattice_eq (d := d) L)

@[simp] lemma equivStandardLattice_apply (x : SchwartzMap.standardLattice d) :
    ((equivStandardLattice (d := d) L x : L) : E) = (latticeEquiv L) x := by
  simp [equivStandardLattice]

lemma Bₗ_comp_Aadjₗ : Bₗ L ∘ₗ Aadjₗ L = (LinearMap.id : E →ₗ[ℝ] E) := by
  simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp,
    show (latticeEquiv L).toLinearMap ∘ₗ (latticeEquiv L).symm.toLinearMap = LinearMap.id from by
      ext x; simp]

lemma Aadjₗ_comp_Bₗ : Aadjₗ L ∘ₗ Bₗ L = (LinearMap.id : E →ₗ[ℝ] E) := by
  simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp,
    show (latticeEquiv L).symm.toLinearMap ∘ₗ (latticeEquiv L).toLinearMap = LinearMap.id from by
      ext x; simp]

/-- `Bₗ L` as a linear automorphism of `E`, with inverse `Aadjₗ L`. Kept as a named definition: it
realizes the standard-lattice-to-dual-lattice transport as an equivalence, so its `tsum_eq`
reindexes the spectral sum. -/
noncomputable def adjointSymmEquiv : E ≃ₗ[ℝ] E where
  toLinearMap := Bₗ L
  invFun := Aadjₗ L
  left_inv x := by simpa using DFunLike.congr_fun (Aadjₗ_comp_Bₗ L) x
  right_inv x := by simpa using DFunLike.congr_fun (Bₗ_comp_Aadjₗ L) x

lemma map_standardLattice_adjointSymm_eq_dualSubmodule :
    Submodule.map ((Bₗ L).restrictScalars ℤ) (standardLattice d) = dualLattice (d := d) L := by
  have hmapL : Submodule.map ((latticeEquiv L).toLinearMap.restrictScalars ℤ)
      (standardLattice d) = L := map_standardLattice_eq (d := d) L
  have hdualStd : dualLattice (d := d) (standardLattice d) = standardLattice d := by
    simpa [dualLattice] using PoissonSummation.Standard.dualSubmodule_standardLattice_eq (d := d)
  have hBA (y w : E) : inner ℝ ((Bₗ L) y) ((latticeEquiv L) w) = inner ℝ y w := by
    simpa [Bₗ] using LinearMap.adjoint_inner_left ((latticeEquiv L).symm.toLinearMap)
      ((latticeEquiv L) w) y
  have hAadj (p w : E) : inner ℝ ((Aadjₗ L) p) w = inner ℝ p ((latticeEquiv L) w) := by
    simpa [Aadjₗ] using LinearMap.adjoint_inner_left ((latticeEquiv L).toLinearMap) w p
  ext x
  refine ⟨?_, fun hx => ⟨(Aadjₗ L) x, ?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ : (z : E) ∈ Submodule.map ((latticeEquiv L).toLinearMap.restrictScalars ℤ)
        (standardLattice d) := by rw [hmapL]; exact hz
    simpa [dualLattice, innerₗ_apply_apply, hBA] using
      (by simpa [hdualStd] using hy : y ∈ dualLattice (d := d) (standardLattice d)) w hw
  · suffices hydual : (Aadjₗ L) x ∈ dualLattice (d := d) (standardLattice d) by
      simpa [hdualStd] using hydual
    intro w hw
    have hwL : (latticeEquiv L) w ∈ L := by
      have hmem : (latticeEquiv L) w ∈ Submodule.map
        ((latticeEquiv L).toLinearMap.restrictScalars ℤ) (standardLattice d) := ⟨w, hw, rfl⟩
      rwa [hmapL] at hmem
    simpa [dualLattice, innerₗ_apply_apply, hAadj] using hx ((latticeEquiv L) w) hwL
  · simpa using DFunLike.congr_fun (Bₗ_comp_Aadjₗ L) x

/-- LHS rewrite for `poissonSummation_lattice`: pull back the lattice sum along `latticeEquiv`. -/
private lemma poissonSummation_lattice_lhs (f : SchwartzMap E ℂ) (v : E) :
    (∑' ℓ : SchwartzMap.standardLattice d, f (v + (latticeEquiv L) (ℓ : E))) =
      ∑' ℓ : L, f (v + (ℓ : E)) := by
  simpa [equivStandardLattice_apply] using
    (equivStandardLattice (d := d) L).toEquiv.tsum_eq (f := fun ℓ : L => f (v + (ℓ : E)))

/-- Inner-product rewrite for exponentials: `⟪(latticeEquiv L).symm v, w⟫ = ⟪v, Bₗ L w⟫`. -/
private lemma poissonSummation_lattice_inner_swap (v w : E) :
    ⟪(latticeEquiv L).symm v, w⟫_[ℝ] = ⟪v, (Bₗ L) w⟫_[ℝ] := by
  simp only [← RCLike.inner_eq_wInner_one]
  simpa [Bₗ] using (LinearMap.adjoint_inner_right ((latticeEquiv L).symm.toLinearMap) v w).symm

/-- RHS rewrite for `poissonSummation_lattice`: descend the standard-lattice dual sum
to the dual lattice `L*` along `Bₗ = (latticeEquiv L).symm.adjoint`. -/
private lemma poissonSummation_lattice_rhs (f : SchwartzMap E ℂ) (v : E) :
    (∑' n : Fin d → ℤ,
        (𝓕 (fun x : E => f ((latticeEquiv L) x))
          (intVec (d := d) n)) *
          Complex.exp (2 * π * Complex.I *
            ⟪(latticeEquiv L).symm v, intVec (d := d) n⟫_[ℝ])) =
      (1 / ZLattice.covolume L) *
        ∑' m : dualLattice (d := d) L,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
  -- Abbreviations: the dual-lattice summand `F`, the determinant `detA` of the change of
  -- variables and its reciprocal `cC = |detA|⁻¹`, and the integer-vector embedding `iv`.
  let F : dualLattice (d := d) L → ℂ :=
    fun m => (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ])
  let detA : ℝ := (LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) ((latticeEquiv L) : E →ₗ[ℝ] E)
  let cC : ℂ := ((abs detA)⁻¹ : ℝ)
  let iv : (Fin d → ℤ) → E := intVec (d := d)
  have hfourier (w : E) : 𝓕 (fun x : E => f ((latticeEquiv L) x)) w =
      cC * 𝓕 (fun x : E => f x) ((Bₗ L) w) := by
    simpa [Bₗ, detA, cC, Complex.real_smul] using
      SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
        (A := latticeEquiv L) (f := fun x : E => f x) w
  have hreindex : (∑' n : Fin d → ℤ, (𝓕 (fun x : E => f ((latticeEquiv L) x)) (iv n)) *
        Complex.exp (2 * π * Complex.I * ⟪(latticeEquiv L).symm v, iv n⟫_[ℝ])) =
      cC * ∑' m : dualLattice (d := d) L, F m := by
    rw [← (PoissonSummation.Standard.equivIntVec.trans
      ((LinearEquiv.restrictScalars ℤ (adjointSymmEquiv L)).ofSubmodules _ _ <| by
          simpa [LinearEquiv.restrictScalars_apply] using
            map_standardLattice_adjointSymm_eq_dualSubmodule (d := d) (L := L)).toEquiv).tsum_eq
      (f := F), ← tsum_mul_left]
    exact tsum_congr fun n ↦ by
      simpa [F, mul_assoc, poissonSummation_lattice_inner_swap (L := L) v (w := iv n)] using
        congrArg (· * Complex.exp (2 * π * Complex.I * ⟪v, (Bₗ L) (iv n)⟫_[ℝ]))
          (hfourier (w := iv n))
  rw [hreindex]
  simp [F, cC, show ZLattice.covolume L = abs detA from by
    simpa [latticeEquiv, detA] using covolume_eq_abs_det_latticeEquiv (d := d) (L := L), one_div]

/-- Poisson summation over a full-rank `ℤ`-lattice `L`. -/
public theorem poissonSummation_lattice (f : SchwartzMap E ℂ) (v : E) :
    (∑' ℓ : L, f (v + (ℓ : E))) =
      (1 / ZLattice.covolume L) *
        ∑' m : dualLattice (d := d) L,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
  -- `A` is the change of variables `ℤ^d → L`; `g = f ∘ A` is again Schwartz.
  -- The local instance short-circuits a `ContinuousSMul ℝ E` search that otherwise loops on
  -- `EuclideanSpace`'s `PiLp` structure inside `LinearEquiv.toContinuousLinearEquiv`.
  have : ContinuousSMul ℝ E := inferInstance
  let A : E ≃ₗ[ℝ] E := latticeEquiv L
  let g : SchwartzMap E ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hlhs : (∑' ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E))) =
      ∑' ℓ : L, f (v + (ℓ : E)) := by
    have hg : ∀ ℓ : SchwartzMap.standardLattice d,
        g (A.symm v + (ℓ : E)) = f (v + A (ℓ : E)) := fun ℓ => by simp [g, map_add]
    rw [tsum_congr hg]
    exact poissonSummation_lattice_lhs (L := L) f v
  have hrhs : (∑' n : Fin d → ℤ,
        (𝓕 (fun x : E => g x) (intVec (d := d) n)) *
          Complex.exp (2 * π * Complex.I *
            ⟪A.symm v, intVec (d := d) n⟫_[ℝ])) =
      (1 / ZLattice.covolume L) *
        ∑' m : dualLattice (d := d) L,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
    simpa [g, A] using poissonSummation_lattice_rhs (L := L) f v
  simpa [hlhs, hrhs] using
    poissonSummation_standard
      (d := d) (f := g) (v := A.symm v)

end SchwartzMap.PoissonSummationLattices

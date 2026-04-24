module
public import SpherePacking.CohnElkies.PoissonSummationSchwartz.PoissonSummation
import SpherePacking.CohnElkies.PoissonSummationSchwartz.Basic
public import SpherePacking.ForMathlib.FourierLinearEquiv

public import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Poisson summation for general lattices

This file proves Poisson summation for Schwartz functions over a full-rank `ℤ`-lattice `L ⊆ ℝ^d`.
It provides the lattice statement used by `SpherePacking.CohnElkies.Prereqs`.

The proof transports the standard-lattice result from
`SpherePacking.CohnElkies.PoissonSummationSchwartz.PoissonSummation` along a linear equivalence
sending `ℤ^d` to the given lattice.
-/

open scoped BigOperators FourierTransform Real

open MeasureTheory Module

namespace SchwartzMap

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dual `ℤ`-lattice with respect to the Euclidean inner product. -/
public noncomputable abbrev dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E)) L

noncomputable def zBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℤ L := by
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hfinrank : Module.finrank ℤ L = d :=
    (ZLattice.rank (K := ℝ) (L := L)).trans (by simp)
  exact (Module.Free.chooseBasis ℤ L).reindex <| Fintype.equivOfCardEq <| by
    simpa [hfinrank] using (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm

noncomputable def rBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℝ E :=
  (zBasis (d := d) L).ofZLatticeBasis ℝ L

noncomputable def stdBasis : Basis (Fin d) ℝ E :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

noncomputable def A (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    E ≃ₗ[ℝ] E :=
  (stdBasis (d := d)).equiv (rBasis (d := d) L) (Equiv.refl (Fin d))

@[simp] lemma A_apply_stdBasis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin d) : (A (d := d) L) ((stdBasis (d := d)) i) = (rBasis (d := d) L) i := by
  simpa [A, stdBasis, rBasis] using
    Basis.equiv_apply (b := stdBasis (d := d)) (b' := rBasis (d := d) L) (e := Equiv.refl _)
      (i := i)

lemma map_standardLattice_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.map ((A (d := d) L).toLinearMap.restrictScalars ℤ)
        (SchwartzMap.standardLattice d) = L := by
  have himage :
      (fun a : E => (A (d := d) L) a) '' (Set.range (stdBasis (d := d))) =
        Set.range (rBasis (d := d) L) := by
    simpa [show (fun a : E => (A (d := d) L) a) ∘ stdBasis (d := d) = rBasis (d := d) L from by
      funext i; simp [Function.comp]] using
      (Set.range_comp (g := fun a : E => (A (d := d) L) a) (f := stdBasis (d := d))).symm
  calc
    Submodule.map ((A (d := d) L).toLinearMap.restrictScalars ℤ) (SchwartzMap.standardLattice d) =
        Submodule.span ℤ ((fun a : E => (A (d := d) L) a) '' Set.range (stdBasis (d := d))) := by
          simp [SchwartzMap.standardLattice, stdBasis, Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (rBasis (d := d) L)) := by rw [himage]
    _ = L := by
      simpa [rBasis] using
        Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := zBasis (d := d) L)

section FundamentalDomain

lemma volume_real_fundamentalDomain_stdBasis :
    (volume : Measure E).real
        (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
  let f : E ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ
  have hf : MeasurePreserving (fun x : E => (f x)) volume volume := by
    simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
      PiLp.volume_preserving_ofLp (ι := Fin d)
  have himage :
      f.toLinearEquiv '' ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) =
        ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)) := by
    simpa [show ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).map f.toLinearEquiv =
        Pi.basisFun ℝ (Fin d) from rfl] using
      ZSpan.map_fundamentalDomain
        (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) f.toLinearEquiv
  have hpre :
      f ⁻¹' (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) =
        ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) := by
    simpa
        [Set.preimage_image_eq (f := fun x : E => f x)
          (s := ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))
          f.injective]
      using congrArg (fun s => (fun x : E => f x) ⁻¹' s) himage.symm
  have hcube : (volume : Measure (Fin d → ℝ)).real
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) = 1 := by
    simp [ZSpan.volume_real_fundamentalDomain,
      show (Matrix.of (Pi.basisFun ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ) = 1 by
        ext i j
        simp [Matrix.of_apply, Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]]
  simpa [hpre, hcube] using hf.measureReal_preimage
    (ZSpan.fundamentalDomain_measurableSet (b := (Pi.basisFun ℝ (Fin d)))).nullMeasurableSet

end FundamentalDomain

section CovolumeDet

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

lemma covolume_eq_abs_det_A :
    ZLattice.covolume L =
      abs ((LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) ((A L).toLinearMap)) := by
  let bZ : Basis (Fin d) ℤ L := zBasis L
  have hr : rBasis (d := d) L = fun i : Fin d => (bZ i : E) := by funext i; simp [rBasis, bZ]
  have hcovol : ZLattice.covolume L =
      |(stdBasis (d := d)).det (fun i : Fin d => (bZ i : E))| := by
    simpa [stdBasis, volume_real_fundamentalDomain_stdBasis (d := d)] using
      ZLattice.covolume_eq_det_mul_measureReal
        (L := L) (b := bZ) (b₀ := stdBasis (d := d)) (μ := (volume : Measure E))
  rw [hcovol, ← hr]; simp [A, stdBasis]

end CovolumeDet

section PoissonSummationLattices

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

noncomputable def Aₗ : E ≃ₗ[ℝ] E := A (d := d) L

noncomputable def Bₗ : E →ₗ[ℝ] E := ((Aₗ (d := d) (L := L)).symm.toLinearMap).adjoint

noncomputable def Aadjₗ : E →ₗ[ℝ] E := ((Aₗ (d := d) (L := L)).toLinearMap).adjoint

noncomputable def equivStandardLattice : SchwartzMap.standardLattice d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (Aₗ (d := d) (L := L))).ofSubmodules
    (SchwartzMap.standardLattice d) L
    (by simpa [LinearEquiv.restrictScalars_apply] using map_standardLattice_eq (d := d) L)

@[simp]
lemma equivStandardLattice_apply (x : SchwartzMap.standardLattice d) :
    ((equivStandardLattice (d := d) L x : L) : E) = (Aₗ (d := d) (L := L)) x := by
  simp [equivStandardLattice]

lemma Bₗ_comp_Aadjₗ :
    (Bₗ (d := d) L ∘ₗ Aadjₗ (d := d) L) = (LinearMap.id : E →ₗ[ℝ] E) := by
  have h : (Aₗ (d := d) (L := L)).toLinearMap ∘ₗ
      (Aₗ (d := d) (L := L)).symm.toLinearMap = LinearMap.id := by ext x; simp
  simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp, h]

lemma Aadjₗ_comp_Bₗ :
    (Aadjₗ (d := d) L ∘ₗ Bₗ (d := d) L) = (LinearMap.id : E →ₗ[ℝ] E) := by
  have h : (Aₗ (d := d) (L := L)).symm.toLinearMap ∘ₗ
      (Aₗ (d := d) (L := L)).toLinearMap = LinearMap.id := by ext x; simp
  simp [Bₗ, Aadjₗ, ← LinearMap.adjoint_comp, h]

noncomputable def adjointSymmEquiv : E ≃ₗ[ℝ] E :=
  { toLinearMap := Bₗ (d := d) L
    invFun := Aadjₗ (d := d) L
    left_inv := fun x => by
      simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Aadjₗ_comp_Bₗ (d := d) (L := L))
    right_inv := fun x => by
      simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Bₗ_comp_Aadjₗ (d := d) (L := L)) }

lemma map_standardLattice_adjointSymm_eq_dualSubmodule :
    Submodule.map ((Bₗ (d := d) L).restrictScalars ℤ) (standardLattice d) =
      dualLattice (d := d) L := by
  ext x
  have hdualStd : dualLattice (d := d) (standardLattice d) = standardLattice d := by
    simpa [dualLattice] using PoissonSummation.Standard.dualSubmodule_standardLattice_eq (d := d)
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ : (z : E) ∈
        Submodule.map ((Aₗ (d := d) L).toLinearMap.restrictScalars ℤ) (standardLattice d) := by
      simpa [Aₗ, map_standardLattice_eq (d := d) L] using hz
    have hydual : y ∈ dualLattice (d := d) (standardLattice d) := by simpa [hdualStd] using hy
    have hinter : inner ℝ ((Bₗ (d := d) L) y) ((Aₗ (d := d) (L := L)) w) = inner ℝ y w := by
      simpa [Bₗ, Aₗ] using
        LinearMap.adjoint_inner_left ((Aₗ (d := d) (L := L)).symm.toLinearMap)
          ((Aₗ (d := d) (L := L)) w) y
    simpa [dualLattice, innerₗ_apply_apply, hinter] using hydual w hw
  · refine ⟨(Aadjₗ (d := d) L) x, ?_, ?_⟩
    · have hydual : (Aadjₗ (d := d) L) x ∈ dualLattice (d := d) (standardLattice d) := by
        intro w hw
        have hwL : (Aₗ (d := d) (L := L)) w ∈ L := by
          have : (Aₗ (d := d) (L := L)) w ∈
              Submodule.map (((Aₗ (d := d) (L := L)).toLinearMap).restrictScalars ℤ)
                (standardLattice d) := ⟨w, hw, rfl⟩
          simpa [Aₗ, map_standardLattice_eq (d := d) L] using this
        have hinner : inner ℝ ((Aadjₗ (d := d) L) x) w = inner ℝ x ((Aₗ (d := d) (L := L)) w) := by
          simpa [Aadjₗ, Aₗ] using
            LinearMap.adjoint_inner_left ((Aₗ (d := d) (L := L)).toLinearMap) w x
        simpa [dualLattice, innerₗ_apply_apply, hinner] using hx ((Aₗ (d := d) (L := L)) w) hwL
      simpa [hdualStd] using hydual
    · simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) (Bₗ_comp_Aadjₗ (d := d) (L := L))

noncomputable def equivStandardLatticeToDual :
    SchwartzMap.standardLattice d ≃ₗ[ℤ] dualLattice (d := d) L :=
  (LinearEquiv.restrictScalars ℤ (adjointSymmEquiv (d := d) (L := L))).ofSubmodules
    (SchwartzMap.standardLattice d) (dualLattice (d := d) L) <| by
      simpa [LinearEquiv.restrictScalars_apply] using
        map_standardLattice_adjointSymm_eq_dualSubmodule (d := d) (L := L)

noncomputable def equivIntVecToDual : (Fin d → ℤ) ≃ dualLattice (d := d) L :=
  (PoissonSummation.Standard.equivIntVec (d := d)).trans
    (equivStandardLatticeToDual (d := d) L).toEquiv

@[simp]
lemma equivStandardLatticeToDual_apply (x : SchwartzMap.standardLattice d) :
    ((equivStandardLatticeToDual (d := d) L x : dualLattice (d := d) L) : E) =
      (Bₗ (d := d) L) x := by simp [equivStandardLatticeToDual, adjointSymmEquiv]

@[simp]
lemma equivIntVecToDual_coe (n : Fin d → ℤ) :
    ((equivIntVecToDual (d := d) L n : dualLattice (d := d) L) : E) =
      (Bₗ (d := d) L) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) := by
  simp [equivIntVecToDual]

/--
Poisson summation over a full-rank `ℤ`-lattice `L`.

The sum of a Schwartz function over `L` is expressed as a (normalized) sum of its Fourier transform
over the dual lattice.
-/
public theorem poissonSummation_lattice (f : SchwartzMap E ℂ) (v : E) :
    (∑' ℓ : L, f (v + (ℓ : E))) =
      (1 / ZLattice.covolume L) *
        ∑' m : dualLattice (d := d) L,
          (𝓕 (fun x : E => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
  let A : E ≃ₗ[ℝ] E := Aₗ (d := d) (L := L)
  let g : SchwartzMap E ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hstd :=
    SchwartzMap.PoissonSummation.Standard.poissonSummation_standard
      (d := d) (f := g) (v := A.symm v)
  have hlhs :
      (∑' ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E))) =
        ∑' ℓ : L, f (v + (ℓ : E)) := calc
    (∑' ℓ : SchwartzMap.standardLattice d, g (A.symm v + (ℓ : E))) =
        ∑' ℓ : SchwartzMap.standardLattice d, f (v + A (ℓ : E)) :=
          tsum_congr fun ℓ ↦ by simp [g, map_add]
    _ = ∑' ℓ : L, f (v + (ℓ : E)) := by
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
    have hfourier (w : E) : 𝓕 (fun x : E => g x) w =
        cC * 𝓕 (fun x : E => f x) ((Bₗ (d := d) L) w) := by
      simpa [g, A, Bₗ, detA, cC, Complex.real_smul] using
        SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
          (A := A) (f := fun x : E => f x) w
    have hexp (w : E) :
        Complex.exp (2 * π * Complex.I * ⟪A.symm v, w⟫_[ℝ]) =
          Complex.exp (2 * π * Complex.I * ⟪v, (Bₗ (d := d) L) w⟫_[ℝ]) := by
      simp [show ⟪A.symm v, w⟫_[ℝ] = ⟪v, (Bₗ (d := d) L) w⟫_[ℝ] by
        simpa [RCLike.inner_eq_wInner_one, A, Bₗ] using
          (LinearMap.adjoint_inner_right ((A.symm : E ≃ₗ[ℝ] E).toLinearMap) v w).symm]
    have hsum :
        (∑' n : Fin d → ℤ,
            (𝓕 (fun x : E => g x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)) *
              Complex.exp
                (2 * π * Complex.I *
                  ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.intVec (d := d) n⟫_[ℝ])) =
          cC * ∑' m : dualLattice (d := d) L, F m := by
      rw [← (equivIntVecToDual (d := d) L).tsum_eq (f := F), ← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      simpa [F, mul_assoc] using
        congrArg₂ (· * ·)
          (hfourier (w := SchwartzMap.PoissonSummation.Standard.intVec (d := d) n))
          (hexp (w := SchwartzMap.PoissonSummation.Standard.intVec (d := d) n))
    simp [hsum, F, cC, show ZLattice.covolume L = abs detA from by
      simpa [A, Aₗ, detA] using covolume_eq_abs_det_A (d := d) (L := L), one_div]
  simpa [hlhs, hrhs] using hstd

end SchwartzMap.PoissonSummationLattices

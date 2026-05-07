module
public import SpherePacking.CohnElkies.PoissonSummationSchwartz.PoissonSummation
import SpherePacking.CohnElkies.PoissonSummationSchwartz.Basic
public import SpherePacking.ForMathlib.FourierLinearEquiv

public import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Poisson summation for Schwartz functions over a full-rank `ℤ`-lattice `L ⊆ ℝ^d`,
reduced to the standard case via a linear equivalence sending `ℤ^d` to `L`. -/

open scoped BigOperators FourierTransform Real

open MeasureTheory Module

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

private lemma volume_real_fundamentalDomain_stdBasis :
    (volume : Measure E).real
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

lemma covolume_eq_abs_det_A :
    ZLattice.covolume L =
      abs ((LinearMap.det : (E →ₗ[ℝ] E) →* ℝ) ((A L).toLinearMap)) := by
  have hr : rBasis (d := d) L = fun i : Fin d => (zBasis (d := d) L i : E) :=
    funext fun i => by simp [rBasis]
  have hcovol : ZLattice.covolume L =
      |(stdBasis (d := d)).det (fun i : Fin d => (zBasis (d := d) L i : E))| := by
    simpa [stdBasis, volume_real_fundamentalDomain_stdBasis (d := d)] using
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

noncomputable def equivStandardLatticeToDual :
    SchwartzMap.standardLattice d ≃ₗ[ℤ] dualLattice (d := d) L :=
  (LinearEquiv.restrictScalars ℤ (adjointSymmEquiv L)).ofSubmodules _ _ <| by
    simpa [LinearEquiv.restrictScalars_apply] using
      map_standardLattice_adjointSymm_eq_dualSubmodule (d := d) (L := L)

noncomputable def equivIntVecToDual : (Fin d → ℤ) ≃ dualLattice (d := d) L :=
  PoissonSummation.Standard.equivIntVec.trans (equivStandardLatticeToDual L).toEquiv

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
      rw [← (equivIntVecToDual L).tsum_eq (f := F), ← tsum_mul_left]
      exact tsum_congr fun n ↦ by
        simpa [F, mul_assoc] using congrArg₂ (· * ·) (hfourier (w := iv n)) (hexp (w := iv n))]
    simp [F, cC, show ZLattice.covolume L = abs detA from by
      simpa [A, Aₗ, detA] using covolume_eq_abs_det_A (d := d) (L := L), one_div]
  simpa [hlhs, hrhs] using SchwartzMap.PoissonSummation.Standard.poissonSummation_standard
    (d := d) (f := g) (v := A.symm v)

end SchwartzMap.PoissonSummationLattices

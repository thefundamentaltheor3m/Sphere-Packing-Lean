module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.Basic.PeriodicPacking.Theorem22
public import SpherePacking.Basic.PeriodicPacking.DensityFormula
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
public import SpherePacking.Basic.PeriodicPacking.BoundaryControl

/-!
# Auxiliary summability and reindexing for the LP bound

Summability of Schwartz functions over translates of `ℤ`-lattices and reindexing helpers for the
Cohn-Elkies argument. Given a fundamental domain `D` uniquely covering every point up to a
lattice translate, the explicit equivalence `(P.centers ∩ D) × P.lattice ≃ P.centers` reindexes
the `tsum` expressions appearing in the proof.
-/

open scoped SchwartzMap FourierTransform RealInnerProductSpace
open BigOperators Module

namespace SpherePacking.CohnElkies
variable {d : ℕ}

namespace LPBoundAux

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]

/-- A Schwartz function has summable norms on any translate of a `ℤ`-lattice. -/
public lemma summable_norm_comp_add_zlattice (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 2
  obtain ⟨C, _hCpos, hC⟩ := f.decay k 0
  have hC' : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ k * ‖f x‖ ≤ C := fun x => by
    simpa [norm_iteratedFDeriv_zero] using hC x
  set b : EuclideanSpace ℝ (Fin d) := -a
  refine Summable.of_norm_bounded_eventually
    (f := fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖)
    (g := fun ℓ : Λ => (C + 1) * ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖⁻¹ ^ k) ?_ ?_
  · simpa [mul_assoc] using
      (ZLattice.summable_norm_sub_inv_pow (L := Λ) (n := k) (by simp [k]) b).mul_left (C + 1)
  · have hClosed : IsClosed (X := EuclideanSpace ℝ (Fin d))
        (Λ : Set (EuclideanSpace ℝ (Fin d))) := by
      letI : DiscreteTopology Λ.toAddSubgroup := inferInstanceAs (DiscreteTopology Λ)
      simpa [Submodule.coe_toAddSubgroup] using
        AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
    have hFiniteBad :
        ({ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ≤ (1 : ℝ)} : Set Λ).Finite := by
      have hpre :
          ((fun ℓ : Λ => (ℓ : EuclideanSpace ℝ (Fin d))) ⁻¹'
              (Metric.closedBall b (1 : ℝ) ∩ (Λ : Set (EuclideanSpace ℝ (Fin d))))).Finite := by
        simpa using (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
          Metric.isBounded_closedBall hClosed).preimage_embedding
          (f := (⟨Subtype.val, Subtype.coe_injective⟩ : Λ ↪ EuclideanSpace ℝ (Fin d)))
      simpa [Set.preimage, Metric.mem_closedBall, dist_eq_norm, and_true] using hpre
    refine hFiniteBad.subset ?_
    intro ℓ hfail
    by_contra hlarge
    have hlarge' : (1 : ℝ) < ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ := lt_of_not_ge hlarge
    have hpos : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k :=
      pow_pos (lt_of_lt_of_le one_pos hlarge'.le) _
    have hdec :
        ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k *
          ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤ C := by
      have hnorm : ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ = ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ := by
        simp [b, sub_eq_add_neg, add_comm]
      simpa [hnorm] using hC' (a + (ℓ : EuclideanSpace ℝ (Fin d)))
    have hmono :
        C / ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k ≤
          (C + 1) / ‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k := by
      simpa [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
          (by positivity : 0 ≤ (‖(ℓ : EuclideanSpace ℝ (Fin d)) - b‖ ^ k)⁻¹)
    refine hfail (by simpa [div_eq_mul_inv, inv_pow] using
      ((le_div_iff₀' hpos).2 hdec).trans (by simpa using hmono))

end LPBoundAux

namespace LPBoundSummability

open SpherePacking.CohnElkies.LPBoundAux

section ZLattice

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))

/-- A Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate :
    Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) :=
  Summable.of_norm (summable_norm_comp_add_zlattice (Λ := Λ) f a)

/-- The real part of a Schwartz function is summable on any translate of a discrete `ℤ`-lattice. -/
public theorem summable_lattice_translate_re :
    Summable (fun ℓ : Λ => (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
  Complex.reCLM.summable (summable_lattice_translate (Λ := Λ) f a)

end ZLattice

end LPBoundSummability

/-- A discrete `ℤ`-lattice has a discrete dual submodule (for the Euclidean inner product). -/
public instance (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ) := by
  let bZ : Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ := Module.Free.chooseBasis ℤ Λ
  let bR := bZ.ofZLatticeBasis ℝ Λ
  have hB : LinearMap.BilinForm.Nondegenerate (innerₗ (EuclideanSpace ℝ (Fin d)) :
      LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx
    all_goals
      have : ⟪x, x⟫ = (0 : ℝ) := by simpa [innerₗ_apply_apply] using hx x
      exact inner_self_eq_zero.1 this
  have hdual :
      LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ =
        Submodule.span ℤ (Set.range
          (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR)) := by
    simpa [bR, bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using
      LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB bR
  exact hdual ▸ inferInstance

noncomputable section

/-- Equivalence `((P.centers ∩ D) × P.lattice) ≃ P.centers` from a unique-covering assumption. -/
@[expose] public def centersInterProdEquiv (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  have hcover :
      ∀ x : P.centers, ∃! g : P.lattice, g +ᵥ (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers ∩ D :=
    fun x =>
      let ⟨g, hg, hguniq⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
      ⟨g, ⟨P.lattice_action g.property x.property, hg⟩, fun g' hg' => hguniq g' hg'.2⟩
  let cover : P.centers → P.lattice := fun x => Classical.choose (hcover x)
  let repr : P.centers → ↑(P.centers ∩ D) := fun x =>
    ⟨cover x +ᵥ (x : EuclideanSpace ℝ (Fin d)), (Classical.choose_spec (hcover x)).1⟩
  let toCenter : ↑(P.centers ∩ D) × P.lattice → P.centers := fun p =>
    ⟨p.2 +ᵥ (p.1 : EuclideanSpace ℝ (Fin d)), P.lattice_action p.2.property p.1.property.1⟩
  let toPair : P.centers → ↑(P.centers ∩ D) × P.lattice := fun x => (repr x, -cover x)
  refine { toFun := toCenter, invFun := toPair, left_inv := ?_, right_inv := ?_ }
  · intro p
    have hcov : cover (toCenter p) = -p.2 :=
      ((Classical.choose_spec (hcover (toCenter p))).2 (-p.2)
        (by simp [toCenter, p.1.property])).symm
    exact Prod.ext (Subtype.ext (by simp [toPair, repr, toCenter, hcov])) (by simp [toPair, hcov])
  · exact fun x => Subtype.ext (by simp [toPair, repr, toCenter, neg_vadd_vadd])

/-- Reindex the `x : P.centers` sum as a `x₀ : P.centers ∩ D` sum over lattice translates,
the periodic decomposition used in `LPBound.lean`. -/
public lemma tsum_centers_eq_tsum_centersInter_centersInter_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re =
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
  haveI : Finite (↑(P.centers ∩ D)) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite _
  let e : (↑(P.centers ∩ D) × P.lattice) ≃ P.centers :=
    centersInterProdEquiv (P := P) (D := D) hD_unique_covers
  have he_sub (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) :
      ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))) =
        (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)) := by
    simp [e, centersInterProdEquiv, Submodule.vadd_def, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  rw [show (∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)
        = ∑' p : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re from by
      simpa [e] using (e.tsum_eq (f := fun x : P.centers =>
        ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)).symm]
  have hSummable_p :
      Summable (fun p : ↑(P.centers ∩ D) × P.lattice => ∑' y : ↑(P.centers ∩ D),
        (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) := by
    simp_rw [tsum_fintype]
    refine summable_sum fun y _ => Summable.of_norm_bounded
      (g := fun p : ↑(P.centers ∩ D) × P.lattice =>
        ‖f ((p.1 : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (p.2 : EuclideanSpace ℝ (Fin d)))‖) ?_ ?_
    · refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2
        ⟨fun x => by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice (Λ := P.lattice) f
            ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))), Summable.of_finite⟩
    · rintro ⟨x, ℓ⟩
      simpa [he_sub x y ℓ, Real.norm_eq_abs] using
        Complex.abs_re_le_norm (f
          ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))
  rw [show (∑' p : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re)
        = ∑' (x : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          ∑' y : ↑(P.centers ∩ D),
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re from by
      simpa using hSummable_p.tsum_prod]
  have hy_comm : ∀ x : ↑(P.centers ∩ D),
      (∑' ℓ : P.lattice, ∑' y : ↑(P.centers ∩ D),
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) =
        ∑' y : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
          (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)))).re := fun x => by
    simpa [tsum_fintype] using
      (Summable.tsum_finsetSum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
        (f := fun (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) =>
          (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re)
        (fun y _ =>
          (summable_congr fun b => congrArg Complex.re (congrArg (⇑f) (he_sub x y b))).mpr
            (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
              (Λ := P.lattice) (f := f)
              ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))))
  simp_rw [hy_comm]
  exact tsum_congr fun x =>
    tsum_congr₂ fun b c => congrArg Complex.re (congrArg (⇑f) (he_sub x b c))

end

end SpherePacking.CohnElkies

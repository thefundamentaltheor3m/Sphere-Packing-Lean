module
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.Basic.PeriodicPacking.Theorem22
public import SpherePacking.Basic.PeriodicPacking.DensityFormula
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
public import SpherePacking.Basic.PeriodicPacking.BoundaryControl
public import SpherePacking.CohnElkies.LPBoundAux

/-!
# Reindexing periodic sums for the LP bound

Given a fundamental domain `D` uniquely covering every point up to a lattice translate, the
explicit equivalence `(P.centers ∩ D) × P.lattice ≃ P.centers` reindexes the `tsum` expressions
appearing in the Cohn-Elkies argument.
-/

namespace SpherePacking.CohnElkies

noncomputable section

open scoped BigOperators SchwartzMap

variable {d : ℕ}

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

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
import SpherePacking.CohnElkies.LPBoundSummability


/-!
# Reindexing periodic sums for the LP bound

Sums over all centers of a periodic packing can be rewritten using a fundamental domain `D` for the
lattice action. Assuming `D` uniquely covers every point up to a lattice translate, we construct an
explicit equivalence `(P.centers ∩ D) × P.lattice ≃ P.centers` and use it to reindex `tsum`
expressions that appear in the Cohn-Elkies argument.
-/

namespace SpherePacking.CohnElkies

noncomputable section

open scoped BigOperators SchwartzMap

variable {d : ℕ}

/-- An explicit equivalence `((P.centers ∩ D) × P.lattice) ≃ P.centers` obtained from the
`hD_unique_covers` assumption (each point has a unique lattice translate lying in `D`). -/
@[expose] public def centersInterProdEquiv (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  have hcover :
      ∀ x : P.centers, ∃! g : P.lattice, g +ᵥ (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers ∩ D :=
    fun x =>
      PeriodicSpherePacking.unique_covers_of_centers (d := d) (S := P) (D := D) hD_unique_covers x
  let cover : P.centers → P.lattice := fun x => Classical.choose (hcover x)
  have cover_spec :
      ∀ x : P.centers, ((cover x) +ᵥ (x : EuclideanSpace ℝ (Fin d))) ∈ P.centers ∩ D := by
    intro x
    exact (Classical.choose_spec (hcover x)).1
  have cover_unique :
      ∀ x : P.centers,
        ∀ g : P.lattice,
          (g +ᵥ (x : EuclideanSpace ℝ (Fin d))) ∈ P.centers ∩ D → g = cover x := by
    intro x g hg
    exact (Classical.choose_spec (hcover x)).2 g hg
  let repr : P.centers → ↑(P.centers ∩ D) := fun x =>
    ⟨(cover x) +ᵥ (x : EuclideanSpace ℝ (Fin d)), cover_spec x⟩
  let toCenter : ↑(P.centers ∩ D) × P.lattice → P.centers := fun p =>
    ⟨p.2 +ᵥ (p.1 : EuclideanSpace ℝ (Fin d)), by
      have hx0 : (p.1 : EuclideanSpace ℝ (Fin d)) ∈ P.centers := (p.1.property).1
      exact P.lattice_action p.2.property hx0⟩
  let toPair : P.centers → ↑(P.centers ∩ D) × P.lattice := fun x =>
    (repr x, -cover x)
  refine
    { toFun := toCenter
      invFun := toPair
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    have hcover : cover (toCenter p) = -p.2 := by
      symm
      refine cover_unique (toCenter p) (-p.2) ?_
      simp [toCenter, p.1.property]
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      simp [toPair, repr, toCenter, hcover]
    · simp [toPair, hcover]
  · intro x
    -- `(-cover x) +ᵥ (cover x +ᵥ x) = x`
    apply Subtype.ext
    simp [toPair, repr, toCenter, neg_vadd_vadd]

/-- Reindex the `x : P.centers` sum as a `x₀ : P.centers ∩ D` sum over lattice translates. This is
the periodic decomposition used in `LPBound.lean` to pass from a sum over all centers to a sum
over centers in a fundamental domain and lattice shifts. -/
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
  have hfinite : Finite (↑(P.centers ∩ D)) :=
    finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite (↑(P.centers ∩ D))
  let e : (↑(P.centers ∩ D) × P.lattice) ≃ P.centers :=
    centersInterProdEquiv (P := P) (D := D) hD_unique_covers
  have he_sub (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) :
      ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))) =
        (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)) := by
    -- `e (x, ℓ) = ℓ +ᵥ x` by definition; rearrange in the additive commutative group.
    simp [e, centersInterProdEquiv, Submodule.vadd_def, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  -- Reindex the outer `x` sum using `e`.
  have hx :
      (∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)
        =
        ∑' p : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re := by
    -- `e.tsum_eq` has the form `∑' p, g (e p) = ∑' x, g x`.
    simpa [e] using (e.tsum_eq (f := fun x : P.centers =>
      ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re)).symm
  rw [hx]
  -- Summability on the product index so we can use `Summable.tsum_prod`.
  have hSummable_p :
      Summable
        (fun p : ↑(P.centers ∩ D) × P.lattice =>
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re) := by
    -- Reduce the inner `tsum` to a finite sum.
    simp_rw [tsum_fintype]
    -- It suffices to show summability for each summand indexed by `y`.
    refine summable_sum fun y _ => ?_
    -- Show the series is absolutely summable by bounding the absolute value of the real part by the
    -- complex norm, and summing the norms over `((P.centers ∩ D) × P.lattice)`.
    refine Summable.of_norm_bounded
      (g := fun p : ↑(P.centers ∩ D) × P.lattice =>
        ‖f ((p.1 : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (p.2 : EuclideanSpace ℝ (Fin d)))‖)
      ?_ ?_
    · -- Summability of the norm on the product follows from fiberwise summability on the lattice,
      -- and finiteness of `(P.centers ∩ D)`.
      have hnonneg :
          ∀ p : ↑(P.centers ∩ D) × P.lattice,
            0 ≤ ‖f ((p.1 : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
              (p.2 : EuclideanSpace ℝ (Fin d)))‖ := fun _ => norm_nonneg _
      -- Use the characterization of summability on a product for nonnegative functions.
      refine (summable_prod_of_nonneg hnonneg).2 ?_
      constructor
      · intro x
        -- Summability on the lattice translate.
        -- This is absolute summability: we sum the norms.
        -- `x - y` is the translation.
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice (Λ := P.lattice) f
            ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))
      · exact Summable.of_finite
    · rintro ⟨x, ℓ⟩
      have hle :
          |(f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re| ≤
            ‖f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))‖ := by
        simpa [Real.norm_eq_abs] using
          Complex.abs_re_le_norm (f
            ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))
      simpa [he_sub x y ℓ] using hle
  -- Split the product sum into iterated sums.
  have hprod :
      (∑' p : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((e p : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re)
        =
        ∑' (x : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          ∑' y : ↑(P.centers ∩ D),
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re := by
    simpa using hSummable_p.tsum_prod
  rw [hprod]
  -- Commute the lattice sum with the finite `y` sum, for each fixed `x`.
  have hy_comm :
      ∀ x : ↑(P.centers ∩ D),
        (∑' ℓ : P.lattice,
              ∑' y : ↑(P.centers ∩ D),
                (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)))).re)
          =
          ∑' y : ↑(P.centers ∩ D),
            ∑' ℓ : P.lattice,
              (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)))).re := by
    intro x
    -- Rewrite the finite `y` sum as a finite sum and use `Summable.tsum_finsetSum`.
    have hℓ :
        ∀ y ∈ (Finset.univ : Finset ↑(P.centers ∩ D)),
          Summable fun ℓ : P.lattice =>
            (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)))).re := by
      intro y _
      -- Use Schwartz decay on lattice translates.
      -- First, rewrite `e (x, ℓ) - y` as `x - y + ℓ`.
      have hs :
          Summable fun ℓ : P.lattice =>
            (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re :=
        (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
          (Λ := P.lattice) (f := f)
          ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))
      -- Rewrite back to the original expression.
      exact (summable_congr fun b => congrArg Complex.re (congrArg (⇑f) (he_sub x y b))).mpr hs
    -- swap and rewrite back to `tsum`
    simpa [tsum_fintype] using
      (Summable.tsum_finsetSum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
            (f := fun (y : ↑(P.centers ∩ D)) (ℓ : P.lattice) =>
              (f ((e (x, ℓ) : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)))).re) hℓ)
  -- Apply the commutation lemma under the outer `x` sum.
  simp_rw [hy_comm]
  -- Finally, simplify `e (x, ℓ)` and rearrange `(e (x, ℓ) - y)` to `(x - y + ℓ)`.
  refine tsum_congr fun x => ?_
  exact tsum_congr₂ fun b c => congrArg Complex.re (congrArg (⇑f) (he_sub x b c))

end

end SpherePacking.CohnElkies

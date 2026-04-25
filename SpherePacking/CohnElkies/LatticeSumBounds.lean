module

public import SpherePacking.CohnElkies.Prereqs
public import SpherePacking.CohnElkies.LPBoundSummability

/-!
# Lattice sum bounds for the Cohn-Elkies argument

This file isolates the pointwise estimate that bounds the real lattice sum
`∑' ℓ, (f (x - y + ℓ)).re` by the diagonal contribution when `x = y`, and by `0` otherwise.

It is used both in the LP bound (`SpherePacking.CohnElkies.LPBound`) and in the equality-case
analysis.
-/

open scoped BigOperators SchwartzMap

namespace SpherePacking.CohnElkies

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}

section FundamentalDomain

variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}

/-- Pointwise bound on the lattice sum appearing in the Cohn-Elkies argument. -/
public lemma lattice_sum_re_le_ite (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  -- If `x,y ∈ D` and `x + ℓ = y`, then `ℓ = 0` by uniqueness of the cover of `y`.
  have hℓ_eq_zero_of_vadd_eq {x y : ↑(P.centers ∩ D)} {ℓ : P.lattice}
      (hxy :
        (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) =
          (y : EuclideanSpace ℝ (Fin d))) :
      ℓ = 0 := by
    obtain ⟨g0, -, hg0_unique⟩ := hD_unique_covers (y : EuclideanSpace ℝ (Fin d))
    have hy0 : (0 : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      simpa [Submodule.vadd_def] using y.property.2
    have hyℓ : (-ℓ : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      have hEq : ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d)) =
          (x : EuclideanSpace ℝ (Fin d)) := by
        have hx := eq_sub_of_add_eq hxy
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx.symm
      have : ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) +
          (y : EuclideanSpace ℝ (Fin d)) ∈ D := hEq ▸ x.property.2
      simpa [Submodule.vadd_def] using this
    have : (-ℓ : P.lattice) = 0 :=
      (hg0_unique (-ℓ) hyℓ).trans (hg0_unique 0 hy0).symm
    simpa using neg_eq_zero.mp this
  by_cases hxy : x = y
  · subst hxy
    have hs : Summable fun ℓ : P.lattice => (f (ℓ : EuclideanSpace ℝ (Fin d))).re := by
      simpa [zero_add] using
        (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
          (Λ := P.lattice) (f := f) (a := (0 : EuclideanSpace ℝ (Fin d))))
    have htail : (∑' ℓ : P.lattice,
          ite (ℓ = (0 : P.lattice)) 0 (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ 0 := by
      refine tsum_nonpos fun ℓ => ?_
      by_cases hℓ : ℓ = 0
      · simp [hℓ]
      · have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
          simpa [add_comm] using P.lattice_action ℓ.property x.property.1
        have hneq : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
              (x : EuclideanSpace ℝ (Fin d)) := fun h => hℓ (hℓ_eq_zero_of_vadd_eq h)
        have hdist := P.centers_dist' _ _ hxℓ x.property.1 hneq
        have hnorm : (1 : ℝ) ≤ ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ := by
          have : (1 : ℝ) ≤ dist
              ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
              (x : EuclideanSpace ℝ (Fin d)) := by simpa [hP] using hdist
          simpa [dist_eq_norm, add_sub_cancel_left] using this
        have hle := hCohnElkies₁ (ℓ : EuclideanSpace ℝ (Fin d))
          (by simpa [ge_iff_le] using hnorm)
        simp [hℓ, hle]
    have hsum_le : (∑' ℓ : P.lattice, (f (ℓ : EuclideanSpace ℝ (Fin d))).re) ≤ (f 0).re := by
      rw [hs.tsum_eq_add_tsum_ite (0 : P.lattice)]
      simpa using add_le_add_left htail (f 0).re
    simpa using hsum_le
  · have hnonpos : ∀ ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re ≤ 0 := by
      intro ℓ
      have hxℓ : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
        simpa [add_comm] using P.lattice_action ℓ.property x.property.1
      have hneq : (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
            (y : EuclideanSpace ℝ (Fin d)) := by
        intro h
        have : ℓ = 0 := hℓ_eq_zero_of_vadd_eq (x := x) (y := y) (ℓ := ℓ) h
        subst this
        exact hxy (Subtype.ext (by simpa using h))
      have hdist := P.centers_dist' _ _ hxℓ y.property.1 hneq
      have hnorm : (1 : ℝ) ≤ ‖(x : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))‖ := by
        have : (1 : ℝ) ≤ dist
            ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
            (y : EuclideanSpace ℝ (Fin d)) := by simpa [hP] using hdist
        simpa [dist_eq_norm] using this
      have hle := hCohnElkies₁ _ (by simpa [ge_iff_le] using hnorm)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle
    simpa [hxy] using tsum_nonpos hnonpos

end FundamentalDomain

end SpherePacking.CohnElkies

import Mathlib
import SpherePacking.Basic.EuclideanLattice

open Metric BigOperators EuclideanLattice

/-!
# The choices made in this file mirror those made in `Algebra.Module.Zlattice.Basic`. Specifically,
- All conditions pertaining to types of sphere packings are defined on the sets of centres
- A sphere packing can be built from any set of centres using `Packing_of_Centres`.
-/

variable (d : ℕ)
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "V" d => EuclideanSpace ℝ (Fin d)

noncomputable local instance instTopSpaceV : TopologicalSpace (V d) := by infer_instance

namespace SpherePacking

section Definitions

class SpherePackingCentres (X : Set V) (r : ℝ) where
  nonoverlapping : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → r ≤ ‖x - y‖

set_option linter.unusedVariables false in
@[simp]
def Packing_of_Centres (X : Set V) (r : ℝ) [SpherePackingCentres d X r] : Set V :=
  ⋃ x ∈ X, ball x (r / 2)

/-
instance instDiscreteTopologyOfSpherePackingCentres (X : Set (V d)) (r : ℝ) [Fact (r > 0)]
  [SpherePackingCentres d X r] : DiscreteTopology X := by
  sorry
The above gives the following error:
```
cannot find synthesization order for instance instDiscreteTopologyOfSpherePackingCentres with type
  ∀ (d : ℕ) (X : Set (V d)) (r : ℝ) [inst : Fact (r > 0)] [inst : SpherePackingCentres d X r],
  DiscreteTopology ↑X
all remaining arguments have metavariables:
  Fact (?r > 0)
  SpherePackingCentres d X ?r
```
-/

/- Whoopsie! The following should be `DiscreteTopology X` and not the packing!
instance instSpherePackingCentresDiscrete (X : Set V) (r : ℝ) [SpherePackingCentres d X r]
  [Fact (r > 0)] : DiscreteTopology (Packing_of_Centres d X r) := by
  rw [discreteTopology_iff_singleton_mem_nhds]
  intro H
  rcases H with ⟨v, U, hU, hvU⟩
  rw [mem_nhds_subtype]
  simp only [Set.subset_singleton_iff, Set.mem_preimage, Subtype.forall, Subtype.mk.injEq]
  use ball v (r / 2)
  constructor
  · simp only [isOpen_ball, ball, _root_.mem_nhds_iff]
    use ball v (r / 4)
    constructor
    · intro y hy
      rw [Set.mem_setOf_eq]
      sorry
    · constructor
      · exact isOpen_ball
      · refine mem_ball_self ?h.right.right.h
        simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right]
        exact Fact.out
  · intro a ha₁ ha₂

    sorry
-/

end Definitions

noncomputable section Density

open scoped ENNReal
open MeasureTheory Filter

set_option linter.unusedVariables false

def FiniteDensity (X : Set V) (r : ℝ) [SpherePackingCentres d X r] (R : ℝ) : ℝ≥0∞ :=
  volume ((Packing_of_Centres d X r) ∩ ball 0 R) / (volume (ball (0 : V) R))

def Density (X : Set V) (r : ℝ) [SpherePackingCentres d X r] : ℝ≥0∞ :=
  limsup (FiniteDensity d X r) atTop

-- TODO: maybe we need some API around Fin 0 stuff. Or maybe we just ignore them lol
example (X : Set (EuclideanSpace ℝ (Fin 0))) : volume X = 0 := by
  refine exists_measurable_superset_iff_measure_eq_zero.mp ?_
  sorry

theorem Density_zero' (X : Set (V 0)) (r : ℝ) [SpherePackingCentres 0 X r] (R : ℝ) :
    FiniteDensity 0 X r R = 0 := by
  simp_rw [FiniteDensity]
  convert ENNReal.zero_div
  refine measure_inter_null_of_null_left (ball 0 R) ?h.e'_2.h.e'_5.h
  sorry

theorem Density_zero (X : Set (V 0)) (r : ℝ) [SpherePackingCentres 0 X r] :
    Density 0 X r = 0 := by
  sorry

/-- The `PeriodicSpherePackingConstant'` in dimension d with separation radius r is the supremum of
the density of all periodic packings in dimension d with separation radius r. We later prove that
all `PeriodicSpherePackingConstant'` with positive separation radius r are the same, and define
`PeriodicSpherePackingConstant` as that unique value. See also `PeriodicSpherePackingConstant` and
`periodicSpherePackingConstant'_eq_periodicSpherePackingConstant'`. -/
def PeriodicSpherePackingConstant' (r : ℝ) : ℝ≥0∞ :=
  ⨆ (X : Set V) (Λ : AddSubgroup V) (inst1 : SpherePackingCentres d X r)
    (inst2 : DiscreteTopology Λ) (inst3 : IsZlattice ℝ Λ) (inst4 : AddAction Λ X), Density d X r

/-- The `SpherePackingConstant` in dimension d with separation radius r is the supremum of the
density of all packings in dimension d with separation radius r. We later prove that all
`SpherePackingConstant'` with positive separation radius r are the same, and define
`SpherePackingConstant` as that unique value. See also `SpherePackingConstant`. -/
def SpherePackingConstant' (r : ℝ) : ℝ≥0∞ :=
  ⨆ (X : Set V) (inst : SpherePackingCentres d X r), Density d X r

/-- The `PeriodicSpherePackingConstant` in dimension d is the supremum of the
density of all periodic packings in dimension d with separation radius 1. See also
`PeriodicSpherePackingConstant'`. -/
def PeriodicSpherePackingConstant : ℝ≥0∞ := PeriodicSpherePackingConstant' d 1

/-- The `PeriodicSpherePackingConstant` in dimension d is the supremum of the
density of all periodic packings in dimension d with separation radius 1. See also
`PeriodicSpherePackingConstant'`. -/
def SpherePackingConstant : ℝ≥0∞ := SpherePackingConstant' d 1

-- Obvious TODO: Extend to ConditionallyCompleteLattice
theorem Real.ciCup_prod_eq_ciCup₂ {α β : Type*} [inst : Nonempty (α × β)] (f : α → β → ℝ)
    (hf : BddAbove (Set.range f.uncurry)) :
      ⨆ x : α × β, f x.fst x.snd = ⨆ (x : α) (y : β), f x y := by
  haveI : Nonempty α := ⟨(Classical.choice inst).fst⟩
  haveI : Nonempty β := ⟨(Classical.choice inst).snd⟩
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro ⟨x, y⟩
    trans ⨆ y', f x y'
    · refine le_ciSup (f := fun y' ↦ f x y') ?_ _
      obtain ⟨u, hu⟩ := hf
      use u
      simp [mem_upperBounds] at hu ⊢
      intro y'
      exact hu _ x y' rfl
    · refine le_ciSup (f := fun x' ↦ ⨆ y, f x' y) ?_ _
      obtain ⟨u, hu⟩ := hf
      use u
      simp [mem_upperBounds] at hu ⊢
      intro x'
      apply ciSup_le
      intro y'
      exact hu _ x' y' rfl
  · intro w hw
    obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hw
    obtain ⟨y, hy⟩ := exists_lt_of_lt_ciSup hx
    use ⟨x, y⟩

-- TODO: Change this to CompleteLattice
theorem ENNReal.ciCup_prod_eq_ciCup₂ {α β : Type*} [inst : Nonempty (α × β)] (f : α → β → ℝ≥0∞) :
    ⨆ x : α × β, f x.fst x.snd = ⨆ (x : α) (y : β), f x y := by
  haveI : Nonempty α := ⟨(Classical.choice inst).fst⟩
  haveI : Nonempty β := ⟨(Classical.choice inst).snd⟩
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro ⟨x, y⟩
    trans ⨆ y', f x y'
    · apply le_iSup
    · apply le_iSup (fun x ↦ ⨆ y, f x y)
  · intro w hw
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hw
    obtain ⟨y, hy⟩ := lt_iSup_iff.mp hx
    use ⟨x, y⟩

theorem periodicSpherePackingConstant'_eq_periodicSpherePackingConstant'
    (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r') :
      PeriodicSpherePackingConstant' d r = PeriodicSpherePackingConstant' d r' := by
  by_cases hd : d = 0
  · subst hd; sorry -- simp
  simp_rw [PeriodicSpherePackingConstant']
  apply le_antisymm
  all_goals
    apply iSup_le; intro X
    apply iSup_le; intro Λ
    apply iSup_le; intro inst1
    apply iSup_le; intro inst2
    apply iSup_le; intro inst3
    apply iSup_le; intro inst4
  · calc
      _ ≤ ⨆ (XΛ : Set V × AddSubgroup V) (_ : SpherePackingCentres d XΛ.fst r')
            (_ : DiscreteTopology XΛ.snd) (_ : IsZlattice ℝ XΛ.snd) (_ : AddAction XΛ.snd XΛ.fst),
              Density d XΛ.fst r' := by
        sorry
      _ = ⨆ (X : Set V) (Λ : AddSubgroup V) (_ : SpherePackingCentres d X r')
            (_ : DiscreteTopology Λ) (_ : IsZlattice ℝ Λ) (_ : AddAction Λ X), Density d X r' := by
        sorry -- exact ENNReal.ciCup_prod_eq_ciCup₂ _
  · sorry -- done

example {ι : Type*} {f : ι → ℝ} [IsEmpty ι] : iSup f = 0 := Real.iSup_of_isEmpty f

example {f : ℝ → ℝ → ℝ} {s t : Set ℝ} {a b : ℝ} (ha : a ∈ s) (hb : b ∈ t)
      (hf : BddAbove (Set.range f.uncurry)) :
    f a b ≤ ⨆ (x ∈ s) (y ∈ t), f x y := by
  convert_to _ ≤ ⨆ (x : s), ⨆ (y ∈ t), f (x : ℝ) y
  · sorry
  · sorry -- done
  -- apply le_iSup₂

example {f : ℝ → ℝ → ℝ} {s t : Set ℝ} {a b : ℝ} (ha : a ∈ s) (hb : b ∈ t)
      (hf : BddAbove (Set.range f.uncurry)) :
    f a b ≤ ⨆ (x ∈ s) (y ∈ t), f x y := calc
  f a b ≤ ⨆ (x ∈ s), f x b := by
    sorry -- apply le_iSup
  _ ≤ ⨆ (x ∈ s) (y ∈ t), f x y := by
    sorry

theorem periodicSpherePackingConstant_eq_periodicSpherePackingConstant'
    (r : ℝ) (hr : 0 < r) :
      PeriodicSpherePackingConstant d = PeriodicSpherePackingConstant' d r :=
  periodicSpherePackingConstant'_eq_periodicSpherePackingConstant' _ _ _ zero_lt_one hr

end Density

end SpherePacking

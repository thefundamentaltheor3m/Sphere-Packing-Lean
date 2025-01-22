/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Topology.Separation.CompletelyRegular

import SpherePacking.Basic.PeriodicPacking

/-!
This file proves lemmas involving the summability of functions that decay in a manner comparable to
inverse powers of the norm function on subsets of Euclidean space.
-/

variable {d : ℕ}

open BigOperators Complex Real

section Definitions

-- Consider putting this in `EuclideanSpace` namespace
@[simp]
def Inv_Pow_Norm_Summable_Over_Set_Euclidean (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ (d + 1))

-- TODO: Remove after proving that d + 1 does, indeed, work.
-- Else, use as hack for `Summable_of_Inv_Pow_Summable'`.
def Exists_Inv_Pow_Norm_Summable_Over_Set_Euclidean (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ k > 0, Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖^k)

def IsDecayingMap (X : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ x ∈ X, ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k * ‖f x‖ ≤ C

end Definitions

namespace DecayingMap

section Subtype

lemma summable_union_disjoint.{u_1, u_2}
    {α : Type u_1} {β : Type u_2} [AddCommMonoid α] [TopologicalSpace α] {f : β → α}
  [T2Space α] [ContinuousAdd α] {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ (↑) : s → α))
  (ht : Summable (f ∘ (↑) : t → α)) :
  Summable (f ∘ (↑) : (s ∪ t : Set β) → α) :=
  (hs.hasSum.add_disjoint hd ht.hasSum).summable

variable {X X' : Set (EuclideanSpace ℝ (Fin d))} {f : EuclideanSpace ℝ (Fin d) → ℝ}
variable (hf : IsDecayingMap X f)

include hf in
lemma IsDecayingMap.subset (hX' : X' ⊆ X) : IsDecayingMap X' f := by
  intro k
  obtain ⟨C, hC⟩ := hf k
  use C
  intro x hx
  exact hC x (hX' hx)

-- TODO: Change from `Subtype`s to `Set`s and add appropriate 'decaying over subsets' lemma

end Subtype

section EuclideanSpace

variable {X} {f : EuclideanSpace ℝ (Fin d) → ℝ}
  (hf : IsDecayingMap X f)

include hf in
theorem Summable_of_Inv_Pow_Summable'
    (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X) (hne_zero : 0 ∉ X) :
  Summable (fun x : X => f x) := by
  rcases X.eq_empty_or_nonempty with rfl | hX'
  · case inl =>
    dsimp only [Summable, HasSum]
    use 0
    intro ε hε
    simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, le_of_subsingleton,
      Set.mem_preimage, true_implies, exists_const]
    intro b
    rw [eq_top_of_bot_eq_top rfl b]
    simp only [Finset.top_eq_univ, Finset.univ_eq_empty, Finset.sum_empty]
    exact mem_of_mem_nhds hε
  · case inr =>
    rw [summable_iff_vanishing_norm]
    intro ε hε
    let k := d + 1
    have hk' : 0 < k := by positivity
    rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean] at hX
    simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs] at hX
    obtain ⟨C, hC⟩ := hf k
    simp only [Set.top_eq_univ, Real.norm_eq_abs, Subtype.forall, Set.mem_univ, true_implies] at hC
    have hC_nonneg : 0 ≤ C := by
      obtain ⟨i, hi⟩ := hX'
      specialize hC i hi
      refine hC.trans' (by positivity)
    have haux₁ : 0 < C + 1 := by linarith
    specialize hX (ε / (C + 1)) (div_pos hε haux₁)
    obtain ⟨s, hs⟩ := hX
    use s
    intro t ht
    specialize hs t ht
    suffices htriangle : ∑ x ∈ t, |f ↑x| < ε
    · refine lt_of_le_of_lt ?_ htriangle
      rw [Real.norm_eq_abs]
      exact Finset.abs_sum_le_sum_abs (fun i : X ↦ f ↑i) t
    have haux₂ : |∑ x ∈ t, (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹| < ε := by
      rw [← Finset.mul_sum, IsAbsoluteValue.abv_mul (fun (x : ℝ) ↦ |x|) _ _, abs_of_pos haux₁]
      exact (lt_div_iff' haux₁).mp hs
    refine lt_of_le_of_lt ?_ haux₂
    have haux₃ : ∀ x ∈ t, (0 : ℝ) ≤ (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹ := by
      intro x _
      apply mul_nonneg
      · linarith
      · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
    rw [Finset.abs_sum_of_nonneg haux₃]
    cases t.eq_empty_or_nonempty
    · case inl hempty =>
      rw [hempty, Finset.sum_empty, Finset.sum_empty]
    · case inr hnonempty =>
      apply Finset.sum_le_sum
      intro x _
      have haux₄ : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
        intro h
        apply hne_zero
        rw [← h]
        exact Subtype.coe_prop x
      have haux₅ : 0 < (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k) := by
        apply pow_pos
        positivity
      refine le_of_mul_le_mul_of_pos_right ?_ haux₅
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ (ne_of_gt haux₅), mul_one]
      specialize hC x
      refine LE.le.trans (hC x.2) ?_
      rw [le_add_iff_nonneg_right]
      exact zero_le_one

set_option pp.funBinderTypes true

#check tsum_union_disjoint

-- should be in mathlib!!
lemma Summable.subset {α β : Type*}
    [AddCommGroup β] [UniformSpace β] [UniformAddGroup β] [CompleteSpace β]
    (f : α → β)
    {X X' : Set α}
    (hX : Summable (fun x : X => f x)) (hX' : X' ⊆ X) :
    Summable (fun x : X' => f x) := by
  let g : X' → X := fun x => ⟨x.1, hX' x.2⟩
  have hg : Function.Injective g := by
    intro x₁ x₂ h
    simp only [g, Subtype.mk_eq_mk] at h
    exact Subtype.ext h
  have := Summable.comp_injective hX hg
  exact this

-- set_option maxHeartbeats 1000000
lemma Inv_Pow_Norm_Summable_Over_Set_Euclidean.subset {X X' : Set (EuclideanSpace ℝ (Fin d))}
    (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X) (hX' : X' ⊆ X) :
    Inv_Pow_Norm_Summable_Over_Set_Euclidean X' := by
  rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean] at *
  exact Summable.subset (fun (x : EuclideanSpace ℝ (Fin d)) ↦ 1 / ‖x‖ ^ (d + 1)) hX hX'

-- include hf in
theorem Summable_of_Inv_Pow_Summable
  (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X)
  (hf : IsDecayingMap X f) :
  Summable (fun x : X => f x) := by
  if hzero : 0 ∈ X then
    have haux₁ : IsDecayingMap (X \ {0}) f := IsDecayingMap.subset hf Set.diff_subset
    have haux₂ : Inv_Pow_Norm_Summable_Over_Set_Euclidean (X \ {0}) := by
      exact Inv_Pow_Norm_Summable_Over_Set_Euclidean.subset hX (by simp)
    have := Summable_of_Inv_Pow_Summable' (X := X \ {0}) (f := f) haux₁ haux₂ (by simp)
    have : Summable (fun x : ({0} ∪ (X \ {0}) : Set (EuclideanSpace ℝ (Fin d))) => f x) := by
      apply summable_union_disjoint
      · simp
      · refine Set.Finite.summable (by simp) _
      · exact this
    convert this <;> simp [hzero]
  else
    exact Summable_of_Inv_Pow_Summable' hf hX hzero

end EuclideanSpace

end DecayingMap

section Schwartz

namespace SchwartzMap

variable (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)

lemma IsDecaying : IsDecayingMap Set.univ f := by
  intro k
  obtain ⟨C, hC⟩ := f.decay' k 0
  use C
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hC
  simp only [Set.top_eq_univ, Real.norm_eq_abs, Subtype.forall, Set.mem_univ, true_implies]
  exact hC

theorem Summable_of_Inv_Pow_Summable'
  {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X)
  (hne_zero : 0 ∉ X) : Summable (fun x : X => f x) :=
  DecayingMap.Summable_of_Inv_Pow_Summable' (DecayingMap.IsDecayingMap.subset (IsDecaying f)
    (Set.subset_univ X)) hX hne_zero

end SchwartzMap

end Schwartz

/-
The idea of everything we've done so far is that if we have a set over which the inverse norm power
is summable, we have several summability results for decaying maps (and therefore Schwartz maps).

The next step is to prove that the inverse norm power is summable over the set of centers of a
sphere packing, or, more generally, over any set of points in Euclidean space that is acted upon by
a lattice such that the number of orbits is finite.
-/

section Sets_Acted_Upon_By_Lattice

open ZLattice ZSpan

theorem extracted_1 {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))}
  {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))} [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ] :
  let bℤ := (Module.Free.chooseBasis ℤ ↥Λ).reindex (basis_index_equiv Λ);
  let bℝ := Basis.ofZLatticeBasis ℝ Λ bℤ;
  let D := {m | ∀ (i : Fin d), (bℝ.repr m) i ∈ Set.Ico (-1) 1};
  Finite ↑(X ∩ D) :=
  -- Consider function from this thing to set of orbits. Show preimage of any singleton in `Quotient` consists of 2^d elements. Then card is card of 2^d
  sorry

-- set_option diagnostics true
theorem Summable_Inverse_Powers_of_Finite_Orbits
  {X : Set (EuclideanSpace ℝ (Fin d))} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
  [DiscreteTopology Λ] [IsZLattice ℝ Λ] (ρ : AddAction Λ X)
  [Fintype (Quotient ρ.orbitRel)]
  -- (hFin : Finite ((X ∩ (fundamentalDomain (Basis.ofZLatticeBasis ℝ Λ ((ZLattice.module_free ℝ Λ).chooseBasis)))) : Set (EuclideanSpace ℝ (Fin d))))
  : Inv_Pow_Norm_Summable_Over_Set_Euclidean X := by
  rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean]
  simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs]
  intro ε hε
  -- Translating and scaling fundamental domains could be a good idea - discussion with Bhavik
  let bℤ : Basis _ ℤ Λ :=
    ((ZLattice.module_free ℝ Λ).chooseBasis).reindex (ZLattice.basis_index_equiv Λ)
  let bℝ := Basis.ofZLatticeBasis ℝ Λ bℤ
  let D := {m | ∀ i, bℝ.repr m i ∈ Set.Ico (-1 : ℝ) 1}
  -- let N := Fintype.card ((X ∩ D) : Set (EuclideanSpace ℝ (Fin d)))

  sorry

theorem Summable_Inverse_Powers_over_Periodic_Packing_Centres (P : PeriodicSpherePacking d) :
  Inv_Pow_Norm_Summable_Over_Set_Euclidean P.centers :=
  Summable_Inverse_Powers_of_Finite_Orbits P.addAction -- P.finiteOrbitRelQuotient

/- *TODO:* Move to `SpherePacking/CohnElkies/Prereqs.lean` -/

/-
# CHECK OUT https://github.com/leanprover-community/mathlib4/blob/9d883e2896b1b16d8e646c336c647da4fc1cacd5/Mathlib/NumberTheory/ModularForms/EisensteinSeries/UniformConvergence.lean#L146!

What's wild is that this is CHRIS's file! **ASK ABOUT IT**
-/

end Sets_Acted_Upon_By_Lattice

#min_imports

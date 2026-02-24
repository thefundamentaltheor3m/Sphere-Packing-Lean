/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/
module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Summable
public import SpherePacking.ForMathlib.ZLattice

/-!
# Summability from inverse-power decay

This file proves summability results for functions that decay comparably to inverse powers of the
norm on subsets of Euclidean space.
-/

variable {d : ℕ}

open scoped BigOperators
open Module Bornology

section Definitions

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Summability of the inverse power `‖x‖^{-(d+1)}` over a subset of Euclidean space. -/
@[expose, simp] public def Inv_Pow_Norm_Summable_Over_Set_Euclidean
    (X : Set E) :
    Prop :=
  Summable (fun x : X => 1 / ‖(x : E)‖ ^ (d + 1))

/-- A weaker variant of `Inv_Pow_Norm_Summable_Over_Set_Euclidean` with an arbitrary exponent. -/
@[expose] public def Exists_Inv_Pow_Norm_Summable_Over_Set_Euclidean
    (X : Set E) :
    Prop :=
  ∃ k > 0, Summable (fun x : X => 1 / ‖(x : E)‖ ^ k)

/-- A function `f` decays on `X` if every polynomial weight `‖x‖ ^ k` controls `‖f x‖`. -/
@[expose] public def IsDecayingMap (X : Set E) (f : E → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ x ∈ X, ‖(x : E)‖ ^ k * ‖f x‖ ≤ C

end Definitions

namespace DecayingMap

section Subtype

lemma summable_union_disjoint
    {α β : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : β → α} [ContinuousAdd α]
    {s t : Set β} (hd : Disjoint s t) (hs : Summable fun x : s => f x)
    (ht : Summable fun x : t => f x) :
    Summable fun x : (s ∪ t : Set β) => f x :=
  (hs.hasSum.add_disjoint hd ht.hasSum).summable

variable {X X' : Set (EuclideanSpace ℝ (Fin d))} {f : EuclideanSpace ℝ (Fin d) → ℝ}
variable (hf : IsDecayingMap X f)

include hf in
lemma IsDecayingMap.subset (hX' : X' ⊆ X) : IsDecayingMap X' f :=
  fun k => (hf k).imp fun _C hC x hx => hC x (hX' hx)

end Subtype

section EuclideanSpace

variable {X} {f : EuclideanSpace ℝ (Fin d) → ℝ}
  (hf : IsDecayingMap X f)

include hf in
/-- If `‖x‖^{-(d+1)}` is summable on `X` and `f` decays on `X`, then `f` is summable on `X`.

The prime indicates this lemma additionally assumes `0 ∉ X` to avoid division by zero.
-/
public theorem Summable_of_Inv_Pow_Summable'
    (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X) (hne_zero : 0 ∉ X) :
  Summable (fun x : X => f x) := by
  rcases X.eq_empty_or_nonempty with rfl | hX'
  · simp
  · rw [summable_iff_vanishing_norm]
    intro ε hε
    let k := d + 1
    rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean] at hX
    simp only [one_div, summable_iff_vanishing_norm, gt_iff_lt, Real.norm_eq_abs] at hX
    obtain ⟨C, hC⟩ := hf k
    simp only [Real.norm_eq_abs] at hC
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
    suffices htriangle : ∑ x ∈ t, |f ↑x| < ε by
      refine lt_of_le_of_lt ?_ htriangle
      rw [Real.norm_eq_abs]
      exact Finset.abs_sum_le_sum_abs (fun i : X ↦ f ↑i) t
    have haux₂ : |∑ x ∈ t, (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹| < ε := by
      rw [← Finset.mul_sum, IsAbsoluteValue.abv_mul (fun (x : ℝ) ↦ |x|) _ _, abs_of_pos haux₁]
      exact (lt_div_iff₀' haux₁).mp hs
    refine lt_of_le_of_lt ?_ haux₂
    have haux₃ : ∀ x ∈ t, (0 : ℝ) ≤ (C + 1) * (‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹ := by
      intro x _
      exact mul_nonneg haux₁.le (by positivity)
    rw [Finset.abs_sum_of_nonneg haux₃]
    refine Finset.sum_le_sum ?_
    intro x _
    have hx0 : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro hx
      exact hne_zero (hx ▸ x.property)
    have hx0' : 0 < ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k :=
      pow_pos (norm_pos_iff.2 hx0) _
    refine le_of_mul_le_mul_of_pos_right ?_ hx0'
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (ne_of_gt hx0'), mul_one]
    specialize hC x
    refine LE.le.trans (hC x.2) ?_
    rw [le_add_iff_nonneg_right]
    exact zero_le_one

/-- Restrict a summable family along a subset. -/
lemma Summable.subset {α β : Type*}
    [AddCommGroup β] [UniformSpace β] [IsUniformAddGroup β] [CompleteSpace β]
    (f : α → β)
    {X X' : Set α}
    (hX : Summable (fun x : X => f x)) (hX' : X' ⊆ X) :
    Summable (fun x : X' => f x) := by
  simpa using
    hX.comp_injective (i := Set.inclusion hX') (Set.inclusion_injective hX')

lemma Inv_Pow_Norm_Summable_Over_Set_Euclidean.subset {X X' : Set (EuclideanSpace ℝ (Fin d))}
    (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X) (hX' : X' ⊆ X) :
    Inv_Pow_Norm_Summable_Over_Set_Euclidean X' := by
  simpa [Inv_Pow_Norm_Summable_Over_Set_Euclidean] using
    (Summable.subset (f := fun x : EuclideanSpace ℝ (Fin d) ↦ 1 / ‖x‖ ^ (d + 1)) hX hX')

/-- If `‖x‖^{-(d+1)}` is summable on `X` and `f` decays on `X`, then `f` is summable on `X`. -/
public theorem Summable_of_Inv_Pow_Summable
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X)
    (hf : IsDecayingMap X f) :
    Summable (fun x : X => f x) := by
  by_cases hzero : 0 ∈ X
  · have hsum : Summable (fun x : (X \ {0} : Set (EuclideanSpace ℝ (Fin d))) => f x) :=
      Summable_of_Inv_Pow_Summable' (X := X \ {0}) (f := f)
        (IsDecayingMap.subset hf Set.diff_subset)
        (Inv_Pow_Norm_Summable_Over_Set_Euclidean.subset hX Set.diff_subset) (by simp)
    have :
        Summable (fun x : ({0} ∪ (X \ {0}) : Set (EuclideanSpace ℝ (Fin d))) => f x) :=
      summable_union_disjoint (f := f) (s := ({0} : Set (EuclideanSpace ℝ (Fin d))))
        (t := X \ {0}) (by simp) (Set.Finite.summable (by simp) _) hsum
    convert this <;> simp [hzero]
  · simpa using Summable_of_Inv_Pow_Summable' (X := X) (f := f) hf hX hzero

end DecayingMap.EuclideanSpace
section Schwartz

namespace SchwartzMap

variable (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)

lemma IsDecaying : IsDecayingMap Set.univ f := fun k => by
  simpa [norm_iteratedFDeriv_zero] using (f.decay' k 0)

/-- A specialization of `DecayingMap.Summable_of_Inv_Pow_Summable'` to Schwartz maps. -/
public theorem Summable_of_Inv_Pow_Summable'
  {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X)
  (hne_zero : 0 ∉ X) : Summable (fun x : X => f x) :=
  DecayingMap.Summable_of_Inv_Pow_Summable'
    (DecayingMap.IsDecayingMap.subset (IsDecaying f) (Set.subset_univ X)) hX hne_zero

end Schwartz.SchwartzMap

/-!
If `‖x‖⁻(d+1)` is summable on `X`, then decaying (hence Schwartz) maps are summable on `X`.
The remainder of the file packages this for sets arising from finite-orbit lattice actions.
-/

open ZLattice ZSpan

section Sets_Acted_Upon_By_Lattice

open scoped Pointwise

namespace InvPowSummability

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-!
### A bounded "symmetric fundamental domain"

We will use the set
`D := {m | ∀ i, b.repr m i ∈ Ico (-1) 1}`.
This is bounded because the coefficients in the `b`-coordinates are uniformly bounded by `1`,
and `m = ∑ i, (b.repr m i) • b i`.
-/
noncomputable def symmFundamentalDomain (b : Basis (Fin d) ℝ E) : Set E :=
  {m | ∀ i : Fin d, (b.repr m) i ∈ Set.Ico (-1 : ℝ) 1}

@[simp] lemma mem_symmFundamentalDomain {b : Basis (Fin d) ℝ E} {m : E} :
    m ∈ symmFundamentalDomain (d := d) b ↔ ∀ i : Fin d, (b.repr m) i ∈ Set.Ico (-1 : ℝ) 1 :=
  Iff.rfl

lemma isBounded_symmFundamentalDomain (b : Basis (Fin d) ℝ E) :
    IsBounded (symmFundamentalDomain (d := d) b) := by
  refine isBounded_iff_forall_norm_le.2 ⟨∑ i : Fin d, ‖b i‖, ?_⟩
  intro m hm
  have hm_abs : ∀ i : Fin d, |(b.repr m) i| ≤ (1 : ℝ) := by
    intro i
    rcases hm i with ⟨hi₁, hi₂⟩
    exact abs_le.2 ⟨by simpa using hi₁, le_of_lt hi₂⟩
  calc
    ‖m‖ = ‖∑ i : Fin d, (b.repr m) i • b i‖ := by simp [b.sum_repr]
    _ ≤ ∑ i : Fin d, ‖(b.repr m) i • b i‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, |(b.repr m) i| * ‖b i‖ := by
      simp [norm_smul, Real.norm_eq_abs, mul_comm]
    _ ≤ ∑ i : Fin d, ‖b i‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      simpa [one_mul] using mul_le_mul_of_nonneg_right (hm_abs i) (norm_nonneg (b i))

/-!
### Finiteness of a bounded slice of a single orbit

If the action is by translations in the ambient Euclidean space, then each orbit is a translate of
the lattice and hence intersects bounded sets in a finite set.
-/
lemma finite_orbit_inter_of_isBounded
    {X : Set E} {Λ : Submodule ℤ E} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ρ : AddAction Λ X)
    (hρ : ∀ (g : Λ) (x : X), ((g +ᵥ x : X) : E) = (g : E) + x)
    {D : Set E} (hD : IsBounded D) (x₀ : X) :
    Set.Finite ({x : X | x ∈ AddAction.orbit Λ x₀ ∧ (x : E) ∈ D} : Set X) := by
  let sE : Set E := (- (x₀ : E)) +ᵥ D
  have hsE : IsBounded sE := hD.vadd (- (x₀ : E))
  let bℤ : Basis _ ℤ Λ :=
    ((ZLattice.module_free ℝ Λ).chooseBasis).reindex (ZLattice.basis_index_equiv Λ)
  let bℝ : Basis (Fin d) ℝ E := Basis.ofZLatticeBasis ℝ Λ bℤ
  have hfinE : Set.Finite (sE ∩ (Λ : Set E)) := by
    have : Set.Finite (sE ∩ Submodule.span ℤ (Set.range bℝ)) :=
      ZSpan.setFinite_inter (b := bℝ) (s := sE) hsE
    have hspan : Submodule.span ℤ (Set.range bℝ) = Λ := by
      simpa [bℝ] using (Basis.ofZLatticeBasis_span ℝ Λ bℤ)
    simpa [hspan] using this
  have hfin : Set.Finite {g : Λ | (g : E) ∈ sE} := by
    simpa [Set.preimage, and_true] using
      (Set.Finite.preimage_embedding
        (f := (⟨Subtype.val, Subtype.coe_injective⟩ : Λ ↪ E)) hfinE)
  refine (hfin.image (fun g : Λ => (g +ᵥ x₀ : X))).subset ?_
  rintro _ ⟨⟨g, rfl⟩, hxD⟩
  refine ⟨g, Set.mem_vadd_set.2 ?_, rfl⟩
  refine ⟨(g : E) + (x₀ : E), by simpa [hρ g x₀] using hxD, ?_⟩
  simp [add_assoc, add_comm]

end InvPowSummability

/-- Summability of inverse powers on a set with finitely many orbits under a lattice action. -/
public theorem Summable_Inverse_Powers_of_Finite_Orbits
  {X : Set (EuclideanSpace ℝ (Fin d))} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
  [DiscreteTopology Λ] [IsZLattice ℝ Λ] (ρ : AddAction Λ X)
  [Finite (Quotient ρ.orbitRel)]
  (hρ : ∀ (g : Λ) (x : X),
    ((g +ᵥ x : X) : EuclideanSpace ℝ (Fin d)) = (g : EuclideanSpace ℝ (Fin d)) + x)
  : Inv_Pow_Norm_Summable_Over_Set_Euclidean X := by
  rw [Inv_Pow_Norm_Summable_Over_Set_Euclidean]
  let Q := Quotient ρ.orbitRel
  haveI : Fintype Q := Fintype.ofFinite Q
  let f : X → ℝ := fun x => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ (d + 1)
  have hf_nonneg : 0 ≤ f := fun _ => by positivity
  let s : Q → Set X := fun q => AddAction.orbit Λ q.out
  have hs : ∀ x : X, ∃! q : Q, x ∈ s q := by
    intro x
    refine ⟨Quotient.mk _ x, ?_, ?_⟩
    · have hx_rel : (ρ.orbitRel).r (Quotient.out (Quotient.mk _ x : Q)) x :=
        Quotient.exact (Quotient.out_eq (Quotient.mk _ x : Q))
      simpa [s, AddAction.orbitRel_apply] using (ρ.orbitRel).symm hx_rel
    · intro q hxq
      have hx_rel : (ρ.orbitRel).r x q.out := by
        simpa [s, AddAction.orbitRel_apply] using hxq
      have hquot : (Quotient.mk _ x : Q) = Quotient.mk _ q.out := Quotient.sound hx_rel
      -- Replace `⟦q.out⟧` by `q` using `Quotient.out_eq`.
      simpa [Quotient.out_eq q] using hquot.symm
  have horb : ∀ q : Q, Summable (fun x : s q => f x) := by
    intro q
    let φ : Λ → s q := fun g =>
      ⟨g +ᵥ q.out, by
        change g +ᵥ q.out ∈ AddAction.orbit Λ q.out
        exact ⟨g, rfl⟩⟩
    have hφ_inj : Function.Injective φ := by
      intro g₁ g₂ h
      have hsum :
          (g₁ : EuclideanSpace ℝ (Fin d)) + (q.out : EuclideanSpace ℝ (Fin d)) =
            (g₂ : EuclideanSpace ℝ (Fin d)) + (q.out : EuclideanSpace ℝ (Fin d)) := by
        simpa [φ, hρ g₁ q.out, hρ g₂ q.out] using
          congrArg (fun x : s q => ((x : X) : EuclideanSpace ℝ (Fin d))) h
      have : (g₁ : EuclideanSpace ℝ (Fin d)) = (g₂ : EuclideanSpace ℝ (Fin d)) :=
        add_right_cancel hsum
      exact Subtype.ext (by simpa using this)
    have hn : Module.finrank ℤ Λ < d + 1 := by
      have hrank : Module.finrank ℤ Λ = d := by
        calc
          Module.finrank ℤ Λ = Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
            simpa using (ZLattice.rank (K := ℝ) (L := Λ))
          _ = d := by simp
      simp [hrank]
    let v : EuclideanSpace ℝ (Fin d) := q.out
    have hΛ :
        Summable (fun g : Λ => 1 / ‖((g : EuclideanSpace ℝ (Fin d)) + v)‖ ^ (d + 1)) := by
      have := ZLattice.summable_norm_sub_inv_pow (L := Λ) (n := d + 1) hn
        (-v)
      simpa [one_div, sub_eq_add_neg, add_assoc] using this
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨_, ⟨g, rfl⟩⟩
      exact ⟨g, rfl⟩
    have hcomp : Summable (fun g : Λ => f (φ g)) := by
      simpa [f, φ, hρ] using hΛ
    exact (Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).summable_iff.1 hcomp
  -- Apply `Real.summable_partition` and use finiteness of the orbit quotient.
  exact
    (summable_partition (f := f) hf_nonneg (s := s) hs).2
      ⟨horb, Summable.of_finite (f := fun q : Q => ∑' x : s q, f x)⟩

end Sets_Acted_Upon_By_Lattice

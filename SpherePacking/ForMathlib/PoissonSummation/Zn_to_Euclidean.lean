import SpherePacking.ForMathlib.PoissonSummation.Zn_Pi
import SpherePacking.ForMathlib.PoissonSummation.DualLattice

open LinearMap (BilinForm)
open ZLattice ZSpan Submodule LinearMap.BilinForm

/-!
# The Canonical Lattice ℤ^n in Euclidean Space

In this file, we explore the properties of the canonical lattice ℤⁿ in Euclidean space ℝⁿ. This
allows us to talk about properties like the self-dual property, which only makes sense in settings
where we have an inner-product (or some bilinear form) to work with.

## Main Definition
1. `Zn_Submodule_Euclidean` : The canonical lattice ℤⁿ, viewed as a submodule of Euclidean space.
2. `isZLattice_EucLattice` : The canonical lattice ℤⁿ is indeed a lattice in Euclidean space.

## Main Results
1. `EuclideanSpace.mem_Zn_Submodule_iff` : An element of Euclidean space lies in ℤⁿ iff it comes
  from a ℤ-valued vector.
2. `Zn_dualSubmodule_eq_Zn` : The lattice ℤⁿ is self-dual.
-/

/-- We denote by `Euc(n)` the Euclidean Space in `n` dimensions. -/
notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

section Submodule

/-!
In this section, we develop the theory of ℤⁿ as a submodule of Euclidean space.
-/

/-- The canonical lattice `ℤ^n`, viewed as a submodule of Euclidean space. -/
def Zn_Submodule_Euclidean (n : ℕ) : Submodule ℤ Euc(n) where
  carrier := {x | x ∈ ℤ^n}
  add_mem' := (ℤ^n).add_mem'
  zero_mem' := (ℤ^n).zero_mem'
  smul_mem' := (ℤ^n).smul_mem'

/-- An element of the Euclidean space lies in `ℤ^n` iff it comes from a ℤ-valued vector. -/
theorem EuclideanSpace.mem_Zn_Submodule_iff (n : ℕ) : ∀ x : Euc(n),
    x ∈ (Zn_Submodule_Euclidean n) ↔ ∃ m : Fin n → ℤ, ∀ i, x i = m i :=
  fun _ ↦ ⟨id, id⟩

/-- An element of the Euclidean space lies in `ℤ^n` iff all its coordinates are integers. -/
theorem EuclideanSpace.mem_Zn_Submodule_iff' (n : ℕ) : ∀ x : Euc(n),
    x ∈ (Zn_Submodule_Euclidean n) ↔ ∀ i : Fin n, ∃ m : ℤ, x i = m := by
  intro x
  constructor <;> intro h
  · obtain ⟨m, hm⟩ := h
    exact fun i => ⟨m i, hm i⟩
  · use fun i => (h i).choose
    exact fun i => Exists.choose_spec (h i)

end Submodule

/-- We denote by `EuclideanLattice(n)` the canonical free `ℤ`-submodule of `Euc(n)`. -/
notation "EucLattice(" n:arg ")" => Zn_Submodule_Euclidean n

section ZLattice

/-!
In this section, we develop the theory of ℤⁿ as a lattice in Euclidean space.
-/

instance instDiscreteTopology_EucLattice (n : ℕ) : DiscreteTopology (EucLattice(n)) :=
  instDiscreteTopology_Zn n

instance isZLattice_EucLattice (n : ℕ) : IsZLattice ℝ (EucLattice(n)) where
  span_top := by
    rw [← (isZLattice_Zn n).span_top]
    congr

end ZLattice

section Basis

/-!
In this section, we prove a few results about the interaction of `EucLattice(n)` with the standard
basis of `Euc(n)`.
-/

theorem PiLp_basisFun_mem_EucLattice (n : ℕ) :
    ∀ i : Fin n, (PiLp.basisFun 2 ℝ (Fin n)) i ∈ (ℤ^n) := by
  intro i
  simp only [PiLp.basisFun_apply, WithLp.equiv_symm_single]
  use fun j ↦ (if j = i then 1 else 0)
  intro i
  simp only [EuclideanSpace.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]

end Basis

section Self_Dual

/-! In this section, we show that the canonical lattice is self-dual. -/

theorem Zn_dualSubmodule_eq_Zn (n : ℕ) :
    ZLattice.Dual bilinFormOfRealInner EucLattice(n) = EucLattice(n) := by
  ext x
  simp only [Dual, dualSubmodule, bilinFormOfRealInner_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, mem_one, algebraMap_int_eq, eq_intCast, mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor <;> intro hx
  · rw [EuclideanSpace.mem_Zn_Submodule_iff']
    intro i
    obtain ⟨m, hm⟩ := hx (PiLp.basisFun 2 ℝ (Fin n) i) (PiLp_basisFun_mem_EucLattice n i)
    use m
    simp only [PiLp.basisFun_apply, WithLp.equiv_symm_pi_apply, Pi.single_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hm
    exact hm.symm
  · intro y hy
    rw [EuclideanSpace.mem_Zn_Submodule_iff] at hx hy
    obtain ⟨m₁, hm₁⟩ := hx
    obtain ⟨m₂, hm₂⟩ := hy
    use ∑ i : Fin n, m₁ i * m₂ i
    simp only [Int.cast_sum, Int.cast_mul]
    congr; ext i
    rw [mul_comm, hm₂ i, hm₁ i]


end Self_Dual

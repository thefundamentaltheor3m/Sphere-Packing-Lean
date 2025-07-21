import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have

import SpherePacking.ForMathlib.PoissonSummation.EuclideanSpace

/-! # The Canonical Lattice ℤ^n

In this file, we develop some theory about the canonical free ℤ-submodule of rank `n`, denoted
`ℤ^n`, of the Pi space `ℝ^n`. In particular, we devlop some theory about `ℤ^n` as a lattice, with
the long-term goal of proving the Poisson Summation Formula for Schwartz functions over `ℤ^n`.

## Main Definition
1. `Zn_Submodule` : The canonical free `ℤ`-submodule of `ℝ^n`.
2. `isZLattice_Zn` : `ℤ^n` is a lattice.

## Main Results
1. `Zn_eq_ZSpan_Pi_basisFun` : `ℤ^n` is the `ℤ`-span of the canonical `ℝ`-basis of `ℝ^n`.
2. `Zn_covolume` : The covolume of `ℤ^n` is `1`.
-/

open Submodule Set ZLattice IsZLattice LinearMap BilinForm Module MeasureTheory ZSpan

/-! We begin by defining some useful notation. -/

/-- We denote by `ℝ^n` the Pi type `Fin n → ℝ`. -/
notation "ℝ^" n:arg => Fin n → ℝ

section Submodule

/-! We now develop the theory of ℤ^n as a submodule of Euclidean space. -/

/-- We can define a submodule of `ℝ^n` whose elements are precisely those of `ℤ^n` that are coerced
into `ℝ^n`. -/
def Zn_Submodule (n : ℕ) : Submodule ℤ (ℝ^n) where
  carrier := {x : ℝ^n | ∃ (m : Fin n → ℤ), ∀ (i : Fin n), x i = m i}
  add_mem' := fun {a b} ha hb => by
    rw [mem_setOf_eq] at ha hb ⊢
    obtain ⟨m₁, hm₁⟩ := ha
    obtain ⟨m₂, hm₂⟩ := hb
    use m₁ + m₂
    simp [hm₁, hm₂]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    simp only [mem_setOf_eq, zsmul_eq_mul, forall_exists_index]
    intro c x v hxv
    use c • v
    simp [hxv]

end Submodule

-- Since `Zn_Submodule` is defined in a way that mimics how one would view `ℤ` as a submodule of
-- `ℝ`, we define the following notation for it.
/-- We denote by `ℤ^n` the canonical free `ℤ`-submodule living inside `Fin n → ℝ`. -/
notation "ℤ^" n:arg => Zn_Submodule n

noncomputable section Basis

/-!
In this section, we will use the standard basis for the Pi type `ℝ^n` to construct a basis for the
submodule `ℤ^n`. We will then be able to use this basis to show that `ℤ^n` has covolume `1`.
-/

/-- The canonical basis of `ℝ^n` embeds into `ℤ^n`. -/
theorem Pi_basisFun_mem_Zn (n : ℕ) : ∀ i : Fin n, (Pi.basisFun ℝ (Fin n)) i ∈ (ℤ^n) := by
  intro i
  simp only [Zn_Submodule, mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_setOf_eq]
  use fun j ↦ (if j = i then 1 else 0)
  simp only [Pi.basisFun_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  -- Below courtesy `aesop`
  intro i_1
  split
  next h =>
    subst h
    simp_all only [Pi.single_eq_same]
  next h => simp_all only [ne_eq, not_false_eq_true, Pi.single_eq_of_ne]

/-- The canonical basis of `ℤ^n`, defined as a family of vectors. -/
def Pi_basisFun_Zn (n : ℕ) : Fin n → ℤ^n :=
  fun i => ⟨Pi.basisFun ℝ (Fin n) i, Pi_basisFun_mem_Zn n i⟩

/-- The canonical basis of `ℝ^n` is `ℤ`-linearly independent. -/
theorem Pi_basisFun_Z_linear_independent (n : ℕ) :
    LinearIndependent ℤ (Pi.basisFun ℝ (Fin n)) := by
  have hLinIndep : LinearIndependent ℝ (PiLp.basisFun 2 ℝ (Fin n)) :=
    Basis.linearIndependent (PiLp.basisFun 2 ℝ (Fin n))
  rw [linearIndependent_iff'] at hLinIndep ⊢
  intro s g
  specialize hLinIndep s (fun i => g i)
  norm_cast at hLinIndep

/-- The canonical basis of `ℤ^n` is `ℤ`-linearly independent. -/
theorem Pi_basisFun_Zn_Z_linear_independent (n : ℕ) :
    LinearIndependent ℤ (Pi_basisFun_Zn n) := by
  have hLinIndep : LinearIndependent ℤ (Pi.basisFun ℝ (Fin n)) :=
    Pi_basisFun_Z_linear_independent n
  simp only [linearIndependent_iff', Pi_basisFun_Zn] at hLinIndep ⊢
  intro s g
  specialize hLinIndep s g
  intro hsum
  apply hLinIndep
  have : (0 : ℝ^n) = (@OfNat.ofNat (↥(ℤ^n)) 0 Zero.toOfNat0 : ↥(ℤ^n)) := by norm_cast
  rw [this, ← hsum]
  simp

/-- `ℤ^n` is the `ℤ`-span of the canonical `ℝ`-basis of `ℝ^n`. -/
theorem Zn_eq_ZSpan_Pi_basisFun {n : ℕ} :
    ℤ^n = span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
  ext ℓ
  simp only [Zn_Submodule, mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_setOf_eq,
    mem_span_range_iff_exists_fun, Pi.basisFun_apply]
  constructor <;> intro H
  · obtain ⟨m, hm⟩ := H
    use m
    calc ∑ i : Fin n, m i • Pi.single i (1 : ℝ)
    _ = ∑ i : Fin n, Pi.single i (m i : ℝ) := by congr; ext x y; simp [Pi.single_apply]
    _ = ∑ i : Fin n, Pi.single i (ℓ i : ℝ) := by simp only [hm]
    _ = ℓ := by ext x; simp
  · obtain ⟨c, hc⟩ := H
    use c
    rw [← hc]
    suffices : (∑ x : Fin n, c x • Pi.single x 1) = fun i ↦ (c i : ℝ)
    · simp only [this]
      tauto
    ext j
    simp [Pi.single_apply]

/-- The canonical basis of `ℤ^n` spans `ℤ^n`. -/
theorem Pi_basisFun_Zn_Zspan (n : ℕ) :
    ⊤ ≤ span ℤ (Set.range (Pi_basisFun_Zn n)) := by
  rw [top_le_iff]
  ext x
  simp only [mem_top, iff_true]
  have hy : ∃ y : ℝ^n, y ∈ ℤ^n ∧ y = x := by simp only [exists_eq_right, SetLike.coe_mem]
  obtain ⟨y, hy₁, hy₂⟩ := hy
  rw [Zn_eq_ZSpan_Pi_basisFun, hy₂] at hy₁
  rw [mem_span_range_iff_exists_fun] at hy₁ ⊢
  obtain ⟨f, hf⟩ := hy₁
  use fun i => f i
  unfold Pi_basisFun_Zn
  ext j
  rw [← hf]
  simp

/-- The canonical basis of `ℤ^n`. -/
def Pi_BasisFun_Z_basis (n : ℕ) : Basis (Fin n) ℤ (ℤ^n) := Basis.mk
  (Pi_basisFun_Zn_Z_linear_independent n) (Pi_basisFun_Zn_Zspan n)

/-- The canonical basis of `ℝ^n` has matrix equal to the identity matrix. -/
theorem Pi_BasisFun_basis.toMatrix (n : ℕ) :
    (Matrix.of (Pi.basisFun ℝ (Fin n))) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.one_apply]
  -- Below courtesy `aesop`
  simp_all only [Pi.basisFun_apply]
  split
  next h =>
    subst h
    simp_all only [Pi.single_eq_same]
  next h => simp_all only [ne_eq, not_false_eq_true, Pi.single_eq_of_ne']

-- Note that everything is explicit in the following theorem because that is the form in which we
-- will need it later.
/-- The canonical basis of `ℤ^n` has matrix equal to the identity matrix. -/
theorem Pi_BasisFun_Z_basis.toMatrix (n : ℕ) :
    (Matrix.of (@Function.comp (Fin n) (↥(ℤ^n)) (Fin n → ℝ) Subtype.val ⇑(Pi_BasisFun_Z_basis n)))
    = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [Pi_BasisFun_Z_basis, Basis.coe_mk, Matrix.of_apply, Function.comp_apply,
    Pi_basisFun_Zn, Pi.basisFun_apply, Matrix.one_apply]
  split
  next h =>
    subst h
    simp_all only [Pi.single_eq_same]
  next h => simp_all only [ne_eq, not_false_eq_true, Pi.single_eq_of_ne']

/-- The fundamental domain of the canonical basis of `ℝ^n` has volume `1`. -/
theorem Pi_BasisFun_fundamentalDomain (n : ℕ) :
    volume (fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
  rw [volume_fundamentalDomain (Pi.basisFun ℝ (Fin n)), Pi_BasisFun_basis.toMatrix n]
  simp

end Basis

section ZLattice

/-- `ℤ^n` has the discrete topology. -/
instance instDiscreteTopology_Zn (n : ℕ) : DiscreteTopology (ℤ^n) := by
  rw [Zn_eq_ZSpan_Pi_basisFun]
  exact ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
    (PiLp.basisFun 2 ℝ (Fin n))

/-- `ℤ^n` is a lattice. -/
instance isZLattice_Zn (n : ℕ) : IsZLattice ℝ (ℤ^n) := by
  simp only [Zn_eq_ZSpan_Pi_basisFun]
  exact instIsZLatticeRealSpan (Pi.basisFun ℝ (Fin n))
  -- exact isZLattice (PiLp.basisFun 2 ℝ (Fin n))

end ZLattice

section Free

/-!
In this section, we will explore the freeness of `ℤ^n` as a module over `ℤ`.
-/

/-- `ℤ^n` is a free `ℤ`-module. -/
theorem Zn_free (n : ℕ) : Free ℤ (ℤ^n) := instModuleFree_of_discrete_submodule (ℤ^n)

/-- The `finrank` of the free `ℤ`-module `ℤ^n` is `n`. -/
theorem Zn_finrank (n : ℕ) : finrank ℤ (ℤ^n) = n := by
  rw [ZLattice.rank ℝ]
  exact finrank_euclideanSpace_fin

/-- The `rank` of the free `ℤ`-module `ℤ^n` is `n`. -/
theorem Zn_rank (n : ℕ) : Module.rank ℤ (ℤ^n) = n := by rw [← finrank_eq_rank, Zn_finrank n]

end Free

section Covolume

/-! In this section, we show that the covolume of the canonical lattice in `Fin n → ℝ` is `1`. -/

-- The key ingredient:
-- #check ZLattice.covolume_eq_det

/-- The lattice `ℤ^n` has covolume `1`. -/
theorem Zn_covolume (n : ℕ) : covolume (ℤ^n) = 1 := by
  rw [ZLattice.covolume_eq_det (ℤ^n) (Pi_BasisFun_Z_basis n), Pi_BasisFun_Z_basis.toMatrix n]
  simp

end Covolume

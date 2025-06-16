/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.ForMathlib.Finsupp
import SpherePacking.ForMathlib.Vec


/-!
# Basic properties of the E₈ lattice

We define the E₈ lattice in two ways, as the ℤ-span of a chosen basis (`E8Matrix`), and as the set
of vectors in ℝ^8 with sum of coordinates an even integer and coordinates either all integers or
half-integers (`E8_Set`). We prove these two definitions are equivalent, and prove various
properties about the E₈ lattice.

See also earlier work which inspired this one by Gareth Ma (TODO: add permalink to old file)

## Main theorems

* `E8Matrix`: a fixed ℤ-basis for the E₈ lattice
* `E8_is_basis`: `E8Matrix` forms a ℝ-basis of ℝ⁸
* `E8_Set`: the set of vectors in E₈, characterised by relations of their coordinates
* `E8_Set_eq_span`: the ℤ-span of `E8Matrix` coincides with `E8_Set`
* `E8_norm_eq_sqrt_even`: E₈ is even
* `E8_unimodular`: E₈ is unimodular
* `E8_posDef`: E₈ is positive definite

-/

lemma AddCommGroup.ModEq.zsmul' {α : Type*} [AddCommGroup α] {p a b : α} {n : ℤ}
    (h : a ≡ b [PMOD p]) :
    n • a ≡ n • b [PMOD p] := by
  obtain ⟨k, hk⟩ := h
  refine ⟨n * k, ?_⟩
  rw [← zsmul_sub, hk, mul_smul]

@[simps]
def LinearMap.intCast {ι : Type*} (R : Type*) [Ring R] : (ι → ℤ) →ₗ[ℤ] (ι → R) where
  toFun f := fun i ↦ Int.cast (f i)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

def Submodule.evenLatticeInt : Submodule ℤ (Fin 8 → ℤ) where
  carrier := {v | ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [AddCommGroup.modEq_iff_int_modEq, Set.mem_setOf_eq, Pi.add_apply,
      Finset.sum_add_distrib]
    intro a b ha hb
    exact (ha.add hb).trans (by simp)
  zero_mem' := by simp
  smul_mem' := by
    simp only [Set.mem_setOf_eq, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, Int.cast_eq]
    intro c a ha
    rw [← Finset.mul_sum]
    exact ha.zsmul'.trans (by simp)

def Submodule.evenLattice (R : Type*) [Ring R] : Submodule ℤ (Fin 8 → R) :=
  evenLatticeInt.map (LinearMap.intCast R)

lemma Submodule.coe_evenLattice (R : Type*) [Ring R] [CharZero R] :
    (Submodule.evenLattice R : Set (Fin 8 → R)) =
    {v | (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2]} := by
  ext v
  simp only [evenLattice, map_coe, Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    constructor
    · exact fun i ↦ ⟨f i, by simp⟩
    · rw [evenLatticeInt, mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, AddCommGroup.modEq_comm] at hf
      obtain ⟨a, ha⟩ := hf
      simp only [sub_zero, smul_eq_mul] at ha
      rw [AddCommGroup.modEq_comm]
      use a
      simp [← Int.cast_sum, ha]
  simp only [evenLatticeInt, mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rintro ⟨hv, hv'⟩
  choose w hw using hv
  use w
  constructor
  · simp_rw [← hw, ← Int.cast_sum] at hv'
    obtain ⟨a, ha⟩ := hv'
    simp only [sub_zero, zsmul_eq_mul] at ha ⊢
    use a
    norm_cast at ha
  · simpa [funext_iff]

def Submodule.E8 (R : Type*) [Field R] :
    Submodule ℤ (EuclideanSpace R (Fin 8)) := evenLattice R ⊔ Submodule.span ℤ {fun _ ↦ 2⁻¹}

lemma Submodule.coe_E8 (R : Type*) [Field R] [CharZero R] :
    (Submodule.E8 R : Set (EuclideanSpace R (Fin 8))) =
    {v : EuclideanSpace R (Fin 8) |
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]} := by
  rw [E8]
  refine le_antisymm ?_ ?_
  · sorry
  intro (x : Fin 8 → R)
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_setOf_eq, SetLike.mem_coe, and_imp]
  rintro (hx | hx)
  · intro hx'
    have : x ∈ evenLattice R := by
      rw [← SetLike.mem_coe, coe_evenLattice]
      exact ⟨hx, hx'⟩
    exact mem_sup_left this
  intro hx'
  simp only [Odd] at hx
  choose y hy hy' using hx
  choose z hz using hy
  simp only [hz, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat] at *
  clear y hz
  have hi (i : Fin 8) : x i = z i + 2⁻¹ := by linear_combination - 2⁻¹ * hy' i
  have : span ℤ (evenLattice R) = evenLattice R := by simp
  rw [← this, sup_comm, ← Submodule.span_insert, Submodule.mem_span_insert, this]
  refine ⟨1, LinearMap.intCast R z, ?_, ?_⟩
  · rw [← SetLike.mem_coe, coe_evenLattice]
    constructor
    · simp
    simp only [LinearMap.intCast_apply]
    simp_rw [hi] at hx'
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, (show (8 : R) * 2⁻¹ = 2 • 2 by norm_num)] at hx'
    exact (AddCommGroup.add_nsmul_modEq _).symm.trans hx'
  · ext i
    rw [Pi.add_apply, LinearMap.intCast_apply, Pi.smul_apply, one_smul]
    linear_combination - 2⁻¹ * hy' i

#exit

-- TODO (BM): this shouldn't be noncomputable... check with @zwarich
noncomputable def Submodule.E8 (R : Type*) [NormedField R] [NeZero (2 : R)] :
    Submodule ℤ (EuclideanSpace R (Fin 8)) where
  carrier :=
    {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [Set.mem_setOf_eq, PiLp.add_apply, and_imp]
    rintro a b ha has hb hbs
    constructor
    · obtain ha | ha := ha
      · refine hb.imp ?_ ?_
        · intro hb i
          obtain ⟨a', ha⟩ := ha i
          obtain ⟨b', hb⟩ := hb i
          use a' + b'
          simp [ha, hb]
        · intro hb i
          obtain ⟨a', ha⟩ := ha i
          obtain ⟨b', hb', hb⟩ := hb i
          exact ⟨2 * a' + b', Even.add_odd (by simp) hb', by simp [← ha, ← hb, mul_add]⟩
      · refine hb.symm.imp ?_ ?_
        · intro hb i
          obtain ⟨a', ha', ha⟩ := ha i
          obtain ⟨b', hb', hb⟩ := hb i
          use (a' + b') / 2
          rw [Int.cast_div _ (by simpa using NeZero.ne 2), Int.cast_add, add_div (K := R), ha, hb,
            nsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Int.cast_ofNat,
            mul_div_cancel_left₀ _ (NeZero.ne 2), mul_div_cancel_left₀ _ (NeZero.ne _)]
          rw [← even_iff_two_dvd]
          apply ha'.add_odd hb'
        · intro hb i
          obtain ⟨a', ha', ha⟩ := ha i
          obtain ⟨b', hb⟩ := hb i
          exact ⟨a' + 2 * b', ha'.add_even (by simp), by simp [ha, hb, mul_add]⟩
    · rw [Finset.sum_add_distrib]
      exact ((has.add_right _).trans (hbs.add_left _)).trans (by simp)
  zero_mem' := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_setOf_eq, PiLp.zero_apply, forall_const,
      mul_zero, Finset.sum_const_zero, AddCommGroup.modEq_refl, and_true]
    refine Or.inl ⟨0, by simp⟩
  smul_mem' := by
    simp only [Set.mem_setOf_eq, PiLp.smul_apply, zsmul_eq_mul, and_imp]
    intro c a ha has
    constructor
    · obtain ha | ha := ha
      · left
        intro i
        obtain ⟨a, ha⟩ := ha i
        simp only [← ha, ← Int.cast_mul, Int.cast_inj, exists_eq]
        exact ⟨_, rfl⟩
      · obtain ⟨c, rfl⟩ | hc := c.even_or_odd
        · left
          intro i
          obtain ⟨j, hj, hj'⟩ := ha i
          refine ⟨c * j, ?_⟩
          rw [Int.cast_mul, hj', Int.cast_add]
          ring
        · right
          intro i
          obtain ⟨j, hj, hj'⟩ := ha i
          refine ⟨c * j, ?_⟩
          simp [hc, hj, hj', mul_left_comm]
    · rw [← Finset.mul_sum, ← zsmul_eq_mul]
      exact has.zsmul'.trans (by simp)

theorem Submodule.mem_E8 {R : Type*} [NormedField R] [NeZero (2 : R)]
    {v : EuclideanSpace R (Fin 8)} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rfl

theorem Submodule.mem_E8' {R : Type*} [NormedField R] [NeZero (2 : R)]
    {v : EuclideanSpace R (Fin 8)} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, Even n ∧ n = 2 • v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have (k : R) : (∃ n : ℤ, Even n ∧ n = 2 • k) ↔ (∃ n : ℤ, n = k) :=
    ⟨fun ⟨n, ⟨⟨l, hl⟩, hn⟩⟩ ↦ ⟨l, by simpa [← two_mul, hl, NeZero.ne (2 : R)] using hn⟩,
     fun ⟨n, hn⟩ ↦ ⟨2 * n, ⟨even_two_mul n, by simp [hn]⟩⟩⟩
  simp_rw [this, mem_E8]

section E8_basis

def E8Matrix (R : Type*) [Field R] : Matrix (Fin 8) (Fin 8) R := !![
    2,   0,   0,   0,   0,   0,   0,   0;
   -1,   1,   0,   0,   0,   0,   0,   0;
    0,  -1,   1,   0,   0,   0,   0,   0;
    0,   0,  -1,   1,   0,   0,   0,   0;
    0,   0,   0,  -1,   1,   0,   0,   0;
    0,   0,   0,   0,  -1,   1,   0,   0;
    0,   0,   0,   0,   0,  -1,   1,   0;
  2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹]

lemma lowerTriangular_E8Matrix {R : Type*} [Field R] :
    (E8Matrix R).BlockTriangular OrderDual.toDual := by
  simp [Matrix.BlockTriangular, E8Matrix, Fin.forall_fin_succ]

theorem E8Matrix_det_eq_one (R : Type*) [Field R] [NeZero (2 : R)] : (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ lowerTriangular_E8Matrix]
  simp [E8Matrix, Fin.prod_univ_eight, (NeZero.ne (2 : R))]

-- /--
-- A collection of 8 vectors which form a basis of the E8 lattice.
-- It's useful to make this separate from E8Matrix to avoid abusing defeq on EuclideanSpace.
-- -/
-- def E8BasisVectors (R : Type*) [Field R] : Fin 8 → EuclideanSpace R (Fin 8) :=
--   fun i ↦ ((E8Matrix R).col i)

-- lemma E8BasisVectors_apply (R : Type*) [Field R] (i : Fin 8) :
--     E8BasisVectors R i = (E8Matrix R).col i := rfl
--     --             if this rfl breaks, it's because WithLp changed    ^
--     --             my guess is `simp [E8BasisVectors]` will work as the new proof

-- lemma withLpEquiv_comp_E8BasisVectors (R : Type*) [Field R] :
--     WithLp.equiv 2 _ ∘ (E8BasisVectors R) = (E8Matrix R).col := rfl

-- private def E8_integer_basis (R : Type*) [Field R] : Fin 8 → EuclideanSpace R (Fin 8) :=
--   fun i ↦ (WithLp.equiv 2 _).symm ((E8Matrix R).col i)

private theorem E8BasisVectors_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_det_eq_one]
  simp
  -- rw [is_basis_iff_det (PiLp.basisFun 2 _ _), PiLp.basisFun_eq_pi_basisFun, Basis.det_map,
  --   LinearEquiv.symm_symm, WithLp.linearEquiv_apply, Pi.basisFun_det, ← Matrix.det,
  --   withLpEquiv_comp_E8BasisVectors, Matrix.col, Matrix.det_transpose, E8Matrix_det_eq_one]
  -- simp

private theorem linearIndependent_E8BasisVectors (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8BasisVectors_is_basis _).1

private theorem span_E8BasisVectors_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8BasisVectors_is_basis _).2

noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] :=
  Basis.mk (linearIndependent_E8BasisVectors R) (span_E8BasisVectors_eq_top R).ge

theorem range_E8Matrix_row_subset (R : Type*) [NormedField R] [NeZero (2 : R)] :
    Set.range (E8Matrix R).row ⊆ (Submodule.E8 R : Set (EuclideanSpace R (Fin 8))) := by
  suffices ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R by simpa [Set.subset_def]
  suffices
      ![2, 0, 0, 0, 0, 0, 0, 0] ∈ Submodule.E8 R ∧
      ![-1, 1, 0, 0, 0, 0, 0, 0] ∈ Submodule.E8 R ∧
      ![0, -1, 1, 0, 0, 0, 0, 0] ∈ Submodule.E8 R ∧
      ![0, 0, -1, 1, 0, 0, 0, 0] ∈ Submodule.E8 R ∧
      ![0, 0, 0, -1, 1, 0, 0, 0] ∈ Submodule.E8 R ∧
      ![0, 0, 0, 0, -1, 1, 0, 0] ∈ Submodule.E8 R ∧
      ![0, 0, 0, 0, 0, -1, 1, 0] ∈ Submodule.E8 R ∧
      ![2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹] ∈ Submodule.E8 R by
    simp only [Fin.forall_fin_succ, Fin.isValue, Fin.reduceSucc, IsEmpty.forall_iff, and_true]
    simp? [E8Matrix]

    sorry



  --   simp only [Set.subset_def, Set.mem_setOf_eq, forall_range_iff]
  --   exact this
  -- simp [Fin.range_fin_succ, E8BasisVectors, Fin.tail]


theorem span_E8Matrix (R : Type*) [NormedField R] [NeZero (2 : R)] :
    Submodule.span ℤ (Set.range (E8Matrix R).row) = Submodule.E8 R := by
  apply Submodule.span_eq_of_le
  · sorry
  · sorry

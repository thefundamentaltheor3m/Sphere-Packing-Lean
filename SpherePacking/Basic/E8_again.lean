/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
-- import SpherePacking.Basic.PeriodicPacking
-- import SpherePacking.ForMathlib.Finsupp
import Mathlib


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

variable {R : Type*}

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

def Submodule.evenLatticeInt (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
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

def Submodule.evenLattice (R : Type*) (n : ℕ) [Ring R] : Submodule ℤ (Fin n → R) :=
  (evenLatticeInt n).map (LinearMap.intCast R)

lemma Submodule.coe_evenLattice (R : Type*) (n : ℕ) [Ring R] [CharZero R] :
    (Submodule.evenLattice R n : Set (Fin n → R)) =
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

lemma Submodule.mem_evenLattice {R : Type*} [Ring R] [CharZero R] (n : ℕ)
    {v : Fin n → R} :
    v ∈ Submodule.evenLattice R n ↔
      (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [← SetLike.mem_coe, Submodule.coe_evenLattice];
  rfl

-- TODO (BM): this shouldn't be noncomputable... check with @zwarich
@[simps]
noncomputable def Submodule.E8 (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule ℤ (Fin 8 → R) where
  carrier :=
    {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [Set.mem_setOf_eq, and_imp, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply]
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
            Int.cast_ofNat,
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
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_image_equiv, Equiv.symm_symm,
      WithLp.equiv_zero, Set.mem_setOf_eq, Pi.zero_apply, forall_const, mul_zero,
      Finset.sum_const_zero, AddCommGroup.modEq_refl, and_true]
    refine Or.inl ⟨0, by simp⟩
  smul_mem' := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_image_equiv, Equiv.symm_symm, Set.mem_setOf_eq,
      WithLp.equiv_pi_apply, WithLp.equiv_smul, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply,
      and_imp]
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

theorem Submodule.mem_E8 {R : Type*} [Field R] [NeZero (2 : R)]
    {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [E8]
  simp

theorem Submodule.mem_E8' {R : Type*} [Field R] [NeZero (2 : R)]
    {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, Even n ∧ n = 2 • v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have (k : R) : (∃ n : ℤ, Even n ∧ n = 2 • k) ↔ (∃ n : ℤ, n = k) :=
    ⟨fun ⟨n, ⟨⟨l, hl⟩, hn⟩⟩ ↦ ⟨l, by simpa [← two_mul, hl, NeZero.ne (2 : R)] using hn⟩,
     fun ⟨n, hn⟩ ↦ ⟨2 * n, ⟨even_two_mul n, by simp [hn]⟩⟩⟩
  simp_rw [this, mem_E8]

theorem Submodule.mem_E8'' {R : Type*} [Field R] [NeZero (2 : R)]
    {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, n + 2⁻¹ = v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [mem_E8]
  suffices ∀ i, (∃ n : ℤ, Odd n ∧ n = 2 • v i) ↔ (∃ n : ℤ, n + 2⁻¹ = v i) by
    simp_rw [this]
  intro i
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hn'⟩
    use k
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, nsmul_eq_mul,
      Nat.cast_ofNat] at hn'
    have : (2 : R)⁻¹ * 2 = 1 := inv_mul_cancel₀ (NeZero.ne 2)
    linear_combination 2⁻¹ * hn' - (k - v i) * this
  · rintro ⟨k, hk⟩
    refine ⟨2 * k + 1, by simp, ?_⟩
    rw [← hk]
    simp [mul_inv_cancel₀, NeZero.ne]

lemma Submodule.E8_eq_sup (R : Type*) [Field R] [CharZero R] :
    E8 R = (evenLattice R 8 ⊔ Submodule.span ℤ {fun _ ↦ (2⁻¹ : R)}) := by
  refine le_antisymm ?h1 ?h2
  case h2 =>
    rw [sup_le_iff]
    constructor
    · intro v hv
      rw [mem_evenLattice] at hv
      simp [mem_E8, hv]
    · rw [Submodule.span_le]
      have h1 : (8 * 2⁻¹ : R) = (2 : ℤ) • 2 := by norm_num
      simpa [h1] using AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2
  case h1 =>
    intro x
    rw [mem_E8]
    simp only [Set.mem_setOf_eq, and_imp]
    rintro (hx | hx)
    · intro hx'
      apply mem_sup_left
      rw [← SetLike.mem_coe, coe_evenLattice]
      exact ⟨hx, hx'⟩
    intro hx'
    simp only [Odd] at hx
    choose y hy hy' using hx
    choose z hz using hy
    simp only [hz, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat] at *
    clear y hz
    have hi (i : Fin 8) : x i = z i + 2⁻¹ := by linear_combination - 2⁻¹ * hy' i
    have : span ℤ (evenLattice R 8) = evenLattice R 8 := by simp
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

lemma E8Matrix_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Matrix R = (E8Matrix ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Matrix]

lemma lowerTriangular_E8Matrix {R : Type*} [Field R] :
    (E8Matrix R).BlockTriangular OrderDual.toDual := by
  simp [Matrix.BlockTriangular, E8Matrix, Fin.forall_fin_succ]

theorem E8Matrix_det_eq_one (R : Type*) [Field R] [NeZero (2 : R)] : (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ lowerTriangular_E8Matrix]
  simp [E8Matrix, Fin.prod_univ_eight, (NeZero.ne (2 : R))]

private theorem E8Matrix_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_det_eq_one]
  simp

private theorem linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

theorem span_E8Matrix_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8Matrix_is_basis _).2

noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] :=
  Basis.mk (linearIndependent_E8Matrix R) (span_E8Matrix_eq_top R).ge

theorem range_E8Matrix_row_subset (R : Type*) [Field R] [CharZero R] :
    Set.range (E8Matrix R).row ⊆ Submodule.E8 R := by
  suffices ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R by
    simpa [- Submodule.coe_E8, Set.subset_def]
  rw [Fin.forall_fin_succ']
  refine ⟨?h1, ?h2⟩
  case h2 =>
    simp only [E8Matrix, Fin.reduceLast, Matrix.of_row, Fin.isValue, Matrix.cons_val]
    rw [Submodule.E8_eq_sup]
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [funext_iff, Fin.forall_fin_succ]
  intro i
  rw [Submodule.E8_eq_sup]
  apply Submodule.mem_sup_left
  revert i
  have h2 : ∃ n : ℤ, (n : R) = 2 := ⟨2, by simp⟩
  have hneg1 : ∃ n : ℤ, (n : R) = -1 := ⟨-1, by simp⟩
  have h1 : ∃ n : ℤ, (n : R) = 1 := ⟨1, by simp⟩
  simp [Fin.forall_fin_succ, E8Matrix, Submodule.mem_evenLattice, h1, h2, hneg1, Fin.sum_univ_eight]

def E8Inverse (R : Type*) [Field R] [NeZero (2 : R)] : Matrix (Fin 8) (Fin 8) R := !![
  2⁻¹, 0, 0, 0, 0, 0, 0, 0;
  2⁻¹, 1, 0, 0, 0, 0, 0, 0;
  2⁻¹, 1, 1, 0, 0, 0, 0, 0;
  2⁻¹, 1, 1, 1, 0, 0, 0, 0;
  2⁻¹, 1, 1, 1, 1, 0, 0, 0;
  2⁻¹, 1, 1, 1, 1, 1, 0, 0;
  2⁻¹, 1, 1, 1, 1, 1, 1, 0;
  -7 * 2⁻¹, -6, -5, -4, -3, -2, -1, 2]

lemma E8Inverse_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Inverse R = (E8Inverse ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Inverse]

lemma E8Inverse_mul_E8Matrix_rat : E8Inverse ℚ * E8Matrix ℚ = 1 := by decide +kernel

lemma E8Inverse_mul_E8Matrix {R : Type*} [Field R] [CharZero R] :
    E8Inverse R * E8Matrix R = 1 := by
  rw [E8Matrix_eq_cast, E8Inverse_eq_cast, ← Matrix.map_mul, E8Inverse_mul_E8Matrix_rat]
  simp

lemma E8Matrix_mul_E8Inverse {R : Type*} [Field R] [CharZero R] :
    E8Matrix R * E8Inverse R = 1 := by
  rw [Matrix.mul_eq_one_comm, E8Inverse_mul_E8Matrix]

lemma exists_cast_eq_vecMul_E8Inverse_aux {R : Type*} [Field R] [CharZero R]
    (v : Fin 8 → R) (w : Fin 8 → ℤ) (hv : v ∈ Submodule.E8 R)
    (hw : ∑ i, w i = 0) :
    ∃ c : ℤ, c = ∑ i, v i * w i := by
  obtain ⟨(hv' | hv'), hv⟩ := Submodule.mem_E8''.1 hv
  · choose v' hv' using hv'
    simp only [← hv']
    norm_cast
    simp
  · choose v' hv' using hv'
    simp only [← hv', add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    norm_cast
    simp only [Int.cast_sum, Int.cast_mul, hw, Int.cast_zero, mul_zero, add_zero]
    norm_cast
    simp

lemma exists_cast_eq_vecMul_E8Inverse {R : Type*} [Field R] [CharZero R]
    (v : Fin 8 → R) (hv : v ∈ Submodule.E8 R) :
    ∃ c : Fin 8 → ℤ, LinearMap.intCast R c = Matrix.vecMul v (E8Inverse R) := by
  set c' := Matrix.vecMul v (E8Inverse R)
  obtain ⟨c0, hc0⟩ : ∃ n : ℤ, (n : R) = c' 0 := by
    have h0' : c' 0 = (∑ i, v i) * 2⁻¹ - 4 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]
      ring
    obtain ⟨h0, h1⟩ := Submodule.mem_E8.1 hv
    obtain ⟨a, ha⟩ := h1.symm
    simp only [sub_zero, zsmul_eq_mul] at ha
    rw [ha, mul_inv_cancel_right₀ (NeZero.ne 2)] at h0'
    obtain h0 | h0 := h0
    · obtain ⟨n, hn⟩ := h0 7
      use a - 4 * n
      simp [hn, h0']
    · obtain ⟨n, hn⟩ := h0 7
      use a - 2 * n
      norm_num [hn, h0', mul_add, add_comm, ← mul_assoc]
  obtain ⟨c7, hc7⟩ : ∃ n : ℤ, (n : R) = c' 7 := by
    have hc7 : c' 7 = 2 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse, mul_comm]
    rw [Submodule.mem_E8''] at hv
    obtain ⟨(h0 | h0), _⟩ := hv
    · obtain ⟨n, hn⟩ := h0 7
      use 2 * n
      simp [hn, hc7]
    · obtain ⟨n, hn⟩ := h0 7
      use 2 * n + 1
      simp [← hn, hc7, mul_add]
  obtain ⟨c1, hc1⟩ : ∃ n : ℤ, (n : R) = c' 1 := by
    have := exists_cast_eq_vecMul_E8Inverse_aux v ![0, 1, 1, 1, 1, 1, 1, -6] hv rfl
    simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
  obtain ⟨c2, hc2⟩ : ∃ n : ℤ, (n : R) = c' 2 := by
    have := exists_cast_eq_vecMul_E8Inverse_aux v ![0, 0, 1, 1, 1, 1, 1, -5] hv rfl
    simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
  obtain ⟨c3, hc3⟩ : ∃ n : ℤ, (n : R) = c' 3 := by
    have := exists_cast_eq_vecMul_E8Inverse_aux v ![0, 0, 0, 1, 1, 1, 1, -4] hv rfl
    simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
  obtain ⟨c4, hc4⟩ : ∃ n : ℤ, (n : R) = c' 4 := by
    have := exists_cast_eq_vecMul_E8Inverse_aux v ![0, 0, 0, 0, 1, 1, 1, -3] hv rfl
    simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
  obtain ⟨c5, hc5⟩ : ∃ n : ℤ, (n : R) = c' 5 := by
    have := exists_cast_eq_vecMul_E8Inverse_aux v ![0, 0, 0, 0, 0, 1, 1, -2] hv rfl
    simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
  obtain ⟨c6, hc6⟩ : ∃ n : ℤ, (n : R) = c' 6 := by
    have := exists_cast_eq_vecMul_E8Inverse_aux v ![0, 0, 0, 0, 0, 0, 1, -1] hv rfl
    simpa [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using this
  refine ⟨![c0, c1, c2, c3, c4, c5, c6, c7], ?_⟩
  rw [funext_iff]
  simp [Fin.forall_fin_succ, *]

theorem span_E8Matrix (R : Type*) [Field R] [CharZero R] :
    Submodule.span ℤ (Set.range (E8Matrix R).row) = Submodule.E8 R := by
  apply Submodule.span_eq_of_le
  · exact range_E8Matrix_row_subset R
  intro v hv
  rw [Submodule.mem_span_range_iff_exists_fun]
  convert_to ∃ c : Fin 8 → ℤ, Matrix.vecMul (LinearMap.intCast R c) (E8Matrix R) = v
      using 3 with c
  · simp only [Matrix.vecMul_eq_sum, Matrix.row, LinearMap.intCast_apply, zsmul_eq_mul]
    rfl
  obtain ⟨c, hc⟩ := exists_cast_eq_vecMul_E8Inverse v hv
  use c
  rw [hc, Matrix.vecMul_vecMul, E8Inverse_mul_E8Matrix]
  simp

def E8.inn : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, -2, 0, 0, 0, 0, 0, 1;
    -2, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0, 0;
    0, 0, -1, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, 0;
    1, 0, 0, 0, 0, 0, 0, 2]

lemma E8Matrix_mul_E8Matrix_transpose_rat : E8Matrix ℚ * (E8Matrix ℚ).transpose =
    E8.inn.map (↑) := by decide +kernel

lemma E8Matrix_mul_E8Matrix_transpose [Field R] [CharZero R] :
    E8Matrix R * (E8Matrix R).transpose = E8.inn.map (↑) := by
  rw [E8Matrix_eq_cast, ← Matrix.transpose_map, ← Matrix.map_mul,
    E8Matrix_mul_E8Matrix_transpose_rat, Matrix.map_map]
  congr! 1
  ext n
  simp

lemma dotProduct_eq_inn {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j = E8.inn i j := by
  have : (E8Matrix R * (E8Matrix R).transpose) i j = (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j := by
    rw [Matrix.mul_apply']
    rfl
  rw [← this, E8Matrix_mul_E8Matrix_transpose]
  simp

lemma dotProduct_is_integer {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    ∃ z : ℤ, z = (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j :=
  ⟨_, (dotProduct_eq_inn _ _).symm⟩

lemma sum_dotProduct {α β γ : Type*} [Fintype β] [CommSemiring γ]
    {s : Finset α} {v : α → β → γ} {w : β → γ} :
    (∑ i ∈ s, v i) ⬝ᵥ w = ∑ i ∈ s, v i ⬝ᵥ w := by
  simp_rw [dotProduct, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma dotProduct_sum {α β γ : Type*} [Fintype β] [CommSemiring γ]
    {s : Finset α} {v : β → γ} {w : α → β → γ} :
    v ⬝ᵥ (∑ i ∈ s, w i) = ∑ i ∈ s, v ⬝ᵥ w i := by
  simp_rw [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma e8_integral {R : Type*} [Field R] [CharZero R] (v w : Fin 8 → R)
    (hv : v ∈ Submodule.E8 R) (hw : w ∈ Submodule.E8 R) :
    ∃ z : ℤ, z = v ⬝ᵥ w := by
  rw [← span_E8Matrix, Submodule.mem_span_range_iff_exists_fun] at hv hw
  obtain ⟨c, rfl⟩ := hv
  obtain ⟨d, rfl⟩ := hw
  simp_rw [sum_dotProduct, dotProduct_sum, dotProduct_smul, smul_dotProduct, dotProduct_eq_inn]
  simp only [zsmul_eq_mul]
  norm_cast
  simp

lemma e8_integral_self {R : Type*} [Field R] [CharZero R] (v : Fin 8 → R)
    (hv : v ∈ Submodule.E8 R) :
    ∃ z : ℤ, Even z ∧ z = v ⬝ᵥ v := by
  have h4 : Even (4 : ℤ) := ⟨2, rfl⟩
  rw [← span_E8Matrix, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  simp_rw [sum_dotProduct, dotProduct_sum, dotProduct_smul, smul_dotProduct, dotProduct_eq_inn,
    zsmul_eq_mul]
  norm_cast
  simp only [exists_eq_right, E8.inn, Int.reduceNeg, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Fin.sum_univ_eight, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, mul_neg, mul_zero, add_zero, mul_one, zero_add]
  ring_nf
  simp [h4, parity_simps]

open InnerProductSpace RCLike

theorem E8_norm_eq_sqrt_even
    (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    ∃ n : ℤ, Even n ∧ n = ‖(WithLp.equiv 2 _).symm v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_piLp_equiv_symm, star_trivial]
  exact e8_integral_self _ hv

theorem E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖(WithLp.equiv 2 _).symm v‖ := by
  rw [or_iff_not_imp_left, ← ne_eq]
  intro hv'
  obtain ⟨n, hn, hn'⟩ := E8_norm_eq_sqrt_even v hv
  have : 0 ≤ (n : ℝ) := by rw [hn']; positivity
  have : 0 ≤ n := mod_cast this
  have : n ≠ 0 := by contrapose! hv'; simpa [hv'] using hn'.symm
  have : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  apply le_of_sq_le_sq _ (by simp)
  rw [← hn', Real.sq_sqrt zero_le_two]
  exact mod_cast this

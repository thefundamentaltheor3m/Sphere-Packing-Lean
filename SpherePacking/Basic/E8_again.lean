/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import SpherePacking.Basic.PeriodicPacking
-- import SpherePacking.ForMathlib.Finsupp
import Mathlib


/-!
# Basic properties of the E₈ lattice

We define the E₈ lattice in two ways, as the ℤ-span of a chosen basis (`E8Matrix`), and as the set
of vectors in ℝ^8 with sum of coordinates an even integer and coordinates either all integers or
half-integers (`E8_Set`). We prove these two definitions are equivalent, and prove various
properties about the E₈ lattice.

See also earlier work which inspired this one, by Gareth Ma: https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/42c839d1002f5bcc1f8d2eb73190d97cd9c52852/SpherePacking/Basic/E8.lean

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

lemma Submodule.mem_E8 {R : Type*} [Field R] [NeZero (2 : R)]
    {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [E8]
  simp

lemma Submodule.mem_E8' {R : Type*} [Field R] [NeZero (2 : R)]
    {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, Even n ∧ n = 2 • v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have (k : R) : (∃ n : ℤ, Even n ∧ n = 2 • k) ↔ (∃ n : ℤ, n = k) :=
    ⟨fun ⟨n, ⟨⟨l, hl⟩, hn⟩⟩ ↦ ⟨l, by simpa [← two_mul, hl, NeZero.ne (2 : R)] using hn⟩,
     fun ⟨n, hn⟩ ↦ ⟨2 * n, ⟨even_two_mul n, by simp [hn]⟩⟩⟩
  simp_rw [this, mem_E8]

lemma Submodule.mem_E8'' {R : Type*} [Field R] [NeZero (2 : R)]
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

theorem Submodule.E8_eq_sup (R : Type*) [Field R] [CharZero R] :
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
      simpa [mem_E8, h1] using AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2
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

lemma E8Matrix_row_mem_E8 [Field R] [CharZero R] :
    ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R := by
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

lemma E8Matrix_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Matrix R = (E8Matrix ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Matrix]

lemma lowerTriangular_E8Matrix {R : Type*} [Field R] :
    (E8Matrix R).BlockTriangular OrderDual.toDual := by
  simp [Matrix.BlockTriangular, E8Matrix, Fin.forall_fin_succ]

theorem E8Matrix_unimodular (R : Type*) [Field R] [NeZero (2 : R)] : (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ lowerTriangular_E8Matrix]
  simp [E8Matrix, Fin.prod_univ_eight, (NeZero.ne (2 : R))]

private lemma E8Matrix_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_unimodular]
  simp

lemma linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

lemma span_E8Matrix_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8Matrix_is_basis _).2

noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] : Basis (Fin 8) R (Fin 8 → R) :=
  Basis.mk (linearIndependent_E8Matrix R) (span_E8Matrix_eq_top R).ge

lemma E8Basis_apply [Field R] [NeZero (2 : R)] (i : Fin 8) :
    E8Basis R i = (E8Matrix R).row i := by
  rw [E8Basis, Basis.coe_mk, Matrix.row]

lemma of_basis_eq_matrix [Field R] [CharZero R] : Matrix.of (E8Basis R) = E8Matrix R := by
  simp only [E8Basis, Basis.coe_mk]
  rfl

theorem range_E8Matrix_row_subset (R : Type*) [Field R] [CharZero R] :
    Set.range (E8Matrix R).row ⊆ Submodule.E8 R := by
  simpa [Set.subset_def] using E8Matrix_row_mem_E8 (R := R)

private def E8Inverse (R : Type*) [Field R] [NeZero (2 : R)] : Matrix (Fin 8) (Fin 8) R := !![
  2⁻¹, 0, 0, 0, 0, 0, 0, 0;
  2⁻¹, 1, 0, 0, 0, 0, 0, 0;
  2⁻¹, 1, 1, 0, 0, 0, 0, 0;
  2⁻¹, 1, 1, 1, 0, 0, 0, 0;
  2⁻¹, 1, 1, 1, 1, 0, 0, 0;
  2⁻¹, 1, 1, 1, 1, 1, 0, 0;
  2⁻¹, 1, 1, 1, 1, 1, 1, 0;
  -7 * 2⁻¹, -6, -5, -4, -3, -2, -1, 2]

private lemma E8Inverse_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Inverse R = (E8Inverse ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Inverse]

private lemma E8Inverse_mul_E8Matrix_rat : E8Inverse ℚ * E8Matrix ℚ = 1 := by decide +kernel

private lemma E8Inverse_mul_E8Matrix {R : Type*} [Field R] [CharZero R] :
    E8Inverse R * E8Matrix R = 1 := by
  rw [E8Matrix_eq_cast, E8Inverse_eq_cast, ← Matrix.map_mul, E8Inverse_mul_E8Matrix_rat]
  simp

private lemma E8Matrix_mul_E8Inverse {R : Type*} [Field R] [CharZero R] :
    E8Matrix R * E8Inverse R = 1 := by
  rw [Matrix.mul_eq_one_comm, E8Inverse_mul_E8Matrix]

private lemma exists_cast_eq_vecMul_E8Inverse_aux {R : Type*} [Field R] [CharZero R]
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

private lemma exists_cast_eq_vecMul_E8Inverse {R : Type*} [Field R] [CharZero R]
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

lemma E8Matrix_mul_E8Matrix_transpose_rat :
    E8Matrix ℚ * (E8Matrix ℚ).transpose = E8.inn.map (↑) := by
  decide +kernel

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

theorem E8_integral {R : Type*} [Field R] [CharZero R] (v w : Fin 8 → R)
    (hv : v ∈ Submodule.E8 R) (hw : w ∈ Submodule.E8 R) :
    ∃ z : ℤ, z = v ⬝ᵥ w := by
  rw [← span_E8Matrix, Submodule.mem_span_range_iff_exists_fun] at hv hw
  obtain ⟨c, rfl⟩ := hv
  obtain ⟨d, rfl⟩ := hw
  simp_rw [sum_dotProduct, dotProduct_sum, dotProduct_smul, smul_dotProduct, dotProduct_eq_inn]
  simp only [zsmul_eq_mul]
  norm_cast
  simp

theorem E8_integral_self {R : Type*} [Field R] [CharZero R] (v : Fin 8 → R)
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

lemma E8_norm_eq_sqrt_even
    (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    ∃ n : ℤ, Even n ∧ n = ‖(WithLp.equiv 2 _).symm v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_piLp_equiv_symm, star_trivial]
  exact E8_integral_self _ hv

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
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

noncomputable abbrev E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 _ (Fin 8 → ℝ)).symm

instance instDiscreteE8Lattice : DiscreteTopology E8Lattice := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  use 1, by norm_num
  rintro ⟨v, hv⟩ h
  simp only [dist_zero_right, AddSubgroupClass.coe_norm] at h
  simp only [Submodule.mk_eq_zero]
  simp only [Submodule.mem_map, WithLp.linearEquiv_symm_apply] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  simp only [WithLp.equiv_symm_eq_zero_iff]
  apply (E8_norm_lower_bound v hv).resolve_right ?_
  have : 1 < √2 := by rw [Real.lt_sqrt zero_le_one, sq, mul_one]; exact one_lt_two
  linarith

lemma span_E8_eq_top : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ := by
  simp only [Submodule.span, sInf_eq_top, Set.mem_setOf_eq]
  intros M hM
  rw [eq_top_iff, ← span_E8Matrix_eq_top ℝ, Submodule.span_le]
  exact (range_E8Matrix_row_subset ℝ).trans hM

lemma span_E8_eq_top' :
    Submodule.span ℝ (E8Lattice : Set (EuclideanSpace ℝ (Fin 8))) = ⊤ := by
  change Submodule.span ℝ ((WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm '' _) = _
  rw [Submodule.span_image, span_E8_eq_top]
  simp

theorem span_E8_eq_E8Lattice :
    Submodule.span ℤ
      (Set.range fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
      E8Lattice := by
  have : Set.range (fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
      (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm '' Set.range (E8Matrix ℝ).row := by
    rw [← Set.range_comp]
    rfl
  rw [this, Submodule.span_image, span_E8Matrix ℝ]

instance instIsZLatticeE8Lattice : IsZLattice ℝ E8Lattice where
  span_top := by rw [span_E8_eq_top']

lemma Submodule.span_restrict {ι M : Type*}
    [AddCommMonoid M] [Module ℤ M]
    (p : Submodule ℤ M)
    (f : ι → M) (h : ∀ i, f i ∈ p) :
    (span ℤ (Set.range f)).submoduleOf p = span ℤ (Set.range fun i ↦ (⟨f i, h i⟩ : p)) := by
  apply Submodule.map_injective_of_injective (f := Submodule.subtype p) (by simp)
  rw [Submodule.submoduleOf, map_comap_subtype, LinearMap.map_span, ← Set.range_comp]
  change _ = span ℤ (Set.range f)
  simp only [inf_eq_right, span_le]
  simpa [Set.subset_def]

noncomputable def E8_ℤBasis : Basis (Fin 8) ℤ E8Lattice := by
  refine Basis.mk
      (v := fun i ↦ ⟨(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i), ?_⟩) ?_ ?_
  · exact Submodule.mem_map_of_mem (E8Matrix_row_mem_E8 i)
  · refine LinearIndependent.of_comp (Submodule.subtype _) ?_
    refine LinearIndependent.of_comp (M' := (Fin 8 → ℝ)) (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)) ?_
    exact (linearIndependent_E8Matrix ℝ).restrict_scalars' ℤ
  · rw [← Submodule.map_le_map_iff_of_injective (f := E8Lattice.subtype) (by simp)]
    simp only [Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_E8_eq_E8Lattice.ge

lemma coe_E8_ℤBasis_apply (i : Fin 8) :
    E8_ℤBasis i = (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i) := by
  rw [E8_ℤBasis, Basis.coe_mk]

lemma E8_ℤBasis_ofZLatticeBasis_apply (i : Fin 8) :
    E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice i =
      (WithLp.equiv 2 (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i) := by
  simp only [Basis.ofZLatticeBasis_apply]
  rw [coe_E8_ℤBasis_apply]
  simp

section Packing

open scoped Real

noncomputable def E8Packing : PeriodicSpherePacking 8 where
  separation := √2
  lattice := E8Lattice
  centers := E8Lattice
  centers_dist := by
    simp only [Pairwise, E8Lattice, Submodule.map_coe, WithLp.linearEquiv_symm_apply, ne_eq,
      Subtype.forall, Set.mem_image_equiv, Subtype.mk.injEq]
    intro a ha b hb hab
    simpa [sub_eq_zero, hab, Subtype.dist_eq] using
      E8_norm_lower_bound _ (Submodule.sub_mem _ ha hb)
  lattice_action x y := add_mem

-- sanity checks
example : E8Packing.separation = √2 := rfl
example : E8Packing.lattice = E8Lattice := rfl

lemma E8Packing_numReps : E8Packing.numReps = 1 :=
  PeriodicSpherePacking.numReps_eq_one _ rfl

lemma E8Basis_apply_norm : ∀ i : Fin 8, ‖(WithLp.equiv 2 _).symm (E8Basis ℝ i)‖ ≤ 2 := by
  have : √2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  simp [E8Basis, E8Matrix, EuclideanSpace.norm_eq, Fin.forall_fin_succ, Fin.sum_univ_eight]
  norm_num [this]

lemma E8_ℤBasis_apply_norm : ∀ i : Fin 8, ‖E8_ℤBasis i‖ ≤ 2 := by
  intro i
  simp only [AddSubgroupClass.coe_norm]
  rw [coe_E8_ℤBasis_apply, ← E8Basis_apply]
  exact E8Basis_apply_norm i

section hack

def Matrix.myDet {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : R := M.det

lemma E8Matrix_myDet_eq_one (R : Type*) [Field R] [NeZero (2 : R)] : (E8Matrix R).myDet = 1 :=
  E8Matrix_unimodular R

open MeasureTheory ZSpan

lemma ZSpan.volume_fundamentalDomain' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ (ι → ℝ)) :
    volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).myDet| :=
  volume_fundamentalDomain b

lemma E8Basis_volume : volume (fundamentalDomain (E8Basis ℝ)) = 1 := by
  rw [volume_fundamentalDomain', of_basis_eq_matrix, E8Matrix_myDet_eq_one]
  simp

end hack

lemma test : MeasureTheory.volume (Set.Icc (0 : Fin 2 → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]
  simp

lemma test' {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) :
    MeasureTheory.volume (WithLp.equiv 2 _ ⁻¹' s) = MeasureTheory.volume s := by
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv ι).measure_preimage_equiv]
  rfl

lemma test'' {ι : Type*} [Fintype ι] (s : Set (EuclideanSpace ℝ ι)) :
    MeasureTheory.volume ((WithLp.equiv 2 _).symm ⁻¹' s) = MeasureTheory.volume s := by
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv ι).symm.measure_preimage_equiv]
  rfl

open MeasureTheory ZSpan in
lemma same_domain :
    (WithLp.linearEquiv 2 ℝ _).symm ⁻¹' fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) =
      fundamentalDomain (E8Basis ℝ) := by
  rw [← LinearEquiv.image_eq_preimage, ZSpan.map_fundamentalDomain]
  congr! 1
  ext i : 1
  simp [E8_ℤBasis, E8Basis_apply]

open MeasureTheory ZSpan in
lemma E8_Basis_volume :
    volume (fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice)) = 1 := by
  rw [← test'']
  erw [same_domain]
  rw [E8Basis_volume]

open MeasureTheory ZSpan in
theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
  rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]
  · rw [E8Packing_numReps, Nat.cast_one, one_mul, volume_ball, finrank_euclideanSpace,
      Fintype.card_fin, Nat.cast_ofNat]
    simp only [E8Packing]
    have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := calc
      √x ^ 8 = (√x ^ 2) ^ 4 := by rw [← pow_mul]
      _ = x ^ 4 := by rw [Real.sq_sqrt hx]
    rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, div_pow, this, this, ← mul_div_assoc,
      div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_div_assoc]
    norm_num [Nat.factorial, mul_one_div]
    convert div_one _
    · rw [E8_Basis_volume]
    · rw [← ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] <;> positivity
    · positivity
    · positivity
  · intro x hx
    trans ∑ i, ‖E8_ℤBasis i‖
    · rw [← fract_eq_self.mpr hx]
      convert norm_fract_le (K := ℝ) _ _
      simp; rfl
    · refine (Finset.sum_le_sum (fun i hi ↦ E8_ℤBasis_apply_norm i)).trans ?_
      norm_num

end Packing

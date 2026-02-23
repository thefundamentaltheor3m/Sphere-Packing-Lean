/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma
-/
module
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.Basic.PeriodicPacking.Theorem22
public import SpherePacking.Basic.PeriodicPacking.DensityFormula
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
public import SpherePacking.Basic.PeriodicPacking.BoundaryControl

/-!
# Basic properties of the E₈ lattice

We define the E₈ lattice in two ways, as the ℤ-span of a chosen basis (`E8Matrix`), and as the set
of vectors in ℝ^8 with sum of coordinates an even integer and coordinates either all integers or
half-integers (`E8_Set`). We prove these two definitions are equivalent, and prove various
properties about the E₈ lattice.

See also earlier work which inspired this one, by Gareth Ma: https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/42c839d1002f5bcc1f8d2eb73190d97cd9c52852/SpherePacking/Basic/E8.lean

## Main declarations

* `Submodule.E8`: The E₈ lattice as a submodule of `Fin 8 → R` for a field `R` in which `2` is
  nonzero. We define it to be the set of vectors in `Fin 8 → R` such that the sum of coordinates is
  even, and either all coordinates are integers, or all coordinates are half of an odd integer.
* `Submodule.E8_eq_sup`: The E₈ lattice can be seen as the smallest submodule containing both:
  the even lattice (the lattice of all integer points whose sum of coordinates is even); and the
  submodule spanned by the vector which is 2⁻¹ in each coordinate.
* `E8Matrix`: An explicit matrix whose rows form a basis for the E₈ lattice over ℤ.
* `E8Matrix_unimodular`: A proof that `E8Matrix` has determinant 1.
* `span_E8Matrix_eq_top`: The `ℝ`-span of `E8Matrix` is the whole of `ℝ⁸`.
* `span_E8Matrix`: The `ℤ`-span of `E8Matrix` is the E₈ lattice. This is the third characterisation
  of the E₈ lattice given in this file.
* `E8_integral`: The E₈ lattice is integral, i.e., the dot product of any two vectors in E₈ is an
  integer.
* `E8_integral_self`: The E₈ lattice is even, i.e., the norm-squared of any vector in E₈ is an even
  integer.
* `E8Lattice`: The E₈ lattice as a submodule of eight-dimensional Euclidean space. This additional
  definition is valuable, since it now puts the correct metric space structure on the lattice.
* `E8Packing`: The E₈ packing as a periodic sphere packing.
* `E8Packing_density`: The density of the E₈ packing is `π ^ 4 / 384`.
-/

variable {R : Type*}

open Module

lemma AddCommGroup.ModEq.zsmul' {α : Type*} [AddCommGroup α] {p a b : α} {n : ℤ}
    (h : a ≡ b [PMOD p]) :
    n • a ≡ n • b [PMOD p] :=
  (h.zsmul (z := n)).of_zsmul

/-- The coefficientwise cast map `(ι → ℤ) → (ι → R)` as a `ℤ`-linear map. -/
@[expose, simps]
public def LinearMap.intCast {ι : Type*} (R : Type*) [Ring R] : (ι → ℤ) →ₗ[ℤ] (ι → R) where
  toFun f := fun i ↦ Int.cast (f i)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

/-- The submodule of integer vectors in `Fin n → ℤ` whose coordinate sum is even. -/
public def Submodule.evenLatticeInt (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    intro a b ha hb
    simpa [AddCommGroup.modEq_iff_intModEq, Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib]
      using (ha.add hb)
  zero_mem' := by simp
  smul_mem' := by
    simp only [Set.mem_setOf_eq, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq]
    intro c a ha
    simpa [Finset.mul_sum] using (ha.zsmul' (n := c))

/-- The `ℤ`-submodule of `Fin n → R` consisting of integer vectors with even coordinate sum. -/
public def Submodule.evenLattice (R : Type*) (n : ℕ) [Ring R] : Submodule ℤ (Fin n → R) :=
  (evenLatticeInt n).map (LinearMap.intCast R)

/-- A membership characterization for `evenLattice` in terms of coordinates and an even sum. -/
public lemma Submodule.coe_evenLattice (R : Type*) (n : ℕ) [Ring R] [CharZero R] :
    (Submodule.evenLattice R n : Set (Fin n → R)) =
    {v | (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2]} := by
  ext v
  simp only [evenLattice, map_coe, Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun i ↦ ⟨f i, by simp⟩, ?_⟩
    have hf' : (∑ i, f i : ℤ) ≡ 0 [PMOD 2] := by simpa [evenLatticeInt] using hf
    simpa [Int.cast_sum] using (hf'.intCast (G := R))
  · rintro ⟨hv, hv'⟩
    choose w hw using hv
    refine ⟨w, ?_, by ext i; simpa using hw i⟩
    have hwZ :
        (∑ i, w i : ℤ) ≡ 0 [PMOD 2] :=
      (AddCommGroup.intCast_modEq_intCast' (G := R) (a := ∑ i, w i) (b := 0) (n := 2)).1
        (by simpa [← hw, Int.cast_sum] using hv')
    simpa [evenLatticeInt] using hwZ

/-- Membership in `evenLattice` (as a proposition). -/
public lemma Submodule.mem_evenLattice {R : Type*} [Ring R] [CharZero R] (n : ℕ)
    {v : Fin n → R} :
    v ∈ Submodule.evenLattice R n ↔
      (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [← SetLike.mem_coe, Submodule.coe_evenLattice]
  rfl

/-- The `E8` lattice as a `ℤ`-submodule of `Fin 8 → R`, defined by parity conditions. -/
public noncomputable def Submodule.E8 (R : Type*) [Field R] [NeZero (2 : R)] :
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
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_setOf_eq, Pi.zero_apply, forall_const,
      mul_zero, Finset.sum_const_zero, AddCommGroup.modEq_refl, and_true]
    refine Or.inl ⟨0, by simp⟩
  smul_mem' := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_setOf_eq, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, and_imp]
    intro c a ha has
    constructor
    · obtain ha | ha := ha
      · left
        intro i
        obtain ⟨a, ha⟩ := ha i
        simp only [← ha, ← Int.cast_mul]
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
    · simpa [zsmul_eq_mul, Finset.mul_sum] using (has.zsmul' (n := c))

lemma Submodule.mem_E8 {R : Type*} [Field R] [NeZero (2 : R)]
    {v : Fin 8 → R} :
    v ∈ E8 R ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rfl

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
    simp [NeZero.ne]

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
      simpa [mem_E8, (show (8 * 2⁻¹ : R) = (2 : ℤ) • 2 by norm_num)] using
        AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2
  case h1 =>
    intro x
    rw [mem_E8]
    rintro ⟨hx | hx, hx'⟩
    · refine mem_sup_left ?_
      exact (mem_evenLattice (R := R) (n := 8)).2 ⟨hx, hx'⟩
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

/-- A concrete matrix whose rows form a basis for the `E8` lattice. -/
@[expose] public def E8Matrix (R : Type*) [Field R] : Matrix (Fin 8) (Fin 8) R := !![
    2,   0,   0,   0,   0,   0,   0,   0;
   -1,   1,   0,   0,   0,   0,   0,   0;
    0,  -1,   1,   0,   0,   0,   0,   0;
    0,   0,  -1,   1,   0,   0,   0,   0;
    0,   0,   0,  -1,   1,   0,   0,   0;
    0,   0,   0,   0,  -1,   1,   0,   0;
    0,   0,   0,   0,   0,  -1,   1,   0;
  2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹]

/-- Each row of `E8Matrix` lies in the `E8` submodule. -/
public lemma E8Matrix_row_mem_E8 [Field R] [CharZero R] :
    ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R := by
  rw [Fin.forall_fin_succ']
  refine ⟨?h1, ?h2⟩
  case h2 =>
    rw [Submodule.E8_eq_sup]
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [E8Matrix, Fin.reduceLast, Matrix.of_row, Matrix.cons_val, funext_iff, Fin.forall_fin_succ]
  intro i
  rw [Submodule.E8_eq_sup]
  apply Submodule.mem_sup_left
  revert i
  have h2 : ∃ n : ℤ, (n : R) = 2 := ⟨2, by simp⟩
  have hneg1 : ∃ n : ℤ, (n : R) = -1 := ⟨-1, by simp⟩
  simp [Fin.forall_fin_succ, E8Matrix, Submodule.mem_evenLattice, h2, hneg1, Fin.sum_univ_eight]

lemma E8Matrix_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Matrix R = (E8Matrix ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]
  norm_num [Fin.forall_fin_succ, E8Matrix]

lemma lowerTriangular_E8Matrix {R : Type*} [Field R] :
    (E8Matrix R).BlockTriangular OrderDual.toDual := by
  simp [Matrix.BlockTriangular, E8Matrix, Fin.forall_fin_succ]

/-- The determinant of `E8Matrix` is `1`. -/
public theorem E8Matrix_unimodular (R : Type*) [Field R] [NeZero (2 : R)] :
    (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ lowerTriangular_E8Matrix]
  simp [E8Matrix, Fin.prod_univ_eight, (NeZero.ne (2 : R))]

lemma E8Matrix_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_unimodular]
  simp

/-- The rows of `E8Matrix` are linearly independent. -/
public lemma linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

/-- The rows of `E8Matrix` span the whole space. -/
public lemma span_E8Matrix_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8Matrix_is_basis _).2

/-- The basis of `Fin 8 → R` given by the rows of `E8Matrix`. -/
@[expose] public noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] :
    Basis (Fin 8) R (Fin 8 → R) :=
  Basis.mk (linearIndependent_E8Matrix R) (span_E8Matrix_eq_top R).ge

/-- Unfolding lemma for `E8Basis`. -/
public lemma E8Basis_apply [Field R] [NeZero (2 : R)] (i : Fin 8) :
    E8Basis R i = (E8Matrix R).row i := by
  rw [E8Basis, Basis.coe_mk, Matrix.row]

/-- The matrix of `E8Basis` is `E8Matrix`. -/
public lemma of_basis_eq_matrix [Field R] [CharZero R] : Matrix.of (E8Basis R) = E8Matrix R := by
  ext i j
  simp [E8Basis_apply, Matrix.row]

/-- The row vectors of `E8Matrix` all lie in the `E8` submodule. -/
public theorem range_E8Matrix_row_subset (R : Type*) [Field R] [CharZero R] :
    Set.range (E8Matrix R).row ⊆ Submodule.E8 R := by
  simpa [Set.subset_def] using E8Matrix_row_mem_E8 (R := R)

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
  let w1 : Fin 8 → ℤ := ![0, 1, 1, 1, 1, 1, 1, -6]
  let w2 : Fin 8 → ℤ := ![0, 0, 1, 1, 1, 1, 1, -5]
  let w3 : Fin 8 → ℤ := ![0, 0, 0, 1, 1, 1, 1, -4]
  let w4 : Fin 8 → ℤ := ![0, 0, 0, 0, 1, 1, 1, -3]
  let w5 : Fin 8 → ℤ := ![0, 0, 0, 0, 0, 1, 1, -2]
  let w6 : Fin 8 → ℤ := ![0, 0, 0, 0, 0, 0, 1, -1]
  obtain ⟨c0, hc0⟩ : ∃ n : ℤ, (n : R) = c' 0 := by
    have h0' : c' 0 = (∑ i, v i) * 2⁻¹ - 4 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]; ring
    obtain ⟨h0, h1⟩ := Submodule.mem_E8.1 hv
    rcases (AddCommGroup.modEq_iff_zsmul'.1 h1.symm) with ⟨a, ha⟩
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
    simpa [w1, c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using
      (exists_cast_eq_vecMul_E8Inverse_aux (R := R) v w1 hv rfl)
  obtain ⟨c2, hc2⟩ : ∃ n : ℤ, (n : R) = c' 2 := by
    simpa [w2, c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using
      (exists_cast_eq_vecMul_E8Inverse_aux (R := R) v w2 hv rfl)
  obtain ⟨c3, hc3⟩ : ∃ n : ℤ, (n : R) = c' 3 := by
    simpa [w3, c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using
      (exists_cast_eq_vecMul_E8Inverse_aux (R := R) v w3 hv rfl)
  obtain ⟨c4, hc4⟩ : ∃ n : ℤ, (n : R) = c' 4 := by
    simpa [w4, c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using
      (exists_cast_eq_vecMul_E8Inverse_aux (R := R) v w4 hv rfl)
  obtain ⟨c5, hc5⟩ : ∃ n : ℤ, (n : R) = c' 5 := by
    simpa [w5, c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using
      (exists_cast_eq_vecMul_E8Inverse_aux (R := R) v w5 hv rfl)
  obtain ⟨c6, hc6⟩ : ∃ n : ℤ, (n : R) = c' 6 := by
    simpa [w6, c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse] using
      (exists_cast_eq_vecMul_E8Inverse_aux (R := R) v w6 hv rfl)
  refine ⟨![c0, c1, c2, c3, c4, c5, c6, c7], ?_⟩
  rw [funext_iff]
  simp [Fin.forall_fin_succ, *]

/-- The `E8` lattice is the `ℤ`-span of the rows of `E8Matrix`. -/
public theorem span_E8Matrix (R : Type*) [Field R] [CharZero R] :
    Submodule.span ℤ (Set.range (E8Matrix R).row) = Submodule.E8 R := by
  apply Submodule.span_eq_of_le
  · exact range_E8Matrix_row_subset R
  intro v hv
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨c, hc⟩ := exists_cast_eq_vecMul_E8Inverse v hv
  refine ⟨c, ?_⟩
  have hvec : Matrix.vecMul (LinearMap.intCast R c) (E8Matrix R) = v := by
    rw [hc, Matrix.vecMul_vecMul, E8Inverse_mul_E8Matrix]
    simp
  simpa [Matrix.vecMul_eq_sum, Matrix.row, LinearMap.intCast_apply, zsmul_eq_mul] using hvec

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
  ext i j
  simp

lemma dotProduct_eq_inn {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j = E8.inn i j := by
  simpa [Matrix.mul_apply', Matrix.col_transpose] using
    congrArg (fun M => M i j) (E8Matrix_mul_E8Matrix_transpose (R := R))

/-- The squared norm of a vector in `E8` is an even integer. -/
public theorem E8_integral_self {R : Type*} [Field R] [CharZero R] (v : Fin 8 → R)
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

end E8_basis

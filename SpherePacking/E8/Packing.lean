/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma
-/
module
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.Basic.PeriodicPacking.DensityFormula

/-! # The E₈ lattice and packing

* Basic properties of the E₈ lattice: as parity submodule of `Fin 8 → R` and as the ℤ-span of
  `E8Matrix`, plus integrality of squared norms.
* The E₈ packing in `EuclideanSpace ℝ (Fin 8)` and the density `π^4 / 384`.
-/

variable {R : Type*}

open Module InnerProductSpace RCLike

/-! ## Basic E₈ lattice (merged from `E8.Basic`) -/

lemma AddCommGroup.ModEq.zsmul' {α : Type*} [AddCommGroup α] {p a b : α} {n : ℤ}
    (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD p] := (h.zsmul (z := n)).of_zsmul

/-- The coefficientwise cast map `(ι → ℤ) → (ι → R)` as a `ℤ`-linear map. -/
@[expose, simps]
public def LinearMap.intCast {ι : Type*} (R : Type*) [Ring R] : (ι → ℤ) →ₗ[ℤ] (ι → R) where
  toFun f i := Int.cast (f i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Integer vectors in `Fin n → ℤ` with even coordinate sum. -/
public def Submodule.evenLatticeInt (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' {a b} ha hb := by
    simpa [AddCommGroup.modEq_iff_intModEq, Pi.add_apply, Finset.sum_add_distrib] using ha.add hb
  zero_mem' := by simp
  smul_mem' c a ha := by simpa [Finset.mul_sum] using ha.zsmul' (n := c)

/-- `evenLatticeInt n` cast into `Fin n → R`. -/
public def Submodule.evenLattice (R : Type*) (n : ℕ) [Ring R] : Submodule ℤ (Fin n → R) :=
  (evenLatticeInt n).map (LinearMap.intCast R)

/-- Coordinatewise characterization of `evenLattice`: integer entries with even sum. -/
public lemma Submodule.coe_evenLattice (R : Type*) (n : ℕ) [Ring R] [CharZero R] :
    (Submodule.evenLattice R n : Set (Fin n → R)) =
    {v | (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2]} := by
  ext v
  simp only [evenLattice, map_coe, Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  refine ⟨fun ⟨f, hf, hfv⟩ => hfv ▸ ⟨fun i ↦ ⟨f i, by simp⟩, ?_⟩, fun ⟨hv, hv'⟩ => ?_⟩
  · simpa [Int.cast_sum] using
      (by simpa [evenLatticeInt] using hf : (∑ i, f i : ℤ) ≡ 0 [PMOD 2]).intCast (G := R)
  choose w hw using hv
  refine ⟨w, ?_, by ext i; simpa using hw i⟩
  simpa [evenLatticeInt] using (AddCommGroup.intCast_modEq_intCast' (G := R)
    (a := ∑ i, w i) (b := 0) (n := 2)).1 (by simpa [← hw, Int.cast_sum] using hv')

public lemma Submodule.mem_evenLattice {R : Type*} [Ring R] [CharZero R] (n : ℕ) {v : Fin n → R} :
    v ∈ Submodule.evenLattice R n ↔
      (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  simp [← SetLike.mem_coe, Submodule.coe_evenLattice]

/-- The `E8` lattice as a `ℤ`-submodule of `Fin 8 → R`, defined by parity conditions. -/
public noncomputable def Submodule.E8 (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule ℤ (Fin 8 → R) where
  carrier :=
    {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [Set.mem_setOf_eq, and_imp, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply]
    rintro a b ha has hb hbs
    refine ⟨?_, by simpa [Finset.sum_add_distrib] using
      ((has.add_right _).trans (hbs.add_left _)).trans (by simp)⟩
    obtain ha | ha := ha
    · refine hb.imp (fun hb i => ?_) (fun hb i => ?_) <;> obtain ⟨a', ha⟩ := ha i
      · exact let ⟨b', hb⟩ := hb i; ⟨a' + b', by simp [ha, hb]⟩
      exact let ⟨b', hb', hb⟩ := hb i
        ⟨2 * a' + b', Even.add_odd (by simp) hb', by simp [← ha, ← hb, mul_add]⟩
    refine hb.symm.imp (fun hb i => ?_) (fun hb i => ?_) <;> obtain ⟨a', ha', ha⟩ := ha i
    · obtain ⟨b', hb', hb⟩ := hb i
      exact ⟨(a' + b') / 2, by
        rw [Int.cast_div ((even_iff_two_dvd ..).1 (ha'.add_odd hb')) (by simpa using NeZero.ne 2),
          Int.cast_add, add_div (K := R), ha, hb, Int.cast_ofNat,
          mul_div_cancel_left₀ _ (NeZero.ne 2), mul_div_cancel_left₀ _ (NeZero.ne _)]⟩
    exact let ⟨b', hb⟩ := hb i
      ⟨a' + 2 * b', ha'.add_even (by simp), by simp [ha, hb, mul_add]⟩
  zero_mem' := ⟨.inl fun _ => ⟨0, by simp⟩, by simp⟩
  smul_mem' := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Set.mem_setOf_eq, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, and_imp]
    refine fun c a ha has => ⟨?_, by simpa [zsmul_eq_mul, Finset.mul_sum] using has.zsmul' (n := c)⟩
    rcases ha with ha | ha
    · exact .inl fun i ↦ let ⟨a, ha⟩ := ha i; ⟨c * a, by simp [← ha, Int.cast_mul]⟩
    rcases c.even_or_odd with ⟨c, rfl⟩ | hc
    · exact .inl fun i ↦ let ⟨j, hj, hj'⟩ := ha i
        ⟨c * j, by rw [Int.cast_mul, hj', Int.cast_add]; ring⟩
    exact .inr fun i ↦ let ⟨j, hj, hj'⟩ := ha i
      ⟨c * j, by simp [hc, hj, hj', mul_left_comm]⟩

lemma Submodule.mem_E8 {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔ ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 • v i))
      ∧ ∑ i, v i ≡ 0 [PMOD 2] := Iff.rfl

lemma Submodule.mem_E8'' {R : Type*} [Field R] [NeZero (2 : R)] {v : Fin 8 → R} :
    v ∈ E8 R ↔ ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, n + 2⁻¹ = v i))
      ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [mem_E8]
  suffices ∀ i, (∃ n : ℤ, Odd n ∧ n = 2 • v i) ↔ (∃ n : ℤ, n + 2⁻¹ = v i) by simp_rw [this]
  exact fun i => ⟨fun ⟨_, ⟨k, rfl⟩, hn'⟩ => ⟨k, by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, nsmul_eq_mul,
      Nat.cast_ofNat] at hn'
    linear_combination 2⁻¹ * hn' - (k - v i) * inv_mul_cancel₀ (NeZero.ne (2 : R))⟩,
    fun ⟨k, hk⟩ => ⟨2 * k + 1, by simp, by rw [← hk]; simp [NeZero.ne]⟩⟩

theorem Submodule.E8_eq_sup (R : Type*) [Field R] [CharZero R] :
    E8 R = (evenLattice R 8 ⊔ Submodule.span ℤ {fun _ ↦ (2⁻¹ : R)}) := by
  refine le_antisymm (fun x => ?_) (sup_le
    (fun v hv ↦ by simp [mem_E8, (mem_evenLattice (R := R) (n := 8)).1 hv])
    (Submodule.span_le.2 <| by
      simpa [mem_E8, show (8 * 2⁻¹ : R) = (2 : ℤ) • 2 by norm_num] using
        AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2))
  rw [mem_E8]
  rintro ⟨hx | hx, hx'⟩
  · exact Submodule.mem_sup_left ((mem_evenLattice (R := R) (n := 8)).2 ⟨hx, hx'⟩)
  simp only [Odd] at hx
  choose y hy hy' using hx
  choose z hz using hy
  simp only [hz, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat] at *
  rw [show (evenLattice R 8 : Submodule ℤ (Fin 8 → R)) = span ℤ (evenLattice R 8) by simp,
    sup_comm, ← Submodule.span_insert, Submodule.mem_span_insert, span_eq]
  refine ⟨1, LinearMap.intCast R z, ?_, by
    ext i; rw [Pi.add_apply, LinearMap.intCast_apply, Pi.smul_apply, one_smul]
    linear_combination - 2⁻¹ * hy' i⟩
  rw [← SetLike.mem_coe, coe_evenLattice]
  simp_rw [show ∀ i, x i = z i + 2⁻¹ from fun i => by linear_combination - 2⁻¹ * hy' i,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (8 : R) * 2⁻¹ = 2 • 2 by norm_num] at hx'
  exact ⟨by simp, by simpa using (AddCommGroup.add_nsmul_modEq _).symm.trans hx'⟩

/-- Concrete matrix whose rows form a basis for the `E8` lattice. -/
@[expose] public def E8Matrix (R : Type*) [Field R] : Matrix (Fin 8) (Fin 8) R :=
  !![2, 0, 0, 0, 0, 0, 0, 0; -1, 1, 0, 0, 0, 0, 0, 0;
     0, -1, 1, 0, 0, 0, 0, 0; 0, 0, -1, 1, 0, 0, 0, 0;
     0, 0, 0, -1, 1, 0, 0, 0; 0, 0, 0, 0, -1, 1, 0, 0;
     0, 0, 0, 0, 0, -1, 1, 0; 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹]

public lemma E8Matrix_row_mem_E8 [Field R] [CharZero R] :
    ∀ i, (E8Matrix R).row i ∈ Submodule.E8 R := by
  rw [Submodule.E8_eq_sup, Fin.forall_fin_succ']
  refine ⟨fun i => Submodule.mem_sup_left ?_, Submodule.mem_sup_right <| Submodule.subset_span <| by
    simp [E8Matrix, Fin.reduceLast, Matrix.of_row, Matrix.cons_val, funext_iff,
      Fin.forall_fin_succ]⟩
  revert i
  simp [Fin.forall_fin_succ, E8Matrix, Submodule.mem_evenLattice, Fin.sum_univ_eight,
    show ∃ n : ℤ, (n : R) = 2 from ⟨2, by simp⟩, show ∃ n : ℤ, (n : R) = -1 from ⟨-1, by simp⟩]

lemma E8Matrix_eq_cast (R : Type*) [Field R] [CharZero R] :
    E8Matrix R = (E8Matrix ℚ).map (Rat.castHom R) := by
  rw [← Matrix.ext_iff]; norm_num [Fin.forall_fin_succ, E8Matrix]

public theorem E8Matrix_unimodular (R : Type*) [Field R] [NeZero (2 : R)] :
    (E8Matrix R).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (by simp [Matrix.BlockTriangular, E8Matrix,
    Fin.forall_fin_succ] : (E8Matrix R).BlockTriangular OrderDual.toDual)]
  simp [E8Matrix, Fin.prod_univ_eight, NeZero.ne (2 : R)]

private lemma E8Matrix_is_basis (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row ∧
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_unimodular]; simp

public lemma linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

public lemma span_E8Matrix_eq_top (R : Type*) [Field R] [NeZero (2 : R)] :
    Submodule.span R (Set.range (E8Matrix R).row) = ⊤ := (E8Matrix_is_basis _).2

/-- Basis of `Fin 8 → R` given by the rows of `E8Matrix`. -/
@[expose] public noncomputable def E8Basis (R : Type*) [Field R] [NeZero (2 : R)] :
    Basis (Fin 8) R (Fin 8 → R) :=
  Basis.mk (linearIndependent_E8Matrix R) (span_E8Matrix_eq_top R).ge

public lemma E8Basis_apply [Field R] [NeZero (2 : R)] (i : Fin 8) :
    E8Basis R i = (E8Matrix R).row i := by simp [E8Basis, Matrix.row]

public lemma of_basis_eq_matrix [Field R] [CharZero R] : Matrix.of (E8Basis R) = E8Matrix R := by
  ext; simp [E8Basis_apply]

public theorem range_E8Matrix_row_subset (R : Type*) [Field R] [CharZero R] :
    Set.range (E8Matrix R).row ⊆ Submodule.E8 R :=
  Set.range_subset_iff.2 (E8Matrix_row_mem_E8 (R := R))

def E8Inverse (R : Type*) [Field R] [NeZero (2 : R)] : Matrix (Fin 8) (Fin 8) R :=
  !![2⁻¹, 0, 0, 0, 0, 0, 0, 0; 2⁻¹, 1, 0, 0, 0, 0, 0, 0;
     2⁻¹, 1, 1, 0, 0, 0, 0, 0; 2⁻¹, 1, 1, 1, 0, 0, 0, 0;
     2⁻¹, 1, 1, 1, 1, 0, 0, 0; 2⁻¹, 1, 1, 1, 1, 1, 0, 0;
     2⁻¹, 1, 1, 1, 1, 1, 1, 0; -7 * 2⁻¹, -6, -5, -4, -3, -2, -1, 2]

lemma exists_cast_eq_vecMul_E8Inverse {R : Type*} [Field R] [CharZero R]
    (v : Fin 8 → R) (hv : v ∈ Submodule.E8 R) :
    ∃ c : Fin 8 → ℤ, LinearMap.intCast R c = Matrix.vecMul v (E8Inverse R) := by
  set c' := Matrix.vecMul v (E8Inverse R)
  have aux (w : Fin 8 → ℤ) (hw : ∑ i, w i = 0) (k : Fin 8)
      (hk : c' k = ∑ i, v i * w i := by
        simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]) :
      ∃ n : ℤ, (n : R) = c' k := by
    obtain ⟨hv' | hv', _⟩ := Submodule.mem_E8''.1 hv <;> choose v' hv' using hv'
    exacts [⟨∑ i, v' i * w i, by simp [hk, ← hv', Int.cast_sum, Int.cast_mul]⟩,
      ⟨∑ i, v' i * w i, by simp [hk, ← hv', add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        Int.cast_sum, Int.cast_mul, show (∑ i, (w i : R)) = 0 from by exact_mod_cast hw]⟩]
  obtain ⟨c0, hc0⟩ : ∃ n : ℤ, (n : R) = c' 0 := by
    have h0' : c' 0 = (∑ i, v i) * 2⁻¹ - 4 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse]; ring
    obtain ⟨h0, h1⟩ := Submodule.mem_E8.1 hv
    obtain ⟨a, ha⟩ := AddCommGroup.modEq_iff_zsmul'.1 h1.symm
    rw [(by simpa [sub_zero, zsmul_eq_mul] using ha : ∑ i, v i = a * 2),
      mul_inv_cancel_right₀ (NeZero.ne 2)] at h0'
    obtain h0 | h0 := h0 <;> obtain ⟨n, hn⟩ := h0 7
    exacts [⟨a - 4 * n, by simp [hn, h0']⟩,
      ⟨a - 2 * n, by norm_num [hn, h0', mul_add, add_comm, ← mul_assoc]⟩]
  obtain ⟨c7, hc7⟩ : ∃ n : ℤ, (n : R) = c' 7 := by
    have hc7' : c' 7 = 2 * v 7 := by
      simp [c', Matrix.vecMul_eq_sum, Fin.sum_univ_eight, E8Inverse, mul_comm]
    obtain ⟨h0 | h0, _⟩ := Submodule.mem_E8''.1 hv <;> obtain ⟨n, hn⟩ := h0 7
    exacts [⟨2 * n, by simp [hn, hc7']⟩, ⟨2 * n + 1, by simp [← hn, hc7', mul_add]⟩]
  obtain ⟨c1, hc1⟩ := aux ![0, 1, 1, 1, 1, 1, 1, -6] rfl 1
  obtain ⟨c2, hc2⟩ := aux ![0, 0, 1, 1, 1, 1, 1, -5] rfl 2
  obtain ⟨c3, hc3⟩ := aux ![0, 0, 0, 1, 1, 1, 1, -4] rfl 3
  obtain ⟨c4, hc4⟩ := aux ![0, 0, 0, 0, 1, 1, 1, -3] rfl 4
  obtain ⟨c5, hc5⟩ := aux ![0, 0, 0, 0, 0, 1, 1, -2] rfl 5
  obtain ⟨c6, hc6⟩ := aux ![0, 0, 0, 0, 0, 0, 1, -1] rfl 6
  exact ⟨![c0, c1, c2, c3, c4, c5, c6, c7], by rw [funext_iff]; simp [Fin.forall_fin_succ, *]⟩

/-- The `E8` lattice is the `ℤ`-span of the rows of `E8Matrix`. -/
public theorem span_E8Matrix (R : Type*) [Field R] [CharZero R] :
    Submodule.span ℤ (Set.range (E8Matrix R).row) = Submodule.E8 R := by
  refine Submodule.span_eq_of_le _ (range_E8Matrix_row_subset R) fun v hv ↦ ?_
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨c, hc⟩ := exists_cast_eq_vecMul_E8Inverse v hv
  exact ⟨c, by
    simpa [Matrix.vecMul_eq_sum, Matrix.row, LinearMap.intCast_apply, zsmul_eq_mul] using
      show Matrix.vecMul (LinearMap.intCast R c) (E8Matrix R) = v by
        rw [hc, Matrix.vecMul_vecMul, show E8Inverse R * E8Matrix R = 1 by
          rw [E8Matrix_eq_cast, show E8Inverse R = (E8Inverse ℚ).map (Rat.castHom R) by
              rw [← Matrix.ext_iff]; norm_num [Fin.forall_fin_succ, E8Inverse],
            ← Matrix.map_mul, show E8Inverse ℚ * E8Matrix ℚ = 1 by decide +kernel]; simp]
        simp⟩

def E8.inn : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, -2, 0, 0, 0, 0, 0, 1; -2, 2, -1, 0, 0, 0, 0, 0;
     0, -1, 2, -1, 0, 0, 0, 0; 0, 0, -1, 2, -1, 0, 0, 0;
     0, 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0;
     0, 0, 0, 0, 0, -1, 2, 0; 1, 0, 0, 0, 0, 0, 0, 2]

lemma dotProduct_eq_inn {R : Type*} [Field R] [CharZero R] (i j : Fin 8) :
    (E8Matrix R).row i ⬝ᵥ (E8Matrix R).row j = E8.inn i j := by
  simpa [Matrix.mul_apply', Matrix.col_transpose] using congrArg (· i j)
    (show E8Matrix R * (E8Matrix R).transpose = E8.inn.map (↑) by
      rw [E8Matrix_eq_cast, ← Matrix.transpose_map, ← Matrix.map_mul,
        show E8Matrix ℚ * (E8Matrix ℚ).transpose = E8.inn.map (↑) by decide +kernel,
        Matrix.map_map]; ext; simp)

/-- The squared norm of a vector in `E8` is an even integer. -/
public theorem E8_integral_self {R : Type*} [Field R] [CharZero R] (v : Fin 8 → R)
    (hv : v ∈ Submodule.E8 R) : ∃ z : ℤ, Even z ∧ z = v ⬝ᵥ v := by
  rw [← span_E8Matrix, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  simp_rw [sum_dotProduct, dotProduct_sum, dotProduct_smul, smul_dotProduct, dotProduct_eq_inn,
    zsmul_eq_mul]
  norm_cast
  simp only [exists_eq_right, E8.inn, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val, mul_neg,
    mul_zero, add_zero, mul_one, zero_add]
  ring_nf; simp [show Even (4 : ℤ) from ⟨2, rfl⟩, parity_simps]

/-! ## E₈ packing -/

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖WithLp.toLp 2 v‖ := by
  rw [or_iff_not_imp_left, ← ne_eq]
  intro hv'
  obtain ⟨n, hn, hn'⟩ : ∃ n : ℤ, Even n ∧ n = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
    exact E8_integral_self _ hv
  have hn_ne : n ≠ 0 := by contrapose! hv'; simpa [hv'] using hn'.symm
  have hn2 : 2 ≤ n := by
    have : 0 ≤ n := by exact_mod_cast (by simp [hn'] : (0 : ℝ) ≤ (n : ℝ))
    obtain ⟨k, rfl⟩ := hn; omega
  exact le_of_sq_le_sq
    (by simpa [hn', Real.sq_sqrt zero_le_two] using (show (2 : ℝ) ≤ n from mod_cast hn2)) (by simp)

/-- The `E8` lattice as a `ℤ`-submodule of `EuclideanSpace ℝ (Fin 8)`. -/
public noncomputable def E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap

/-- The `E8` lattice is a discrete subgroup of `EuclideanSpace ℝ (Fin 8)`. -/
public instance instDiscreteE8Lattice : DiscreteTopology E8Lattice := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, by norm_num, ?_⟩
  rintro ⟨_, ⟨v, hv, rfl⟩⟩ hx'
  suffices v = 0 by simpa using congrArg (WithLp.toLp 2) this
  exact (E8_norm_lower_bound v hv).resolve_right (not_le_of_gt (lt_trans
    (by simpa [dist_zero_right, AddSubgroupClass.coe_norm] using hx') Real.one_lt_sqrt_two))

/-- `E8Lattice` spans the ambient space over `ℝ`. -/
public instance instIsZLatticeE8Lattice : IsZLattice ℝ E8Lattice where
  span_top := by
    have hE8 : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ :=
      eq_top_iff.2 (by simpa [span_E8Matrix_eq_top ℝ] using
        Submodule.span_mono (R := ℝ) (range_E8Matrix_row_subset ℝ))
    change Submodule.span ℝ
      ((WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm.toLinearMap '' (Submodule.E8 ℝ : Set _)) = ⊤
    rw [Submodule.span_image, hE8]; simp

noncomputable def E8_ℤBasis : Basis (Fin 8) ℤ E8Lattice := by
  refine Basis.mk
      (v := fun i ↦ ⟨(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i), ?_⟩) ?_ ?_
  · exact Submodule.mem_map_of_mem (E8Matrix_row_mem_E8 i)
  · exact LinearIndependent.of_comp (Submodule.subtype _) <|
      LinearIndependent.of_comp (M' := (Fin 8 → ℝ)) (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ))
        ((linearIndependent_E8Matrix ℝ).restrict_scalars' ℤ)
  · rw [← Submodule.map_le_map_iff_of_injective (f := E8Lattice.subtype) (by simp),
      Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    refine (?_ : Submodule.span ℤ
        (Set.range fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
        E8Lattice).ge
    rw [show Set.range (fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
          ((WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm :
              (Fin 8 → ℝ) →ₗ[ℤ] EuclideanSpace ℝ (Fin 8)) '' Set.range (E8Matrix ℝ).row by
        simpa [Function.comp] using
          Set.range_comp (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm (E8Matrix ℝ).row,
      ← Submodule.map_span, span_E8Matrix ℝ]
    simp [E8Lattice]

open scoped Real

/-- The periodic sphere packing in `ℝ^8` coming from the `E8` lattice. -/
@[expose] public noncomputable def E8Packing : PeriodicSpherePacking 8 where
  separation := √2
  lattice := E8Lattice
  centers := E8Lattice
  centers_dist := by
    simp only [Pairwise, E8Lattice, ne_eq, Subtype.forall, Subtype.mk.injEq]
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab
    simp only [dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
    convert (E8_norm_lower_bound _ (Submodule.sub_mem _ ha' hb')).resolve_left
      (sub_ne_zero.mpr (by contrapose! hab; simp [hab])) using 2
  lattice_action x y := add_mem

private lemma E8_ℤBasis_apply_norm : ∀ i : Fin 8, ‖E8_ℤBasis i‖ ≤ 2 := by
  have hbase : ∀ i : Fin 8, ‖WithLp.toLp 2 (E8Basis ℝ i)‖ ≤ 2 := by
    simp [E8Basis, E8Matrix, EuclideanSpace.norm_eq, Fin.forall_fin_succ, Fin.sum_univ_eight]
    norm_num [show (√2 : ℝ) ≤ 2 by rw [Real.sqrt_le_iff]; norm_num]
  simpa [E8_ℤBasis, Basis.coe_mk, E8Basis_apply] using hbase

open MeasureTheory ZSpan in
/-- The density of the `E8` packing. -/
public theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
  rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]
  · rw [PeriodicSpherePacking.numReps_eq_one _ rfl, Nat.cast_one, one_mul, volume_ball,
      finrank_euclideanSpace,
      Fintype.card_fin, Nat.cast_ofNat]
    simp only [E8Packing]
    have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hx]
    rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, div_pow, this, this, ← mul_div_assoc,
      div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_div_assoc]
    · norm_num [Nat.factorial, mul_one_div]
      convert div_one _
      · have hpreim : (WithLp.linearEquiv 2 ℝ _).symm ⁻¹' fundamentalDomain
            (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) = fundamentalDomain (E8Basis ℝ) := by
          rw [← LinearEquiv.image_eq_preimage_symm, ZSpan.map_fundamentalDomain]
          congr! 1; ext i : 1; simp [E8_ℤBasis, E8Basis_apply]
        rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
          _).symm.measure_preimage_equiv]
        erw [hpreim, show volume (fundamentalDomain (E8Basis ℝ)) = 1 by
          simp [volume_fundamentalDomain (b := E8Basis ℝ), of_basis_eq_matrix,
            E8Matrix_unimodular (R := ℝ)]]
      · rw [← ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] <;> positivity
    · positivity
    · positivity
  · intro x hx
    trans ∑ i, ‖E8_ℤBasis i‖
    · rw [← fract_eq_self.mpr hx]; convert norm_fract_le (K := ℝ) _ _; simp; rfl
    · exact (Finset.sum_le_sum (fun i _ ↦ E8_ℤBasis_apply_norm i)).trans (by norm_num)

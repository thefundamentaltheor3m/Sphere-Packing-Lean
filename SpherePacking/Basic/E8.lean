/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Gareth Ma
-/
import Architect
import SpherePacking.Basic.PeriodicPacking

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

@[simps]
def LinearMap.intCast {ι : Type*} (R : Type*) [Ring R] : (ι → ℤ) →ₗ[ℤ] (ι → R) where
  toFun f := fun i ↦ Int.cast (f i)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

def Submodule.evenLatticeInt (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | ∑ i, v i ≡ 0 [PMOD 2]}
  add_mem' := by
    simp only [AddCommGroup.modEq_iff_intModEq, Set.mem_setOf_eq, Pi.add_apply,
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
        Set.mem_setOf_eq] at hf
      simp only [LinearMap.intCast_apply, ← Int.cast_sum]
      convert hf.map (Int.castRingHom R) using 2 <;> simp
  simp only [evenLatticeInt, mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rintro ⟨hv, hv'⟩
  choose w hw using hv
  use w
  constructor
  · simp_rw [← hw, ← Int.cast_sum] at hv'
    rw [AddCommGroup.modEq_iff_zsmul] at hv' ⊢
    obtain ⟨m, hm⟩ := hv'
    refine ⟨m, ?_⟩
    apply Int.cast_injective (α := R)
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_zero,
      Int.cast_sum]
    simp only [zsmul_eq_mul, Int.cast_sum] at hm
    exact hm
  · simpa [funext_iff]

lemma Submodule.mem_evenLattice {R : Type*} [Ring R] [CharZero R] (n : ℕ)
    {v : Fin n → R} :
    v ∈ Submodule.evenLattice R n ↔
      (∀ i, ∃ n : ℤ, (n : R) = v i) ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  rw [← SetLike.mem_coe, Submodule.coe_evenLattice]
  rfl

-- TODO (BM): this shouldn't be noncomputable... check with @zwarich
@[blueprint
  "E8-Set"
  (statement := /--
  {($E_8$-lattice, Definition 1)}
    We define the \emph{$E_8$-lattice} (as a subset of $\R^8$) to be
  $$\Lambda_8=\{(x_i)\in\Z^8\cup(\Z+\textstyle\frac12\displaystyle )^8|\;\sum_{i=1}^8x_i\equiv
  0\;(\mathrm{mod\;2})\}.$$
  -/)]
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
      have h1 : (8 * 2⁻¹ : R) = (2 : ℤ) • 2 := by norm_num
      simpa [mem_E8, h1] using AddCommGroup.zsmul_modEq_zero (p := (2 : R)) 2
  case h1 =>
    intro x
    rw [mem_E8]
    simp only [and_imp]
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

@[blueprint
  "E8-Matrix"
  (statement := /--
  {($E_8$-lattice, Definition 2)}
    We define the \emph{$E_8$ basis vectors} to be the set of vectors
    \[ \B_8 =
    \left\{
      \begin{bmatrix}
        1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0
      \end{bmatrix},
      \begin{bmatrix}
        0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0
      \end{bmatrix},
      \begin{bmatrix}
        0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0
      \end{bmatrix},
      \begin{bmatrix}
        0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0
      \end{bmatrix},
      \begin{bmatrix}
        0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0
      \end{bmatrix},
      \begin{bmatrix}
        0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ 1 \\ 0
      \end{bmatrix},
      \begin{bmatrix}
        -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2
      \end{bmatrix},
      \begin{bmatrix}
        0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0
      \end{bmatrix}
    \right\}
    \]
  -/)]
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
  simp [Fin.forall_fin_succ, E8Matrix, Submodule.mem_evenLattice, h2, hneg1, Fin.sum_univ_eight]

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
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det, ← Matrix.det, Matrix.row,
    E8Matrix_unimodular]
  simp

lemma linearIndependent_E8Matrix (R : Type*) [Field R] [NeZero (2 : R)] :
    LinearIndependent R (E8Matrix R).row := (E8Matrix_is_basis _).1

@[blueprint
  "E8-is-basis"
  (statement := /-- $B_8$ is a $\R$-basis of $\R^8$. -/)
  (proof := /--
  It suffices to prove that $\B_8 \in \mathrm{GL}_8(\R)$. We prove this by explicitly defining the
  inverse matrix $\B_8^{-1}$ and proving $\B_8 \B_8^{-1} = I_8$, which implies that $\det(\B_8)$ is
  nonzero. See the Lean code for more details.,
  -/)
  (latexEnv := "lemma")]
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
  rw [mul_eq_one_comm, E8Inverse_mul_E8Matrix]

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
    rw [AddCommGroup.modEq_iff_zsmul] at h1
    obtain ⟨a, ha⟩ := h1
    simp only [zsmul_eq_mul, zero_sub] at ha
    have ha' : ∑ i, v i = ((-a : ℤ) : R) * 2 := by
      simp only [Int.cast_neg, neg_mul]
      rw [ha]
      ring
    rw [ha', mul_inv_cancel_right₀ (NeZero.ne 2)] at h0'
    obtain h0 | h0 := h0
    · obtain ⟨n, hn⟩ := h0 7
      use -a - 4 * n
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, hn, h0']
    · obtain ⟨n, hn⟩ := h0 7
      use -a - 2 * n
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat, h0']
      obtain ⟨_, hn'⟩ := hn
      simp only [two_nsmul] at hn'
      rw [hn']
      ring
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

@[blueprint
  "E8-defs-equivalent"
  (statement := /--
  The two definitions above coincide, i.e. $\Lambda_8 = \mathrm{span}_{\Z}(\B_8)$.
  -/)
  (proof := /--
  We prove each side contains the other side.
  
  For a vector $\vec{v} \in \Lambda_8 \subseteq \R^8$, we have $\sum_i \vec{v}_i \equiv 0 \pmod{2}$
  and $\vec{v}_i$ being either all integers or all half-integers. After some modulo arithmetic, it
  can be seen that $\B_8^{-1}\vec{v}$ as integer coordinates (i.e. it is congruent to $0$ modulo
  $1$). Hence, $\vec{v} \in \mathrm{span}_{\Z}(\B_8)$.
  
  For the opposite direction, we write the vector as $\vec{v} = \sum_i c_i\B_8^i \in
  \mathrm{span}_{\Z}(\B_8)$ with $c_i$ being integers and $\B_8^i$ being the $i$-th basis vector.
  Expanding the definition then gives $\vec{v} = \left(c_1 - \frac{1}{2}c_7, -c_1 + c_2 -
  \frac{1}{2}c_7, \cdots, -\frac{1}{2}c_7\right)$. Again, after some modulo arithmetic, it can be
  seen that $\sum_i \vec{v}_i$ is indeed $0$ modulo $2$ and are all either integers and
  half-integers, concluding the proof.
  
  (Note: this proof doesn't depend on that $\B_8$ is linearly independent.)
  -/)]
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

end E8_basis

open InnerProductSpace RCLike

@[blueprint
  "E8-vector-norms"
  (statement := /--
  All vectors in $\Lambda_8$ have norm of the form $\sqrt{2n}$, where $n$ is a nonnegative integer.
  -/)
  (proof := /--
  Writing $\vec{v} = \sum_i c_i\B_8^i$, we have $\|v\|^2 = \sum_i \sum_j c_ic_j (\B_8^i \cdot
  \B_8^j)$. Computing all $64$ pairs of dot products and simplifying, we get a massive term that is
  a quadratic form in $c_i$ with even integer coefficients, concluding the proof.
  -/)
  (latexEnv := "lemma")]
lemma E8_norm_eq_sqrt_even
    (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    ∃ n : ℤ, Even n ∧ n = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
  exact E8_integral_self _ hv

lemma E8_norm_lower_bound (v : Fin 8 → ℝ) (hv : v ∈ Submodule.E8 ℝ) :
    v = 0 ∨ √2 ≤ ‖WithLp.toLp 2 v‖ := by
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

@[blueprint
  "E8-Lattice"
  (statement := /-- $\Lambda_8$ is an additive subgroup of $\R^8$. -/)
  (proof := /--
  Trivially follows from that $\Lambda_8 \subseteq \R^8$ is the $\Z$-span of $\B_8$ and hence an
  additive group.
  -/)
  (latexEnv := "lemma")]
noncomputable abbrev E8Lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) :=
  (Submodule.E8 ℝ).map (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap

@[blueprint
  (statement := /--
  $c\Lambda_8$ is discrete, i.e. that the subspace topology induced by its inclusion into $\R^8$ is
  the discrete topology.
  -/)
  (proof := /--
  Since $\Lambda_8$ is a topological group and $+$ is continuous, it suffices to prove that $\{0\}$
  is open in $\Lambda_8$. This follows from the fact that there is an open ball $\B(\sqrt{2})
  \subseteq \R^8$ around it containing no other lattice points, since the shortest nonzero vector
  has norm $\sqrt{2}$.
  -/)
  (latexEnv := "lemma")]
instance instDiscreteE8Lattice : DiscreteTopology E8Lattice := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  use 1, by norm_num
  rintro ⟨v, hv⟩ h
  simp only [dist_zero_right, AddSubgroupClass.coe_norm] at h
  simp only [Submodule.mk_eq_zero]
  simp only [Submodule.mem_map] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  suffices v = 0 from congrArg (WithLp.toLp 2) this
  refine (E8_norm_lower_bound v hv).resolve_right ?_
  have : 1 < √2 := by rw [Real.lt_sqrt zero_le_one, sq, mul_one]; exact one_lt_two
  simp only [not_le]
  calc ‖WithLp.toLp 2 v‖ = ‖(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm v‖ := rfl
    _ < 1 := h
    _ < √2 := this

lemma span_E8_eq_top : Submodule.span ℝ (Submodule.E8 ℝ : Set (Fin 8 → ℝ)) = ⊤ := by
  simp only [Submodule.span, sInf_eq_top, Set.mem_setOf_eq]
  intros M hM
  rw [eq_top_iff, ← span_E8Matrix_eq_top ℝ, Submodule.span_le]
  exact (range_E8Matrix_row_subset ℝ).trans hM

lemma span_E8_eq_top' :
    Submodule.span ℝ (E8Lattice : Set (EuclideanSpace ℝ (Fin 8))) = ⊤ := by
  change Submodule.span ℝ ((WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm '' _) = _
  have h : (⇑(WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm : (Fin 8 → ℝ) → _) =
      (⇑(WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm.toLinearMap : (Fin 8 → ℝ) → _) := rfl
  rw [h, ← Submodule.map_span, span_E8_eq_top]
  simp

lemma span_E8Matrix_eq_E8Lattice :
    Submodule.span ℤ
      (Set.range fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
      E8Lattice := by
  have heq : Set.range (fun i ↦ (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i)) =
      (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm '' Set.range (E8Matrix ℝ).row := by
    rw [← Set.range_comp]
    rfl
  have hcoe : (⇑(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm : (Fin 8 → ℝ) → _) =
      (⇑(WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm.toLinearMap : (Fin 8 → ℝ) → _) := rfl
  rw [heq, hcoe, ← Submodule.map_span, span_E8Matrix ℝ]

@[blueprint
  "instLatticeE8"
  (statement := /--
  $c\Lambda_8$ is a $\Z$-lattice, i.e. it is discrete and spans $\R^8$ over $\R$.
  -/)
  (proof := /--
  The first part is by \cref{instDiscreteE8Lattice}, and the second part follows from that $\B_8$ is
  a basis (\cref{E8-is-basis}) and hence linearly independent over $\R$.
  -/)
  (latexEnv := "lemma")]
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
    exact span_E8Matrix_eq_E8Lattice.ge

lemma coe_E8_ℤBasis_apply (i : Fin 8) :
    E8_ℤBasis i = (WithLp.linearEquiv 2 ℤ (Fin 8 → ℝ)).symm ((E8Matrix ℝ).row i) := by
  rw [E8_ℤBasis, Basis.coe_mk]

lemma E8_ℤBasis_ofZLatticeBasis_apply (i : Fin 8) :
    E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice i =
      (WithLp.toLp 2) ((E8Matrix ℝ).row i) := by
  simp only [Basis.ofZLatticeBasis_apply]
  rw [coe_E8_ℤBasis_apply]
  simp

section Packing

open scoped Real

@[blueprint
  (statement := /--
  The \emph{$E_8$ sphere packing} is the (periodic) sphere packing with separation $\sqrt{2}$, whose
  set of centres is $\Lambda_8$.
  -/)]
noncomputable def E8Packing : PeriodicSpherePacking 8 where
  separation := √2
  lattice := E8Lattice
  centers := E8Lattice
  centers_dist := by
    simp only [Pairwise, E8Lattice, ne_eq, Subtype.forall, Subtype.mk.injEq]
    intro a ha b hb hab
    rw [SetLike.mem_coe, Submodule.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hsub : a' - b' ∈ Submodule.E8 ℝ := Submodule.sub_mem _ ha' hb'
    have hne : a' ≠ b' := by
      contrapose! hab
      simp [hab]
    simp only [dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
    have hne' : a' - b' ≠ 0 := sub_ne_zero.mpr hne
    convert (E8_norm_lower_bound _ hsub).resolve_left hne' using 2
  lattice_action x y := add_mem

lemma E8Packing_separation : E8Packing.separation = √2 := rfl
lemma E8Packing_lattice : E8Packing.lattice = E8Lattice := rfl

lemma E8Packing_numReps : E8Packing.numReps = 1 :=
  PeriodicSpherePacking.numReps_eq_one _ rfl

lemma E8Basis_apply_norm : ∀ i : Fin 8, ‖WithLp.toLp 2 (E8Basis ℝ i)‖ ≤ 2 := by
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

@[blueprint
  "E8Packing-covol"
  (statement := /-- $\Vol{\Lambda_8} = \mathrm{Covol}(\R^8 / \Lambda_8) = 1$. -/)
  (proof := /--
  \todo{In theory this should follow directly from $\det(\Lambda_8) = 1$, but Lean hates me and
  \texttt{EuclideanSpace} is being annoying.}
  -/)
  (latexEnv := "lemma")]
lemma E8Basis_volume : volume (fundamentalDomain (E8Basis ℝ)) = 1 := by
  rw [volume_fundamentalDomain', of_basis_eq_matrix, E8Matrix_myDet_eq_one]
  simp

end hack

lemma test'' {ι : Type*} [Fintype ι] (s : Set (EuclideanSpace ℝ ι)) :
    MeasureTheory.volume ((WithLp.equiv 2 _).symm ⁻¹' s) = MeasureTheory.volume s := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm.measure_preimage_equiv]
  rfl

open MeasureTheory ZSpan in
lemma same_domain :
    (WithLp.linearEquiv 2 ℝ _).symm ⁻¹' fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) =
      fundamentalDomain (E8Basis ℝ) := by
  rw [← LinearEquiv.image_eq_preimage_symm, ZSpan.map_fundamentalDomain]
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
@[blueprint
  "E8Packing-density"
  (statement := /-- We have $\Delta_{\mathcal{P}(E_8)} = \frac{\pi^4}{384}$. -/)
  (proof := /--
  By \cref{theorem:psp-density}, we have $\Delta_{\mathcal{P}(E_8)} = |E_8 / E_8| \cdot
  \frac{\Vol{\mathcal{B}_8(\sqrt{2} / 2)}}{\mathrm{Covol}(E_8)} = \frac{\pi^4}{384}$, where the last
  equality follows from \cref{E8Packing-covol} and the formula for volume of a ball:
  $\Vol{\mathcal{B}_d(R)} = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)$.
  -/)]
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
    · norm_num [Nat.factorial, mul_one_div]
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

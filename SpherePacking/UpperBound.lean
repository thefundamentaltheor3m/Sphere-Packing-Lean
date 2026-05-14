module
public import SpherePacking.Basic.SpherePacking
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.CohnElkies.LPBound
import SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.B.AnotherIntegral
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.MagicFunction.g.CohnElkies.SignConditions

/-!
# Upper bound for sphere packing in dimension 8

Defines `scaledMagic`, obtained from Viazovska's magic function `g` by precomposing with scaling
by `Real.sqrt 2`, transfers the Cohn-Elkies sign conditions from `g` to the scaled function
`scaledMagic`, and uses the Cohn-Elkies linear programming bound to obtain an upper bound for
`SpherePackingConstant 8`. Includes `g_real` / `g_real_fourier` (blueprint `thm:g1`/`thm:g`)
showing that `g` and its Fourier transform are real-valued, and packages the final main theorem.

Also contains basic properties of the E₈ lattice (merged from `E8.Packing`): the E₈ lattice as
the parity submodule of `Fin 8 → R` and as the ℤ-span of `E8Matrix`, integrality of squared
norms, and the periodic sphere packing `E8Packing` of density `π^4 / 384`.

## Main statements
* `SpherePacking.SpherePackingConstant_le_E8Packing_density`
* `SpherePacking.MainTheorem`
* `E8Packing_density`
-/

section E8LatticeAndPacking

variable {R : Type*}

open Module InnerProductSpace RCLike

/-! ## Basic E₈ lattice -/

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

end E8LatticeAndPacking

namespace SpherePacking

open scoped FourierTransform ENNReal SchwartzMap
open SchwartzMap SpherePacking.ForMathlib.Fourier
open MeasureTheory Real SpherePacking Metric

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

/-- Non-vanishing of `Real.sqrt 2`. -/
public lemma sqrt2_ne_zero : (Real.sqrt (2 : ℝ)) ≠ 0 :=
  Real.sqrt_ne_zero'.2 (by positivity)

/-- The scaled Schwartz function used for the dimension-8 Cohn-Elkies LP bound. -/
@[expose] public noncomputable def scaledMagic : 𝓢(ℝ⁸, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero).toContinuousLinearEquiv
    g

/-- The value of `scaledMagic` at `0` is `1`. -/
public theorem scaledMagic_zero : scaledMagic 0 = 1 := by
  simp [scaledMagic, g_zero]

/-- The value of the Fourier transform of `scaledMagic` at `0` is `1 / 16`. -/
public theorem fourier_scaledMagic_zero : FT scaledMagic 0 = (1 / 16 : ℂ) := by
  let c : ℝ := Real.sqrt 2
  let A : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ := LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) c sqrt2_ne_zero
  have hdet : abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)) = (16 : ℝ) := by
    have hA : (A : ℝ⁸ →ₗ[ℝ] ℝ⁸) = c • (LinearMap.id : ℝ⁸ →ₗ[ℝ] ℝ⁸) := by ext x; simp [A]
    have hc_pow : c ^ 8 = (16 : ℝ) := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul,
        show c ^ 2 = 2 from Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hA]; simp [LinearMap.det_smul, LinearMap.det_id, hc_pow]
  have hg0 : (𝓕 (g : ℝ⁸ → ℂ)) 0 = (1 : ℂ) := by
    simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using
      (fourier_g_zero : FT g 0 = 1)
  have hscaled :
      FT scaledMagic 0 =
        (abs (LinearMap.det (A : ℝ⁸ →ₗ[ℝ] ℝ⁸)))⁻¹ • (𝓕 (g : ℝ⁸ → ℂ)) 0 := by
    simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe, scaledMagic, c, A,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv
        (A := A) (f := (g : ℝ⁸ → ℂ)) (w := (0 : ℝ⁸)))
  simp_all

/-- Convenience form of `fourier_scaledMagic_zero` for the coerced function `⇑scaledMagic`. -/
public theorem fourier_scaledMagic_zero_fun : 𝓕 (⇑scaledMagic) 0 = (1 / 16 : ℂ) := by
  simpa [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_coe] using fourier_scaledMagic_zero

end SpherePacking

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap
open Real Complex MagicFunction.FourierEigenfunctions
open MeasureTheory

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)

namespace PureImaginary

private lemma setIntegral_im_ofReal (f : ℝ → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), ((f t : ℝ) : ℂ)).im = 0 := by
  simpa using congrArg Complex.im
    (integral_ofReal (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) (𝕜 := ℂ) (f := f))

lemma a'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (a' u).re = 0 := by
  have hEq := IntegralReps.aRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        ((((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
                ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
                ((8640 / π : ℝ) : ℂ) * t -
                ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) *
            Real.exp (-π * u * t))
  set E : ℂ := (36 : ℂ) / (π ^ (3 : ℕ) * (u - 2)) -
    (8640 : ℂ) / (π ^ (3 : ℕ) * u ^ (2 : ℕ)) + (18144 : ℂ) / (π ^ (3 : ℕ) * u) + Iterm
  have hEq' : a' u = (4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.aAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t => (t ^ (2 : ℕ)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
      (36 / (π ^ (2 : ℕ)) : ℝ) * Real.exp (2 * π * t) +
      (8640 / π : ℝ) * t - (18144 / (π ^ (2 : ℕ)) : ℝ)
    rw [show Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t (ht : 0 < t) => by
          rw [show φ₀'' ((Complex.I : ℂ) / (t : ℂ)) =
            ((φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re : ℂ) from by
              apply Complex.ext <;> simp [φ₀''_imag_axis_div_im t ht]]
          push_cast [innerR]; ring]
    exact setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t))
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, Complex.sub_im, hIterm, Complex.div_im, Complex.mul_im,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((π : ℂ)).im = 0 by simp) 3,
      Complex.im_pow_eq_zero_of_im_eq_zero (show ((u : ℂ)).im = 0 by simp) 2]
  rw [hEq', show ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
      (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by simp [Complex.ofReal_pow]]
  have : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  simp_all

lemma b'_re_eq_zero_of_pos_ne_two {u : ℝ} (hu : 0 < u) (hu2 : u ≠ 2) : (b' u).re = 0 := by
  have hEq := IntegralReps.bRadial_eq_another_integral_main (u := u) hu hu2
  set Iterm : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ),
        (ψI' ((Complex.I : ℂ) * (t : ℂ)) - (144 : ℂ) - Real.exp (2 * π * t)) *
          Real.exp (-π * u * t)
  set E : ℂ := (144 : ℂ) / (π * u) + (1 : ℂ) / (π * (u - 2)) + Iterm
  have hEq' : b' u = (-4 * (Complex.I : ℂ)) * (Real.sin (π * u / 2)) ^ (2 : ℕ) * E := by
    simpa [E, Iterm, IntegralReps.bAnotherIntegrand, mul_assoc] using hEq
  have hIterm : Iterm.im = 0 := by
    let innerR : ℝ → ℝ := fun t =>
      (ψI' ((Complex.I : ℂ) * (t : ℂ))).re - (144 : ℝ) - Real.exp (2 * π * t)
    rw [show Iterm = ∫ t in Set.Ioi (0 : ℝ), ((innerR t * Real.exp (-π * u * t) : ℝ) : ℂ) from
      MeasureTheory.setIntegral_congr_fun (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi fun t (ht : 0 < t) => by
          rw [show ψI' ((Complex.I : ℂ) * (t : ℂ)) =
            ((ψI' ((Complex.I : ℂ) * (t : ℂ))).re : ℂ) from by
              apply Complex.ext <;> simp [ψI'_imag_axis_im t ht]]
          push_cast [innerR]; ring]
    exact setIntegral_im_ofReal (f := fun t => innerR t * Real.exp (-π * u * t))
  have hEim : E.im = 0 := by
    simp [E, Complex.add_im, hIterm, Complex.div_im, Complex.mul_im]
  rw [hEq', show ((Real.sin (π * u / 2) : ℂ) ^ (2 : ℕ)) =
      (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) by simp [Complex.ofReal_pow]]
  have : (((Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  simp_all

/-- Extend `re = 0` from `(0,∞) \ {2}` to all of `(0,∞)` using continuity. -/
private lemma re_eq_zero_of_pos_from_ne_two (f : ℝ → ℂ) (hcont : Continuous f)
    (h : ∀ {u : ℝ}, 0 < u → u ≠ 2 → (f u).re = 0) {u : ℝ} (hu : 0 < u) : (f u).re = 0 := by
  by_cases hu2 : u = 2
  · subst hu2
    refine (IsClosed.closure_subset_iff
        (isClosed_eq (Complex.continuous_re.comp hcont) continuous_const)).2
      (fun r (hr : r ∈ Set.Ioi (0 : ℝ) \ ({2} : Set ℝ)) =>
        h hr.1 fun h' => hr.2 (by simp [h']))
      (Metric.mem_closure_iff.2 fun ε hε => ⟨2 + ε / 2,
        ⟨show (0 : ℝ) < 2 + ε / 2 by positivity,
          fun h => by linarith [show (2 + ε / 2 : ℝ) = 2 by simpa using h]⟩, ?_⟩)
    rw [Real.dist_eq, show (2 : ℝ) - (2 + ε / 2) = -(ε/2) by ring, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
  · exact h hu hu2

end PureImaginary

/-- The eigenfunction `a` is purely imaginary-valued (its real part vanishes). -/
public theorem a_pureImag (x : ℝ⁸) : (a x).re = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [MagicFunction.a.SpecialValues.a_zero]
  · simpa [MagicFunction.FourierEigenfunctions.a, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using PureImaginary.re_eq_zero_of_pos_from_ne_two a'
        (SchwartzMap.continuous a') PureImaginary.a'_re_eq_zero_of_pos_ne_two
        (u := ‖x‖ ^ 2) (by simpa using pow_pos (norm_pos_iff.2 hx) 2)

/-- The eigenfunction `b` is purely imaginary-valued (its real part vanishes). -/
public theorem b_pureImag (x : ℝ⁸) : (b x).re = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [MagicFunction.b.SpecialValues.b_zero]
  · simpa [MagicFunction.FourierEigenfunctions.b, schwartzMap_multidimensional_of_schwartzMap_real,
      SchwartzMap.compCLM_apply] using PureImaginary.re_eq_zero_of_pos_from_ne_two b'
        (SchwartzMap.continuous b') PureImaginary.b'_re_eq_zero_of_pos_ne_two
        (u := ‖x‖ ^ 2) (by simpa using pow_pos (norm_pos_iff.2 hx) 2)

private theorem ofReal_re_eq (z : ℂ) (hz : z.im = 0) : (↑z.re : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

/-- The magic function `g` is real-valued. -/
public theorem g_real (x : ℝ⁸) : (↑(g x).re : ℂ) = g x :=
  ofReal_re_eq (g x) <| by
    simp [g, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.sub_im,
      Complex.mul_im, a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

/-- The Fourier transform `𝓕 g` is real-valued. -/
public theorem g_real_fourier (x : ℝ⁸) : (↑((𝓕 g x).re : ℂ)) = (𝓕 g x) := by
  refine ofReal_re_eq (𝓕 g x) ?_
  have hFg : FT g = ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  change ((𝓕 g) x).im = 0
  rw [show (𝓕 g) = FT g from by simp, hFg]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
    a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]

end MagicFunction.g.CohnElkies

namespace SpherePacking

open scoped FourierTransform ENNReal SchwartzMap
open Real Complex SpherePacking MeasureTheory Metric

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.g.CohnElkies

private noncomputable def scaleEquiv : ℝ⁸ ≃ₗ[ℝ] ℝ⁸ :=
  LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ⁸) (Real.sqrt 2) sqrt2_ne_zero

/-- `scaledMagic` is real-valued (scaled variant of `g_real`). -/
public theorem scaledMagic_real' : ∀ x : ℝ⁸, (↑(scaledMagic x).re : ℂ) = scaledMagic x := by
  simpa [SpherePacking.scaledMagic] using fun x => g_real (x := (Real.sqrt 2) • x)

private lemma fourier_scaledMagic_eq (x : ℝ⁸) :
    (𝓕 scaledMagic x) =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ •
        𝓕 g ((LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x) := by
  simpa [SpherePacking.scaledMagic, scaleEquiv, SchwartzMap.fourier_coe] using
    SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := scaleEquiv) (f := g) (w := x)

/-- The Fourier transform `𝓕 scaledMagic` is real-valued (scaled variant of `g_real_fourier`). -/
public theorem scaledMagic_real_fourier' :
    ∀ x : ℝ⁸, (↑((𝓕 scaledMagic x).re : ℂ)) = (𝓕 scaledMagic x) := by
  intro x
  let y0 : ℝ⁸ := (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hImG : (𝓕 g y0).im = 0 := by
    simpa using (congrArg Complex.im (g_real_fourier (x := y0))).symm
  have hImScaled : (𝓕 scaledMagic x).im = 0 := by
    simpa [y0, Complex.smul_im, hImG] using congrArg Complex.im (fourier_scaledMagic_eq (x := x))
  exact Complex.ext (by simp) (by simp [hImScaled])

/-- Cohn-Elkies sign condition for `scaledMagic` outside the unit ball (scaled variant). -/
public theorem scaledMagic_cohnElkies₁' : ∀ x : ℝ⁸, ‖x‖ ≥ 1 → (scaledMagic x).re ≤ 0 := by
  intro x hx
  have h2 : (2 : ℝ) ≤ ‖(Real.sqrt 2) • x‖ ^ (2 : ℕ) := by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    nlinarith [mul_le_mul hx hx (by positivity) (norm_nonneg x), sq_nonneg ‖x‖]
  simpa [SpherePacking.scaledMagic] using
    g_nonpos_of_norm_sq_ge_two (x := (Real.sqrt 2) • x) h2

/-- Cohn-Elkies nonnegativity for `𝓕 scaledMagic` (scaled variant). -/
public theorem scaledMagic_cohnElkies₂' : ∀ x : ℝ⁸, (𝓕 scaledMagic x).re ≥ 0 := by
  intro x
  let y0 : ℝ⁸ := (LinearMap.adjoint ((scaleEquiv.symm : ℝ⁸ ≃ₗ[ℝ] ℝ⁸) : ℝ⁸ →ₗ[ℝ] ℝ⁸)) x
  have hre : (𝓕 scaledMagic x).re =
      |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • (𝓕 g y0).re := by
    have hre' : (𝓕 scaledMagic x).re =
        (|LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹ • 𝓕 g y0).re := by
      simpa [y0] using congrArg Complex.re (fourier_scaledMagic_eq (x := x))
    exact hre'.trans (by
      simpa using
        Complex.smul_re (r := |LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸)|⁻¹) (z := 𝓕 g y0))
  simpa [hre] using
    smul_nonneg (inv_nonneg.2 (abs_nonneg (LinearMap.det (scaleEquiv : ℝ⁸ →ₗ[ℝ] ℝ⁸))))
      (by simpa using fourier_g_nonneg (x := y0))

/-- Upper bound on `SpherePackingConstant 8` given by the density of the `E8` lattice packing. -/
public theorem SpherePackingConstant_le_E8Packing_density :
    SpherePackingConstant 8 ≤ E8Packing.density := by
  have hne : (scaledMagic : 𝓢(ℝ⁸, ℂ)) ≠ 0 := fun h => by
    simpa [scaledMagic_zero] using congrArg (fun f : 𝓢(ℝ⁸, ℂ) => f 0) h
  have hLP :
      SpherePackingConstant 8 ≤ (scaledMagic 0).re.toNNReal / (𝓕 (⇑scaledMagic) 0).re.toNNReal *
        volume (ball (0 : ℝ⁸) (1 / 2 : ℝ)) := by
    simpa using
      (LinearProgrammingBound (d := 8) (f := (scaledMagic : 𝓢(ℝ⁸, ℂ))) hne
        scaledMagic_real' scaledMagic_real_fourier' scaledMagic_cohnElkies₁'
        scaledMagic_cohnElkies₂' (Nat.succ_pos 7))
  have hratio : (scaledMagic 0).re.toNNReal / (𝓕 (⇑scaledMagic) 0).re.toNNReal = (16 : ℝ≥0∞) := by
    simp [ENNReal.ofNNReal_toNNReal, scaledMagic_zero, fourier_scaledMagic_zero_fun]
  calc
    SpherePackingConstant 8 ≤ (16 : ℝ≥0∞) * volume (ball (0 : ℝ⁸) (1 / 2 : ℝ)) := by
      simpa [mul_assoc, hratio] using hLP
    _ = ENNReal.ofReal π ^ 4 / 384 := by
      calc (16 : ℝ≥0∞) * volume (ball (0 : ℝ⁸) (1 / 2 : ℝ))
          = (16 : ℝ≥0∞) *
            (ENNReal.ofReal (1 / 2 : ℝ) ^ 8 * ENNReal.ofReal (π ^ 4 / 24)) := by
            simp [InnerProductSpace.volume_ball_of_dim_even (E := ℝ⁸) (k := 4) (hk := by simp),
              finrank_euclideanSpace, Nat.factorial]
        _ = ENNReal.ofReal ((16 : ℝ) * (((1 / 2 : ℝ) ^ 8) * (π ^ 4 / 24))) := by
            have hinv : (2⁻¹ : ℝ≥0∞) ^ 8 = (2 ^ 8 : ℝ≥0∞)⁻¹ := by
              simpa using (ENNReal.inv_pow (a := (2 : ℝ≥0∞)) (n := 8)).symm
            simp [mul_left_comm, ENNReal.ofReal_mul, (by norm_num : (0 : ℝ) ≤ (16 : ℝ)), hinv]
        _ = ENNReal.ofReal (π ^ 4 / 384 : ℝ) := by congr 1; ring
        _ = ENNReal.ofReal π ^ 4 / 384 := by
            simp [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 384),
              ENNReal.ofReal_pow Real.pi_pos.le]
    _ = E8Packing.density := by simpa using E8Packing_density.symm

open SpherePacking E8

/-- Main theorem (dimension 8): the optimal packing density equals `E8Packing.density`. -/
public theorem MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  le_antisymm SpherePackingConstant_le_E8Packing_density <| by
    simpa [SpherePackingConstant] using
      le_iSup (fun S : SpherePacking 8 => S.density) E8Packing.toSpherePacking

end SpherePacking

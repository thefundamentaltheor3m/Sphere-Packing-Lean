import Mathlib

-- import SpherePacking.Basic.EuclideanLattice
import SpherePacking.Basic.SpherePacking
import SpherePacking.Basic.Vec

import SpherePacking.ForMathlib.Finsupp
import SpherePacking.ForMathlib.InnerProductSpace

open Euclidean EuclideanSpace BigOperators EuclideanLattice SpherePacking Matrix algebraMap
  Pointwise

/-
* NOTE: *
It will probably be useful, at some point in the future, to subsume this file under a more general
file tackling the classification of crystallographic, irreducible Coxeter groups and their root
systems (or something like that). It might also be useful to add general API that will make it
easier to construct a `SpherePackingCentres` instance for such lattices, which would be useful for
the sphere packing problem in other dimensions.
-/

local notation "V" => EuclideanSpace ℝ (Fin 8)
-- def V : Type := EuclideanSpace ℝ (Fin 8)
local notation "ℝ⁸" => Fin 8 → ℝ

#check V

instance : SMul ℝ V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

instance : HMul ℝ V V := ⟨fun (r : ℝ) (v : V) => (fun i => r * v i)⟩

/-- E₈ is characterised as the set of vectors with (1) coordinates summing to an even integer,
and (2) all its coordinates either an integer or a half-integer. -/
@[simp]
def E8_Set : Set V :=
  {v | ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 * v i)) ∧ ∑ i, v i ≡ 0 [PMOD 2]}

@[simp]
def E8_Normalised_Set : Set V := (1 / Real.sqrt 2) • E8_Set

theorem mem_E8_Set {v : V} :
    v ∈ E8_Set ↔
      ((∀ i, ∃ n : ℤ, n = v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 * v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  simp

theorem mem_E8_Set' {v : V} :
    v ∈ E8_Set ↔
      ((∀ i, ∃ n : ℤ, Even n ∧ n = 2 * v i) ∨ (∀ i, ∃ n : ℤ, Odd n ∧ n = 2 * v i))
        ∧ ∑ i, v i ≡ 0 [PMOD 2] := by
  have (k : ℝ) : (∃ n : ℤ, Even n ∧ n = 2 * k) ↔ (∃ n : ℤ, n = k) :=
    ⟨fun ⟨n, ⟨⟨l, hl⟩, hn⟩⟩ ↦ ⟨l, by simp [← two_mul, hl] at hn; exact hn⟩,
     fun ⟨n, hn⟩ ↦ ⟨2 * n, ⟨even_two_mul n, by simp [hn]⟩⟩⟩
  simp_rw [this, mem_E8_Set]

section E8_Over_ℚ
/-! Credit for the code proving linear independence goes to Gareth Ma. -/

/-! # Choice of Simple Roots
There are many possible choices of simple roots for the E8 root system. Here, we choose the one
mentioned in the Wikipedia article https://en.wikipedia.org/wiki/E8_(mathematics).
-/

/-- E₈ is also characterised as the ℤ-span of the following vectors. -/
@[simp]
def E8' : Matrix (Fin 8) (Fin 8) ℚ := !![
1,-1,0,0,0,0,0,0;
0,1,-1,0,0,0,0,0;
0,0,1,-1,0,0,0,0;
0,0,0,1,-1,0,0,0;
0,0,0,0,1,-1,0,0;
0,0,0,0,0,1,1,0;
-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2;
0,0,0,0,0,1,-1,0
]

/-- F₈ is the inverse matrix of E₈, used to assist computation below. -/
@[simp]
def F₈' : Matrix (Fin 8) (Fin 8) ℚ := !![
1,1,1,1,1,1/2,0,1/2;
0,1,1,1,1,1/2,0,1/2;
0,0,1,1,1,1/2,0,1/2;
0,0,0,1,1,1/2,0,1/2;
0,0,0,0,1,1/2,0,1/2;
0,0,0,0,0,1/2,0,1/2;
0,0,0,0,0,1/2,0,-1/2;
-1,-2,-3,-4,-5,-7/2,-2,-5/2
]

@[simp]
theorem E8_mul_F₈_eq_id_Q : E8' * F₈' = !![
    1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,1;
    ] := by
  rw [E8', F₈']
  norm_num

@[simp]
theorem E8_mul_F₈_eq_one_Q : E8' * F₈' = 1 := by
  -- TODO: un-sorry (slow)
  sorry
  /- convert E8_mul_F₈_eq_id_Q -/
  /- rw [← Matrix.diagonal_one] -/
  /- ext i j -/
  /- by_cases h : i = j -/
  /- · subst h -/
  /-   fin_cases i <;> norm_num -/
  /- · rw [Matrix.diagonal_apply_ne _ h] -/
  /-   fin_cases i <;> fin_cases j <;> norm_num at h ⊢ -/

@[simp]
theorem F₈_mul_E8_eq_one_Q : F₈' * E8' = 1 := by
  rw [Matrix.mul_eq_one_comm, E8_mul_F₈_eq_one_Q]

end E8_Over_ℚ

noncomputable section E8_Over_ℝ

@[simp]
def E8_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix E8'

@[simp]
def F₈_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix F₈'

theorem E8_Matrix_apply {i j : Fin 8} : E8_Matrix i j = E8' i j := by
  rfl

@[simp]
theorem E8_mul_F₈_eq_one_R : E8_Matrix * F₈_Matrix = 1 := by
  rw [E8_Matrix, F₈_Matrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    E8_mul_F₈_eq_one_Q] --, map_one _ coe_zero coe_one]  -- Doesn't work for some reason
  simp only [map_zero, _root_.map_one, Matrix.map_one]

@[simp]
theorem F₈_mul_E8_eq_one_R : F₈_Matrix * E8_Matrix = 1 := by
  rw [E8_Matrix, F₈_Matrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    F₈_mul_E8_eq_one_Q] --, map_one _ coe_zero coe_one]
  simp only [map_zero, _root_.map_one, Matrix.map_one]

theorem E8_is_basis :
    LinearIndependent ℝ E8_Matrix ∧ Submodule.span ℝ (Set.range E8_Matrix) = ⊤ := by
  -- This code seems to be generating a recursion error for some reason
  -- rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det]
  -- change IsUnit E8_Matrix.det
  -- have : E8_Matrix.det * F₈_Matrix.det = 1 := by
  --   rw [← det_mul, E8_mul_F₈_eq_one_R, det_one]
  -- exact isUnit_of_mul_eq_one _ _ this
  sorry

section E8_sum_apply_lemmas

variable {α : Type*} [Semiring α] [Module α ℝ] (y : Fin 8 → α)

lemma E8_sum_apply_0 :
    (∑ j : Fin 8, y j • E8_Matrix j) 0 = y 0 • 1 - y 6 • (1 / 2) := by
  simp [Fin.sum_univ_eight, neg_div, ← sub_eq_add_neg]

lemma E8_sum_apply_1 :
    (∑ j : Fin 8, y j • E8_Matrix j) 1 = y 0 • (-1) + y 1 • 1 - y 6 • ((1 : ℝ) / 2) := by
  simp [Fin.sum_univ_eight, neg_div, smul_neg, -one_div, ← sub_eq_add_neg]

lemma E8_sum_apply_2 :
    (∑ j : Fin 8, y j • E8_Matrix j) 2 = y 1 • (-1) + y 2 • 1 - y 6 • ((1 : ℝ) / 2) := by
  simp [Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

lemma E8_sum_apply_3 :
    (∑ j : Fin 8, y j • E8_Matrix j) 3 = y 2 • (-1) + y 3 • 1 - y 6 • ((1 : ℝ) / 2) := by
  simp [Fin.sum_univ_eight, neg_div, ← sub_eq_add_neg]

lemma E8_sum_apply_4 :
    (∑ j : Fin 8, y j • E8_Matrix j) 4 = y 3 • (-1) + y 4 • 1 - y 6 • ((1 : ℝ) / 2) := by
  simp [Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

lemma E8_sum_apply_5 :
    (∑ j : Fin 8, y j • E8_Matrix j) 5 = y 4 • (-1) + y 5 • 1 - y 6 • ((1 : ℝ) / 2) + y 7 • 1 := by
  simp [Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

lemma E8_sum_apply_6 :
    (∑ j : Fin 8, y j • E8_Matrix j) 6 = y 5 • 1 - y 6 • ((1 : ℝ) / 2) - y 7 • 1 := by
  simp [Fin.sum_univ_eight, neg_div, mul_neg, ← sub_eq_add_neg]

lemma E8_sum_apply_7 :
    (∑ j : Fin 8, y j • E8_Matrix j) 7 = y 6 • (-(1 : ℝ) / 2) := by
  simp [Fin.sum_univ_eight]

macro "simp_E8_sum_apply" : tactic =>
  `(tactic |
    simp only [E8_sum_apply_0, E8_sum_apply_1, E8_sum_apply_2, E8_sum_apply_3, E8_sum_apply_4,
      E8_sum_apply_5, E8_sum_apply_6, E8_sum_apply_7])

end E8_sum_apply_lemmas

theorem E8_Set_eq_span : E8_Set = (Submodule.span ℤ (Set.range E8_Matrix) : Set (Fin 8 → ℝ)) := by
  ext v
  rw [SetLike.mem_coe, ← Finsupp.range_total, LinearMap.mem_range]
  constructor <;> intro hv
  · obtain ⟨hv₁, hv₂⟩ := mem_E8_Set'.mp hv
    convert_to (∃ y : Fin 8 →₀ ℤ, (∑ i, y i • E8_Matrix i) = v)
    · ext y
      rw [← Finsupp.total_eq_sum]
      rfl
    · cases' hv₁ with hv₁ hv₁
      -- TODO (the y is just F8_Matrix * v, need to prove it has integer coefficients)
      <;> sorry
  · obtain ⟨y, hy⟩ := hv
    erw [Finsupp.total_eq_sum] at hy
    constructor
    · by_cases hy' : Even (y 6)
      · left
        obtain ⟨k, hk⟩ := hy'
        intro i
        -- TODO: un-sorry (slow)
        sorry
        /- fin_cases i -/
        /- <;> [use y 0 - k; use -y 0 + y 1 - k; use -y 1 + y 2 - k; use -y 2 + y 3 - k; -/
        /-   use -y 3 + y 4 - k; use -y 4 + y 5 - k + y 7; use y 5 - k - y 7; use -k] -/
        /- <;> convert congrFun hy _ -/
        /- all_goals -/
        /-   simp_rw [Fintype.sum_apply, Pi.smul_apply, Fin.sum_univ_eight, E8_Matrix_apply] -/
        /-   simp [hk] -/
        /-   ring_nf -/
      · right
        intro i
        -- TODO: un-sorry (slow)
        sorry
        /- fin_cases i -/
        /- <;> [use 2 * y 0 - y 6; use -2 * y 0 + 2 * y 1 - y 6; use -2 * y 1 + 2 * y 2 - y 6; -/
        /-   use -2 * y 2 + 2 * y 3 - y 6; use -2 * y 3 + 2 * y 4 - y 6; -/
        /-   use -2 * y 4 + 2 * y 5 - y 6 + 2 * y 7; use 2 * y 5 - y 6 - 2 * y 7; use -y 6] -/
        /- <;> simp [Int.even_sub, Int.even_add, hy'] -/
        /- <;> subst hy -/
        /- <;> simp_E8_sum_apply -/
        /- <;> try simp only [mul_sub, mul_add, neg_div] -/
        /- <;> norm_num -/
        /- <;> rw [← mul_assoc, mul_right_comm, mul_one_div_cancel (by norm_num), one_mul] -/
    · subst hy
      simp_rw [Fintype.sum_apply, Pi.smul_apply, E8_Matrix_apply, Fin.sum_univ_eight]
      -- TODO: un-sorry (slow)
      sorry
      /- simp -/
      /- use y 6 * 2 - y 5 -/
      /- ring_nf -/
      /- rw [zsmul_eq_mul, Int.cast_sub, sub_mul, Int.cast_mul, mul_assoc] -/
      /- norm_num -/

lemma Top_Le_Span_E8 : ⊤ ≤ Submodule.span ℝ (Set.range E8_Matrix) :=
  E8_is_basis.right.symm.le

@[simp]
def E8_Basis : Basis (Fin 8) ℝ V := Basis.mk E8_is_basis.left Top_Le_Span_E8

end E8_Over_ℝ

noncomputable section E8_Normalised_Over_ℝ

@[simp]
def E8_Normalised_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (1 / Real.sqrt 2) • E8_Matrix

@[simp]
def E8_Normalised_Basis_Set : Set V := Set.range E8_Normalised_Matrix

@[simp]
def F₈_Normalised_Matrix : Matrix (Fin 8) (Fin 8) ℝ := (Real.sqrt 2) • F₈_Matrix

@[simp]
theorem E8_Normalised_mul_F₈_Normalised_eq_one_R : E8_Normalised_Matrix * F₈_Normalised_Matrix = 1
  := by
  have : (Real.sqrt 2) ≠ 0 := by
    simp only [ne_eq, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [E8_Normalised_Matrix, F₈_Normalised_Matrix, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_div, inv_smul_smul₀ this]
  exact E8_mul_F₈_eq_one_R

theorem E8_Normalised_is_basis :
    LinearIndependent ℝ E8_Normalised_Matrix ∧
      Submodule.span ℝ (Set.range E8_Normalised_Matrix) = ⊤ := by
  -- TODO: un-sorry (kernel error, #15045)
  sorry
  -- rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det]
  -- change IsUnit E8_Normalised_Matrix.det
  -- have : E8_Normalised_Matrix.det * F₈_Normalised_Matrix.det = 1 := by
  --   rw [← det_mul, E8_Normalised_mul_F₈_Normalised_eq_one_R, det_one]
  -- exact isUnit_of_mul_eq_one _ _ this

lemma Top_Le_Span_E8_Normalised : ⊤ ≤ Submodule.span ℝ (Set.range E8_Normalised_Matrix) :=
  E8_Normalised_is_basis.right.symm.le

@[simp]
def E8_Normalised_Basis : Basis (Fin 8) ℝ V :=
  Basis.mk E8_Normalised_is_basis.left Top_Le_Span_E8_Normalised

end E8_Normalised_Over_ℝ

noncomputable section Lattice

theorem E8_add_mem {a b : V} (ha : a ∈ E8_Set) (hb : b ∈ E8_Set) : a + b ∈ E8_Set := by
  obtain ⟨hv1, hv2⟩ := mem_E8_Set'.mp ha
  obtain ⟨hw1, hw2⟩ := mem_E8_Set'.mp hb
  rw [mem_E8_Set']
  constructor
  · simp_rw [PiLp.add_apply]
    cases' hv1 with hv1 hv1 <;> cases' hw1 with hw1 hw1 <;> [left; right; right; left]
    all_goals
      intro i
      obtain ⟨m, ⟨hm1, hm2⟩⟩ := hv1 i
      obtain ⟨n, ⟨hn1, hn2⟩⟩ := hw1 i
      use m + n, ?_, by simp [hm2, hn2, mul_add]
      simp only [Int.odd_iff_not_even] at *
      simp [Int.even_add, hm1, hn1]
  · simp_rw [PiLp.add_apply, Finset.sum_add_distrib]
    convert AddCommGroup.ModEq.add hv2 hw2
    rw [add_zero]

theorem E8_neg_mem {a : V} (ha : a ∈ E8_Set) : -a ∈ E8_Set := by
  rw [mem_E8_Set'] at *
  obtain ⟨hv1, hv2⟩ := ha
  constructor
  · cases' hv1 with hv1 hv1 <;> [left; right]
    all_goals
      intro i
      obtain ⟨a, ⟨ha1, ha2⟩⟩ := hv1 i
      use -a, by simp [Int.odd_iff_not_even, ha1], by simp [ha2]
  · simp_rw [PiLp.neg_apply, Finset.sum_neg_distrib]
    convert hv2.neg
    rw [zero_eq_neg]

def E8_Lattice : AddSubgroup V where
  carrier := E8_Set
  zero_mem' := by simp [mem_E8_Set]
  add_mem' := E8_add_mem
  neg_mem' := E8_neg_mem

def E8_Normalised_Lattice : AddSubgroup V where
  carrier := E8_Normalised_Set
  zero_mem' := by simp [E8_Normalised_Set, Set.mem_smul_set]
  add_mem' ha hb := by
    rw [E8_Normalised_Set, Set.mem_smul_set] at *
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    use a + b, E8_add_mem ha hb, by simp
  neg_mem' ha := by
    simp only [E8_Normalised_Set, Set.mem_smul_set] at *
    obtain ⟨a, ha, rfl⟩ := ha
    use -a, E8_neg_mem ha, by simp

open Topology TopologicalSpace Filter Function InnerProductSpace RCLike

theorem E8_Matrix_inner {i j : Fin 8} :
    haveI : Inner ℝ (Fin 8 → ℝ) := (inferInstance : Inner ℝ V)
    ⟪(E8_Matrix i : V), E8_Matrix j⟫_ℝ = ∑ k, E8' i k * E8' j k := by
  change ∑ k, E8_Matrix i k * E8_Matrix j k = _
  simp_rw [E8_Matrix, RingHom.mapMatrix_apply, map_apply, eq_ratCast, Rat.cast_sum, Rat.cast_mul]

set_option maxHeartbeats 2000000 in
/-- All vectors in E₈ have norm √(2n) -/
theorem E8_norm_eq_sqrt_even (v : E8_Lattice) :
    ∃ n : ℤ, Even n ∧ ‖v‖ ^ 2 = n := by
  sorry
  /- rcases v with ⟨v, hv⟩ -/
  /- change ∃ n : ℤ, Even n ∧ ‖v‖ ^ 2 = n -/
  /- rw [norm_sq_eq_inner (𝕜 := ℝ) v] -/
  /- simp_rw [E8_Lattice, AddSubgroup.mem_mk, E8_Set_eq_span, SetLike.mem_coe, ← Finsupp.range_total, -/
  /-   LinearMap.mem_range] at hv -/
  /- replace hv : ∃ y : Fin 8 →₀ ℤ, ∑ i, y i • E8_Matrix i = v := by -/
  /-   convert hv -/
  /-   rw [← Finsupp.total_eq_sum E8_Matrix _] -/
  /-   rfl -/
  /- obtain ⟨y, ⟨⟨w, hw⟩, rfl⟩⟩ := hv -/
  /- simp_rw [re_to_real, sum_inner, inner_sum, intCast_smul_left, intCast_smul_right, zsmul_eq_mul, -/
  /-   Fin.sum_univ_eight] -/
  /- repeat rw [E8_Matrix_inner] -/
  /- repeat rw [Fin.sum_univ_eight] -/
  /- -- compute the dot products -/
  /- norm_num -/
  /- -- normalise the goal to ∃ n, Even n ∧ _ = n -/
  /- norm_cast -/
  /- rw [exists_eq_right'] -/
  /- -- now simplify the rest algebraically -/
  /- ring_nf -/
  /- simp [Int.even_sub, Int.even_add] -/

theorem E8_norm_lower_bound (v : E8_Lattice) : v = 0 ∨ √2 ≤ ‖v‖ := by
  rw [or_iff_not_imp_left]
  intro hv
  obtain ⟨n, ⟨hn, hn'⟩⟩ := E8_norm_eq_sqrt_even v
  have : 0 ≤ (n : ℝ) := by rw [← hn']; exact sq_nonneg ‖↑v‖
  have : 0 ≤ n := by norm_cast at this
  have : n ≠ 0 := by contrapose! hv; simpa [hv] using hn'
  have : 2 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  have : √2 ^ 2 ≤ ‖v‖ ^ 2 := by rw [sq, Real.mul_self_sqrt zero_le_two, hn']; norm_cast
  rwa [sq_le_sq, abs_norm, abs_eq_self.mpr ?_] at this
  exact Real.sqrt_nonneg 2

theorem E8_Normalised_norm_lower_bound (v : E8_Normalised_Lattice) : v = 0 ∨ 1 ≤ ‖v‖ := by
  obtain ⟨v, hv⟩ := v
  simp [E8_Normalised_Lattice, -E8_Set, Set.mem_smul_set] at hv
  obtain ⟨y, ⟨hy, hy'⟩⟩ := hv
  simp_rw [← hy', AddSubmonoid.mk_eq_zero, smul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero zero_le_two,
    OfNat.ofNat_ne_zero, false_or, AddSubgroup.coe_norm]
  simp_rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_eq_self.mpr (Real.sqrt_nonneg 2)]
  have : 0 < √2 := Real.sqrt_pos.mpr zero_lt_two
  rw [inv_mul_eq_div, le_div_iff this, one_mul]
  convert E8_norm_lower_bound ⟨y, hy⟩
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero]

instance instDiscreteE8NormalisedSet : DiscreteTopology E8_Normalised_Set := by
  convert_to DiscreteTopology E8_Normalised_Lattice
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  use 1 / 2, by norm_num,
    fun v h ↦ (E8_Normalised_norm_lower_bound v).resolve_right (by linarith [dist_zero_right v ▸ h])

instance instDiscreteE8NormalisedLattice : DiscreteTopology E8_Normalised_Lattice :=
  instDiscreteE8NormalisedSet

instance instLatticeE8 : isLattice E8_Normalised_Lattice where
  span_top := by
    unfold Submodule.span
    simp only [sInf_eq_top, Set.mem_setOf_eq]
    intros M hM
    have HSet : ↑E8_Normalised_Lattice = E8_Normalised_Set := rfl
    rw [HSet] at hM
    suffices hbasis : ∃ B : Basis (Fin 8) ℝ V, ((Set.range B) : Set V) ⊆ (M : Set V)
    { rcases hbasis with ⟨B, hB⟩
      ext y
      constructor
      { simp only [Submodule.mem_top, implies_true] }
      { intro hy
        have h1 : ((Submodule.span ℝ (Set.range B)) : Set V) ⊆ (M : Set V) := by
          intro z hz
          rw [Basis.span_eq] at hz
          rw [← B.span_eq] at hz
          unfold Submodule.span at hz
          simp only [Submodule.sInf_coe, Set.mem_setOf_eq, Set.mem_iInter, SetLike.mem_coe] at hz ⊢
          specialize hz M hB
          exact hz
        rw [Basis.span_eq] at h1
        exact h1 hy } }
    suffices hE8basis : ∃ B : Basis (Fin 8) ℝ V, ((Set.range B) : Set V) ⊆ E8_Normalised_Set
    { rcases hE8basis with ⟨B, hB⟩
      use B
      intro x hx
      exact hM (hB hx) }
    use E8_Normalised_Basis
    have hbasiselts : Set.range E8_Normalised_Basis = E8_Normalised_Basis_Set := by
      ext x
      constructor
      { intro hx
        rcases hx with ⟨i, hi⟩
        use i
        simp only [← hi, E8_Normalised_Basis, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
          coe_basisOfLinearIndependentOfCardEqFinrank, E8_Normalised_Matrix, Pi.smul_apply,
          E8_Matrix, Basis.coe_mk] }
      { intro hx
        apply Set.mem_range.mpr
        rcases hx with ⟨i, hi⟩
        use i
        simp only [hi, E8_Normalised_Basis, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
          coe_basisOfLinearIndependentOfCardEqFinrank, E8_Normalised_Matrix, Pi.smul_apply,
          E8_Matrix, Basis.coe_mk, Pi.smul_apply, ← hi] }
    intro x hx
    rw [hbasiselts] at hx
    cases' hx with i hi
    unfold E8_Normalised_Set
    simp only [Set.mem_setOf_eq, E8_Set]
    sorry
    /-
    rcases i with ⟨i₀ | i₁ | i₂ | i₃ | i₄ | i₅ | i₆ | i₇ | n, hn⟩
    -- A lot of steps here are repeated. Can this code be optimised?
    { use E8_Matrix 0
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 1
            simp only [Int.cast_one, Fin.isValue, Fin.zero_eta, E8_Matrix, E8_Matrix,
              Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
              Matrix.empty_val', Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.cast_one, Fin.zero_eta, E8_Matrix, E8_Matrix,
              Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
              Int.reduceNeg, Int.cast_neg, zero_add, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
              Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_zero]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { simp only [E8_Matrix, E8_Matrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero]
          sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, Fin.isValue, one_div] } }
    { use E8_Matrix 1
      constructor
      { constructor
        { left
          intro j
          -- Rest done by copilot, pattern-matching with first. Very cool
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons] }
          { use 1
            simp only [Int.cast_one, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E8_Matrix, E8_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { simp only [Finset.sum, Fin.isValue, Fin.univ_val_map, List.ofFn_succ,
            Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe,
            List.sum_cons, List.sum_nil, add_zero, Fin.succ, Fin.isValue, Nat.succ_eq_add_one,
            Nat.reduceAdd, Fin.val_zero, Fin.mk_one, Fin.reduceFinMk, E8_Matrix, Int.cast_zero,
            Int.cast_one, add_right_neg, AddCommGroup.modEq_refl]
          simp only [E8_Matrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
            Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four, zero_add,
            add_neg_cancel_left]
          sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, Fin.isValue, one_div, zero_add, Fin.mk_one, Fin.isValue] } }
    { use E8_Matrix 2
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one,
              Nat.reduceAdd, Matrix.tail_cons] }
          { use 1
            simp only [Int.cast_one, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Nat.reduceAdd,
              Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val',
              Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E8_Matrix, E8_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E8_Matrix 3
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_three,
              Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_three] }
          { use 1
            simp only [Int.cast_one, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Nat.reduceAdd,
              Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_three,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val',
              Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E8_Matrix, E8_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_three] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E8_Matrix 4
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one,
              Nat.reduceAdd, Matrix.tail_cons] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_two, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four] }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
              Matrix.cons_val_three, Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four] }
          { use 1
            simp only [Int.cast_one, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Nat.reduceAdd,
              Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_four,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val',
              Matrix.cons_val_fin_one] }
          { use (-1)
            simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E8_Matrix, E8_Matrix,
              Fin.isValue, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply,
              Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_four,
              Nat.succ_eq_add_one, Matrix.tail_cons, Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add,
              Nat.reduceAdd, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_four, Nat.succ_eq_add_one, Matrix.tail_cons,
              Matrix.head_cons]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E8_Matrix 5
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one]
            sorry }
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, zero_add, Fin.mk_one,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
              Matrix.empty_val', Matrix.cons_val_fin_one]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 1
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 1
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { -- This case will need to be dealt with slightly differently
      use E8_Matrix 6
      constructor
      { constructor
        { right
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { constructor
            { use -1
              simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, E8_Matrix, E8_Matrix,
                Fin.isValue, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
                Matrix.empty_val', Matrix.cons_val_fin_one]
              sorry }
            { intro hcontra
              simp only [Int.cast_one, Fin.isValue, E8_Matrix, Int.reduceNeg, Int.cast_neg,
                Int.cast_one] at hcontra
              rcases hcontra with ⟨p, hp⟩
              have even_one : Even (1 : ℤ) := by
              { use -1 * p
                rify
                simp only [hp, E8_Matrix, Fin.isValue, Fin.zero_eta, Matrix.of_apply,
                  Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
                  Matrix.cons_val_fin_one, neg_mul, one_mul]
                norm_num
                sorry }
              contradiction } }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { use E8_Matrix 7
      constructor
      { constructor
        { left
          intro j
          rcases j with ⟨j₀ | j₁ | j₂ | j₃ | j₄ | j₅ | j₆ | j₇ | m, hm⟩
          { use 0
            simp only [Int.cast_zero, E8_Matrix, E8_Matrix, Fin.isValue, Fin.zero_eta,
              Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
              Matrix.cons_val_fin_one]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 1
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use -1
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { use 0
            simp only [Int.cast_zero, Fin.isValue, E8_Matrix, Int.cast_zero]
            sorry }
          { exfalso
            simp only [Nat.add_one, Nat.succ] at hm
            cases m
            { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hm }
            { linarith } } }
        { sorry } }
      { simp only [E8_Normalised_Matrix, Fin.zero_eta, Fin.isValue, Pi.smul_apply] at hi
        simp only [← hi, zero_add, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, one_div] } }
    { exfalso
      simp only [Nat.add_one, Nat.succ] at hn
      cases n
      { simp only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, lt_self_iff_false] at hn }
      { linarith } }
    -/


end Lattice

section Packing

-- def E8 := Packing_of_Centres 8 (EuclideanLattice.E8_Normalised_Set)

instance instSpherePackingE8NormalisedLattice : SpherePackingCentres 8 E8_Normalised_Lattice where
  nonoverlapping := by
    intros x hx y hy hxy
    rcases hx with ⟨v, hv1, hv2⟩
    rcases hy with ⟨w, hw1, hw2⟩
    unfold E8_Set at hv1 hw1
    rw [Set.mem_setOf_eq] at hv1 hw1
    rcases hv1 with ⟨hv11, hv12⟩
    rcases hw1 with ⟨hw11, hw12⟩
    -- rw [PiLp.dist_eq_of_L2 x y]
    -- The above doesn't work because of the difference between `Dist.dist` and ``Euclidean.dist`!!
    -- The only strategy that comes to mind to tackle this proof is to expand `Euclidean.dist`
    -- somehow and then do cases on `hv11` and `hw11` (as in the def of `E8_Normalised_Lattice`, ie,
    -- the proof that it is an additive, commutative subgroup of the ambient space).
    sorry

def E8_Packing := Packing_of_Centres 8 E8_Normalised_Lattice

theorem Main : Constant 8 = Density 8 E8_Normalised_Lattice := sorry

end Packing

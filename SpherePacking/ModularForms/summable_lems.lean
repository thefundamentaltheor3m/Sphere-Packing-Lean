import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import SpherePacking.ModularForms.exp_lems
import SpherePacking.ModularForms.upperhalfplane
import Mathlib

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := by apply neg_neg
  right_inv := by apply neg_neg

theorem int_sum_neg {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α] (f : ℤ → α) :
  ∑' d : ℤ, f d = ∑' d, f (-d) := by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ negEquiv.toFun :=
    by
    funext
    simp
    rfl
  rw [h]
  apply symm
  apply negEquiv.tsum_eq

theorem summable_neg {α : Type*} [TopologicalSpace α] [AddCommMonoid α] (f : ℤ → α) (hf : Summable f) :
  Summable fun d => f (-d) := by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ negEquiv.toFun :=
    by
    funext
    simp
    rfl
  rw [h]
  have := negEquiv.summable_iff.mpr hf
  apply this


lemma aux33 (f : ℕ → ℂ) (hf : Summable f) : ∑' n, f (n) =
    limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.range N, f (n)) := by
  rw [Filter.Tendsto.limUnder_eq]
  have  := hf.hasSum
  have V := this.comp tendsto_finset_range
  apply V

/- this is being Pr'd-/
lemma tsum_pnat_eq_tsum_succ3 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1) := by sorry

lemma tsum_pnat_eq_tsum_succ4 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n := by sorry



theorem nat_pos_tsum2' {α : Type*} [TopologicalSpace α] [AddCommMonoid α]  (f : ℕ → α) :
    (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) :=
  by
  rw [← Equiv.summable_iff _root_.Equiv.pnatEquivNat]
  constructor
  intro hf
  apply Summable.congr hf
  intro b
  simp
  intro hf
  apply Summable.congr hf
  intro b
  simp

/-this is from the mod forms repo-/
theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α]  [ IsUniformAddGroup α] [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) :=
  by sorry


/- This is from the mod forms repo -/
theorem lhs_summable (z : ℍ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) := by sorry



lemma neg_div_neg_aux ( a b : ℂ) : -a/b = a / -b := by
  ring


theorem summable_diff (z : ℍ) (d : ℤ) :
  Summable fun m : ℕ+ ↦ 1 / (-(d : ℂ) / ↑z - ↑↑m) + 1 / (-↑d / ↑z + ↑↑m) := by
  by_cases hd : d = 0
  rw [hd]
  simp only [Int.cast_zero, neg_zero, zero_div, zero_sub, one_div, zero_add]
  conv =>
    enter [1]
    ext m
    ring_nf
  apply summable_zero
  by_cases hd2 : 0 < d
  have := lhs_summable ⟨ -d / z, by simpa using pos_nat_div_upper d hd2 z⟩
  apply this.congr
  intro b
  simp
  let D := (-d).natAbs
  have hd : 0 < D := by
    aesop
  have hd22 : (D : ℂ) = -d := by
    simp only [Int.natAbs_neg, D]
    have : 0 ≤ -d := by
      linarith
    have := Int.natAbs_of_nonneg this
    norm_cast
    rw [← this, Int.natAbs_neg ]
    rfl
  have := lhs_summable ⟨ -D/ z, by simpa using pnat_div_upper ⟨D, hd⟩ z⟩
  rw [← summable_mul_left_iff (a := -1) (by norm_num) ]
  simp at *
  rw [hd22] at this
  apply this.congr
  intro b
  field_simp
  congr 1
  rw [neg_div_neg_aux]
  ring
  rw [neg_div_neg_aux]
  ring

lemma arg1 (a b c d e f g h : ℂ) : e/ f + g /h  - a / b - c / d = e / f + g / h + a / -b + c / -d := by
  ring

lemma sum_int_pnat3 (z : ℍ) (d : ℤ) :
  ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d)) =
  (2 / z) * ∑' m : ℕ+,
    ((1 / (-(d : ℂ)/↑z - m) + 1 / (-d/↑z + m))) := by
  rw [← Summable.tsum_mul_left ]
  congr
  funext m
  have he : ∀ m d : ℂ , ((m : ℂ) * z + d) = z * ((d : ℂ)/z + m) := by
    intro m
    ring_nf
    have : (z : ℂ) ≠ (0 : ℂ) := by
      exact ne_zero z
    field_simp
  rw [arg1]
  ring_nf
  rw [add_comm]
  have h4 := ne_zero z
  simp [UpperHalfPlane.coe] at *
  congr 1
  · field_simp
  · field_simp
  · apply summable_diff


lemma pow_max (x y : ℕ) : (max x y)^2 = max (x^2) (y ^ 2) := by
    by_cases h:  max x y = x
    rw [h]
    simp at *
    nlinarith
    have hh : max x y = y := by
      simp at *
      apply h.le
    rw [hh]
    simp at *
    nlinarith

theorem extracted_abs_norm_summable (z : ℍ) (i : ℤ) :
  Summable fun m ↦ 1 / (r z ^ 2 * 2⁻¹ * ‖![m, i]‖ ^ 2) := by
  have hS : Summable fun m : ℤ => 1 / (r z ^ 2 * 2⁻¹ * m ^ 2) := by
    simp only [one_div, mul_inv_rev, inv_inv]
    apply Summable.mul_right
    norm_cast
    have := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    simpa only [Int.cast_pow, one_div] using this
  apply hS.of_norm_bounded_eventually
  rw [Filter.eventually_iff_exists_mem ]
  use (Finset.Icc (-|i|) (|i|))ᶜ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, mem_cofinite, compl_compl,
    finite_singleton, Finite.insert, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
    Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv, norm_pow, and_imp, true_and]
  simp only [Finset.coe_Icc, norm_norm, Real.norm_ofNat, inv_inv,
    Real.norm_eq_abs, _root_.sq_abs]
  constructor
  exact finite_Icc (-|i|) |i|
  intro y hy
  apply le_of_eq
  simp only [mul_eq_mul_right_iff, inv_inj, norm_nonneg, mul_eq_zero, OfNat.ofNat_ne_zero,
    inv_eq_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or]
  left
  simp [norm_eq_max_natAbs]
  have hg : ((y.natAbs : ℝ) ⊔ ↑i.natAbs) ^ 2 = y.natAbs ^ 2 ⊔ i.natAbs ^ 2 := by
    zify
    norm_cast
    rw [pow_max]
  rw [hg]
  have hg2 :  y.natAbs ^ 2 ⊔ i.natAbs ^ 2 =  y.natAbs ^ 2:= by
    simp only [sup_eq_left]
    have hii : i^2 ≤ y^2 := by
      rw [@sq_le_sq]
      simp only [mem_Icc, not_and, not_le] at hy
      rw [@le_abs']
      by_cases hh : -|i| ≤ y
      have hhy := hy hh
      right
      exact hhy.le
      simp only [not_le] at hh
      left
      exact hh.le
    zify
    aesop
  rw [hg2]
  simp only [Nat.cast_pow, Nat.cast_nonneg]
  have := Int.natAbs_pow_two y
  norm_cast
  rw [← this]
  rfl


lemma aux (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a⁻¹ ≤ c * b⁻¹ ↔ b ≤ c * a := by
  constructor
  intro h
  simp_rw [inv_eq_one_div] at h
  rw [mul_one_div, le_div_comm₀ _ hb] at h
  simp only [one_div, div_inv_eq_mul] at h
  apply h
  simp only [one_div, inv_pos]
  exact ha
  intro h
  simp_rw [inv_eq_one_div]
  rw [← div_le_comm₀ _ ha]
  simp only [one_div, mul_inv_rev, inv_inv]
  rw [propext (mul_inv_le_iff₀ hc), mul_comm]
  exact h
  simp only [one_div]
  apply mul_pos hc (inv_pos.mpr hb)

/- lemma summable_hammer (f g : ℕ → ℂ) (a b : ℝ) (hab : 1 < a + b)
    (hf : (fun n => (f n)⁻¹) =O[atTop] fun n => (n : ℝ) ^ (-a : ℝ))
    (hg : (fun n => (g n)⁻¹) =O[atTop] fun n => (n : ℝ) ^ (-b : ℝ))  :
    Summable fun n => (f n * g n)⁻¹ := by

  have := (Real.summable_nat_rpow_inv (p := a + b)).mpr (by norm_cast at *)
  rw [← summable_nat_add_iff 1] at *
  apply summable_of_isBigO_nat this
  conv =>
    enter [3]
    ext nReA
    rw [← Real.rpow_neg (by norm_cast; simp), neg_add, Real.rpow_add (by norm_cast; simp)]
  conv =>
    enter [2]
    ext n
    rw [mul_inv]

  apply Asymptotics.IsBigO.mul hf hg -/


lemma summable_hammerTime  {α : Type} [NormedField α] [CompleteSpace α] (f  : ℤ → α) (a : ℝ) (hab : 1 < a)
    (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) :
    Summable fun n => (f n)⁻¹ := by
  apply summable_of_isBigO _ hf
  have := Real.summable_abs_int_rpow hab
  apply this.congr
  intro b
  refine Real.rpow_neg ?_ a
  exact abs_nonneg (b : ℝ)


lemma AA (f g e : ℤ → ℝ) (hf : f =O[cofinite] g) (h : e =O[cofinite] f) : e =O[cofinite] g := by
  exact Asymptotics.IsBigO.trans h hf

/- lemma chris (f g e : ℤ → ℝ) (hf : f =O[cofinite] g) (h : (fun x => ‖e x‖) ≤ᶠ[cofinite] f) : e =O[cofinite] g := by
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  rw [@Asymptotics.isBigO_iff'] at hf

  rw [@eventuallyLE_iff_all_subsets] at h

  --simp at hh
  rw [@eventuallyLE_iff_all_subsets]
  intro s
  have hh := h s

  sorry -/

lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y,x]‖ := by
  simp_rw [EisensteinSeries.norm_eq_max_natAbs]
  rw [max_comm]
  simp

lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have h1 : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    (fun n : ℤ => ((r z * ‖![n, m]‖))⁻¹) := by
    rw [@Asymptotics.isBigO_iff']
    use 1
    simp
    constructor
    repeat{
    use 0
    intro n hn
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![m, n]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ge_iff_le] at *
    nth_rw 2 [mul_comm]
    simp_rw [Real.rpow_neg_one] at this
    have hr : (r z)⁻¹ = |r z|⁻¹ := by
      simp only [inv_inj]
      apply symm
      rw [abs_eq_self]
      exact (r_pos z).le
    rw [← hr, norm_symm]
    exact this}
  apply  Asymptotics.IsBigO.trans  h1
  rw [@Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp; exact r_pos z, ?_⟩
  simp
  constructor
  use min (-1) m
  intro n hn
  --have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · rw [EisensteinSeries.norm_eq_max_natAbs]
    simp
    left
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · simp at *;
    left
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl

lemma linear_bigO' (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have h1 : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    (fun n : ℤ => ((r z * ‖![m, n]‖))⁻¹) := by
    rw [@Asymptotics.isBigO_iff']
    use 1
    simp
    constructor
    repeat{
    use 0
    intro n hn
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ge_iff_le] at *
    nth_rw 2 [mul_comm]
    simp_rw [Real.rpow_neg_one] at this
    have hr : (r z)⁻¹ = |r z|⁻¹ := by
      simp only [inv_inj]
      apply symm
      rw [abs_eq_self]
      exact (r_pos z).le
    rw [← hr, norm_symm]
    exact this}
  apply  Asymptotics.IsBigO.trans  h1
  rw [@Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp; exact r_pos z, ?_⟩
  simp
  constructor
  use min (-1) m
  intro n hn
  --have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · rw [EisensteinSeries.norm_eq_max_natAbs]
    simp
    right
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · simp at *;
    right
    norm_cast
    rw [Int.abs_eq_natAbs]
    rfl


theorem summable_diff_denom (z : ℍ) (i : ℤ) :
  Summable fun (m : ℤ) ↦ ((m : ℂ) * ↑z + ↑i + 1)⁻¹ * ((m : ℂ) * ↑z + ↑i)⁻¹ := by
  conv =>
    enter [1]
    ext m
    rw [← mul_inv]
  apply summable_hammerTime _ 2 (by norm_num)
  have h1 := linear_bigO' (i+1) z
  have h2 := linear_bigO' i z
  have h3 := h2.mul h1
  apply h3.congr
  · intro n
    rw [mul_comm]
    simp
    ring
  · intro n
    norm_cast
    rw [pow_two]
    rw [← mul_inv]
    simp

lemma summable_pain (z : ℍ) (i : ℤ) :
  Summable (fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i + 1)) := by
  rw [← Finset.summable_compl_iff (s := {0})]
  have h1 : (fun m : { x // x ∉ ({0} : Finset ℤ) } ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i + 1)) =
    (fun m :  { x // x ∉ ({0} : Finset ℤ) } ↦ 1 / (((m.1 : ℂ) * ↑z + ↑i)*((m : ℂ) * ↑z + ↑i + 1))) := by
    funext m
    rw [ div_sub_div]
    simp only [one_mul, mul_one, add_sub_cancel_left, one_div, mul_inv_rev]
    have := linear_ne_zero ![m, i] z ?_
    simpa using this
    aesop
    have h2 := linear_ne_zero ![m, i + 1] z ?_
    simp only [Fin.isValue, Matrix.cons_val_zero, ofReal_intCast, Matrix.cons_val_one,
      Matrix.head_cons, ofReal_add, ofReal_one, ne_eq] at h2
    rw [add_assoc]
    exact h2
    aesop
  rw [h1]
  simp
  have :  Summable fun (m : ℤ) ↦ (↑(m : ℂ) * (z  : ℂ) + ↑i + 1)⁻¹ * (↑(m : ℂ) * (z : ℂ) + ↑i)⁻¹ := by
    apply summable_diff_denom
  rw [← Finset.summable_compl_iff  (s := {0}) ]  at this
  apply this


theorem vector_norm_bound (b : Fin 2 → ℤ) (hb : b ≠ 0) (HB1 : b ≠ ![0, -1]) :
    ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) ≤ 2 * ‖b‖ ^ (-3 : ℝ) := by
  rw [show (-3 : ℝ) = -1 -2  by norm_num]
  have ht : b = ![b 0, b 1] := by
    ext i
    fin_cases i <;> rfl
  nth_rw 3 [Real.rpow_of_add_eq (y := -1) (z := -2) (by apply norm_nonneg) (by norm_num)
    (by norm_num)]
  rw [← mul_assoc]
  apply mul_le_mul
  · simp_rw [Real.rpow_neg_one]
    rw [aux]
    · simp only [norm_eq_max_natAbs, Nat.cast_max, Nat.succ_eq_add_one, Nat.reduceAdd,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, max_le_iff]
      have : 2 * max ↑(b 0).natAbs ↑(b 1 + 1).natAbs = max (2*(b 0)).natAbs (2*(b 1 + 1)).natAbs := by
        simp_rw [Int.natAbs_mul]
        exact (Nat.mul_max_mul_left 2 (b 0).natAbs (b 1 + 1).natAbs).symm
      refine ⟨?_ , ?_⟩
      · norm_cast
        simp only [this, Fin.isValue, le_max_iff]
        left
        simp only [Int.natAbs_mul, Int.reduceAbs]
        apply Nat.le_mul_of_pos_left _ Nat.zero_lt_two
      norm_cast
      rcases eq_or_ne (b 1) (-1) with hr | hr
      · simp only [this, le_max_iff]
        left
        simp only [hr, Int.reduceNeg, IsUnit.neg_iff, isUnit_one, Int.natAbs_of_isUnit, Fin.isValue, Int.natAbs_mul, Int.reduceAbs, Fin.isValue]
        have hb0 : b 0 ≠ 0 := by
          rw [ht, hr] at HB1
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Int.reduceNeg, ne_eq] at HB1
          by_contra hh
          simp only [hh, Int.reduceNeg, not_true_eq_false] at HB1
        omega
      · rw [this]
        simp only [Fin.isValue, le_max_iff]
        right
        simp only [Int.natAbs_mul, Int.reduceAbs]
        omega
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, norm_pos_iff, ne_eq,
      Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and]
      intro h
      by_contra H
      rw [@add_eq_zero_iff_eq_neg] at H
      rw [ht, h, H] at HB1
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, ne_eq, not_true_eq_false] at HB1
    · exact norm_pos_iff.mpr hb
    · simp only [Nat.ofNat_pos]
  · rfl
  · apply Real.rpow_nonneg
    apply norm_nonneg
  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    apply Real.rpow_nonneg
    apply norm_nonneg


lemma G_2_alt_summable (z : ℍ) : Summable fun  (m : Fin 2 → ℤ) =>
    1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1))  := by
  have hk' : 2 < (3 : ℝ) := by linarith
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-3 : ℝ) *  2).of_norm_bounded_eventually
  rw [Filter.eventually_iff_exists_mem ]
  use { ![0,0], ![0,-1]}ᶜ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, mem_cofinite, compl_compl,
    finite_singleton, Finite.insert, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
    Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv,  norm_pow, and_imp, true_and]
  intro b HB1 HB2
  have hk0 : 0 ≤ (2 : ℝ) := by norm_num
  have hk0' : 0 ≤ (1 : ℝ) := by norm_num
  have p1 := summand_bound z  hk0 b
  let b' : Fin 2 → ℤ := ![b 0, b 1 + 1]
  have p2 := summand_bound z hk0' b'
  simp only [Nat.ofNat_nonneg, zero_le_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Int.cast_add, Int.cast_one, one_div, mul_inv_rev, map_mul, map_inv₀, map_pow,
     ge_iff_le, b'] at *
  have := mul_le_mul p2 p1 ?_ ?_
  have hpow : ‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1))‖ ^ (-2 : ℝ) =
    (‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1))‖ ^ 2)⁻¹ :=
    by norm_cast
  have hpow2 : ‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1)) + 1‖ ^ (-1 : ℝ) =
    (‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1)) + 1‖)⁻¹ :=
    by apply Real.rpow_neg_one
  rw [← hpow, ← hpow2]
  rw [← add_assoc] at this
  apply le_trans this
  have :  r z ^ (-1 : ℝ) * ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * (r z ^ (-2 : ℝ) * ‖b‖ ^ (-2 : ℝ)) =
    r z ^ (-3 : ℝ) * ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) := by
    rw [show (-3 : ℝ) = -2 -1  by norm_num]
    nth_rw 5 [Real.rpow_of_add_eq (y := -2) (z := -1)]
    ring
    exact (r_pos z).le
    norm_cast
    norm_cast
  rw [this]
  have hg : r z ^ (-3 : ℝ) * 2 * ‖b‖ ^ (-3 : ℝ) = r z ^ (-3 : ℝ) * (2 * ‖b‖ ^ (-3 : ℝ)) := by ring
  rw [hg, mul_assoc]
  apply mul_le_mul
  rfl
  apply  vector_norm_bound
  convert HB1
  apply symm
  simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self]
  simpa using HB2
  · exact
    mul_nonneg (Real.rpow_nonneg (norm_nonneg ![b 0, b 1 + 1]) (-1))
      (Real.rpow_nonneg (norm_nonneg b) (-2))
  · apply Real.rpow_nonneg
    apply (r_pos z).le
  · apply Real.rpow_nonneg
    apply norm_nonneg
  · exact
    mul_nonneg (Real.rpow_nonneg (LT.lt.le (r_pos z)) (-1))
      (Real.rpow_nonneg (norm_nonneg ![b 0, b 1 + 1]) (-1))


def δ (a b : ℤ): ℂ := if a = 0 ∧ b = 0 then 1 else if a = 0 ∧ b = -1 then 2 else 0

@[simp]
lemma δ_eq : δ 0 0 = 1 := by simp [δ]

@[simp]
lemma δ_eq2 : δ 0 (-1) = 2 := by simp [δ]

lemma δ_neq (a b : ℤ) (h : a ≠ 0) : δ a b = 0 := by
  simp [δ, h]

lemma G_2_alt_summable_δ (z : ℍ) : Summable fun  (m : Fin 2 → ℤ) =>
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)):= by
    let s : Finset (Fin 2 → ℤ) := { ![0,0], ![0,-1]}
    rw [← Finset.summable_compl_iff s]
    have := (G_2_alt_summable z).subtype sᶜ
    simp at *
    apply this.congr
    intro b
    simp at *
    have hb1 : b.1 ≠ ![0, 0] := by aesop
    have hb2 : b.1 ≠ ![0, -1] := by aesop
    simp [δ]
    split_ifs with h1 h2
    exfalso
    have hb : b.1 = ![0, 0] := by
      nth_rw 1 [← h1.1, ← h1.2]
      simp
      exact List.ofFn_inj.mp rfl
    exact hb1 hb
    exfalso
    have hb : b.1 = ![0, -1] := by
      nth_rw 1 [← h2.1, ← h2.2]
      simp
      exact List.ofFn_inj.mp rfl
    exact hb2 hb
    rfl

theorem G2_prod_summable1 (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ := by
  have := G_2_alt_summable z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor b

theorem G2_prod_summable1_δ (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ + δ b c := by
  have := G_2_alt_summable_δ z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor b



def swap : (Fin 2 → ℤ) → (Fin 2 → ℤ) := fun x => ![x 1, x 0]

@[simp]
lemma swap_apply (b : Fin 2 → ℤ) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive (b : Fin 2 → ℤ) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

def swap_equiv : Equiv (Fin 2 → ℤ) (Fin 2 → ℤ) := Equiv.mk swap swap
  (by rw [LeftInverse]; apply swap_involutive)
  (by rw [Function.RightInverse]; apply swap_involutive)


lemma G2_alt_indexing_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1))  =
    ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z + n)^2 * (m * z + n +1)) + (δ m n)) := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  simp
  refine tsum_prod' ?h ?h₁
  have := G_2_alt_summable_δ z
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this
  intro b
  simp
  have := G_2_alt_summable_δ z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor




lemma G2_alt_indexing2_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1))  =
    ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  have := (G_2_alt_summable_δ z)
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  rw [tsum_comm']
  rw [G2_alt_indexing_δ]
  apply this.congr
  intro b
  simp
  rfl
  intro b
  simp
  apply this.prod_factor
  intro c
  simp
  have H := (G_2_alt_summable_δ z)
  simp at this
  rw [← swap_equiv.summable_iff] at H
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
  simp [Fin.isValue, one_div, mul_inv_rev, swap_equiv, Equiv.coe_fn_mk,
    finTwoArrowEquiv_symm_apply, swap_apply] at H
  have := H.prod_factor c
  simp at this
  apply this

/-This is proven in the modular forms repo. -/
lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by sorry



lemma sum_range_zero (f : ℤ → ℂ) (n : ℕ) : ∑ m ∈ Finset.range (n+1), f m = f 0 +
  ∑ m ∈ Finset.range n, f (m+1) := by
  rw [Finset.sum_range_succ' ]
  rw [add_comm]
  simp


/-This is from the modforms repo, so no need to prove it. -/
theorem q_exp_iden (k : ℕ) (hk : 2 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
      ∑' n : ℕ+, n ^ ((k - 1) ) * Complex.exp (2 * ↑π * Complex.I * z * n) := sorry

/-This is straight from the mod forms repo-/
theorem tsum_sigma_eqn {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c.1 * c.2) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * e * z) := by sorry

/-This is straight from the mod forms repo-/
theorem a1 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * e * c) := by sorry

/-This is straight from the mod forms repo-/
theorem a3 {k : ℕ} (h : 2 ≤ k) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ (k - 1) * exp (2 * ↑π * Complex.I * e * ↑z * c) := by sorry

/-This is straight from the mod forms repo-/
theorem a4 (k : ℕ) (z : ℍ) :
    Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑c * ↑z * ↑b)) := by sorry


lemma t9 (z : ℍ) : ∑' m : ℕ,
  ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n))  =  -
    8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * n * z) := by
  have := tsum_pnat_eq_tsum_succ3 (fun m => 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n))
  simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one, Nat.cast_add] at *
  rw [← this]
  have := tsum_sigma_eqn z (k := 1)
  rw [tsum_mul_left, ← this]
  have he :  2 * (2 * ↑π * Complex.I) ^ 2 = - 8 * π ^ 2 := by
     rw [pow_two]
     ring_nf
     simp only [I_sq, mul_neg, mul_one, neg_mul]
  rw [he]
  simp only [neg_mul, pow_one, neg_inj, mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
    ne_eq, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, false_or]
  left
  symm
  simp only [pow_one, neg_mul] at *
  rw [tsum_prod, tsum_comm' ]
  congr
  funext m
  congr
  funext n
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false]
  congr 1
  ring
  · have := (a4 2 z).prod_symm
    simp [_root_.swap] at *
    apply this.congr
    intro b
    rw [Prod.swap]
    simp [uncurry]
    ring_nf
  · intro e
    have := a3 (k := 2) (by rfl) e z
    simp at *
    apply this.congr
    intro b
    ring_nf
  · intro e
    have := a1 2 e z
    simp at *
    exact this
  have := a4 2 z
  apply this.congr
  intro b
  simp [uncurry]
  congr 1
  ring

lemma ada (f : ℤ → ℂ) (h : ∀ i, f i = 0) : ∑' n, f n = 0 := by
  convert tsum_zero
  aesop


lemma summable_pnats (f : ℕ → ℂ) : Summable (fun n : ℕ+ => f n) ↔ Summable f := by
  rw [nat_pos_tsum2', summable_nat_add_iff]

lemma auxf (a b c d : ℂ) : a / b - (c / d) = a / b  + (c / -d) := by
  ring

theorem summable_diff_right_a (z : ℍ) (d : ℕ+) :
  Summable fun n : ℕ ↦ 1 / ((n : ℂ) * ↑z - ↑↑d) - 1 / (↑↑n * ↑z + ↑↑d) := by
  rw [← summable_pnats]
  have := (summable_diff z d).mul_left ((z : ℂ))⁻¹
  apply this.congr
  intro b
  have hz := ne_zero z
  simp [UpperHalfPlane.coe] at *
  field_simp
  rw [add_comm, auxf, add_mul]
  congr 1
  ring
  ring

theorem summable_diff_right  (z : ℍ) (d : ℕ+) :
  Summable fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z - ↑↑d) - 1 / (↑m * ↑z + ↑↑d) := by
  rw [summable_int_iff_summable_nat_and_neg ]
  constructor
  · apply summable_diff_right_a
  · rw [← summable_pnats]
    have := (summable_diff z d).mul_left ((z : ℂ))⁻¹
    apply this.congr
    intro b
    have hz := ne_zero z
    simp [UpperHalfPlane.coe] at *
    field_simp
    rw [auxf, add_mul]
    congr 1
    ring
    ring

lemma sum_int_pnatt (z : ℍ) (d : ℕ+) :
  2/ d + ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d))  = ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d)) := by

  rw [int_tsum_pNat]
  simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
    neg_mul]
  ring_nf
  rw [← tsum_add]
  congr
  funext m
  ring
  group
  simp only [Int.reduceNeg, zpow_neg, zpow_one]

  · have := (summable_diff_right z d)
    rw [summable_int_iff_summable_nat_and_neg ] at this
    have H := this.1
    simp at *
    have v : Summable fun (n : ℕ) ↦ (-↑(d : ℂ) + (n : ℂ) * ↑z)⁻¹ - (↑↑d + (n : ℂ)* ↑z)⁻¹ := by
      apply H.congr
      intro b
      ring
    apply v.subtype
  · have := (summable_diff_right z d)
    rw [summable_int_iff_summable_nat_and_neg ] at this
    have H := this.2
    simp only [Int.cast_natCast, one_div, Int.cast_neg, neg_mul] at *
    have v : Summable fun (n : ℕ) ↦ (-((n : ℂ) * ↑z)  - ↑(d : ℂ))⁻¹ - (-((n : ℂ)* ↑z) + ↑↑d )⁻¹ := by
      apply H.congr
      intro b
      ring
    apply v.subtype

  · have := summable_diff_right z d
    exact this


lemma sum_int_pnat2_pnat (z : ℍ) (d : ℕ+) :
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d))  = -2/d + ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d)) := by
  rw [← sum_int_pnatt]
  ring


lemma exp_aux (z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * n * ↑z) =
    cexp (2 * ↑π * Complex.I * ↑z) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem summable_exp_pow (z : ℍ) : Summable fun i : ℕ ↦
     ‖(cexp (2 * ↑π * Complex.I * (↑i + 1) * z))‖ := by
  conv =>
    enter [1]
    ext i
    rw [show ((i : ℂ) + 1) = ((i + 1) : ℕ) by simp, exp_aux, norm_pow]
  rw [summable_nat_add_iff 1 ]
  simp only [summable_geometric_iff_norm_lt_one, norm_norm]
  apply exp_upperHalfPlane_lt_one

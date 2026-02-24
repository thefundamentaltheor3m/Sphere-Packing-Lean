module
public import SpherePacking.ModularForms.SummableLemmas.Basic

/-!
# Cotangent and Eisenstein series summability lemmas

This file proves summability statements and rearrangements of infinite sums that arise when
working with cotangent expansions and the alternative definition of `G_2`.

## Main statements
* `lhs_summable`
* `sum_int_even`
* `summable_diff`
* `G_2_alt_summable`

## Main definitions
* `δ`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open ArithmeticFunction

lemma pnat_inv_sub_squares (z : ℍ) :
    (fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n)) =
      fun n : ℕ+ => 2 * z.1 * (1 / (z ^ 2 - n ^ 2)) := by
  funext n
  have hsub : (z : ℂ) - n ≠ 0 := by simpa [sub_eq_zero] using upp_half_not_ints z (n : ℤ)
  have hplus : (z : ℂ) + n ≠ 0 := upper_half_plane_ne_int_add z n
  rw [one_div_add_one_div (ha := hsub) (hb := hplus)]
  have hnum : (z : ℂ) - n + (z + n) = 2 * (z : ℂ) := by ring
  have hden : ((z : ℂ) - n) * ((z : ℂ) + n) = (z : ℂ) ^ 2 - n ^ 2 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (sq_sub_sq (z : ℂ) (n : ℂ)).symm
  rw [hnum, hden, div_eq_mul_inv, one_div]


lemma upper_half_plane_ne_int_pow_two (z : ℍ) (n : ℤ) : (z : ℂ) ^ 2 - n ^ 2 ≠ 0 := by
  have hsub : (z : ℂ) - n ≠ 0 := by simpa [sub_eq_zero] using upp_half_not_ints z n
  have hplus : (z : ℂ) + n ≠ 0 := upper_half_plane_ne_int_add z n
  simpa [sq_sub_sq, mul_assoc, mul_left_comm, mul_comm] using mul_ne_zero hplus hsub

theorem upbnd (z : ℍ) (d : ℤ) : (d ^ 2 : ℝ) * r z ^ 2 ≤ ‖((z : ℂ) ^ 2 - d ^ 2)‖ := by
  by_cases hd : d ≠ 0
  · have h1 : (z ^ 2 : ℂ) - d ^ 2 = d ^ 2 * (1 / d * z - 1) * (1 / d * z + 1) := by
      ring_nf; simp [hd]
    rw [h1]
    simp only [one_div, Complex.norm_mul, norm_pow, norm_intCast, sq_abs, ge_iff_le]
    rw [mul_assoc]
    gcongr
    rw [pow_two]
    gcongr
    · exact (r_pos _).le
    · refine (auxbound2 z ((d : ℝ)⁻¹) (d := -1) (by norm_num)).trans_eq ?_
      congr
      simp only [ofReal_inv, ofReal_intCast, ofReal_neg, ofReal_one]
      ring
    · refine (auxbound2 z ((d : ℝ)⁻¹) (d := 1) (by norm_num)).trans_eq ?_
      congr
      simp only [ofReal_inv, ofReal_intCast]
  · simp only [ne_eq, Decidable.not_not] at hd
    simp only [hd, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      sub_zero, norm_pow, norm_nonneg, pow_nonneg]

/-- Summability of the cotangent-style series `∑_{n>0} (1/(z-n) + 1/(z+n))` for `z ∈ ℍ`. -/
public theorem lhs_summable (z : ℍ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) := by
  rw [pnat_inv_sub_squares]
  apply Summable.mul_left
  apply summable_norm_iff.1
  simp only [one_div, norm_inv]
  have hs : Summable fun n : ℕ+ => (r z ^ 2 * n ^ 2)⁻¹ := by
    simp only [mul_inv_rev]
    apply Summable.mul_right
    have hrr : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ 2)⁻¹ := by
      simp
    apply hrr.subtype
  apply Summable.of_nonneg_of_le _ _ hs
  · intro b
    simp [inv_nonneg]
  intro b
  rw [inv_le_inv₀]
  · rw [mul_comm]
    apply upbnd z
  · simpa using (upper_half_plane_ne_int_pow_two z b)
  positivity [r_pos z]

/-- If `f` is even and summable over `ℤ`, then its `tsum` is `f 0 + 2 * ∑_{n>0} f n`. -/
public theorem sum_int_even {α : Type*} [UniformSpace α] [CommRing α] [IsUniformAddGroup α]
    [CompleteSpace α] [T2Space α] (f : ℤ → α) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) :
    ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n := by
  simpa using tsum_int_eq_zero_add_two_mul_tsum_pnat (f := f) (fun n => by simpa using hf (-n)) hf2

/-- Summability of a symmetric translated series of simple poles. -/
public theorem summable_diff (z : ℍ) (d : ℤ) :
    Summable fun m : ℕ+ ↦ 1 / (-(d : ℂ) / ↑z - ↑↑m) + 1 / (-↑d / ↑z + ↑↑m) := by
  by_cases hd : d = 0
  · subst hd
    simp
  by_cases hd2 : 0 < d
  · have := lhs_summable ⟨ -d / z, by simpa using pos_nat_div_upper d hd2 z⟩
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
    rw [← this, Int.natAbs_neg]
    rfl
  have := lhs_summable ⟨ -D/ z, by simpa using pnat_div_upper ⟨D, hd⟩ z⟩
  rw [← summable_mul_left_iff (a := -1) (by norm_num)]
  simp only [not_lt, one_div, neg_mul, one_mul, neg_add_rev] at *
  rw [hd22] at this
  apply this.congr
  intro b
  field_simp
  simp [neg_inv, sub_eq_add_neg, add_comm]

lemma arg1 (a b c d e f g h : ℂ) : e / f + g / h - a / b - c / d = e / f + g / h + a / -b + c / -d
    := by ring

/-- Rewrite a difference of symmetric `ℕ+` sums as a scaled sum in the variable `-d/z`. -/
public lemma sum_int_pnat3 (z : ℍ) (d : ℤ) :
  ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d))
      =
  (2 / z) * ∑' m : ℕ+,
    ((1 / (-(d : ℂ)/↑z - m) + 1 / (-d/↑z + m))) := by
  rw [← Summable.tsum_mul_left]
  · congr
    funext m
    rw [arg1]
    ring_nf
    rw [add_comm]
    have : (z : ℂ) ≠ (0 : ℂ) := ne_zero z
    field_simp
  · apply summable_diff


private lemma aux (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a⁻¹ ≤ c * b⁻¹ ↔ b ≤ c * a := by
  have h2 : (a⁻¹ : ℝ) * b ≤ c ↔ b ≤ c * a := by
    simpa [mul_comm] using (mul_inv_le_iff₀ (a := c) (b := b) (c := a) ha)
  exact (le_mul_inv_iff₀ (a := (a⁻¹ : ℝ)) (b := c) (c := b) hb).trans h2

/--
A helper summability lemma: if `f n` grows at least like `n^a` for `a > 1`, then `∑ 1 / f n`
converges.
-/
public lemma summable_hammerTime_nat {α : Type} [NormedField α] [CompleteSpace α]
    (f : ℕ → α) (a : ℝ) (hab : 1 < a)
    (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) :
    Summable fun n => (f n)⁻¹ := by
  apply summable_of_isBigO _ hf
  have hs := Real.summable_nat_rpow_inv.mpr hab
  refine hs.congr ?_
  intro b
  simp

theorem summable_diff_denom (z : ℍ) (i : ℤ) :
  Summable fun (m : ℤ) ↦ ((m : ℂ) * ↑z + ↑i + 1)⁻¹ * ((m : ℂ) * ↑z + ↑i)⁻¹ := by
  conv =>
    enter [1]
    ext m
    rw [← mul_inv]
  apply summable_inv_of_isBigO_rpow_inv one_lt_two
  have h3 := (linear_bigO' i z).mul (linear_bigO' (i + 1) z)
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

public lemma summable_pain (z : ℍ) (i : ℤ) :
  Summable (fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i + 1)) := by
  rw [← Finset.summable_compl_iff (s := {0})]
  have h1 : (fun m : { x // x ∉ ({0} : Finset ℤ) } ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i +
    1)) =
    (fun m : { x // x ∉ ({0} : Finset ℤ) } ↦ 1 / (((m.1 : ℂ) * ↑z + ↑i)*((m : ℂ) * ↑z + ↑i + 1)))
    := by
    funext m
    rw [div_sub_div]
    · simp only [one_mul, mul_one, add_sub_cancel_left, one_div, mul_inv_rev]
    · have := linear_ne_zero (cd := ![m, i]) z ?_
      · simpa using this
      aesop
    have h2 := linear_ne_zero (cd := ![m, i + 1]) z ?_
    · simp only [Fin.isValue, Matrix.cons_val_zero, ofReal_intCast, Matrix.cons_val_one,
        ofReal_add, ofReal_one, ne_eq] at h2
      rw [add_assoc]
      exact h2
    aesop
  rw [h1]
  simp only [one_div, mul_inv_rev]
  simpa using
    (summable_diff_denom z i).comp_injective (i := fun m : { x // x ∉ ({0} : Finset ℤ) } ↦ (m : ℤ))
      Subtype.coe_injective


theorem vector_norm_bound (b : Fin 2 → ℤ) (hb : b ≠ 0) (HB1 : b ≠ ![0, -1]) :
    ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) ≤ 2 * ‖b‖ ^ (-3 : ℝ) := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hvpos : 0 < ‖![b 0, b 1 + 1]‖ := by
    refine norm_pos_iff.2 ?_
    intro h
    have hb0 : b 0 = 0 := by simpa using congrArg (fun v => v 0) h
    have hb1 : b 1 = -1 := by
      have : b 1 + 1 = 0 := by simpa using congrArg (fun v => v 1) h
      linarith
    have : b = ![0, -1] := by
      ext i
      fin_cases i <;> simp [hb0, hb1]
    exact HB1 this
  rw [show (-3 : ℝ) = -1 -2 by norm_num]
  nth_rw 3 [Real.rpow_of_add_eq (y := -1) (z := -2) (by apply norm_nonneg) (by norm_num)
    (by norm_num)]
  rw [← mul_assoc]
  apply mul_le_mul
  · simp_rw [Real.rpow_neg_one]
    rw [aux (a := ‖![b 0, b 1 + 1]‖) (b := ‖b‖) (c := 2) hvpos hbpos]
    simp only [norm_eq_max_natAbs, Nat.cast_max, Nat.succ_eq_add_one, Nat.reduceAdd,
      Matrix.cons_val_zero, Matrix.cons_val_one, max_le_iff]
    have hmax :
        2 * max ↑(b 0).natAbs ↑(b 1 + 1).natAbs =
          max (2 * (b 0)).natAbs (2 * (b 1 + 1)).natAbs := by simp [Int.natAbs_mul]
    refine ⟨?_, ?_⟩
    · norm_cast
      simp only [hmax, le_max_iff]
      left
      simp only [Int.natAbs_mul, Int.reduceAbs]
      exact Nat.le_mul_of_pos_left _ Nat.zero_lt_two
    · norm_cast
      rcases eq_or_ne (b 1) (-1) with hr | hr
      · have hb0 : b 0 ≠ 0 := by
          intro hb0
          apply HB1
          ext i
          fin_cases i <;> simp [hb0, hr]
        simp only [hmax, le_max_iff]
        left
        simp only [hr, Int.reduceNeg, IsUnit.neg_iff, isUnit_one, Int.natAbs_of_isUnit,
          Int.natAbs_mul, Int.reduceAbs]
        omega
      · simp only [hmax, le_max_iff]
        right
        simp only [Int.natAbs_mul, Int.reduceAbs]
        omega
  · rfl
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    exact Real.rpow_nonneg (norm_nonneg _) _


/-- Summability of the alternative `G_2` defining series (excluding the correction term `δ`). -/
public lemma G_2_alt_summable (z : ℍ) : Summable fun (m : Fin 2 → ℤ) =>
    1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) := by
  have hk' : (2 : ℝ) < 3 := by norm_num
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-3 : ℝ) * 2).of_norm_bounded_eventually
  rw [Filter.eventually_iff_exists_mem]
  use { ![0,0], ![0,-1]}ᶜ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, mem_cofinite, compl_compl,
    finite_singleton, Finite.insert, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
    Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv, norm_pow, and_imp, true_and]
  intro b HB1 HB2
  have p1 := summand_bound z (by norm_num : (0 : ℝ) ≤ 2) b
  have p2 := summand_bound z (by norm_num : (0 : ℝ) ≤ 1) ![b 0, b 1 + 1]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_add, Int.cast_one,
    ge_iff_le] at *
  have hmul :=
      mul_le_mul p2 p1 (Real.rpow_nonneg (norm_nonneg _) (-2))
        (mul_nonneg (Real.rpow_nonneg (r_pos z).le (-1))
          (Real.rpow_nonneg (norm_nonneg ![b 0, b 1 + 1]) (-1)))
  have hpow : ‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1))‖ ^ (-2 : ℝ) =
      (‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1))‖ ^ 2)⁻¹ := by norm_cast
  have hpow2 : ‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1)) + 1‖ ^ (-1 : ℝ) =
      (‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1)) + 1‖)⁻¹ := by simpa using Real.rpow_neg_one _
  rw [← hpow, ← hpow2]
  have hmul' := hmul
  rw [← add_assoc] at hmul'
  refine (le_trans hmul' ?_)
  have hsplit :
      r z ^ (-1 : ℝ) * ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * (r z ^ (-2 : ℝ) * ‖b‖ ^ (-2 : ℝ)) =
        r z ^ (-3 : ℝ) * ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) := by
    rw [show (-3 : ℝ) = -2 -1 by norm_num]
    nth_rw 5 [Real.rpow_of_add_eq (y := -2) (z := -1)]
    · ring
    · exact (r_pos z).le
    · norm_cast
    norm_cast
  rw [hsplit]
  have hbnd : ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) ≤ 2 * ‖b‖ ^ (-3 : ℝ) := by
    refine vector_norm_bound b ?_ ?_
    · convert HB1
      apply symm
      simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self]
    · simpa using HB2
  have hznonneg : 0 ≤ r z ^ (-3 : ℝ) := Real.rpow_nonneg (r_pos z).le _
  have := mul_le_mul_of_nonneg_left hbnd hznonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

/--
The correction term in the alternative definition of `G_2`, supported at `(0,0)` and `(0,-1)`.
-/
@[expose] public noncomputable def δ (a b : ℤ) : ℂ :=
  if a = 0 ∧ b = 0 then 1 else if a = 0 ∧ b = -1 then 2 else 0

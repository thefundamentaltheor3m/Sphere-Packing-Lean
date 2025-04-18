import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import SpherePacking.ModularForms.exp_lems
import SpherePacking.ModularForms.upperhalfplane
import SpherePacking.ModularForms.cotangent
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
  (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1) := by
  apply tsum_pnat_eq_tsum_succ



theorem nat_pos_tsum2   {α : Type _} [TopologicalSpace α] [AddCommMonoid α]
  (f : ℕ → α) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f :=
  by
  apply Function.Injective.summable_iff
  exact PNat.coe_injective
  intro x hx
  simp at *
  by_cases h : 0 < x
  have := hx ⟨x,h⟩
  simp at this
  simp at *
  rw [h]
  exact hf

theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [T2Space α]
  [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n :=
  by
  by_cases hf2 : Summable f
  rw [tsum_eq_zero_add]
  rw [hf]
  simp
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw  [← _root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    have hf3 : Summable ((fun n : ℕ => f (n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by
        apply hf2.subtype
      apply Summable.congr hs
      intro b; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
  apply symm
  apply hpos.tsum_eq
  apply hf2
  have h1 := tsum_eq_zero_of_not_summable hf2
  rw [← nat_pos_tsum2 f hf] at hf2
  have h2 := tsum_eq_zero_of_not_summable hf2
  simp [h1, h2]


lemma tsum_pnat_eq_tsum_succ4 {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α]
  (f : ℕ → α) (hf : Summable f) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n := by
  rw [tsum_eq_zero_add hf]
  simp
  exact tsum_pnat_eq_tsum_succ f




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

theorem int_nat_sum {α : Type*} [AddCommGroup α] [UniformSpace α] [ IsUniformAddGroup α]  [CompleteSpace α]
  (f : ℤ → α) : Summable f → Summable fun x : ℕ => f x :=
  by
  have : IsCompl (Set.range (Int.ofNat : ℕ → ℤ)) (Set.range Int.negSucc) :=
    by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) _
      exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  intro h
  have H:= @summable_subtype_and_compl _ _ _ _ _ f _ (Set.range (Int.ofNat : ℕ → ℤ))
  simp at H
  rw [← H] at h
  cases' h with h_left h_right
  rw [← (Equiv.ofInjective (Int.ofNat : ℕ → ℤ) Nat.cast_injective).symm.summable_iff]
  apply Summable.congr h_left
  intro b
  simp
  apply congr_arg
  exact Eq.symm (Equiv.apply_ofInjective_symm Nat.cast_injective b)

def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := by apply Int.pred_succ
  right_inv := by apply Int.succ_pred

theorem HasSum.nonneg_add_neg {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) := by
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl


theorem HasSum.pos_add_zero_add_neg {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) := by
    intro g hg
    simpa using (hasSum_nat_add_iff _).mp hg
  (this (fun n => f n) hpos).nonneg_add_neg hneg


/-this is from the mod forms repo-/
theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α]  [ IsUniformAddGroup α] [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf2 : Summable f) :
  ∑' n, f n = f 0 + ∑' n : ℕ+, f n + ∑' m : ℕ+, f (-m) := by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw [←_root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply (int_nat_sum f hf2).subtype
      apply Summable.congr hs
      intro b; simp; congr; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
    congr
    norm_cast
    simp
  have hneg : HasSum (fun n : ℕ => f (-n.succ)) (∑' n : ℕ+, f (-n)) :=
    by
    rw [←_root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    rw [Summable.hasSum_iff _]
    congr
    funext
    simp
    congr
    simp_rw [PNat.natPred]
    simp
    ring
    rw [Equiv.summable_iff]
    have H : Summable fun d : ℤ => f d.pred :=
      by
      have := succEquiv.symm.summable_iff.2 hf2
      apply this
    have H2 := summable_neg _ H
    have := int_nat_sum _ H2
    apply Summable.congr this
    intro b
    simp
    congr
    simp_rw [Int.pred]
    ring
  have := (HasSum.pos_add_zero_add_neg hpos hneg).tsum_eq
  rw [this]
  ring_nf

theorem upp_half_not_ints (z : ℍ) (n : ℤ) : (z : ℂ) ≠ n :=
  by
  simp
  apply UpperHalfPlane.ne_int


lemma aus (a b : ℂ) : a + b ≠ 0 ↔ a ≠ -b := by
  refine Iff.ne ?_
  exact Iff.symm eq_neg_iff_add_eq_zero

lemma pnat_inv_sub_squares (z : ℍ) :
  (fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n)) = fun n : ℕ+ => 2 * z.1 * (1 / (z ^ 2 - n ^ 2)):=
  by
  funext n
  field_simp
  rw [one_div_add_one_div]
  norm_cast
  ring_nf
  have h2 := upp_half_not_ints z n
  simp [h2] at *
  have h1 := upp_half_not_ints z (n)
  norm_cast at *
  rw [sub_eq_zero]
  left
  rfl
  have h1 := upp_half_not_ints z (n)
  norm_cast at *
  rw [@sub_eq_zero]
  apply UpperHalfPlane.ne_int
  have := UpperHalfPlane.ne_int z (-(n : ℤ))
  rw [aus]
  aesop


lemma upper_half_plane_ne_int_pow_two (z : ℍ) (n : ℤ) : (z : ℂ) ^ 2 - n ^ 2 ≠ 0 := by
  intro h
  rw [sq_sub_sq, mul_eq_zero] at h
  cases h with
  | inr h =>
    have := upp_half_not_ints z n
    rw [sub_eq_zero] at h
    apply absurd h this
  | inl h =>
    have := upp_half_not_ints z (-n)
    rw [add_eq_zero_iff_eq_neg] at h
    simp only [Int.cast_neg, ne_eq] at *
    apply absurd h this

theorem upbnd (z : ℍ) (d : ℤ) : (d ^ 2 : ℝ) * r z ^ 2 ≤ ‖((z : ℂ) ^ 2 - d ^ 2)‖ := by
  by_cases hd : d ≠ 0
  have h1 : (z ^ 2 : ℂ) - d ^ 2 = d ^ 2 * (1 / d * z  - 1) * (1 / d * z + 1) := by ring_nf; simp [hd]
  rw [h1]
  simp
  rw [mul_assoc]
  gcongr
  rw [pow_two]
  gcongr
  apply (r_pos _).le
  · have h1 := auxbound2 z ((d : ℝ)⁻¹) (d := -1) (by norm_num)
    apply le_trans h1
    apply le_of_eq
    congr
    simp only [ofReal_inv, ofReal_intCast, ofReal_neg, ofReal_one]
    ring
  · have h1 := auxbound2 z ((d : ℝ)⁻¹) (d := 1) (by norm_num)
    apply le_trans h1
    apply le_of_eq
    congr
    simp only [ofReal_inv, ofReal_intCast, ofReal_neg, ofReal_one]
  · simp only [ne_eq, Decidable.not_not] at hd
    simp only [hd, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      sub_zero, norm_pow, norm_nonneg, pow_nonneg]



/- This is from the mod forms repo -/
theorem lhs_summable (z : ℍ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) := by
  have h1 := pnat_inv_sub_squares z
  rw [h1]
  apply Summable.mul_left
  apply summable_norm_iff.1
  simp
  have hs : Summable fun n : ℕ+ => (r z ^ 2 * n ^ 2)⁻¹ := by
    simp
    apply Summable.mul_right
    have hrr : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ 2)⁻¹ := by
      simp
    apply hrr.subtype
  apply Summable.of_nonneg_of_le _ _ hs
  · intro b
    rw [inv_nonneg]
    simp
  intro b
  rw [inv_le_inv₀]
  · rw [mul_comm]
    apply upbnd z
  · simp at *
    simpa using  (upper_half_plane_ne_int_pow_two z b)
  apply mul_pos
  · norm_cast
    apply pow_pos
    apply r_pos
  have hb := b.2
  norm_cast
  apply pow_pos
  simpa using hb


theorem sum_int_even {α : Type*} [UniformSpace α] [CommRing α]  [IsUniformAddGroup α] [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) :
    ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n := by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) :=
    by
    rw [← _root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp at *
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) :=
      by
      have hs : Summable fun n : ℕ+ => f n := by apply (int_nat_sum f hf2).subtype
      apply Summable.congr hs
      intro b; simp; congr; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
    congr
    norm_cast
    simp
  have hneg : HasSum (fun n : ℕ => f (-n.succ)) (∑' n : ℕ+, f n) :=
    by
    have h1 : (fun n : ℕ => f (-↑n.succ)) = fun n : ℕ => f ↑n.succ :=
      by
      funext
      apply hf
    rw [h1]
    convert hpos
  have := (HasSum.pos_add_zero_add_neg hpos hneg).tsum_eq
  rw [this]
  ring

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

lemma summable_hammerTime_nat  {α : Type} [NormedField α] [CompleteSpace α] (f : ℕ → α) (a : ℝ) (hab : 1 < a)
    (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) :
    Summable fun n => (f n)⁻¹ := by
  apply summable_of_isBigO _ hf
  have := Real.summable_nat_rpow_inv.mpr hab
  apply this.congr
  intro b
  simp


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

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) : (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite]
    fun n => ((|(n : ℝ)| ^ k)⁻¹)  := by
  simp_rw [← inv_pow]
  apply Asymptotics.IsBigO.pow
  apply linear_bigO m z


lemma Asymptotics.IsBigO.zify {α β: Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β} (hf : f =O[cofinite] g) :
    (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  rw [@isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  use C
  rw [Int.cofinite_eq] at hC
  rw [Nat.cofinite_eq_atTop]
  apply Filter.Eventually.natCast_atTop  (p := fun n => ‖f n‖ ≤ C * ‖g n‖)
  simp_all only [eventually_sup, eventually_atBot, eventually_atTop, ge_iff_le]


lemma Asymptotics.IsBigO.of_neg {α β: Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β}
    (hf : f =O[cofinite] g) : (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  apply Asymptotics.IsBigO.comp_tendsto hf
  refine Injective.tendsto_cofinite (Equiv.injective (Equiv.neg ℤ))


lemma linear_bigO_nat (m : ℤ) (z : ℍ) : (fun (n : ℕ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have := linear_bigO (m : ℤ) z
  apply this.zify


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



def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x => ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

def swap_equiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
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




theorem summable_1 (k : ℕ) (z : ℍ) (hk : 1 ≤ k) :
    Summable fun (b : ℕ) ↦ (((z : ℂ) - ↑↑b) ^ (k + 1))⁻¹ := by
  have := summable_hammerTime_nat (fun n : ℕ => (((z : ℂ) - n) ^ (k + 1))) (k+1)
      (by norm_cast; omega) ?_
  apply this
  norm_cast

  simp_rw [← inv_pow]
  have : (fun (n : ℕ) ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) = fun (n : ℕ) ↦ (↑(n : ℝ)⁻¹)  ^ (k + 1) := by
    simp
  conv =>
    enter [3]
    rw [this]
  apply Asymptotics.IsBigO.pow
  have hl := linear_bigO_nat (-1) z
  conv =>
    enter [2]
    intro x
    rw [sub_eq_add_neg]
  apply Asymptotics.IsBigO.of_abs_right
  simp only [Nat.cast_pow, inv_pow, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    Nat.abs_cast, Asymptotics.isBigO_abs_right] at *
  have hl2 := Asymptotics.IsBigO.neg_left hl
  apply hl2.congr_left
  intro n
  rw [@neg_inv]
  congr
  ring

theorem summable_2 (k : ℕ) (z : ℍ) (hk : 1 ≤ k) :
    Summable fun (b : ℕ) ↦ (((z : ℂ) + ↑↑b) ^ (k + 1))⁻¹ := by
  have := summable_hammerTime_nat (fun n : ℕ => (((z : ℂ) + n) ^ (k + 1))) (k+1)
      (by norm_cast; omega) ?_
  apply this
  norm_cast
  simp_rw [← inv_pow]
  have : (fun (n : ℕ) ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) = fun (n : ℕ) ↦ (↑(n : ℝ)⁻¹)  ^ (k + 1) := by simp
  conv =>
    enter [3]
    rw [this]
  apply Asymptotics.IsBigO.pow
  have hl := linear_bigO_nat 1 z
  apply Asymptotics.IsBigO.of_abs_right
  simp only [Nat.cast_pow, inv_pow, Int.cast_one, one_mul, Nat.abs_cast,
    Asymptotics.isBigO_abs_right] at *
  exact hl



theorem summable_3 (m : ℕ) (y : {z : ℂ | 0 < z.im}) :
    Summable fun n : ℕ+ =>
      (-1 : ℂ) ^ m * ↑m ! * (1 / (y - ↑n) ^ (m + 1)) + (-1) ^ m * ↑m ! * (1 / (y + ↑n) ^ (m + 1)) :=
  by
  by_cases hm : m = 0
  simp_rw [hm]
  simp
  have := lhs_summable y
  simpa using this
  have hm2 : 2 ≤ m + 1 := by
    have : 1 ≤ m := by
      apply Nat.one_le_iff_ne_zero.mpr hm;
    linarith
  simp_rw [← mul_add]
  rw [summable_mul_left_iff]
  apply Summable.add
  have h0 := summable_1 m y (by linarith)
  simp at *
  apply h0.subtype
  have h1 := summable_2 m y (by linarith)
  simp at *
  apply h1.subtype
  simp [Nat.factorial_ne_zero]

abbrev ℍ' := {z : ℂ | 0 < z.im}

theorem summable_iter_derv' (k : ℕ) (y : ℍ') :
    Summable fun n : ℕ => (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * y) :=
  by
  apply Summable.of_norm
  simp only [mem_setOf_eq, Complex.norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
    norm_I, mul_one]
  simp_rw [mul_pow, mul_assoc]
  apply Summable.mul_left
  apply Summable.mul_left
  conv =>
    enter [1]
    ext n
    rw [← norm_pow]
    rw [← norm_mul]
    rw [show cexp (2 * (↑π * (Complex.I * (↑n * ↑y)))) = cexp (2 * (↑π * (Complex.I * (↑y)))) ^ n by
      rw [← Complex.exp_nsmul]
      congr
      ring]
  apply summable_norm_pow_mul_geometric_of_norm_lt_one
  have := exp_upperHalfPlane_lt_one y
  simp at *
  simp_rw [← mul_assoc] at *
  exact this



def mapdiv (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ :=
  by
  intro x
  have h11 := Nat.fst_mem_divisors_of_mem_antidiagonal x.2
  have h111 := Nat.pos_of_mem_divisors h11
  have h22 := Nat.snd_mem_divisors_of_mem_antidiagonal x.2
  have h222 := Nat.pos_of_mem_divisors h22
  set n1 : ℕ+ := ⟨x.1.1, h111⟩
  set n2 : ℕ+ := ⟨x.1.2, h222⟩
  use n1
  use n2
  exact h222

def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+
    where
  toFun x := mapdiv x.1 x.2
  invFun x :=
    ⟨⟨x.1.1 * x.2.1, by apply mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by
      rw [Nat.mem_divisorsAntidiagonal]; simp; constructor; rfl; constructor;
        linarith [x.1.2]; linarith [x.2.2] ⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    simp_rw [mapdiv]
    simp only [h, PNat.mk_coe, eq_self_iff_true, Subtype.coe_eta]
    ext
    simp at *
    simp_rw [h]
    norm_cast
    simp only
    simp only
  right_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    simp_rw [mapdiv]
    exfalso

    simp at *
    simp_rw [mapdiv]
    simp [eq_self_iff_true, Subtype.coe_eta]
    norm_cast

theorem sigma_eq_sum_div' (k n : ℕ) : sigma k n = ∑ d ∈ Nat.divisors n, (n / d) ^ k :=
  by
  simp [sigma]
  rw [← Nat.sum_div_divisors]


theorem a33 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c) := by
  apply Summable.of_norm
  conv =>
    enter [1]
    ext a
    rw [show cexp (2 * ↑π * Complex.I * ↑e * z * ↑a) = cexp (2 * ↑π * Complex.I * (↑e)* z) ^ (a : ℕ) by
      rw [← Complex.exp_nsmul]
      congr
      ring]
  have := summable_norm_pow_mul_geometric_of_norm_lt_one
    (r := cexp (2 * ↑π * Complex.I * (↑e)* z)) k ?_
  apply this.subtype
  simp [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

lemma hsum (k : ℕ) (z : ℍ) : Summable fun b : ℕ+ => ∑ _ ∈ (b : ℕ).divisors, b ^ k *
    ‖exp (2 * ↑π * Complex.I * ↑z * b)‖  := by
    simp
    have hs := summable_norm_iff.mpr (a33 (k+1) 1 z)
    apply Summable.of_nonneg_of_le _ _ hs
    simp only [Nat.cast_pos, Finset.card_pos, Nat.nonempty_divisors, ne_eq, PNat.ne_zero,
      not_false_eq_true, mul_nonneg_iff_of_pos_left, PNat.pos, pow_pos, norm_nonneg, implies_true]
    intro b
    simp only [PNat.val_ofNat, Nat.cast_one, mul_one, Complex.norm_mul, norm_pow, norm_natCast]
    rw [← mul_assoc]
    gcongr
    rw [pow_add, mul_comm]
    gcongr
    simpa using Nat.card_divisors_le_self (b : ℕ)

theorem summable_auxil_1 (k : ℕ) (z : ℍ) :
  Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦
  ↑(↑(c.snd) : ℕ × ℕ).1 ^ k *
    cexp (2 * ↑π * Complex.I * ↑z * ↑(↑(c.snd) : ℕ × ℕ).1 * ↑↑(↑(c.snd) : ℕ × ℕ).2) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg]
  constructor
  apply fun n => (hasSum_fintype _).summable
  simp
  simp_rw [tsum_fintype]
  have H (n : ℕ+) := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
    (x.1 : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x.1 * x.2)‖)
  have H2 (n : ℕ+) := Nat.sum_divisorsAntidiagonal ((fun (x : ℕ) => fun (y : ℕ) =>
    (x : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x * y)‖)) (n := n)
  conv =>
    enter [1]
    ext b
    simp
    rw [H b]
    rw [H2 b]
  have hsum := hsum k z
  apply Summable.of_nonneg_of_le _ _ hsum
  · intro b
    apply Finset.sum_nonneg
    intro i hi
    simp
  · intro b
    apply Finset.sum_le_sum
    intro i hi
    simp at hi
    gcongr
    apply Nat.le_of_dvd b.2 hi
    apply le_of_eq
    have hni : (i : ℂ) * (b / i : ℕ)  = b := by
      norm_cast
      simp at *
      exact Nat.mul_div_cancel' hi
    rw [mul_assoc, hni]
  · intro i
    simp







lemma sum_range_zero (f : ℤ → ℂ) (n : ℕ) : ∑ m ∈ Finset.range (n+1), f m = f 0 +
  ∑ m ∈ Finset.range n, f (m+1) := by
  rw [Finset.sum_range_succ' ]
  rw [add_comm]
  simp


theorem upper_ne_int (x : ℍ) (d : ℤ) : (x : ℂ) + d ≠ 0 :=
  by
  by_contra h
  rw [add_eq_zero_iff_eq_neg] at h
  have h1 : 0 < (x : ℂ).im := by simp [x.2]; exact im_pos x
  rw [h] at h1
  simp at h1

theorem aut_iter_deriv (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero, pow_zero, Nat.factorial_zero, algebraMap.coe_one, pow_one,
    one_mul]
  simp  at *
  rw [iteratedDerivWithin_succ]
  simp only [one_div, Opens.coe_mk, Nat.cast_succ, Nat.factorial, Nat.cast_mul]
  have := (IH hx)
  have H : derivWithin (fun (z : ℂ) => (-1: ℂ) ^ k * ↑k ! * ((z + ↑d) ^ (k + 1))⁻¹) {z : ℂ | 0 < z.im} x =
   (-1) ^ (↑k + 1) * ((↑k + 1) * ↑k !) * ((x + ↑d) ^ (↑k + 1 + 1))⁻¹ := by
    rw [DifferentiableAt.derivWithin]
    · simp only [deriv_const_mul_field']
      rw [deriv_inv'', deriv_pow'', deriv_add_const', deriv_id'']
      simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, mul_one, ← pow_mul]
      rw [pow_add]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_negSucc, zero_add, Nat.cast_one,
        Int.cast_ofNat, Nat.cast_add,pow_one, Nat.cast_mul, mul_neg, mul_one, Int.cast_add,
          Int.cast_one, neg_mul]
      have Hw : -(((k: ℂ) + 1) * (x + ↑d) ^ k) / (x + ↑d) ^ ((k + 1) * 2) = -(↑k + 1) / (x + ↑d) ^ (k + 2) :=
        by
        rw [div_eq_div_iff]
        norm_cast
        simp
        ring
        norm_cast
        apply pow_ne_zero ((k + 1) * 2) (upper_ne_int ⟨x, hx⟩ d)
        norm_cast
        apply pow_ne_zero (k + 2) (upper_ne_int ⟨x, hx⟩ d)

      simp at *
      rw [Hw]
      ring
      fun_prop
      fun_prop
      norm_cast
      apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
    · apply DifferentiableAt.mul
      · fun_prop
      · apply DifferentiableAt.inv
        fun_prop
        apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
    · apply IsOpen.uniqueDiffWithinAt _ hx
      refine isOpen_lt ?_ ?_
      · fun_prop
      · fun_prop
  rw [←H]
  apply derivWithin_congr
  norm_cast at *
  simp at *
  intro r hr
  apply IH hr
  norm_cast at *
  simp at *
  apply this

theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply HasDerivWithinAt.derivWithin
  apply HasDerivAt.hasDerivWithinAt
  have A :
    ∀ x : ℂ,
      x ∈ s →
        Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
          (𝓝 (∑' n : α, (fun z => f n z) x)) :=
    by
    intro y hy
    apply Summable.hasSum
    simp
    apply hf y hy
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK1 hK2
  have HU := hu K hK1 hK2
  obtain ⟨u, hu1, hu2⟩ := HU
  apply tendstoUniformlyOn_tsum hu1
  intro n x hx
  apply hu2 n ⟨x, hx⟩
  filter_upwards
  intro t r hr
  apply HasDerivAt.sum
  intro q hq
  apply HasDerivWithinAt.hasDerivAt
  apply DifferentiableWithinAt.hasDerivWithinAt
  apply (hf2 q ⟨r, hr⟩).differentiableWithinAt
  exact IsOpen.mem_nhds hs hr
  apply IsOpen.uniqueDiffWithinAt hs hx

theorem aut_iter_deriv' (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) {z : ℂ | 0 < z.im} :=
  by
  intro x hx
  have h1 : (fun z : ℂ => 1 / (z - d)) = fun z : ℂ => 1 / (z + -d) := by rfl
  rw [h1]
  have h2 : x - d = x + -d := by rfl
  simp_rw [h2]
  simpa using aut_iter_deriv (-d : ℤ) k hx

  theorem aut_contDiffOn (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d))
    {z : ℂ | 0 < z.im} := by
  simp only [one_div, Opens.coe_mk]
  apply ContDiffOn.inv
  apply ContDiffOn.sub
  apply contDiffOn_id
  apply contDiffOn_const
  intro x hx
  have := upper_ne_int ⟨x, hx⟩ (-d)
  norm_cast at *
  simp at *
  rw [add_neg_eq_zero] at this
  rw [sub_eq_zero]
  convert this

theorem iter_div_aut_add (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) {z : ℂ | 0 < z.im})
      ((fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  have h1 :
    (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) =
      (fun z : ℂ => 1 / (z - d)) + fun z : ℂ => 1 / (z + d) :=
    by rfl
  rw [h1]
  simp only [Opens.coe_mk, one_div, Pi.add_apply] at *
  rw [iteratedDerivWithin_add hx ?_]
  · have h2 := aut_iter_deriv d k hx
    have h3 := aut_iter_deriv' d k hx
    simp at *
    rw [h2, h3]
  · have h4 := aut_contDiffOn d k
    simp at h4
    apply h4
    exact hx
  · have h5 := aut_contDiffOn (-d) k
    simp at h5
    apply h5
    exact hx
  · refine IsOpen.uniqueDiffOn ?_
    refine isOpen_lt ?_ ?_
    · fun_prop
    · fun_prop

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜)


theorem iteratedDerivWithin_of_isOpen (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  unfold iteratedDerivWithin iteratedDeriv
  intro x hx
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := 𝕜) (F := F) (E := 𝕜) (f := f) n hs hx]



theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * m * s)) {z : ℂ | 0 < z.im})
      (fun t => (2 * ↑π * Complex.I * m) ^ n * Complex.exp (2 * ↑π * Complex.I * m * t)) {z : ℂ | 0 < z.im} :=
  by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen _ _ _ ?_)
  rw [EqOn]
  intro x _
  apply congr_fun (iteratedDeriv_cexp_const_mul ..)
  refine isOpen_lt ?_ ?_
  · fun_prop
  · fun_prop



noncomputable def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)


theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
  DifferentiableAt ℂ
    (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r :=
  by
  have hh :
    DifferentiableOn ℂ (fun t => (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * t)) ℍ' := by
    apply Differentiable.differentiableOn;
    apply Differentiable.const_mul
    apply Differentiable.cexp
    apply Differentiable.const_mul
    apply differentiable_id
  apply DifferentiableOn.differentiableAt
  apply DifferentiableOn.congr hh
  intro x hx
  apply exp_iter_deriv_within k n hx
  refine IsOpen.mem_nhds ?_ ?_
  · apply isOpen_lt (by fun_prop) (by fun_prop)
  exact r.2


lemma upper_half_plane_isOpen :
    IsOpen ℍ' := by
  apply isOpen_lt (by fun_prop) (by fun_prop)


theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ'
        ↑r :=
  by
  simp
  apply symm
  apply DifferentiableAt.derivWithin
  apply der_iter_eq_der_aux2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply r.2

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' ↑r =
      iteratedDerivWithin (k + 1) (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r :=
  by
  rw [iteratedDerivWithin_succ]

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
        ‖(derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' r)‖ ≤
            u n := by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]
    rw [isCompact_iff_isCompact_univ] at hK2
    apply hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ :=
    by
    have : ∀ (n : ℕ), ((2 * ↑π)^(k+1))* ‖((n) ^ (k + 1) * (r ^ n))‖ =
      ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ := by
        intro n
        norm_cast
        simp [BoundedContinuousFunction.norm_mkOfCompact, Nat.cast_pow, map_pow,
          abs_norm, map_mul, mul_eq_mul_right_iff]
        norm_cast
        simp only [Nat.cast_pow]
        have hh : |π| = π := by simp [Real.pi_pos.le]
        rw [hh]
        ring
    apply Summable.congr _ this
    rw [summable_mul_left_iff]
    apply summable_norm_pow_mul_geometric_of_norm_lt_one
    convert hr
    rw [norm_norm]
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    linarith
    apply Real.pi_ne_zero
  refine' ⟨fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖, hu, _⟩
  intro n t
  have go := der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩
  simp at *
  simp_rw [go]
  have h1 := exp_iter_deriv_within (k + 1) n (hK1 t.2)
  norm_cast at *
  simp at *
  rw [h1]
  simp
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
        ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
          norm_cast
          rw [← Complex.norm_pow];
          congr;
          rw [← exp_nat_mul];
          ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    rw [norm_norm]
    simpa using this
  apply mul_le_mul
  simp
  simp at ineqe
  convert ineqe
  positivity
  positivity



theorem exp_series_ite_deriv_uexp2 (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im} x =
      ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) {z : ℂ | 0 < z.im}  x :=
  by
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero]
  rw [iteratedDerivWithin_succ]
  have HH :
    derivWithin (iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im}
        x =
      derivWithin
        (fun z =>
          ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) {z : ℂ | 0 < z.im} z)
        {z : ℂ | 0 < z.im} x :=
    by
    apply derivWithin_congr
    intro y hy
    apply IH ⟨y, hy⟩
    apply IH x
  simp_rw [HH]
  rw [derivWithin_tsum_fun']
  apply tsum_congr
  intro b
  rw [iteratedDerivWithin_succ]
  refine isOpen_lt ?_ ?_
  · fun_prop
  · fun_prop
  · exact x.2
  · intro y hy
    apply Summable.congr (summable_iter_derv' k ⟨y, hy⟩)
    intro b
    apply symm
    apply exp_iter_deriv_within k b hy
  intro K hK1 hK2
  let K2 := Set.image (Set.inclusion hK1) univ
  have hKK2 : IsCompact (Set.image (inclusion hK1) univ) := by
    apply IsCompact.image_of_continuousOn
    · exact isCompact_iff_isCompact_univ.mp hK2
    · exact continuous_inclusion hK1 |>.continuousOn
  apply iter_deriv_comp_bound2 K hK1 hK2 k
  apply der_iter_eq_der_aux2

theorem exp_series_ite_deriv_uexp'' (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im} x =
      ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * x) :=
  by
  rw [exp_series_ite_deriv_uexp2 k x]
  apply tsum_congr
  intro b
  apply exp_iter_deriv_within k b x.2

theorem exp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) ℍ')
      (fun x : ℂ => ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * x)) ℍ' :=
  by
  intro x hx
  apply exp_series_ite_deriv_uexp'' k ⟨x, hx⟩

theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x :=
  by
  have A :
    ∀ x : ℂ,
      x ∈ s →
        Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
          (𝓝 (∑' n : α, (fun z => f n z) x)) :=
    by
    intro y hy
    apply Summable.hasSum
    simp
    apply hf y hy
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK1 hK2
  have HU := hu K hK1 hK2
  obtain ⟨u, hu1, hu2⟩ := HU
  apply tendstoUniformlyOn_tsum hu1
  intro n x hx
  apply hu2 n ⟨x, hx⟩
  filter_upwards
  intro t r hr
  apply HasDerivAt.sum
  intro q hq
  apply HasDerivWithinAt.hasDerivAt
  apply DifferentiableWithinAt.hasDerivWithinAt
  apply (hf2 q ⟨r, hr⟩).differentiableWithinAt
  exact IsOpen.mem_nhds hs hr


theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x := by
  apply (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt




theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n :=
  by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff]
    rw [isCompact_iff_isCompact_univ] at hK2
    apply hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K )‖ < 1 :=
    by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk]
    apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩; linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖ :=
    by
    have : ∀ (n : ℕ), ((2 * ↑π)^(k))* ‖((n) ^ (k) * (r ^ n))‖ =
      ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖ := by
        intro n
        norm_cast
        simp [BoundedContinuousFunction.norm_mkOfCompact, Nat.cast_pow, map_pow,
          abs_norm, map_mul, mul_eq_mul_right_iff]
        norm_cast
        simp only [Nat.cast_pow]
        have hh : |π| = π := by simp [Real.pi_pos.le]
        rw [hh]
        ring
    apply Summable.congr _ this
    rw [summable_mul_left_iff]
    apply summable_norm_pow_mul_geometric_of_norm_lt_one
    convert hr
    rw [norm_norm]
    norm_cast
    apply pow_ne_zero
    apply mul_ne_zero
    linarith
    apply Real.pi_ne_zero
  refine' ⟨fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖, hu, _⟩
  intro n t
  simp
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n :=
    by
    have hw1 :
      ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
        ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
          norm_cast
          rw [← Complex.norm_pow];
          congr;
          rw [← exp_nat_mul];
          ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    rw [norm_norm]
    simpa using this
  apply mul_le_mul
  simp
  simp at ineqe
  convert ineqe
  positivity
  positivity

theorem tsum_uexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) ℍ' :=
  by
  apply contDiffOn_of_differentiableOn_deriv
  intro m _
  apply DifferentiableOn.congr _ (exp_series_ite_deriv_uexp''' m)
  intro x hx
  apply HasDerivWithinAt.differentiableWithinAt
  apply hasDerivWithinAt_tsum_fun _ upper_half_plane_isOpen
  apply hx
  intro y hy
  apply summable_iter_derv' m ⟨y, hy⟩
  intro K hK1 hK2
  have := iter_deriv_comp_bound3 K hK1 hK2 (m + 1)
  obtain ⟨u, hu, hu2⟩ := this
  refine' ⟨u, hu, _⟩
  intro n r
  have HU2 := hu2 n r
  simp
  apply le_trans _ HU2
  apply le_of_eq
  norm_cast
  simp
  rw [derivWithin_mul]
  rw [derivWithin_cexp ]
  rw [derivWithin_const_mul]
  simp
  have hr : derivWithin (fun y ↦ y) ℍ' ↑r = 1 := by
    apply derivWithin_id
    apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
    aesop
  rw [hr]
  simp
  ring
  fun_prop
  fun_prop
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  aesop
  fun_prop
  fun_prop
  intro n r
  fun_prop

theorem iter_der_within_add (k : ℕ+) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k
        (fun z => ↑π * Complex.I - (2 * ↑π * Complex.I) •
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im} x =
      -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) *
      Complex.exp (2 * ↑π * Complex.I * n * x) := by
  rw [iteratedDerivWithin_const_sub (PNat.pos k) ]
  simp
  rw [iteratedDerivWithin_neg' ]
  rw [iteratedDerivWithin_const_mul]
  congr
  have :=  exp_series_ite_deriv_uexp2 k x
  rw [this]
  apply tsum_congr
  intro b
  have := exp_iter_deriv_within k b x.2
  simpa using this
  exact x.2
  refine IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply tsum_uexp_contDiffOn k
  exact x.2

theorem iter_exp_eqOn (k : ℕ+) :
    EqOn
      (iteratedDerivWithin k
        (fun z => ↑π * Complex.I - (2 * ↑π * Complex.I) • ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im})
      (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * x))
      {z : ℂ | 0 < z.im} :=
  by
  intro z hz
  apply iter_der_within_add k ⟨z, hz⟩

theorem summable_iter_aut (k : ℕ) (z : ℍ) :
    Summable fun n : ℕ+ => iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n))
      {z : ℂ | 0 < z.im} z :=
  by
  have := fun d : ℕ+ => iter_div_aut_add d k z.2
  simp only [Int.cast_natCast, one_div, Pi.add_apply] at *
  have ht := (summable_congr this).2 ?_
  norm_cast at *
  by_cases hk : 1 ≤ k
  conv =>
    enter [1]
    ext b
    rw [← mul_add]
  rw [summable_mul_left_iff]
  apply Summable.add
  · apply (summable_1 k z hk).subtype
  · apply (summable_2 k z hk).subtype
  simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
    Nat.cast_eq_zero, false_or]
  exact Nat.factorial_ne_zero k
  simp only [not_le, Nat.lt_one_iff] at hk
  simp_rw [hk]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one, one_mul]
  simpa using lhs_summable z




lemma sub_bound (s : {z : ℂ | 0 < z.im}) (A B : ℝ) (hB : 0 < B) (hs : s ∈ verticalStrip A B) (k : ℕ)
    (n : ℕ+) :
    ‖((-1 : ℂ) ^ (k + 1) * (k + 1)! * (1 / (s - n) ^ (k + 2)))‖ ≤
    ‖((k + 1)! / r ⟨⟨A, B⟩, by simp [hB]⟩ ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹‖ := by
  simp
  rw [div_eq_mul_inv]
  rw [mul_assoc]
  gcongr
  have := summand_bound_of_mem_verticalStrip (k := (k + 2)) (by norm_cast; omega) ![1,-n] hB hs
  simp at *
  simp_rw [← zpow_natCast, ← zpow_neg]
  convert this
  rw [Int.natCast_add]
  simp [sub_eq_add_neg]
  norm_cast
  simp
  norm_cast
  congr
  rw [@abs_eq_self]
  apply (EisensteinSeries.r_pos _).le
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  norm_cast
  congr
  simp
  exact n.2


lemma add_bound (s : {z : ℂ | 0 < z.im}) (A B : ℝ) (hB : 0 < B) (hs : s ∈ verticalStrip A B) (k : ℕ)
    (n : ℕ+) :
    ‖((-1 : ℂ) ^ (k + 1) * (k + 1)! * (1 / (s + n) ^ (k + 2)))‖ ≤
    ‖((k + 1)! / r ⟨⟨A, B⟩, by simp [hB]⟩ ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹‖ := by
  simp
  rw [div_eq_mul_inv]
  rw [mul_assoc]
  gcongr
  have := summand_bound_of_mem_verticalStrip (k := (k + 2)) (by norm_cast; omega) ![1,n] hB hs
  simp at *
  simp_rw [← zpow_natCast, ← zpow_neg]
  convert this
  rw [Int.natCast_add]
  simp
  norm_cast
  rw [Int.natCast_add]
  simp
  norm_cast
  congr
  rw [@abs_eq_self]
  apply (EisensteinSeries.r_pos _).le
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  norm_cast
  congr
  simp
  exact n.2

theorem aut_bound_on_comp (K : Set {z : ℂ | 0 < z.im}) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
        ‖(derivWithin (fun z : ℂ =>
        iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) {z : ℂ | 0 < z.im} z)
        {z : ℂ | 0 < z.im} s)‖ ≤
            u n := by
  by_cases h1 : Set.Nonempty K
  have H := UpperHalfPlane.subset_verticalStrip_of_isCompact hk2
  obtain ⟨A, B, hB, hAB⟩ := H
  let zAB : ℍ := ⟨⟨A, B⟩, by simp [hB]⟩
  refine ⟨fun a : ℕ+ => 2 * ‖((k + 1)! / r (zAB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹‖,
      ?_, ?_⟩
  conv =>
    enter [1]
    ext a
    rw [norm_mul]
    rw [← mul_assoc]
  apply Summable.mul_left
  simp
  have : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ ((k : ℤ) + 2))⁻¹ := by
    have := (Real.summable_nat_rpow_inv (p := k + 2)).mpr (by linarith)
    apply this.congr
    intro n
    norm_cast
  apply this.subtype
  intro n s
  rw [← iteratedDerivWithin_succ]
  let S : ℂ := s
  have hS : S ∈ {z : ℂ | 0 < z.im} := by
    aesop
  have HT := iter_div_aut_add n (k+1) hS
  simp only [Int.cast_natCast, one_div, Pi.add_apply] at HT
  rw [HT]
  apply le_trans (norm_add_le _ _)
  simp_rw [mul_assoc]
  rw [two_mul]
  apply add_le_add
  have := sub_bound ⟨S, hS⟩ A B hB (by aesop) k n
  simpa using this
  have := add_bound ⟨S, hS⟩ A B hB (by aesop) k n
  simpa using this
  refine' ⟨fun _ => 0, _, _⟩
  apply summable_zero
  intro n
  rw [not_nonempty_iff_eq_empty] at h1
  intro r
  exfalso
  have hr := r.2
  simp_rw [h1] at hr
  simp at hr

theorem diff_on_aux (k : ℕ) (n : ℕ+) :
    DifferentiableOn ℂ
      ((fun t : ℂ => (-1 : ℂ) ^ k * k ! * (1 / (t - n) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + n) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.add
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.div
  apply differentiableOn_const
  norm_cast
  apply DifferentiableOn.pow
  fun_prop
  intro x hx
  norm_cast
  apply pow_ne_zero
  have := upper_ne_int ⟨x, hx⟩ (-n : ℤ)
  simp at *
  exact this
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.div
  apply differentiableOn_const
  norm_cast
  apply DifferentiableOn.pow
  fun_prop
  intro x hx
  have := upper_ne_int ⟨x, hx⟩ (n : ℤ)
  simp at *
  exact this

theorem diff_at_aux (s : {z : ℂ | 0 < z.im} ) (k : ℕ) (n : ℕ+) :
    DifferentiableAt ℂ
      (fun z : ℂ => iteratedDerivWithin k (fun z : ℂ => (z - ↑n)⁻¹ + (z + ↑n)⁻¹) {z : ℂ | 0 < z.im} z)
      ↑s := by
  have := iter_div_aut_add n k
  apply DifferentiableOn.differentiableAt
  apply DifferentiableOn.congr (diff_on_aux k n)
  intro r hr
  have ht := this hr
  simp at *
  apply ht
  apply IsOpen.mem_nhds
  refine isOpen_lt ?_ ?_
  · fun_prop
  · fun_prop
  · simp

theorem aut_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ) :
    iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} x =
      ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im} x :=
  by
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero]
  rw [iteratedDerivWithin_succ]
  have HH :
    derivWithin (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} ) {z : ℂ | 0 < z.im}
        x =
      derivWithin
        (fun z => ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im}  z) {z : ℂ | 0 < z.im}
        x :=
    by
    apply derivWithin_congr
    intro y hy
    apply IH ⟨y, hy⟩
    apply IH x
  simp_rw [HH]
  simp
  rw [derivWithin_tsum_fun']
  apply tsum_congr
  intro b
  rw [iteratedDerivWithin_succ]
  refine isOpen_lt ?_ ?_
  · fun_prop
  · fun_prop
  · simpa using x.2
  intro y hy
  simpa using summable_iter_aut k ⟨y, hy⟩
  intro K hK hK2
  let K2 := Set.image (Set.inclusion hK) univ
  have hKK2 : IsCompact (Set.image (inclusion hK) univ) := by
    apply IsCompact.image_of_continuousOn
    · exact isCompact_iff_isCompact_univ.mp hK2
    · exact continuous_inclusion hK |>.continuousOn
  have := aut_bound_on_comp K2 hKK2 k
  obtain ⟨u, hu1, hu2⟩ := this
  refine ⟨u, hu1, ?_⟩
  intro n s
  have := hu2 n ⟨⟨s, by aesop⟩, by aesop⟩
  apply this
  intro n r
  apply diff_at_aux

theorem tsum_ider_der_eq (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im} x =
      ∑' n : ℕ+,
        ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))) :=
  by
  apply tsum_congr
  intro b
  have h2 := iter_div_aut_add b k x.2
  simpa using h2



theorem auxp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im})
      (fun x : ℂ =>
        ∑' n : ℕ+,
          ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))))
      {z : ℂ | 0 < z.im} := by
  intro x hx
  have := aut_series_ite_deriv_uexp2 k ⟨x, hx⟩
  simp at *
  rw [this]
  have h2 := tsum_ider_der_eq k ⟨x, hx⟩
  simpa using h2



theorem tsum_aexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm
  have h1 := auxp_series_ite_deriv_uexp''' m
  apply DifferentiableOn.congr _ h1
  intro x hx

  apply HasDerivWithinAt.differentiableWithinAt

  apply hasDerivWithinAt_tsum_fun _ (by refine isOpen_lt (by fun_prop) (by fun_prop))
  apply hx
  intro y hy
  apply summable_3 m ⟨y, hy⟩
  intro K hK1 hK2
  let K2 := Set.image (Set.inclusion hK1) univ
  have hKK2 : IsCompact (Set.image (inclusion hK1) univ) := by
    apply IsCompact.image_of_continuousOn
    · exact isCompact_iff_isCompact_univ.mp hK2
    · exact continuous_inclusion hK1 |>.continuousOn
  have := aut_bound_on_comp K2 hKK2 m
  obtain ⟨u, hu1, hu2⟩ := this
  refine ⟨u, hu1, ?_⟩
  intro n s
  have := hu2 n ⟨⟨s, by aesop⟩, by aesop⟩

  apply le_trans _ this
  apply le_of_eq
  congr 1
  apply derivWithin_congr
  have h21 := (iter_div_aut_add n m).symm
  simp at *
  intro v hv
  have h22 := h21 hv
  simp at *
  rw [← h22]
  have hss : s.1 ∈ {z : ℂ | 0 < z.im} := by
    aesop
  have h21 := (iter_div_aut_add n m).symm hss
  simpa using h21
  intro n r
  have:= (diff_on_aux m n)
  have hN : {z : ℂ | 0 < z.im} ∈ 𝓝 r.1 := by
    refine IsOpen.mem_nhds ?_ ?_
    apply isOpen_lt (by fun_prop) (by fun_prop)
    apply r.2
  apply DifferentiableOn.differentiableAt _ hN
  simp at *
  apply this


theorem aux_iter_der_tsum (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
    iteratedDerivWithin k
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ (k + 1 : ℕ) := by
  rw [iteratedDerivWithin_add ?_ ?_]
  · have h1 := aut_iter_deriv 0 k x.2
    simp [UpperHalfPlane.coe] at *
    rw [h1]

    have := aut_series_ite_deriv_uexp2 k x
    simp [UpperHalfPlane.coe] at *
    rw [this]
    have h2 := tsum_ider_der_eq k x
    simp at h2
    rw [h2]
    rw [int_tsum_pNat]
    · simp
      rw [tsum_add]
      · rw [tsum_mul_left]
        rw [tsum_mul_left]
        rw [mul_add]
        rw [mul_add]
        conv =>
          enter [2]
          rw [add_assoc]
          conv =>
            enter [2]
            rw [add_comm]
        ring_nf
      rw [summable_mul_left_iff]
      · apply (summable_1 k x hk).subtype
      · simp
        exact Nat.factorial_ne_zero k
      · rw [summable_mul_left_iff]
        · apply (summable_2 k x hk).subtype
        · simp
          exact Nat.factorial_ne_zero k
    · rw [summable_int_iff_summable_nat_and_neg ]
      refine ⟨?_, ?_⟩
      apply (summable_2 k x hk)
      apply (summable_1 k x hk).congr
      intro n
      congr
      simp
      rfl
  · have := (aut_contDiffOn 0 k)
    simp at *
    apply this.contDiffWithinAt
    exact x.2
  · apply tsum_aexp_contDiffOn k
    exact x.2
  · exact x.2
  · refine IsOpen.uniqueDiffOn ?_
    refine isOpen_lt ?_ ?_
    · fun_prop
    · fun_prop

theorem aux_iter_der_tsum_eqOn (k : ℕ) (hk : 2 ≤ k) :
    EqOn
      (iteratedDerivWithin (k - 1)
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im})
      (fun z : ℂ => (-1) ^ (k - 1) * (k - 1)! * ∑' n : ℤ, 1 / (z + n) ^ (k : ℕ)) {z : ℂ | 0 < z.im} :=
  by
  intro z hz
  have hk0 : 1 ≤ k - 1 := le_tsub_of_add_le_left hk
  have := aux_iter_der_tsum (k - 1) hk0 ⟨z, hz⟩
  have hk1 : k - 1 + 1 = k := by
    apply Nat.sub_add_cancel
    linarith
  rw [hk1] at this
  norm_cast at *


theorem pos_sum_eq (k : ℕ) (hk : 0 < k) :
    (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * x)) =
      fun x : ℂ =>
      -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * x) := by
  ext1 x
  simp
  left
  apply symm
  have := tsum_pNat fun n : ℕ => (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * x)
  simp at this
  apply this
  linarith

theorem cot_series_repr (z : ℍ) :
    ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  have := cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement z)
  simp at *
  have hrw := tsum_pnat_eq_tsum_succ3 fun n : ℕ => (1 / ((z : ℂ) - n) + 1 / (z + n))
  simp at hrw
  rw [hrw]
  apply this


lemma EisensteinSeries_Identity (z : ℍ) :
    1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n := by
  have h1 := cot_series_repr z
  rw [pi_mul_cot_pi_q_exp z ] at h1
  rw [← h1]
  ring


theorem q_exp_iden'' (k : ℕ) (hk : 2 ≤ k) :
    EqOn (fun z : ℂ => (-1 : ℂ) ^ (k - 1) * (k - 1)! * ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k)
      (fun z : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ ((k - 1) : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * z))
      {z : ℂ | 0 < z.im} :=
  by
  have := (aux_iter_der_tsum_eqOn k hk).symm
  apply EqOn.trans this
  have hkpos : 0 < k - 1 := by
    apply Nat.sub_pos_of_lt
    linarith
  have h2 := (iter_exp_eqOn (⟨k - 1, hkpos⟩ : ℕ+)).symm
  simp  [one_div,  Subtype.coe_mk, neg_mul, Algebra.id.smul_eq_mul] at *
  have h3 := pos_sum_eq (k - 1) hkpos
  simp at h3
  rw [h3] at h2
  apply EqOn.symm
  apply EqOn.trans h2
  apply iteratedDerivWithin_congr
  intro z hz
  simp
  have := EisensteinSeries_Identity ⟨z, hz⟩
  simp at *
  rw [this]
  congr
  ext n
  rw [← Complex.exp_nsmul]
  congr
  ring

theorem q_exp_iden (k : ℕ) (hk : 2 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * Complex.I) ^ k / (k - 1)! * ∑' n : ℕ+, n ^ ((k - 1) ) * Complex.exp (2 * ↑π * Complex.I * z * n) :=
  by
  have := q_exp_iden'' k hk z.2
  have hkk : 1 ≤ (k: ℤ) := by linarith
  simp [one_div, neg_mul] at *
  have hk2 : (-1 : ℂ) ^ ((k - 1) ) * (k - 1)! ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
      Nat.cast_eq_zero, Nat.factorial_ne_zero, or_self, not_false_eq_true]
  rw [← mul_right_inj' hk2]
  simp only [UpperHalfPlane.coe]
  rw [this]
  have h3 : (-1) ^ ((k - 1) ) * ↑(k - 1)! * ((-(2 * ↑π * Complex.I)) ^ k / ↑(k - 1)!) = -(2 * ↑π * Complex.I) ^ k :=
    by
    rw [mul_div]; rw [div_eq_mul_one_div]; rw [div_eq_inv_mul]; simp_rw [← mul_assoc];
    simp
    have hj :  (-1) ^ (↑k - 1) * ↑(k - 1)! * (-(2 * ↑π * Complex.I)) ^ (k : ℕ) * (↑(k - 1)! : ℂ)⁻¹ =
       (-1) ^ (↑k - 1) * (-(2 * ↑π * Complex.I)) ^ (k : ℕ) * (↑(k - 1)!  * (↑(k - 1)!)⁻¹) := by ring
    rw [hj]
    have h2 : (↑(k - 1)! : ℂ) * (↑(k - 1)!)⁻¹ = 1 := by
      rw [mul_inv_cancel₀]
      norm_cast
      apply Nat.factorial_ne_zero
    rw [h2]
    simp
    rw [mul_comm]
    rw [neg_pow]
    rw [mul_comm, ←mul_assoc]
    rw [←pow_add]
    rw [Odd.neg_one_pow]
    ring
    have hkk : (k - 1) + k = 2 * k - 1 :=
        by
        rw [add_comm]
        rw [← Nat.add_sub_assoc]
        rw [two_mul]
        linarith
    rw [hkk]
    apply Nat.Even.sub_odd
    nlinarith
    simp
    exact odd_one
  rw [← mul_assoc]
  norm_cast at *
  simp at *
  rw [h3]
  have hee :
    ∑' n : ℕ+, (2 * ↑π * Complex.I * ((n : ℕ) : ℂ)) ^ ((k - 1) : ℕ) * exp (2 * ↑π * Complex.I * ((n : ℕ) : ℂ) * ↑z) =
      (2 * ↑π * Complex.I) ^ (k - 1) * ∑' n : ℕ+, n ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * n) :=
    by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro b
    rw [← mul_assoc]
    ring_nf
  simp [UpperHalfPlane.coe] at *
  rw [hee]
  rw [← mul_assoc]
  have he2 : 2 * ↑π * Complex.I * (2 * ↑π * Complex.I) ^ (k - 1) = (2 * ↑π * Complex.I) ^ k :=
    by
    have hke : k = 1 + (k - 1) := by
      apply symm; apply Nat.add_sub_of_le
      linarith
    nth_rw 2 [hke]
    norm_cast
    rw [pow_add]
    simp
  rw [he2]



theorem tsum_sigma_eqn2 (k : ℕ) (z : ℍ) :
    ∑' (c : Fin 2 → ℕ+), (c 0 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c 0 * c 1) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * z * e) := by
  rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq]
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  simp [sigmaAntidiagonalEquivProd, mapdiv]
  simp_rw [sigma_eq_sum_div']
  simp
  rw [tsum_sigma ]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simp
  have := @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
    (x : ℂ) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * z * x * y)) n
  simp at this
  have H := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
    (x.1 : ℂ) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * z * x.1 * x.2))
  simp at H
  rw [H]
  rw [this]
  rw [Finset.sum_mul ]
  apply Finset.sum_congr
  rfl
  intro i hi
  simp
  left
  congr 1
  have hni : (n / i : ℕ) * (i : ℂ) = n := by
    norm_cast
    simp at *
    exact Nat.div_mul_cancel hi
  rw [mul_assoc, hni]
  exact summable_auxil_1 k z


/-This is proven in the modular forms repo. -/
lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by
  apply summable_hammerTime _ k
  norm_cast
  lift k to ℕ using (by linarith)
  have := linear_bigO_pow n z k
  norm_cast at *

/-This is straight from the mod forms repo-/
theorem tsum_sigma_eqn {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c.1 * c.2) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * e * z) := by
  rw [← (piFinTwoEquiv fun _ => ℕ+).tsum_eq]
  have := tsum_sigma_eqn2 k z
  simp
  rw [this]
  congr
  ext n
  congr 1
  ring_nf

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

/-This is straight from the mod forms repo-/
theorem a1 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * e * c) := by
  apply Summable.mul_left
  apply Summable.of_norm
  have : (fun a : ℕ+ ↦ ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e * ↑↑a)‖) =
    fun a : ℕ+ ↦ ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e) ^ (a : ℕ)‖ := by
    ext a
    rw [← Complex.exp_nat_mul]
    ring_nf
  rw [this]
  have h1 : ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e)‖ < 1 := by
    simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
      zero_sub, natCast_re, neg_mul, zero_add, natCast_im, Real.exp_lt_one_iff, Left.neg_neg_iff,
      Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_right]
    positivity
  have h2 := summable_norm_iff.mpr (summable_geometric_iff_norm_lt_one.mpr h1)
  apply h2.subtype


/-This is straight from the mod forms repo-/
theorem a4 (k : ℕ) (z : ℍ) :
    Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑c * ↑z * ↑b)) := by
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp [sigmaAntidiagonalEquivProd, mapdiv]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp
  left
  ring_nf


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
    have := a33 (k := 1) e z
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
    have v : Summable fun (n : ℕ) ↦ ( - ↑(d : ℂ)- z * ((n : ℂ) ))⁻¹ - (↑↑d - z * ((n : ℂ)) )⁻¹ := by
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

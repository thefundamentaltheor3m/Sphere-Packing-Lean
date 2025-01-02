/-
The purpose of this file is to define the Eisenstein series we are interested in using more convenient notation.
-/

import Mathlib

-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0



-- private lemma aux4 : (3 : ℤ) ≤ 4 := by norm_num
-- private lemma aux6 : (3 : ℤ) ≤ 6 := by norm_num

/- The Eisenstein Series E₂, E₄ and E₆ -/

def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2) • eisensteinSeries_MF (by norm_num) standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2) • eisensteinSeries_MF (by norm_num) standardcongruencecondition

def S0 : Set ℤ := {0}ᶜ

def G₂' : ℍ → ℂ := fun z => ∑' (m : ℤ), (∑' (n : ℤ), 1 / (m * z + n) ^ 2) --hmm is this right?


def δ (a b : ℤ): ℂ := if a = 0 ∧ b = 0 then 1 else if a = 0 ∧ b = -1 then 2 else 0

@[simp]
lemma δ_eq : δ 0 0 = 1 := by simp [δ]

@[simp]
lemma δ_eq2 : δ 0 (-1) = 2 := by simp [δ]

lemma δ_neq (a b : ℤ) (h : a ≠ 0) : δ a b = 0 := by
  simp [δ, h]


instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2



theorem natPosSMul_apply (c : ℕ+) (z : ℍ) : ((c  • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := by rfl

/--Maybe this is the definition we want as I cant see how to easily show the other outer sum is
absolutely convergent. -/
def G₂ : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m in Finset.Ico (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

/-This is from the modforms repo, so no need to prove it. -/
theorem q_exp_iden (k : ℕ) (hk : 2 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
      ∑' n : ℕ+, n ^ ((k - 1) ) * Complex.exp (2 * ↑π * Complex.I * z * n) := sorry

lemma t4  (z : ℍ) (k : ℕ) (hk : 2 ≤ k):
    ∑' c : ℕ+, ∑' d : ℤ, 1 / (((c • z : ℍ) : ℂ) + d) ^ k =
      ∑' e : ℕ+,
        (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
        ∑' n : ℕ+, n ^ (k - 1) * Complex.exp (2 * ↑π * Complex.I * e * z * n) := by
      congr
      funext c
      rw [ q_exp_iden k hk (c • z : ℍ), natPosSMul_apply c z, ← mul_assoc]

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

lemma t7 (z : ℍ) (N : ℕ) :
  (∑ m in Finset.Ico (-N : ℤ) 0, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) =
   ∑ m in Finset.Ico (-N : ℤ) 0, (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * -m * z * n) := by
  apply Finset.sum_congr  rfl
  intro m hm
  simp at hm
  have hm : 0 ≤ -m := by linarith
  have hm0 : 0 < -m := by linarith
  set M := (-m).toNat
  have hM : 0 < M := by simp [M, hm0]
  set mm : ℕ+ := ⟨M, hM⟩
  have hmm : (mm : ℂ) = - (m : ℂ) := by
    simp [mm, M]
    have := Int.toNat_of_nonneg hm
    norm_cast
  have := q_exp_iden 2 (by norm_num) (mm • z)
  rw [natPosSMul_apply mm z] at this
  rw [hmm] at this
  simp at *
  conv at this =>
    enter [2,2,1]
    ext n
    rw [← mul_assoc]
  rw [← this]
  nth_rw 1 [int_sum_neg]
  congr
  funext m
  simp
  ring




lemma aux33 (f : ℕ → ℂ) (hf : Summable f) : ∑' n, f (n) =
    limUnder atTop (fun N : ℕ => ∑ n in Finset.range N, f (n)) := by
  rw [Filter.Tendsto.limUnder_eq]
  have  := hf.hasSum
  have V := this.comp tendsto_finset_range
  apply V


lemma aux34 (f : ℕ → ℂ) (hf : Summable f) : ∑' n, f (n + 1) =
    limUnder atTop (fun N : ℕ => ∑ n in Finset.range N, f (n + 1)) := by
    rw [aux33 ]
    rw [summable_nat_add_iff ]
    apply hf

/- this is being Pr'd-/
lemma tsum_pnat_eq_tsum_succ3 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1) := by sorry

lemma tsum_pnat_eq_tsum_succ4 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n := by sorry


lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  norm_cast
  rw [div_im]
  simp only [Int.cast_neg, Int.cast_natCast, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, gt_iff_lt]
  rw [@div_neg_iff]
  right
  simp only [Left.neg_neg_iff, Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left, Complex.normSq_pos,
    ne_eq]
  refine ⟨z.2, ne_zero z⟩

lemma pos_nat_div_upper (n : ℤ) (hn : 0 < n) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  norm_cast
  rw [div_im]
  simp [Int.cast_neg, Int.cast_natCast, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, gt_iff_lt]
  rw [div_neg_iff]
  right
  simp [Left.neg_neg_iff, Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left, Complex.normSq_pos,
    ne_eq]
  have hnr : 0 < (n : ℝ) := by simp [hn]
  refine ⟨by apply mul_pos hnr z.2; , ne_zero z⟩


lemma aux35 (f : ℕ → ℂ) (hf : Summable f) : ∑' n : ℕ+, f n =
  limUnder atTop (fun N : ℕ => ∑ n in Finset.range N, f (n + 1)) := by
  rw [← aux34 f hf]
  apply tsum_pnat_eq_tsum_succ3


def summable_term (z : ℍ) : ℤ → ℂ :=  (fun m : ℤ => (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

lemma term_evem (z : ℍ) (m : ℤ) : summable_term z m = summable_term z (-m) := by
  simp [summable_term]
  nth_rw 1 [int_sum_neg]
  congr
  funext m
  simp
  ring

lemma Icc_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n+1) : ℤ), (n + 1 : ℤ)} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega



lemma Icc_sum_even (f : ℤ → ℂ) (hf : ∀ n, f n = f (-n)) (N : ℕ):
    ∑ m in Finset.Icc (-N : ℤ) N, f m =  2 * ∑ m in Finset.range (N + 1), f m  - f 0 := by
  induction' N with N ih
  simp only [CharP.cast_eq_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton, zero_add,
    Finset.range_one]
  ring
  have := Icc_succ N
  simp only [neg_add_rev, Int.reduceNeg,  Nat.cast_add, Nat.cast_one] at *
  rw [this, Finset.sum_union, Finset.sum_pair, ih]
  nth_rw 2 [Finset.sum_range_succ]
  have HF:= hf (N + 1)
  simp only [neg_add_rev, Int.reduceNeg] at HF
  rw [← HF]
  ring_nf
  norm_cast
  omega
  simp only [Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Icc, le_add_iff_nonneg_left,
    Left.nonneg_neg_iff, Int.reduceLE, add_neg_le_iff_le_add, false_and, not_false_eq_true,
    Finset.disjoint_singleton_right, add_le_iff_nonpos_right, and_false, and_self]

lemma zeta_two_eqn : ∑' (n : ℤ), ((n : ℂ) ^ 2)⁻¹ = 2 * riemannZeta 2 := by
  have := tsum_nat_add_neg (f := fun n => 1/((n : ℂ) ^ 2)) ?_
  simp only [Int.cast_natCast, one_div, Int.cast_neg, even_two, Even.neg_pow, Int.cast_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, add_zero] at this
  rw [← this]
  have hr := zeta_nat_eq_tsum_of_gt_one (k := 2)
  simp only [Nat.one_lt_ofNat, Nat.cast_ofNat, one_div, forall_const] at hr
  rw [hr, tsum_add]
  ring
  repeat{
  have := Complex.summable_one_div_nat_cpow  (p := 2)
  simp only [cpow_ofNat, one_div, re_ofNat, Nat.one_lt_ofNat, iff_true] at this
  exact this}
  simp only [one_div]
  have := Complex.summable_one_div_nat_cpow  (p := 2)
  simp only [cpow_ofNat, one_div, re_ofNat, Nat.one_lt_ofNat, iff_true] at *
  norm_cast at *
  apply  Summable.of_nat_of_neg_add_one
  apply this
  rw [← summable_nat_add_iff 1] at this
  apply this.congr
  intro b
  congr


lemma sum_range_zero (f : ℤ → ℂ) (n : ℕ) : ∑ m in Finset.range (n+1), f m = f 0 +
  ∑ m in Finset.range n, f (m+1) := by
  rw [Finset.sum_range_succ' ]
  rw [add_comm]
  simp

lemma auxer (a c : ℂ) : a + 2*2*c - 2*c =a + 2*c := by ring

lemma t8 (z : ℍ) :
  (fun N : ℕ => ∑ m in Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) =
  (fun _ : ℕ => 2*((riemannZeta 2))) +
  (fun N : ℕ => ∑ m in Finset.range (N), 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
  funext m
  simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
    Nat.cast_one, div_one, pow_one, Pi.add_apply]
  rw [Icc_sum_even]
  simp only [Int.cast_natCast, Int.cast_zero, zero_mul, zero_add]
  rw [ zeta_two_eqn]
  nth_rw 2 [add_comm]
  have := sum_range_zero (fun m =>  (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) m
  simp only [Int.cast_natCast, one_div, Int.cast_zero, zero_mul, zero_add, Int.cast_add,
    Int.cast_one] at this
  rw [this, zeta_two_eqn, add_comm, mul_add, ← mul_assoc, auxer]
  congr
  rw [@Finset.mul_sum]
  congr
  ext d
  let Z : ℍ := ⟨(d +1)* z, by simp; apply mul_pos; linarith; exact z.2⟩
  have := q_exp_iden 2 (by norm_num) (z := Z)
  simp only [coe_mk_subtype, one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one,
    Nat.factorial_one, Nat.cast_one, div_one, pow_one, Z] at *
  rw [this]
  ring_nf
  congr
  ext r
  congr
  ring
  · intro n
    have := term_evem z n
    simp [summable_term] at *
    exact this


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
    simp [swap] at *
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



lemma verga2 : Tendsto (fun N : ℕ => Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)


lemma auxl2 (a b c : ℂ): Complex.abs (a - b) ≤ Complex.abs (a - b + c) + Complex.abs (c) := by
  nth_rw 1 [show a - b = (a - b + c) + -c by ring]
  have : Complex.abs (a - b + c + -c) ≤ Complex.abs (a - b+ c) + Complex.abs (-c) := by exact AbsoluteValue.add_le Complex.abs (a - b+ c) (-c)
  simpa using this

lemma trex (f : ℤ → ℂ) (N : ℕ) (hn : 1 ≤ N) : ∑ m in Finset.Icc (-N : ℤ) N, f m =
  f N + f (-N : ℤ)  + ∑ m in Finset.Icc (-(N - 1) : ℤ) (N-1), f m := by
  induction' N with N ih
  simp
  aesop
  zify
  rw [Icc_succ]
  rw [Finset.sum_union]
  ring_nf
  rw [add_assoc]
  congr
  rw [ Finset.sum_pair]
  ring
  omega
  simp

lemma cc(f : ℤ → ℂ) (hc :  CauchySeq fun N : ℕ => ∑ m in Finset.Icc (-N : ℤ) N, f m)
  (hs : ∀ n , f n = f (-n)) :
  Tendsto f atTop (𝓝 0) := by
  have h := cauchySeq_iff_tendsto_dist_atTop_0.mp hc
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  rw [Metric.tendsto_atTop] at *
  simp at *
  intro ε hε
  have hh := Hg (2 * ε) (by linarith)
  obtain ⟨N, hN⟩ := hh
  use N + 1
  intro n hn
  have H3 := H (n).natAbs (n -1).natAbs N ?_ ?_
  rw [trex f n.natAbs] at H3
  simp [dist_eq_norm] at *
  have h1 : |n| = n := by
    simp
    linarith
  simp_rw [h1] at H3
  have h2 : |n - 1| = n - 1 := by
    simp
    linarith
  simp_rw [h2] at H3
  simp at H3
  rw [← hs n] at H3
  rw [show f n + f n = 2 * f n by ring] at H3
  simp at H3
  have HN := hN N (by rfl)
  have hgn : g N ≤ |g N| := by
    exact le_abs_self (g N)
  have := le_trans H3 hgn
  have hgnn : 2 * Complex.abs (f n) < 2 * ε := by
    apply lt_of_le_of_lt
    exact this
    exact HN
  nlinarith
  omega
  omega
  omega


lemma sum_Icc_eq_sum_Ico_succ {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    {l u : ℤ} (h : l ≤ u) :
    ∑ m in Finset.Icc l u, f m = (∑ m in Finset.Ico l u, f m) + f u := by
  rw [Finset.Icc_eq_cons_Ico h]
  simp only [Finset.cons_eq_insert, Finset.mem_Ico, lt_self_iff_false, and_false, not_false_eq_true,
    Finset.sum_insert]
  rw [add_comm]

lemma CauchySeq_Icc_iff_CauchySeq_Ico (f : ℤ → ℂ) (hs : ∀ n , f n = f (-n))
  (hc : CauchySeq (fun N : ℕ => ∑ m in Finset.Icc (-N : ℤ) N, f m) ) :
  CauchySeq (fun N : ℕ => ∑ m in Finset.Ico (-N : ℤ) N, f m) := by
  have h0 := cc f hc hs
  have : CauchySeq fun n: ℕ => f n := by
    apply Filter.Tendsto.cauchySeq (x := 0)
    rw [Metric.tendsto_atTop] at *
    intro ε hε
    have hf3 := h0 ε hε
    obtain ⟨N, hN⟩ := hf3
    use N.natAbs
    simp at *
    intro n hn
    have hy := hN n
    apply hy
    omega
  have h1 := Filter.Tendsto.mul_const  2 h0
  have hff : Tendsto (fun n : ℕ => 2 * ‖f n‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at *
    simp [dist_eq_norm] at *
    intro ε hε
    have hf3 := h1 ε hε
    obtain ⟨N, hN⟩ := hf3
    use N.natAbs
    intro n hn
    have hy := hN n
    rw [mul_comm]
    apply hy
    omega
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨b, hb, H, hbb⟩ := hc
  obtain ⟨a, ha, H2, haa⟩ := this
  refine ⟨b + a, ?_, ?_, ?_⟩
  · intro n
    simp
    apply add_nonneg
    exact hb n
    apply ha n
  · intro n m N hn hm
    have H3 := H n m N hn hm
    simp [dist_eq_norm] at *
    rw [sum_Icc_eq_sum_Ico_succ _, sum_Icc_eq_sum_Ico_succ _] at H3
    have := auxl2 (∑ m ∈ Finset.Ico (-↑n) ↑n, f m) (∑ m ∈ Finset.Ico (-↑m) ↑m, f m) (f n - f m)
    apply le_trans this
    gcongr
    simp at *
    apply le_trans _ H3
    apply le_of_eq
    congr
    ring
    have H22 := H2 n m N hn hm
    exact H22
    omega
    omega
  · have HG := Filter.Tendsto.add hbb haa
    simpa using HG


theorem nat_pos_tprod2' {α : Type*} [TopologicalSpace α] [CommMonoid α]  (f : ℕ → α) :
    (Multipliable fun x : ℕ+ => f x) ↔ Multipliable  fun x : ℕ => f (x + 1) :=
  by
  rw [← Equiv.multipliable_iff _root_.Equiv.pnatEquivNat]
  constructor
  intro hf
  apply Multipliable.congr hf
  intro b
  simp
  intro hf
  apply Multipliable.congr hf
  intro b
  simp


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

theorem G2_c_tendsto (z : ℍ) :
  Tendsto
    (fun N ↦
      ∑ x ∈ Finset.range N,
        2 * (2 * ↑π * Complex.I) ^ 2 * ∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z * ↑↑n))
    atTop (𝓝 (-8 * ↑π ^ 2 * ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) := by
    rw [← t9]
    have hf : Summable fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) := by
        conv =>
          enter [1]
          ext m
          rw [show (m : ℂ) +  1 = (((m + 1) : ℕ) : ℂ) by simp]
        have := nat_pos_tsum2' (f := fun m : ℕ => ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
        ∑' n : ℕ+, n ^ ((2 - 1) ) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n)) )
        rw  [← this]
        have := (a4 2 z).prod_symm.prod
        apply Summable.mul_left
        apply this.congr
        intro b
        congr
    have := hf.hasSum
    have V := this.comp tendsto_finset_range
    simp at *
    apply V

lemma G2_cauchy (z : ℍ) :
  CauchySeq  (fun N : ℕ => ∑ m in Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2))) := by
  rw [t8]
  simp
  apply CauchySeq.const_add
  apply Filter.Tendsto.cauchySeq (x :=  -
    8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * n * z))
  apply G2_c_tendsto z

lemma fsb (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} :=  by
  ext n
  simp
  omega

theorem telescope_aux (z : ℍ) (m : ℤ) (b : ℕ) :
  ∑ n ∈ Finset.Ico (-b : ℤ) b, (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) =
    1 / (↑m * ↑z - ↑b) - 1 / (↑m * ↑z + ↑b) := by
  induction' b  with b ihb
  aesop
  simp only [Nat.cast_add, Nat.cast_one, Int.reduceNeg, one_div,
      Finset.sum_sub_distrib] at *
  rw [fsb, Finset.sum_union, Finset.sum_union, Finset.sum_pair, Finset.sum_pair,add_sub_add_comm, ihb]
  simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  ring
  · omega
  · omega
  · simp only [neg_add_rev, Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Ico,
    le_add_iff_nonneg_left, Left.nonneg_neg_iff, Int.reduceLE, add_neg_lt_iff_lt_add, false_and,
    not_false_eq_true, Finset.disjoint_singleton_right, neg_le_self_iff, Nat.cast_nonneg,
    lt_self_iff_false, and_false, and_self]
  · simp only [neg_add_rev, Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Ico,
    le_add_iff_nonneg_left, Left.nonneg_neg_iff, Int.reduceLE, add_neg_lt_iff_lt_add, false_and,
    not_false_eq_true, Finset.disjoint_singleton_right, neg_le_self_iff, Nat.cast_nonneg,
    lt_self_iff_false, and_false, and_self]

theorem tendstozero_inv_linear (z : ℍ) (b : ℤ)  :
  Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z + ↑d)) atTop (𝓝 0) := by
    rw [@tendsto_zero_iff_norm_tendsto_zero]
    conv =>
      enter [1]
      simp
    apply squeeze_zero (g := fun n : ℕ => r z ^ (-1 : ℝ) * ‖![b, n]‖ ^ (-1 : ℝ))
    simp
    intro t
    have := EisensteinSeries.summand_bound z (k := 1)  (by simp) ![b, t]
    simp at *
    apply le_trans _ this
    apply le_of_eq
    rw [Real.rpow_neg_one]
    rw [← tendsto_const_smul_iff₀ (c := r z ) ]
    simp
    have hr : r z * r z ^ (-1 : ℝ) = 1 := by
      rw [Real.rpow_neg_one]
      refine mul_inv_cancel₀ (ne_of_lt (r_pos z)).symm
    conv =>
      enter [1]
      intro r
      rw [← mul_assoc, hr]
    simp
    apply squeeze_zero' (g := (fun n : ℕ => |(n : ℝ)| ^ (-1 : ℝ)))
    apply Filter.Eventually.of_forall
    intro x
    refine Real.rpow_nonneg ?g0.hf.hp.hx (-1)
    apply norm_nonneg
    rw [@eventually_atTop]
    use b.natAbs
    intro x hx
    apply le_of_eq
    congr
    rw [EisensteinSeries.norm_eq_max_natAbs ]
    simp [hx]
    simp
    apply tendsto_inverse_atTop_nhds_zero_nat.congr
    intro x
    exact Eq.symm (Real.rpow_neg_one ↑x)
    have := r_pos z
    exact (ne_of_lt this).symm

theorem tendstozero_inv_linear_neg (z : ℍ) (b : ℤ)  :
  Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) := by
    rw [@tendsto_zero_iff_norm_tendsto_zero]
    conv =>
      enter [1]
      simp
    apply squeeze_zero (g := fun n : ℕ => r z ^ (-1 : ℝ) * ‖![b, -n]‖ ^ (-1 : ℝ))
    simp
    intro t
    have := EisensteinSeries.summand_bound z (k := 1)  (by simp) ![b, -t]
    simp at *
    apply le_trans _ this
    apply le_of_eq
    rw [Real.rpow_neg_one]
    congr
    rw [← tendsto_const_smul_iff₀ (c := r z ) ]
    simp
    have hr : r z * r z ^ (-1 : ℝ) = 1 := by
      rw [Real.rpow_neg_one]
      refine mul_inv_cancel₀ (ne_of_lt (r_pos z)).symm
    conv =>
      enter [1]
      intro r
      rw [← mul_assoc, hr]
    simp
    apply squeeze_zero' (g := (fun n : ℕ => |(n : ℝ)| ^ (-1 : ℝ)))
    apply Filter.Eventually.of_forall
    intro x
    refine Real.rpow_nonneg ?g0.hf.hp.hx (-1)
    apply norm_nonneg
    rw [@eventually_atTop]
    use b.natAbs
    intro x hx
    apply le_of_eq
    congr
    rw [EisensteinSeries.norm_eq_max_natAbs ]
    simp [hx]
    simp
    apply tendsto_inverse_atTop_nhds_zero_nat.congr
    intro x
    exact Eq.symm (Real.rpow_neg_one ↑x)
    have := r_pos z
    exact (ne_of_lt this).symm


lemma PS1 (z : ℍ) (m : ℤ) : limUnder atTop
  (fun N : ℕ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = 0 := by
  apply Filter.Tendsto.limUnder_eq
  have :  (fun N : ℕ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) =
    (fun N : ℕ => (1 / ((m : ℂ) * z - N) -  1 / (m * z + N))) := by
    funext N
    rw [telescope_aux]
  rw [this]
  have h0 := tendstozero_inv_linear z m
  have h1 := tendstozero_inv_linear_neg z m
  have h2 := Filter.Tendsto.sub h1 h0
  simpa using h2

lemma ada (f : ℤ → ℂ) (h : ∀ i, f i = 0) : ∑' n, f n = 0 := by
  convert tsum_zero
  aesop


lemma PS2 (z : ℍ) : ∑' m : ℤ, (limUnder atTop
  (fun N : ℕ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1)))) = 0 := by
    convert tsum_zero
    next m =>
    apply PS1
    --apply m.2

/-This is from the modforms repo, so no need to prove it. -/
theorem series_eql' (z : ℍ) :
    ↑π * Complex.I - 2 * ↑π * Complex.I * ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * z * n) =
      1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := sorry


/-this is from the mod forms repo-/
theorem int_tsum_pNat {α : Type*} [UniformSpace α] [CommRing α]  [ UniformAddGroup α] [CompleteSpace α]
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


/- lemma multipliable_pnats (f : ℕ → ℂ) : Multipliable (fun n : ℕ+ => f n) ↔ Multipliable  f := by
  rw [nat_pos_tprod2']
  have :=  multipliable_nat_add_iff (f := f) 1 -/

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
    Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv, norm_eq_abs, norm_pow, and_imp, true_and]
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
    have hS : Summable fun m : ℤ => 1 / (r z ^ 2 * 2⁻¹ * ‖![m, i]‖ ^ 2) := by
      apply extracted_abs_norm_summable
    apply hS.of_norm_bounded_eventually
    rw [Filter.eventually_iff_exists_mem ]
    use {0, -1}ᶜ
    constructor
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, mem_cofinite, compl_compl,
      finite_singleton, Finite.insert, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
      Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv, norm_eq_abs, norm_pow, and_imp, true_and]
    · intro y hy
      have hi := summand_bound z (k := 1) (by norm_num) ![y, i]
      have hi1 := summand_bound z (k := 1) (by norm_num) ![y, i + 1]
      simp only [one_div, mul_inv_rev, Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg,
        mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Int.cast_add, Int.cast_one, norm_mul, norm_inv,
        norm_eq_abs, ge_iff_le] at *
      have := mul_le_mul hi1 hi (by rw [Real.rpow_neg_one, inv_nonneg]; apply AbsoluteValue.nonneg )
        (by simp_rw [Real.rpow_neg_one, ← mul_inv, inv_nonneg]; apply mul_nonneg; exact (r_pos z).le; exact norm_nonneg _)
      have he1 : Complex.abs (↑y * ↑z + (↑i + 1)) ^ (-1 : ℝ) * Complex.abs (↑y * ↑z + ↑i) ^ (-1 : ℝ) =
          (Complex.abs (↑y * ↑z + ↑i + 1))⁻¹ * (Complex.abs (↑y * ↑z + ↑i))⁻¹ := by
          simp_rw [Real.rpow_neg_one]
          congr 1
          congr 1
          norm_cast
          rw [Int.cast_add, ← add_assoc]
          congr
          simp
      rw [he1] at this
      apply le_trans this
      have hl : r z ^ (-1 : ℝ) * ‖![y, i + 1]‖ ^ (-1 : ℝ) * (r z ^ (-1 : ℝ) * ‖![y, i]‖ ^ (-1 : ℝ)) =
        r z ^ (-2 : ℝ) * (‖![y, i + 1]‖⁻¹ * ‖![y, i]‖⁻¹) := by
        rw [show (-2 : ℝ) = -1 + -1 by ring]
        rw [Real.rpow_add]
        simp_rw [Real.rpow_neg_one]
        ring
        exact r_pos z
      have hr : (‖![y, i]‖ ^ 2)⁻¹ * ((2⁻¹)⁻¹ * (r z ^ 2)⁻¹) =
        (r z ^ (-2 : ℝ)) * (2 * (‖![y, i]‖⁻¹) * (‖![y, i]‖⁻¹)) := by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, inv_inv]
        ring_nf
        simp only [inv_pow, mul_eq_mul_right_iff, mul_eq_mul_left_iff, inv_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero,
          Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, or_false]
        left
        have:= r_pos z
        rw [Real.rpow_neg (r_pos z).le, Real.rpow_two]
      rw [hl, hr]
      gcongr
      apply Real.rpow_nonneg
      apply (r_pos z).le
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, norm_eq_max_natAbs, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.cast_max]
      rw [aux]
      · norm_cast
        rw [← Nat.mul_max_mul_left]
        omega
      · simp [hy.1]
      · simp [hy.1]
      · exact zero_lt_two
  rw [← Finset.summable_compl_iff  (s := {0}) ]  at this
  apply this

theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    Complex.abs (Complex.exp (2 * ↑π * Complex.I * z)) < 1 := by
  simp only [abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    Complex.abs (Complex.exp (2 * ↑π * Complex.I * (n+1) * z)) < 1 := by
  simp [abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

lemma pnat_nat_tendsto (f : ℕ → ℝ) (hf : Tendsto (fun n : ℕ+ => f n) atTop (𝓝 0)) :
  Tendsto f atTop (𝓝 0) := by
  exact tendsto_comp_val_Ioi_atTop.mp hf

theorem tsum_exp_tendsto_zero (z : ℍ) :
    Tendsto (fun x : ℕ+ ↦ 2 / ↑z * 2 * ↑π * Complex.I *
    ∑' (n : ℕ), cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) atTop (𝓝 (4 * ↑π * Complex.I / ↑z)) := by
  rw [show  4 * ↑π * Complex.I / ↑z =  2 / ↑z * 2 * ↑π * Complex.I +  0 by ring]
  conv =>
    enter [1]
    ext n
    rw [← tsum_pnat_eq_tsum_succ4, mul_add]
  simp only [CharP.cast_eq_zero, mul_zero, exp_zero, mul_one, add_zero]
  nth_rw 3 [show  2 / ↑z * 2 * ↑π * Complex.I =  2 / ↑z * 2 * ↑π * Complex.I +  2 / ↑z * 2 * ↑π * Complex.I*0 by ring]
  apply Tendsto.add
  simp only [tendsto_const_nhds_iff]
  apply Tendsto.mul
  simp
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun (n : ℕ+) => (0 : ℂ))
    (f := fun d : ℕ+ => fun n : ℕ+ => cexp (2 * ↑π * Complex.I * (-↑↑d / ↑z) * ↑n) )
    (bound := fun n : ℕ+ => (Complex.abs (cexp (2 * ↑π * Complex.I * (-1 / ↑z)))^ (n : ℕ)))
  simp only [norm_eq_abs, ge_iff_le, tsum_zero, forall_exists_index] at this
  apply this
  · apply Summable.subtype
    simpa only [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, Complex.abs_abs] using
      (exp_upperHalfPlane_lt_one ⟨-1 / z, by simpa using (pnat_div_upper 1 z)⟩)
  · intro k
    have : (fun x : ℕ+ ↦ cexp (2 * ↑π * Complex.I * (-↑↑(x : ℂ) / ↑z) * ↑k)) =
    (fun x : ℕ+ ↦ (cexp (2 * ↑π * Complex.I * (-↑↑(k : ℂ) / ↑z)))  ^ (x : ℕ)) := by
      ext n
      rw [← exp_nsmul]
      congr
      simp only [nsmul_eq_mul]
      ring
    rw [this]
    have ht : Tendsto (fun x : ℕ ↦ cexp (2 * ↑π * Complex.I * (-↑k / ↑z)) ^ ↑x) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_pow, norm_eq_abs, tendsto_pow_atTop_nhds_zero_iff, Complex.abs_abs]
      apply exp_upperHalfPlane_lt_one ⟨-k / z, by simpa using (pnat_div_upper k z)⟩
    apply tendsto_comp_val_Ioi_atTop.mpr ht
  · simp only [eventually_atTop, ge_iff_le]
    use 1
    intro b hb k
    have : cexp (2 * ↑π * Complex.I * (-↑↑b / ↑z) * (k : ℕ)) =
      ((cexp (2 * ↑π * Complex.I * (- 1 / ↑z)) ^ (k: ℕ)) ^ (b : ℕ)) := by
      rw [← pow_mul, ← exp_nsmul]
      congr
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [this]
    simp only [AbsoluteValue.map_pow, ge_iff_le]
    rw [← pow_mul]
    apply  Bound.pow_le_pow_right_of_le_one_or_one_le ?_
    right
    constructor
    · apply AbsoluteValue.nonneg Complex.abs
    · have := exp_upperHalfPlane_lt_one ⟨- 1 / z, by simpa using (pnat_div_upper 1 z)⟩
      constructor
      apply this.le
      exact Nat.le_mul_of_pos_right k hb


theorem extracted_12 (z : ℍ) :
    Tendsto (fun n : ℕ => (2 / (z : ℂ) * ∑' (m : ℕ+),
     (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z)) := by
  have : Tendsto (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
     (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))  := by
    have : (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
     (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) = (fun N : ℕ+ =>
      (2 / (z : ℂ) * (↑π * Complex.I - 2 * ↑π * Complex.I *
      ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-N / z) * n) - z / -N))) := by
      funext N
      set Z : ℍ := ⟨-N / z, pnat_div_upper N z⟩
      have hS := series_eql' Z
      simp [Z] at *
      rw [← sub_eq_iff_eq_add'] at hS
      left
      have hSS := hS.symm
      apply hSS
    rw [this]
    have h3 : (fun N : ℕ+ =>
        (2 / (z : ℂ) * (↑π * Complex.I - 2 * ↑π * Complex.I *
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-N / z) * n) - z / -N)))  =
        (fun N : ℕ+ => ((2 / (z : ℂ)) * ↑π * Complex.I - ((2 / z) * 2 * ↑π * Complex.I *
          ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-N / z) * n)) - 2 / -N)) := by
        funext N
        have hz : 2 / -(N : ℂ) = (2 / z) * (z / -N) := by
          have : (z : ℂ) ≠ 0 := ne_zero z
          field_simp
        rw [hz]
        ring
    rw [h3]
    rw [show -2 * ↑π * Complex.I / ↑z =  2 * ↑π * Complex.I / ↑z - 4 * ↑π * Complex.I / ↑z - 0 by ring]
    apply Tendsto.sub
    apply Tendsto.sub
    simp only [tendsto_const_nhds_iff]
    ring
    apply tsum_exp_tendsto_zero
    have := tendsto_const_div_pow 2 1 (Nat.one_ne_zero)
    rw [Metric.tendsto_atTop] at *
    simp only [one_div, gt_iff_lt, ge_iff_le, pow_one, dist_zero_right, norm_div, Real.norm_ofNat,
      Real.norm_natCast, norm_ofNat, norm_neg, norm_natCast] at *
    intro ε hε
    have ht := this ε hε
    obtain ⟨N,HN ⟩ := ht
    use ⟨(N + 1), Nat.zero_lt_succ N⟩
    intro n hn
    apply HN n ?_
    rw [← PNat.coe_le_coe ] at hn
    simp at hn
    omega
  rw [Metric.tendsto_atTop] at *
  simp only [gt_iff_lt, ge_iff_le, one_div, neg_mul] at *
  intro ε hε
  have th := this ε hε
  obtain ⟨N, hN⟩ := th
  use N
  intro n hn
  have hn0 : 0 < n := by
   have l := N.2
   simp only [gt_iff_lt] at *
   apply Nat.lt_of_lt_of_le l hn
  have HNN := hN ⟨n, hn0⟩ ?_
  simp only [PNat.mk_coe, gt_iff_lt] at *
  exact HNN
  norm_cast

lemma int_tendsto_nat {f : ℤ → ℂ} {x : ℂ} (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ => f n) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  use N.natAbs
  intro n hn
  apply hN n ?_
  omega

lemma pnat_tendsto_nat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x)) :
  Tendsto f atTop (𝓝 x) := by
  exact tendsto_comp_val_Ioi_atTop.mp hf

lemma nat_tendsto_pnat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x) := by
  exact tendsto_comp_val_Ioi_atTop.mpr hf

theorem PS3tn22 (z : ℍ) :
  Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N,
    ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1))) atTop
    (𝓝 (-2 * ↑π * Complex.I / ↑z)) := by
  have : (fun N : ℕ+ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) =
    (fun N : ℕ+ =>
    ∑' m : ℤ ,  ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)), (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) := by
    ext n
    rw [tsum_sum]
    intro i hi
    apply summable_pain
  conv at this =>
    enter [2]
    ext
    conv =>
      enter [1]
      ext m
      rw [telescope_aux z]
  have hp := sum_int_pnat2_pnat z
  conv at this =>
    enter [2]
    ext m
    rw [show (m : ℂ) = (m : ℕ+) by simp]
    rw [hp]
  rw [this]
  rw [show -2 * ↑π * Complex.I / ↑z = 0 + -2 * ↑π * Complex.I / ↑z by ring]
  apply Tendsto.add
  ·
    have : Tendsto (fun x : ℕ ↦ -2 / (x : ℂ)) atTop (𝓝 0) := by
        have := Filter.Tendsto.const_div_atTop (g := fun n : ℕ => ‖(n : ℂ)‖) (r := 2) (l := atTop) ?_
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa only [norm_div, norm_neg, norm_ofNat, norm_natCast] using this
        simp only [norm_natCast]
        exact tendsto_natCast_atTop_atTop
    have H := nat_tendsto_pnat _ _ this
    exact H
  · conv =>
      enter [1]
      ext n
      rw [show (n : ℂ) = (n : ℤ) by simp]
      rw [sum_int_pnat3]
    have := nat_tendsto_pnat _ _ (extracted_12 z)
    exact this

lemma PS3 (z : ℍ) : limUnder atTop
  (fun N : ℕ => ∑ n in (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) -  1 / (m * z + n + 1))) = -2 * π * Complex.I / z := by
  apply Filter.Tendsto.limUnder_eq
  apply pnat_tendsto_nat
  apply PS3tn22

theorem extracted_1 (b : Fin 2 → ℤ) (hb : b ≠ 0) (HB1 : b ≠ ![0, -1]) :
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
    Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv, norm_eq_abs, norm_pow, and_imp, true_and]
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
  have hpow : Complex.abs (↑(b 0) * ↑z + ↑(b 1)) ^ (-2 : ℝ) =
    (Complex.abs (↑(b 0) * ↑z + ↑(b 1)) ^ 2)⁻¹ :=
    by norm_cast
  have hpow2 : Complex.abs (↑(b 0) * ↑z + ↑(b 1)+1) ^ (-1 : ℝ) =
    (Complex.abs (↑(b 0) * ↑z + ↑(b 1)+1))⁻¹ :=
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
  apply  extracted_1
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
    exact AbsoluteValue.nonneg Complex.abs _
  · exact
    mul_nonneg (Real.rpow_nonneg (LT.lt.le (r_pos z)) (-1))
      (Real.rpow_nonneg (norm_nonneg ![b 0, b 1 + 1]) (-1))

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

/- lemma G2_alt_indexing (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) =
    ∑' m : ℤ, ∑' n : ℤ, 1 / (((m : ℂ)* z + n)^2 * (m * z + n +1)) := by
  rw [ ← (finTwoArrowEquiv _).symm.tsum_eq]
  simp
  refine tsum_prod' ?h ?h₁
  have := G_2_alt_summable z
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this
  intro b
  simp
  have := G_2_alt_summable z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor -/

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


def swap : (Fin 2 → ℤ) → (Fin 2 → ℤ) := fun x => ![x 1, x 0]

@[simp]
lemma swap_apply (b : Fin 2 → ℤ) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive (b : Fin 2 → ℤ) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

def swap_equiv : Equiv (Fin 2 → ℤ) (Fin 2 → ℤ) := Equiv.mk swap swap
  (by rw [LeftInverse]; apply swap_involutive)
  (by rw [Function.RightInverse]; apply swap_involutive)

/- lemma G2_alt_indexing2 (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) =
    ∑' n : ℤ, ∑' m : ℤ, 1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) := by
  have := (G_2_alt_summable z)
  simp at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  rw [tsum_comm']
  rw [G2_alt_indexing]
  apply this.congr
  intro b
  simp
  rfl
  intro b
  simp
  apply this.prod_factor
  intro c
  simp
  have H := (G_2_alt_summable z)
  simp at this
  rw [← swap_equiv.summable_iff] at H
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
  simp [Fin.isValue, one_div, mul_inv_rev, swap_equiv, Equiv.coe_fn_mk,
    finTwoArrowEquiv_symm_apply, swap_apply] at H
  have := H.prod_factor c
  simp at this
  apply this -/

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


lemma int_add_abs_self_nonneg (n : ℤ) : 0 ≤ n + |n| := by
  by_cases h : 0 ≤ n
  apply add_nonneg h
  exact abs_nonneg n
  simp at *
  rw [abs_of_neg h]
  simp


lemma verga : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  intro x
  use (x).natAbs + 1
  simp [le_abs]
  constructor
  apply le_trans _ (int_add_abs_self_nonneg x)
  omega
  refine Int.lt_add_one_iff.mpr ?_
  exact le_abs_self x

lemma aux3 (f : ℤ → ℂ) (hf : Summable f) : ∑' n, f n =
    limUnder atTop (fun N : ℕ => ∑ n in Finset.Ico (-N : ℤ) N, f n) := by
  rw [Filter.Tendsto.limUnder_eq]
  have  := hf.hasSum
  have V := this.comp verga
  apply V



lemma limUnder_add {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) + (limUnder atTop g) = limUnder atTop (f + g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  rw [@Pi.add_def]
  apply Filter.Tendsto.add
  refine CauchySeq.tendsto_limUnder hf
  refine CauchySeq.tendsto_limUnder hg


lemma limUnder_mul_const {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f : α → ℂ)
    (hf : CauchySeq f) (c : ℂ) :
    c * (limUnder atTop f)= limUnder atTop (c • f) := by
  nth_rw 2 [Filter.Tendsto.limUnder_eq]
  apply Filter.Tendsto.const_mul
  refine CauchySeq.tendsto_limUnder hf


lemma limUnder_sub {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) - (limUnder atTop g) = limUnder atTop (f - g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  rw [@Pi.sub_def]
  apply Filter.Tendsto.sub
  refine CauchySeq.tendsto_limUnder hf
  refine CauchySeq.tendsto_limUnder hg




theorem poly_id (z : ℍ) (b n : ℤ) :
  ((b : ℂ) * ↑z + ↑n + 1)⁻¹ * (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ + (δ b n) +
    (((b : ℂ) * ↑z + ↑n)⁻¹ - ((b : ℂ) * ↑z + ↑n + 1)⁻¹) =
    (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  rw [h.1, h.2]
  simp
  simp at h
  by_cases hb : b = 0
  by_cases hn : n = -1
  simp [hb, hn]
  ring
  have hj := h hb
  have hd : δ 0 n = 0 := by
    simp [δ, hb, hj, hn]
  simp [hd, hb]
  have hn0 : (n : ℂ) ≠ 0 := by aesop
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    norm_cast
    omega
  field_simp
  ring
  have : δ b n = 0 := by simp [δ, hb]
  rw [this]
  simp
  have h : ![(b : ℝ), n + 1] ≠ 0 := by
    aesop
  have hh : ![(b : ℝ), n ] ≠ 0 := by
    aesop
  have h0 : ((b : ℂ) * ↑z + ↑n + 1) ≠ 0 := by
    have := linear_ne_zero ![b, n + 1] z h
    simp at this
    norm_cast at this
    rw [@AddSemigroup.add_assoc]
    aesop
  have h1 : ((b : ℂ) * ↑z + ↑n) ≠ 0 := by
    have := linear_ne_zero ![b, n] z hh
    simpa using this
  field_simp [h0, h1]
  ring


lemma limUnder_congr_eventually (f g : ℕ → ℂ) (h : ∀ᶠ n in atTop, f n = g n)
  (hf : CauchySeq f) (hg : CauchySeq g)  :
  limUnder atTop f = limUnder atTop g := by
  have h0 := CauchySeq.tendsto_limUnder hf
  have h1 := CauchySeq.tendsto_limUnder hg
  rw [Filter.Tendsto.limUnder_eq (x := (limUnder atTop f)) ]
  rw [Filter.Tendsto.limUnder_eq ]
  apply Filter.Tendsto.congr' _ h1
  symm
  apply h
  exact h0
  --apply Filter.Tendsto.congr' ( hf)

theorem extracted_2 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, 1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        ((b  : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹)
  have hA:= (G2_prod_summable1 z b).hasSum
  have ht := hA.comp verga
  simp at *
  apply ht

theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
        (((b  : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹  + δ b x))
  have hA:= (G2_prod_summable1_δ z b).hasSum
  have ht := hA.comp verga
  simp at *
  apply ht


theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
  ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)) := by
  conv =>
      enter [1]
      intro d
      rw [telescope_aux ]
  apply Filter.Tendsto.cauchySeq (x := 0)
  have h1 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) := by
    have := tendstozero_inv_linear z (-b)
    rw [← tendsto_const_smul_iff₀ (c := (-1 : ℂ) ) ] at this
    simp at *
    apply this.congr
    intro x
    rw [neg_inv]
    congr
    ring
    norm_cast
  have h2 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z + ↑d)) atTop (𝓝 0) := by
    apply tendstozero_inv_linear z b
  have := Filter.Tendsto.sub h1 h2
  simpa using this

/-This is proven in the modular forms repo. -/
lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by sorry

lemma extracted_77 (z : ℍ) (n : ℤ) : Summable fun b : ℤ ↦ (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  have := (G2_summable_aux (-n) ⟨-1 /z, by simpa using pnat_div_upper 1 z⟩  2 (by norm_num)).mul_left ((z : ℂ)^2)⁻¹
  apply this.congr
  intro b
  simp only [UpperHalfPlane.coe, Int.cast_neg, neg_mul]
  field_simp
  norm_cast
  congr 1
  rw [← mul_pow]
  congr
  have hz := ne_zero z --this come our with a coe that should be fixed
  simp only [UpperHalfPlane.coe, ne_eq] at hz
  field_simp
  ring


theorem extracted_4 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹))
  have hA:= (G2_summable_aux b z 2 (by norm_num)).hasSum
  have ht := hA.comp verga
  simp at *
  apply ht

theorem extracted_5 (z : ℍ) (b : ℤ) :
  CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z - ↑n) ^ 2 ) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z - ↑x) ^ 2)⁻¹))
  have haa := summable_neg _ (G2_summable_aux b z 2 (by norm_num))
  have hA:= (haa).hasSum
  have ht := hA.comp verga
  simp at *
  have := ht.congr' (f₂ := fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z - ↑n) ^ 2 )) ?_
  simp at this
  apply this
  apply Filter.Eventually.of_forall
  intro N
  simp
  congr

lemma auxr (z : ℍ) (b : ℤ):
    ((limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n)) +
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1))) =
    limUnder atTop fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2) := by
  have := limUnder_add (f := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1))+ δ b n))
    (g := fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-N : ℤ) N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)))
      (extracted_2_δ z b) (by apply extracted_3 z b)
  rw [this]
  apply limUnder_congr_eventually _ _ _
    (by apply CauchySeq.add (extracted_2_δ z b) (extracted_3 z b)) (by apply extracted_4 z b)
  simp only [one_div, mul_inv_rev, Pi.add_apply, eventually_atTop,
    ge_iff_le]
  use 1
  intro c hc
  rw [← Finset.sum_add_distrib ]
  congr
  ext n
  apply  poly_id z b n



--this sum is now abs convergent. Idea is to subtract PS1 from the G₂ defn.
lemma G2_alt_eq (z : ℍ) : G₂ z = ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
    rw [G₂]
    have :=  PS2 z
    set t :=  ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n)
    rw [show t = t + 0 by ring, ← this]
    simp only [t]
    rw [← tsum_add]
    · rw [aux3]
      · congr
        ext n
        congr
        ext m
        rw [aux3, aux3, auxr z m]
        · have H := G2_prod_summable1_δ z m
          simpa using H
        · have H := G2_summable_aux m z 2 (by norm_num)
          simpa using H
      · have H := G_2_alt_summable_δ z
        rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
        have ha := H.prod
        apply ha.congr
        intro b
        simpa using PS1 z b
    · have H := G_2_alt_summable_δ z
      rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
      have ha := H.prod
      apply ha.congr
      intro b
      simp only [Fin.isValue, one_div, mul_inv_rev, finTwoArrowEquiv_symm_apply, comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · have HS : Summable fun m : ℤ => (0 : ℂ) := by apply summable_zero
      apply HS.congr
      intro b
      symm
      apply PS1 z b


lemma CauchySeq.congr (f g : ℕ → ℂ) (hf : f = g) (hh : CauchySeq g) : CauchySeq f := by
  rw [hf]
  exact hh

theorem extracted_66 (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp
  rw [@Finset.mul_sum]
  rw [tsum_sum]
  congr
  ext n
  rw [← tsum_mul_left]
  rw [int_sum_neg]
  congr
  ext d
  have hz := ne_zero z
  rw [← neg_ne_zero] at hz
  rw [← mul_inv]
  congr 1
  rw [show ((d : ℂ) * ↑z + ↑n) ^ 2 = (-↑d * ↑z - ↑n) ^ 2 by ring, ← mul_pow]
  congr
  field_simp
  simp only [UpperHalfPlane.coe]
  ring
  · intro i hi
    exact extracted_77 z i


theorem extracted_66c (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp
  rw [@Finset.mul_sum]
  rw [tsum_sum]
  congr
  ext n
  rw [← tsum_mul_left]
  rw [int_sum_neg]
  congr
  ext d
  have hz := ne_zero z
  rw [← neg_ne_zero] at hz
  rw [← mul_inv]
  congr 1
  rw [show ((d : ℂ) * ↑z + ↑n) ^ 2 = (-↑d * ↑z - ↑n) ^ 2 by ring, ← mul_pow]
  congr
  field_simp
  simp only [UpperHalfPlane.coe]
  ring
  · intro i hi
    exact extracted_77 z i



lemma G2_S_act (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) =  limUnder (atTop)
    fun N : ℕ => ((∑' (n : ℤ), ∑ m in Finset.Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) := by
  rw [ modular_S_smul]
  simp [G₂]
  rw [ limUnder_mul_const]
  congr
  simpa using extracted_66 z
  · apply CauchySeq_Icc_iff_CauchySeq_Ico
    intro d
    rw [int_sum_neg]
    congr
    ext n
    simp only [UpperHalfPlane.coe, Int.cast_neg, neg_mul, inv_inj]
    ring
    have := G2_cauchy ⟨-(1 : ℂ) / z, by simpa using pnat_div_upper 1 z⟩
    simp only [coe_mk_subtype, one_div] at this
    apply this.congr
    ext N
    congr
    ext m
    congr
    ext n
    congr 1
    simp only [UpperHalfPlane.coe]
    have hz := ne_zero z
    rw [← neg_ne_zero] at hz
    field_simp
    ring

theorem extracted_6 (z : ℍ) : CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-(N : ℤ)) ↑N,
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) := by
  have := PS3tn22 z
  apply Filter.Tendsto.cauchySeq
  apply pnat_tendsto_nat
  apply this

lemma cauchy_seq_mul_const (f : ℕ → ℂ) (c : ℂ) (hc  : c ≠ 0) :
  CauchySeq f → CauchySeq (c • f) := by
  intro hf
  rw [Metric.cauchySeq_iff' ] at *
  simp only [ne_eq, gt_iff_lt, ge_iff_le, Pi.smul_apply, smul_eq_mul] at *
  intro ε hε
  have hcc : 0 < ‖c‖ := by
    simp only [norm_eq_abs, AbsoluteValue.pos_iff, ne_eq, hc, not_false_eq_true]
  have hC : 0 < Complex.abs c := by
    simp only [AbsoluteValue.pos_iff, ne_eq, hc, not_false_eq_true]
  have H := hf (ε / ‖c‖) (by simp; rw [lt_div_iff₀' hC]; simp [hε] )
  obtain ⟨N, hN⟩ := H
  use N
  intro n hn
  have h1 := hN n hn
  simp only [dist_eq_norm, norm_eq_abs, AbsoluteValue.pos_iff, ne_eq, gt_iff_lt] at *
  rw [← mul_sub]
  simp only [AbsoluteValue.map_mul]
  rw [lt_div_iff₀' (by simp [hc])] at h1
  exact h1

lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  rw [G2_S_act, ← PS3 z, aux3, limUnder_sub]
  congr
  ext N
  simp only [one_div, Pi.sub_apply, mul_inv_rev]
  rw [tsum_sum, ← Finset.sum_sub_distrib ]
  congr
  ext n
  rw [← tsum_sub]
  congr
  ext m
  have := poly_id z m n
  nth_rw 1 [← this]
  simp only [add_sub_cancel_right]
  · exact extracted_77 z n
  · simpa only [one_div] using (summable_pain z n)
  · intro i hi
    exact extracted_77 z i
  · conv =>
      enter [1]
      ext N
      rw [tsum_sum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    apply CauchySeq_Icc_iff_CauchySeq_Ico
    intro n
    nth_rw 2 [int_sum_neg]
    congr
    ext m
    simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
    ring
    conv =>
      enter [1]
      ext N
      rw [← tsum_sum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    have := G2_cauchy ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
    have  hC := cauchy_seq_mul_const _ ((z : ℂ) ^ 2)⁻¹ (by simp [ne_zero z]) this
    apply hC.congr
    have H := extracted_66c z
    simp at *
    rw [← H]
    ext N
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    left
    congr
    ext n
    congr
    ext m
    congr
    ring
  · apply extracted_6
  · have := G_2_alt_summable_δ z
    simp only [Fin.isValue, one_div, mul_inv_rev] at this
    rw [← swap_equiv.summable_iff, ← (finTwoArrowEquiv _).symm.summable_iff] at this
    have ht := Summable.prod this
    simp only [Fin.isValue, swap_equiv, Equiv.coe_fn_mk, finTwoArrowEquiv_symm_apply, comp_apply,
      swap_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_zero, one_div, mul_inv_rev] at *
    exact ht

lemma G2_transf_aux (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  G₂ z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

def G₂_a : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m in Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

lemma rest (f g : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) (hfg : Tendsto (g - f) atTop (𝓝 0)) :
  Tendsto g atTop (𝓝 x) := by
  have := Tendsto.add hf hfg
  simp at this
  exact this

lemma G₂_eq_G₂_a (z : ℍ) : G₂ z = G₂_a z := by
  rw [G₂]
  rw [G₂_a]
  rw [Filter.Tendsto.limUnder_eq]
  have := CauchySeq.tendsto_limUnder  (G2_cauchy z)
  apply rest _ _ _ this
  have h0 := cc _  (G2_cauchy z) ?_
  conv =>
    enter [1]
    ext N
    simp
    rw [sum_Icc_eq_sum_Ico_succ _ (by omega)]
    simp
  have := Filter.Tendsto.neg h0
  simp only [one_div, neg_zero] at this
  have := int_tendsto_nat this
  apply this
  · intro n
    nth_rw 2 [int_sum_neg]
    congr
    ext m
    simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
    ring



lemma G2_q_exp (z : ℍ) : G₂ z = (2 * riemannZeta 2)  - 8 * π ^ 2 *
  ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
  rw [G₂_eq_G₂_a, G₂_a, Filter.Tendsto.limUnder_eq]
  rw [t8 z]
  rw [sub_eq_add_neg]
  apply Filter.Tendsto.add
  · simp only [tendsto_const_nhds_iff]
  · have := G2_c_tendsto z
    simp only [UpperHalfPlane.coe, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one,
      Nat.factorial_one, Nat.cast_one, div_one, pow_one] at *
    apply this

lemma exp_periodo (z : ℍ) (n : ℕ) :
  cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) := by
  rw [mul_add]
  have :=  exp_periodic.nat_mul n
  rw [Periodic] at this
  have ht := this (2 * π * Complex.I * n * z)
  rw [← ht]
  congr 1
  ring

lemma G2_periodic :  (G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂ := by
  ext z
  simp only [SL_slash, slash_def, slash, ModularGroup.det_coe, ofReal_one, Int.reduceSub, zpow_one,
    mul_one, Int.reduceNeg, zpow_neg]
  have := UpperHalfPlane.modular_T_smul z
  rw [ModularGroup.sl_moeb] at this
  rw [this, ModularGroup.denom_apply]
  simp only [G2_q_exp, coe_vadd, ofReal_one, ModularGroup.T, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.head_fin_const, Int.cast_zero, zero_mul, Matrix.head_cons,
    Int.cast_one, zero_add, one_zpow, inv_one, mul_one, sub_right_inj, mul_eq_mul_left_iff,
    mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero,
    false_or]
  left
  congr
  ext n
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
  left
  apply exp_periodo

def E₂ : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G₂

/-This is being PRd-/
lemma SL2_gens : Subgroup.closure {ModularGroup.S, ModularGroup.T} = ⊤ := by sorry

/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by sorry

/--This we should get from the modular forms repo stuff. Will port these things soon. -/
lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+),
    ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E₂]
  simp
  rw [G2_q_exp]
  rw [mul_sub]
  congr 1

  sorry
  rw [← mul_assoc]
  congr 1

  sorry
  sorry

def D₂ (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma ModularGroup.coe_mul (A B : SL(2, ℤ)) :
    (ModularGroup.coe A) * B = ModularGroup.coe (A * B) := by
  have : Matrix.SpecialLinearGroup.toGLPos ∘ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) = ModularGroup.coe := by
    funext A
    rfl
  let C := MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ))
  have hC : C = ModularGroup.coe := by
    rw [← this]
    rfl
  have := C.map_mul A B
  rw [hC] at this
  exact this.symm

lemma denom_diff (A B : SL(2,ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
  (A 1 0) * B.1.det + (B 1 0) * denom (A* B) z := by
  rw [ModularGroup.coe_mul A B]
  simp_rw [ModularGroup.denom_apply]
  have h0 := Matrix.two_mul_expl A.1 B.1
  have h1 := Matrix.det_fin_two B.1
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul,
    h1, Int.cast_sub, h0.2.2.2]
  ring

lemma D2_mul (A B : SL(2,ℤ)) : D₂ (A * B) = ((D₂ A) ∣[(2 : ℤ)] B) + (D₂ B):= by
  ext z
  have := denom_cocycle A B z
  have hab : (A : GL(2,ℝ)⁺) * B = ((A * B) : SL(2, ℤ)) := by
    apply ModularGroup.coe_mul A B
  simp only [D₂, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, SL_slash, slash_def, Pi.add_apply,
    slash, ModularGroup.det_coe, ofReal_one, Int.reduceSub, zpow_one, mul_one, Int.reduceNeg,
    zpow_neg]
  simp_rw [← mul_div, mul_assoc, ← mul_add]
  congr
  have hde : denom B z ≠ 0 := by exact denom_ne_zero (↑B) z
  field_simp [hde]
  have hd := denom_diff A B z
  rw [ ← sub_eq_iff_eq_add] at hd
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.det_coe,
    Int.cast_one, mul_one] at hd
  simp only [Fin.isValue, ← hab, this, ← hd, zpow_two]
  rw [sub_mul, sub_div, ← mul_assoc,  ← mul_assoc]
  simp_rw [mul_div_mul_right _ _ hde ]
  have : B • z = smulAux B z := by
    rfl
  simp only [Fin.isValue, ← this, ModularGroup.sl_moeb]
  rw [ mul_div_cancel_right₀]
  ring
  exact denom_ne_zero (↑A) (↑B • z)

lemma D2_one : D₂ 1 = 0 := by
  ext z
  simp only [D₂, Fin.isValue, Matrix.SpecialLinearGroup.coe_one, ne_eq, one_ne_zero,
    not_false_eq_true, Matrix.one_apply_ne, Int.cast_zero, mul_zero, zero_div, Pi.zero_apply]

lemma D2_inv (A : SL(2,ℤ)) : (D₂ A)∣[(2 : ℤ)] A⁻¹ = - D₂ (A⁻¹) := by
  have := D2_mul A A⁻¹
  simp only [mul_inv_cancel, SL_slash] at this
  rw [D2_one] at this
  apply eq_neg_of_add_eq_zero_left (_root_.id (Eq.symm this))

lemma D2_T : D₂ ModularGroup.T = 0 := by
  ext z
  simp [D₂, ModularGroup.T]

lemma D2_S (z : ℍ) : D₂ ModularGroup.S z = 2 * (π : ℂ) * Complex.I / z := by
  simp [D₂, ModularGroup.S, ModularGroup.denom_apply]


variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)
theorem modular_slash_S_apply :
    (f ∣[k] ModularGroup.S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash, slash_def, slash, ← ModularGroup.sl_moeb, modular_S_smul]
  simp [denom, ModularGroup.S]


theorem modular_slash_T_apply : (f ∣[k] ModularGroup.T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash, slash_def, slash, ← ModularGroup.sl_moeb, modular_T_smul]
  simp [denom, ModularGroup.T]


/-This is the annoying exercise. -/
lemma G₂_transform (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ):= by
  have := Subgroup.closure_induction (G := SL(2, ℤ)) (p := fun γ _ ↦ G₂ ∣[(2 : ℤ)] γ = G₂ - (D₂ γ))
    (k := ({ModularGroup.S, ModularGroup.T})) ?_ ?_
  apply this
  · intro a b ha hb HA HB
    rw [D2_mul, SlashAction.slash_mul, HA, sub_eq_add_neg, SlashAction.add_slash, HB]
    ext z
    simp only [SlashAction.neg_slash, SL_slash, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  · intro g hg hg2
    have H1 : (G₂ ∣[(2 : ℤ)] g)  ∣[(2 : ℤ)] g⁻¹ = (G₂ - D₂ g)∣[(2 : ℤ)] g⁻¹ := by
      rw [hg2]
    rw [←  SlashAction.slash_mul, sub_eq_add_neg, SlashAction.add_slash] at H1
    simp only [mul_inv_cancel, SlashAction.slash_one, SL_slash, SlashAction.neg_slash] at H1
    nth_rw 2 [H1]
    rw [← sub_eq_add_neg]
    have := D2_inv g
    simp only [SL_slash] at this
    rw [this]
    simp only [SL_slash, sub_neg_eq_add, add_sub_cancel_right]
  · rw [SL2_gens]
    simp only [Subgroup.mem_top]
  · intro a ha
    simp only [mem_insert_iff, mem_singleton_iff, SL_slash] at *
    rcases ha with h1|h2
    · ext z
      simp only [Pi.sub_apply]
      rw [h1, D2_S z]
      have:= modular_slash_S_apply G₂ 2 z
      simp only [SL_slash, Int.reduceNeg, zpow_neg] at this
      rw [this, mul_comm]
      have := G2_transf_aux z
      rw [← this]
      ring_nf
      rw [modular_S_smul]
      congr
      simp only [UpperHalfPlane.coe, inv_pow, inv_inj]
      norm_cast
      simp only [UpperHalfPlane.coe]
      ring
    · simpa only [h2, D2_T, sub_zero] using G2_periodic
  · simp only [SlashAction.slash_one, D2_one, sub_zero]


/-Should be easy from the above.-/
lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
  E₂ z + 6 / ( π * Complex.I * z) := sorry


/-this is being PRd-/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n ≠ 0) : Multipliable (fun n : ℕ => 1 + f n) := by sorry

lemma MultipliableDiscriminantProductExpansion (z : ℍ) :
  Multipliable (fun  (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) := by
  sorry

lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ) := by
  have := Complex.summable_nat_multipliable_one_add (fun (n : ℕ) => (-cexp (2 * π * Complex.I * (n + 1) * z)) ) ?_ ?_
  simp at this
  apply this.congr
  intro n
  ring
  sorry
  intro n
  simp

  sorry

lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z)) ) := by
  conv =>
    enter [1]
    ext n
    rw [sub_eq_add_neg]
  let g := (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * n * z)) )
  have := MultipliableEtaProductExpansion z
  conv at this =>
    enter [1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  rw [← nat_pos_tprod2' g ] at this
  apply this.congr
  intro b
  rfl

/-this is being PRd-/
lemma prod_tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} (K : Set α)
    (hK : IsCompact K) (u : ℕ → ℝ) (hu : Summable u) (h : ∀ n x, x ∈ K → (‖(f n x)‖) ≤ u n)
    (hfn : ∀ x : K, ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by sorry

/- variable {ι κ α : Type*}
variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι → α}

@[to_additive]
theorem le_hasProd_of_le_prod_ev [ClosedIciTopology α]
    (hf : HasProd f a) (h : ∀ᶠ s : Finset ι in atTop, c ≤ ∏ i ∈ s, f i)  : c ≤ a :=
  ge_of_tendsto hf h

@[to_additive]
theorem le_hasProd_of_le_prod_ev_range [ClosedIciTopology α] [T2Space α] (f : ℕ → α) (hm : Multipliable f)
    (hf : HasProd f a) (h : ∀ᶠ s : ℕ in atTop, c ≤ ∏ i ∈ Finset.range s, f i)  : c ≤ a := by
  rw [Multipliable.hasProd_iff_tendsto_nat hm] at hf
  apply ge_of_tendsto hf h -/


/-Being Prd-/
lemma Complex.log_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by sorry

lemma tprod_ne_zero (x : ℂ) (f : ℕ → ℂ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : ℂ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0 := by
  have := Complex.cexp_tsum_eq_tprod (fun n => fun x => 1 + f n x) ?_ ?_
  have hxx := congrFun this x
  simp
  rw [← hxx]
  simp only [comp_apply, exp_ne_zero, not_false_eq_true]
  intro n z
  simp
  apply hf
  intro x
  simp
  apply Complex.log_of_summable
  apply hu x


theorem logDeriv_tprod_eq_tsumb  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend :TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    rw [← Complex.cexp_tsum_eq_tprod]
    rw [logDeriv]
    simp
    rw [deriv_comp]
    simp
    rw [deriv_tsum ]
    simp
    congr
    ext n


    all_goals{sorry}

theorem logDeriv_tprod_eq_tsum  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ) (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend :TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have := logDeriv_tendsto (fun n ↦ ∏ i ∈ Finset.range n, (f i)) g (s := s) hs (p := atTop)
    simp [g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply HT.congr
    intro m
    congr
    ext i
    simp only [Finset.prod_apply]
    exact htend
    use 0
    intro b hb
    rw [DifferentiableOn]
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hp : ∀ (i : ℕ), i ∈ Finset.range b →  DifferentiableAt ℂ (f i) z := by
      intro i hi
      have := (hd i z hz).differentiableAt
      apply this
      exact IsOpen.mem_nhds hs hz
    have := DifferentiableAt.finset_prod hp
    convert this
    simp only [Finset.prod_apply]
    · exact hnez




    --DifferentiableAt.finset_prod
    --logDeriv_tendsto

    --Summable.hasSum_iff_tendsto_nat




lemma MultipliableDiscriminantProductExpansion2 : Multipliable (fun (z : UpperHalfPlane) =>
  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) := by
    --I dont think we mean this
    sorry


/- /- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
def η (z : ℂ) := cexp (2 * π * Complex.I * z / 24) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * n * z)) -/

/- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
def η (z : ℂ) := cexp (2 * π * Complex.I * z / 24) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z))

lemma aux47 (r : ℂ) (hr : ‖r‖ < 1) : Tendsto (fun n : ℕ => 1 - r^n) atTop (𝓝 1) := by
  rw [show (1 : ℂ) = 1 - 0 by ring]
  apply Filter.Tendsto.sub
  simp
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr

lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  rw [logDeriv]
  simp only [Pi.div_apply, differentiableAt_const, differentiableAt_exp, DifferentiableAt.mul,
    deriv_sub, deriv_const', deriv_mul, zero_mul, Complex.deriv_exp, zero_add, zero_sub, neg_mul]

lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw  [logDeriv_comp, logDeriv_one_sub_exp]
  simp only [neg_mul]
  ring
  simp only [differentiableAt_const, differentiableAt_exp, DifferentiableAt.mul,
    DifferentiableAt.sub]
  exact hg y

lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  have := aux47 r hr
  have h1 : Tendsto (fun n : ℕ => (1 : ℂ)) atTop (𝓝 1) := by simp
  have h2 := Filter.Tendsto.div h1 this (by simp)
  rw [Metric.tendsto_atTop] at h2
  simp only [gt_iff_lt, ge_iff_le, Pi.div_apply, one_div, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, dist_eq_norm] at h2
  have h3 := h2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (fun n => 2 * ‖n * r^n‖)
  apply Summable.mul_left
  simp
  · have := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)
    simp at this
    apply this
  · simp
    obtain ⟨N, hN⟩ := h3
    use N
    intro n hn
    have h4 := hN n hn
    have := norm_lt_of_mem_ball h4 (E := ℂ)
    simp at *
    rw [div_eq_mul_inv]
    rw [mul_comm]
    gcongr
    apply le_trans this.le
    norm_cast

lemma eta_tndntunif : TendstoLocallyUniformlyOn (fun n ↦ ∏ x ∈ Finset.range n,
    fun x_1 ↦ 1 + -cexp (2 * ↑π * Complex.I *  (↑x + 1) * x_1))
    (fun x ↦ ∏' (i : ℕ), (1 + -cexp (2 * ↑π * Complex.I * (↑i + 1) * x))) atTop {x | 0 < x.im} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  intro K hK hK2
  by_cases hN : ¬ Nonempty K
  rw [@not_nonempty_iff_eq_empty'] at hN
  rw [hN]
  exact tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by
    fun_prop
  have := IsCompact.exists_sSup_image_eq_and_ge hK2 (by simpa using hN) hc
  obtain ⟨z, hz, hB, HB⟩ := this
  have :=  prod_tendstoUniformlyOn_tprod'  K  hK2 (f := (fun i ↦
    fun x_1 ↦ -cexp (2 * ↑π * Complex.I *  (i + 1) * x_1))) (fun n=> ‖cexp (2 * ↑π * Complex.I * z)^(n + 1)‖) ?_ ?_ ?_ ?_
  simp at *
  convert this
  simp
  · simp_rw [norm_pow]
    rw [summable_nat_add_iff 1]
    simp
    apply  exp_upperHalfPlane_lt_one ⟨z, by simpa using (hK hz)⟩
  · intro n
    intro x hx
    simp only [norm_neg]
    rw [show 2 * ↑π * Complex.I * (↑n + 1) * x = (n+1)* (2 * ↑π * Complex.I  * x) by ring ]
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
    rw [Complex.exp_nat_mul]
    have HB2 := HB x hx
    simp_rw [norm_pow]
    apply pow_le_pow_left₀ _  HB2
    simp only [norm_eq_abs, apply_nonneg]
  · intro x hx
    sorry
  · intro n
    fun_prop
  ·
    sorry

theorem eta_tprod_ne_zero (z : ℍ) :
  ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z)) ≠ 0 := by
  simp_rw [sub_eq_add_neg]
  have := tprod_ne_zero z (fun n x => -cexp (2 * ↑π * Complex.I * (n + 1) * x)) ?_ ?_
  simp at *
  apply this
  intro i x
  simp
  sorry
  sorry

lemma eta_nonzero_on_UpperHalfPlane (z : ℍ) : η z ≠ 0 := by
  rw [η]
  have := eta_tprod_ne_zero z
  simp at *
  apply this

lemma exp_aux (z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * n * ↑z) =
    cexp (2 * ↑π * Complex.I * ↑z) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring


lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ,
    (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  have :=  fun m : ℕ => tsum_choose_mul_geometric_of_norm_lt_one  (r := (cexp (2 * ↑π * Complex.I * ↑z))^(m+1)) 0 (by sorry)
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, pow_one,
    one_div] at this
  conv =>
    enter [1,1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp only [Nat.cast_add, Nat.cast_one],
      exp_aux, div_eq_mul_one_div]
    simp
    rw [← this n, ← tsum_mul_left]
    conv =>
      enter [1]
      ext m
      rw [mul_assoc, ← pow_succ' (cexp (2 * ↑π * Complex.I * ↑z) ^ (n + 1)) m ]
  have := tsum_sigma_eqn z (k := 1)
  conv =>
    enter [2,1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  have h1 := tsum_pnat_eq_tsum_succ3 (fun n => sigma 1 (n) * cexp (2 * π * Complex.I * (n) * z))
  simp only [UpperHalfPlane.coe] at *
  rw [← h1]
  have h2 := fun n : ℕ => tsum_pnat_eq_tsum_succ3
    ( fun m => ↑(n + 1) * (cexp (2 * ↑π * Complex.I * ↑z) ^ (n + 1)) ^ (m))
  simp only [UpperHalfPlane.coe] at h2
  conv =>
    enter [1,1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp only [Nat.cast_add, Nat.cast_one], ← h2 n]
    conv =>
      enter [1]
      ext m
      rw [pow_right_comm]
  have h3 := tsum_pnat_eq_tsum_succ3
      (fun n ↦ ∑' (m : ℕ+), ↑(n) * (cexp (2 * ↑π * Complex.I * ↑z) ^ (m : ℕ)) ^ (n))
  simp only [UpperHalfPlane.coe] at h3
  rw [← h3, ← this]
  simp only [pow_one]
  rw [tsum_prod' ]
  congr
  ext n
  congr
  ext m
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  ring
  · sorry --these sorrys are done in the mod forms repo
  · sorry

lemma tsum_log_deriv_eqn (z : ℍ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ↑z  =  ∑' n : ℕ,
    -(2 * ↑π * Complex.I * (↑n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) := by
  congr
  ext i
  have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
  have h1 := fun i : ℕ => logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
  have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
  have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_mul]
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
        deriv_add, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_id']
  rw [h2 i, h1 i, h3 i]
  simp

lemma logDeriv_z_term (z : ℍ) : logDeriv (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) ↑z  = 2* ↑π * Complex.I / 24 := by
  have : (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z)  := by
    ext y
    simp
    congr
    ring
  rw [this, logDeriv_comp, deriv_const_mul]
  simp only [LogDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]
  · fun_prop
  · fun_prop
  · fun_prop

theorem eta_differentiableAt (z : ℍ) :
  DifferentiableAt ℂ (fun z ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z))) ↑z := by
  have hD := eta_tndntunif.differentiableOn ?_ ?_
  simp_rw [sub_eq_add_neg]
  rw [DifferentiableOn] at hD
  have hDz := (hD z (by apply z.2)).differentiableAt
  apply hDz
  · apply IsOpen.mem_nhds  (isOpen_lt continuous_const Complex.continuous_im)
    apply z.2
  · simp
    use 0
    intro b hb
    have := DifferentiableOn.finset_prod (u := Finset.range b)
      (f := fun i : ℕ => fun x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
      (s := {x : ℂ | 0 < x.im}) ?_
    · apply this.congr
      intro x hx
      simp [sub_eq_add_neg]
    · intro i hi
      fun_prop
  · apply isOpen_lt continuous_const Complex.continuous_im

lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ η z := by
  unfold η
  apply DifferentiableAt.mul
  · conv =>
      enter [2]
      rw [show (fun z => cexp (2 * ↑π * Complex.I * z / 24)) = cexp ∘ (fun z => 2 * ↑π * Complex.I * z / 24) by rfl]
    apply DifferentiableAt.cexp
    fun_prop
  · apply eta_differentiableAt

lemma eta_logDeriv (z : ℍ) : logDeriv η z = (π * Complex.I / 12) * E₂ z := by
  unfold η
  rw [logDeriv_mul]
  have HG := logDeriv_tprod_eq_tsum (s := {x : ℂ | 0 < x.im}) ?_ z
    (fun (n : ℕ) => fun (x : ℂ) => 1 - cexp (2 * π * Complex.I * (n + 1) * x)) ?_ ?_ ?_ ?_ ?_
  simp only [mem_setOf_eq, UpperHalfPlane.coe] at *
  rw [HG]
  · have := tsum_log_deriv_eqn z
    have h0 := logDeriv_z_term z
    simp only [UpperHalfPlane.coe] at *
    rw [this, E₂, h0]
    simp
    rw [G2_q_exp]
    rw [riemannZeta_two]
    conv =>
      enter [1,2,1]
      ext n
      rw [show  -(2 * ↑π * Complex.I * (↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
        (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) =
        (-2 * ↑π * Complex.I) * (((↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
        (1 - cexp (2 * ↑π * Complex.I * (n + 1) * z.1))) by ring]
    rw [tsum_mul_left (a := -2 * ↑π * Complex.I)]
    have := tsum_eq_tsum_sigma z
    simp only [UpperHalfPlane.coe] at *
    rw [this, mul_sub]
    rw [sub_eq_add_neg, mul_add]
    congr 1
    · have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      ring_nf
      field_simp
      ring
    · ring_nf
      rw [show ↑π * Complex.I * (1 / 12) *
        -((↑π ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8 *
        ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1))) =
        (↑π * Complex.I * (1 / 12) * -((↑π ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8)) *
        ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1)) by ring]
      congr 1
      have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      field_simp
      ring
      conv =>
        enter [1,1]
        ext n
        rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
      have hl := tsum_pnat_eq_tsum_succ3
        (fun n ↦ ↑((σ 1) (n)) * cexp (↑π * Complex.I * 2 * (↑n) * ↑z))
      simp only [UpperHalfPlane.coe] at hl
      rw [← hl]
  · exact isOpen_lt continuous_const Complex.continuous_im
  · intro i
    simp only [mem_setOf_eq, ne_eq]
    rw [@sub_eq_zero]
    intro h
    have j := exp_upperHalfPlane_lt_one_nat z i
    simp only [UpperHalfPlane.coe] at *
    rw [← h] at j
    simp at j
  · intro i x hx
    fun_prop
  · simp only [mem_setOf_eq]
    have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
    have h1 := fun i : ℕ => logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
    have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
    have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_mul]
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
        deriv_add, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_id']
    conv =>
      enter [1]
      ext i
      rw [h2 i, h1 i, h3 i]
    simp only [neg_mul, one_mul]
    conv =>
      enter [1]
      ext i
      rw [mul_assoc, neg_div, ← mul_div]
    apply Summable.neg
    apply Summable.mul_left
    have hS := logDeriv_q_expo_summable (cexp (2 * ↑π * Complex.I * ↑z))
      (by simpa only [norm_eq_abs] using exp_upperHalfPlane_lt_one z)
    rw [← summable_nat_add_iff 1] at hS
    apply hS.congr
    intro b
    congr
    simp only [Nat.cast_add, Nat.cast_one]
    · rw [← Complex.exp_nsmul]
      simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf
    · rw [← Complex.exp_nsmul]
      simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf
  · simp_rw [sub_eq_add_neg]
    apply eta_tndntunif
  · exact eta_tprod_ne_zero z
  · simp only [ne_eq, exp_ne_zero, not_false_eq_true]
  · exact eta_tprod_ne_zero z
  · fun_prop
  · apply eta_differentiableAt


end Definitions

noncomputable section Holomorphicity

-- Try and get the desired holomorphicity results for φ₀, φ₂ and φ₄ in terms of the Eᵢ

end Holomorphicity

noncomputable section Integrability

-- Here, we show that

end Integrability

open Complex Real

lemma deriv_eq_iff (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv f = deriv g ↔ ∃z, f = g + (fun _ => z) := by
  constructor
  intro h
  rw [← sub_eq_zero] at h
  have h0 := fun z => congrFun h z
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  have h2 := is_const_of_deriv_eq_zero (f := f - g)
  simp only [Pi.sub_apply] at *
  use f 1 - g 1
  ext x
  simp only [Pi.add_apply]
  have h43 := h2 ?_ ?_ x 1
  rw [← h43]
  simp only [add_sub_cancel]
  apply Differentiable.sub hf hg
  · intro t
    have h1 :=  deriv_sub (f := f) (g := g) (x := t) ?_ ?_
    have h2 := h0 t
    rw [← h2]
    have h3 : f - g = fun y => f y - g y := by rfl
    rw [h3]
    exact h1
    · exact hf.differentiableAt (x := t)
    · exact hg.differentiableAt (x := t)
  intro h
  obtain ⟨z, hz⟩ := h
  rw [hz]
  have ht : g + (fun _ => z) = fun x => g x + (fun _ => z) x := by rfl
  rw [ht]
  simp only [deriv_add_const']

lemma func_div_ext (a b c d : ℂ → ℂ) (hb : ∀ x, b x ≠ 0) (hd : ∀ x, d x ≠ 0) :
     a / b = c /d ↔ a * d = b * c := by
  constructor
  intro h
  have h0 := fun z => congrFun h z
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  ext x
  have h1 := h0 x
  simp only [Pi.div_apply] at h1
  have e1 := hb x
  have e2 := hd x
  simp only [Pi.mul_apply]
  rw [div_eq_div_iff] at h1
  nth_rw 2 [mul_comm]
  exact h1
  exact e1
  exact e2
  intro h
  ext x
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  have hj := congrFun h x
  simp only [Pi.mul_apply] at hj
  nth_rw 2 [mul_comm]
  exact hj
  apply hb x
  apply hd x

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd :  d x ≠ 0) :
     (a / b) x = (c /d) x ↔ (a * d) x = (b * c) x := by
  constructor
  intro h
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  simp only [Pi.mul_apply]
  simp only [Pi.div_apply] at h
  rw [div_eq_div_iff] at h
  nth_rw 2 [mul_comm]
  exact h
  exact hb
  exact hd
  intro h
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  simp only [Pi.mul_apply] at h
  nth_rw 2 [mul_comm]
  exact h
  apply hb
  apply hd


lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) ( deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]
  rw [← derivWithin_of_isOpen hs hx]
  apply derivWithin_congr hfg
  apply hfg hx

lemma logDeriv_eqOn_iff (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hs : s.Nonempty) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s →  g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) : EqOn (logDeriv f) (logDeriv g) s ↔
    ∃( z : ℂ),  z ≠ 0 ∧  EqOn (f) (z • g) s := by
  constructor
  simp_rw [logDeriv]
  intro h
  rw [@nonempty_def] at hs
  obtain ⟨t, ht⟩ := hs
  use (f t) * (g t)⁻¹
  refine ⟨by apply mul_ne_zero (hfn t ht) (by simpa using (hgn t ht)) , ?_⟩
  intro y hy
  have h2 := h hy
  rw [func_div] at h2
  have hderiv : EqOn (deriv (f * g⁻¹))  (deriv f * g⁻¹ - f * deriv g / g ^ 2) s := by
    have hfg : f * g⁻¹ = fun x => f x * (g⁻¹ x) := by rfl
    rw [hfg]
    intro z hz
    rw [deriv_mul]
    have hgi : g⁻¹ = (fun x => x⁻¹) ∘ g := by
      ext y
      simp only [Pi.inv_apply, comp_apply]
    rw [hgi, deriv_comp, deriv_inv]
    simp only [comp_apply, neg_mul, mul_neg, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring
    · refine differentiableAt_inv ?_
      exact hgn z hz
    · apply hg.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
    · exact hf.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
    · apply DifferentiableAt.inv
      exact hg.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
      exact hgn z hz
  have H3 := Convex.is_const_of_fderivWithin_eq_zero (f := f * g⁻¹) (𝕜 := ℂ) (s := s) ?_ ?_ ?_ hy ht
  simp only [Pi.mul_apply, Pi.inv_apply] at H3
  rw [← H3]
  field_simp [hgn y hy]
  · exact hsc
  · apply DifferentiableOn.mul
    exact hf
    apply DifferentiableOn.inv
    exact hg
    exact hgn
  have he : s.EqOn  (deriv f * g⁻¹ - f * deriv g / g ^ 2)  0 := by
    intro z hz
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply, Pi.zero_apply]
    have hgg : g z ≠ 0 := by apply hgn z hz
    field_simp
    rw [pow_two, mul_comm, mul_assoc, ← mul_sub]
    simp only [mul_eq_zero]
    right
    have H := h hz
    rw [func_div] at H
    simp only [Pi.mul_apply] at H
    rw [← H]
    ring
    exact hfn z hz
    exact hgn z hz
  intro v hv
  have H := h hv
  rw [func_div] at H
  have ha := hderiv hv
  have hb := he hv
  rw [hb] at ha
  simp only [deriv, fderiv, Pi.zero_apply] at ha
  split_ifs at ha with hc hd
  apply HasFDerivWithinAt.fderivWithin
  apply HasFDerivAt.hasFDerivWithinAt
  have hc2 := hc.choose_spec
  convert hc2
  exact ContinuousLinearMap.ext_ring (_root_.id (Eq.symm ha))
  exact IsOpen.uniqueDiffWithinAt hs2 hv
  apply fderivWithin_zero_of_not_differentiableWithinAt
  intro ho
  obtain ⟨o, ho⟩ := ho
  have ho2 := ho.hasFDerivAt (by exact IsOpen.mem_nhds hs2 hv)
  aesop
  exact  hfn v hv
  exact  hgn v hv
  exact  hfn y hy
  exact hgn y hy
  · intro h
    obtain ⟨z, hz0, hz⟩ := h
    intro x hx
    have h := hz hx
    simp_rw [logDeriv_apply]
    have HJ := deriv_EqOn_congr s hz hs2 hx
    rw [HJ, h]
    nth_rw 1 [show z • g = fun x => z • g x by rfl]
    rw [deriv_const_smul]
    simp
    rw [mul_div_mul_left (deriv g x) (g x) hz0]
    exact hg.differentiableAt (x := x) (IsOpen.mem_nhds hs2 hx)


noncomputable def csqrt : ℂ → ℂ :=  (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a)))

lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z:= by
  have :  (fun a ↦ cexp (1 / 2 * Complex.log a)) =  cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp
  have hzz : ↑z ∈ slitPlane := by
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only [UpperHalfPlane.coe] at hz
    exact Ne.symm (ne_of_lt hz)
  rw [this, deriv_comp]
  simp
  rw [Complex.exp_neg]
  field_simp
  rw [show cexp (Complex.log ↑z / 2) * deriv Complex.log ↑z * (2 * cexp (Complex.log ↑z / 2)) = cexp (Complex.log ↑z / 2) * (cexp (Complex.log ↑z / 2)) * 2 * deriv Complex.log ↑z by ring]
  rw [← Complex.exp_add]
  ring_nf
  rw [Complex.exp_log]
  have hl := (Complex.hasDerivAt_log (z := z) hzz).deriv
  rw [hl]
  field_simp [ne_zero z]
  · apply ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  apply Complex.differentiableAt_log
  rw [@mem_slitPlane_iff]
  right
  have hz := z.2
  simp only [UpperHalfPlane.coe] at hz
  exact Ne.symm (ne_of_lt hz)

lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = ((z :ℂ)^(2 : ℤ))⁻¹ * (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    congr
    conv =>
      enter [1,1]
      intro z
      rw [neg_div]
      simp
    simp only [deriv.neg', deriv_inv', neg_neg, inv_inj]
    norm_cast
    · sorry
    conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    simp only [differentiableAt_id']
    exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  nth_rw 2 [logDeriv_apply]
  unfold csqrt
  have := csqrt_deriv z
  rw [this]
  simp only [one_div, neg_mul, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg, show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
   (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring, ← Complex.exp_add,
   ← sub_eq_add_neg, show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring, Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
  have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
  simp only [coe_mk_subtype] at Rb
  rw [Rb]
  have E := E₂_transform z
  simp only [one_div, neg_mul, smul_eq_mul, SL_slash, slash_def, slash, ← ModularGroup.sl_moeb,
    modular_S_smul, ModularGroup.det_coe, ofReal_one, Int.reduceSub, zpow_one, mul_one,
    ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
  have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    simp [UpperHalfPlane.mk]
    ring_nf
  rw [h00] at E
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  simp only [UpperHalfPlane.coe] at *
  rw [E, add_mul, add_comm]
  congr 1
  have hzne := ne_zero z
  have hI : Complex.I ≠ 0 := by
    exact I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact pi_ne_zero
  simp [UpperHalfPlane.coe] at hzne ⊢
  field_simp
  ring
  rw [mul_comm]
  · simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · unfold csqrt
    rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
    apply DifferentiableAt.comp
    simp
    apply DifferentiableAt.const_mul
    apply Complex.differentiableAt_log
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only [UpperHalfPlane.coe] at hz
    exact Ne.symm (ne_of_lt hz)
  · apply eta_DifferentiableAt_UpperHalfPlane z

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql ⟨z, hz⟩
  exact this

lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩
    · apply DifferentiableOn.div
      fun_prop
      fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp at *
      rw [neg_div, neg_neg_iff_pos]
      exact this
  · apply DifferentiableOn.mul
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · use UpperHalfPlane.I
    simp only [coe_I, mem_setOf_eq, Complex.I_im, zero_lt_one]
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply eta_nonzero_on_UpperHalfPlane ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := eta_nonzero_on_UpperHalfPlane ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
    simpa only [ne_eq, coe_mk_subtype] using this

lemma csqrt_I : (csqrt (Complex.I)) ^ 24  = 1 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_log]
  have hi4 := Complex.I_pow_four
  have : Complex.I ^ 12 = (Complex.I ^ 4) ^ 3 :=by
    rw [← @npow_mul]
  rw [this, hi4]
  simp
  exact I_ne_zero

lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log hz]


lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const
  obtain ⟨z, hz, h⟩ := h
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    have h:=  eta_nonzero_on_UpperHalfPlane UpperHalfPlane.I
    convert h
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2

noncomputable section  Product_Formula


/- The discriminant form -/
def Δ (z : UpperHalfPlane) :=  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

lemma Multipliable_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) :
     Multipliable (fun i => f i ^ n) := by
  induction' n with n hn
  · simp
    apply multipliable_one
  · conv =>
      enter [1]
      intro u
      rw [pow_succ]
    apply Multipliable.mul hn hf

lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) : (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ), (f i) ^ n := by
  induction' n with n hn
  · simp
  · rw [pow_succ]
    rw [hn]
    rw [← tprod_mul]
    congr
    apply Multipliable_pow f hf n
    exact hf

lemma Δ_eq_η_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  rw [η, Δ, mul_pow]
  congr
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp
  rw [tprod_pow]
  apply MultipliableEtaProductExpansion



/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
def φ₀ (z : UpperHalfPlane) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
def φ₂' (z : UpperHalfPlane) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
def φ₄' (z : UpperHalfPlane) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0


/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Δ_eq_η_pow]
  simpa using eta_nonzero_on_UpperHalfPlane z



/-This one is easy.-/
lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [ modular_slash_T_apply, Δ, Δ]
  simp only [coe_vadd, ofReal_one]
  have h1 : cexp (2 * ↑π * Complex.I * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * (↑z)) := by
    simpa using exp_periodo z 1
  rw [h1]
  simp only [mul_eq_mul_left_iff, Complex.exp_ne_zero, or_false]
  apply tprod_congr
  intro b
  have := exp_periodo z (b+1)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]


/-This is the hard one. -/
lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [ modular_slash_S_apply, Δ_eq_η_pow, Δ_eq_η_pow]
  have he := eta_equality z.2
  simp only [comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, UpperHalfPlane.coe_mk,
    Int.reduceNeg, zpow_neg] at *
  have hi :  -1/(z.1 : ℂ) = (-(z : ℂ))⁻¹ := by
    rw [neg_div]
    rw [← neg_inv]
    simp [UpperHalfPlane.coe]
  rw [hi] at he
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_I]
  simp only [inv_one, one_mul, UpperHalfPlane.coe]
  rw [mul_comm]
  have hzz := csqrt_pow_24 z.1 (ne_zero z)
  rw [hzz, ← mul_assoc]
  have hz := ne_zero z
  simp only [UpperHalfPlane.coe, ne_eq] at hz
  norm_cast
  field_simp

-- use E₂_transform

/-this is from other file-/
theorem slashaction_generators_SL2Z
    (f : ℍ → ℂ) (k : ℤ) (hS : f ∣[k] ModularGroup.S = f) (hT : f ∣[k] ModularGroup.T = f) :
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) := by sorry

def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' A := by
    intro hA
    exact slashaction_generators_SL2Z Δ 12 (Discriminant_S_invariant) (Discriminant_T_invariant) A

open Manifold in
lemma Discriminant_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Discriminant_SIF := sorry

instance : atImInfty.NeBot := by
  classical
  rw [atImInfty]
  rw [Filter.comap_neBot_iff ]
  simp
  intro t x hx

  sorry

lemma arg_pow_aux (n : ℕ) (x : ℂ) (hx : x ≠ 0) (hna : |arg x| < π / n) :
  Complex.arg (x ^ n) = n * Complex.arg x := by
  induction' n with n hn2
  simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul]
  by_cases hn0 : n = 0
  · simp only [hn0, zero_add, pow_one, Nat.cast_one, one_mul]
  · rw [pow_succ, arg_mul, hn2, Nat.cast_add]
    ring
    apply lt_trans hna
    gcongr
    exact (lt_add_one n)
    apply pow_ne_zero n hx
    exact hx
    simp
    rw [hn2]
    rw [abs_lt] at hna
    constructor
    · have hnal := hna.1
      rw [← neg_div] at hnal
      rw [div_lt_iff₀' ] at hnal
      · rw [@Nat.cast_add, add_mul] at hnal
        simpa only [gt_iff_lt, Nat.cast_one, one_mul] using hnal
      · norm_cast
        omega
    · have hnal := hna.2
      rw [lt_div_iff₀'  ] at hnal
      rw [@Nat.cast_add] at hnal
      · rw [add_mul] at hnal
        simpa only [ge_iff_le, Nat.cast_one, one_mul] using hnal.le
      · norm_cast
        omega
    apply lt_trans hna
    gcongr
    exact (lt_add_one n)


lemma one_add_abs_half_ne_zero {x : ℂ} (hb : Complex.abs x < 1 / 2) : 1 + x ≠ 0 := by
  by_contra h
  rw [@add_eq_zero_iff_neg_eq] at h
  rw [← h] at hb
  simp at hb
  linarith

lemma arg_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  simp only [eventually_atTop, ge_iff_le]
  have hf1 := hf.const_add 1
  simp only [add_zero] at hf1
  have h2 := (Complex.continuousAt_arg (x := 1) ?_)
  rw [ContinuousAt] at *
  have h3 := h2.comp hf1
  simp only [arg_one] at h3
  rw [Metric.tendsto_nhds] at *
  simp only [gt_iff_lt, dist_zero_right, Complex.norm_eq_abs, eventually_atTop, ge_iff_le,
    dist_self_add_left, arg_one, Real.norm_eq_abs, comp_apply] at *
  by_cases hn0 : n = 0
  · rw [hn0]
    simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul, implies_true, exists_const]
  · have hpi : 0 < π / n := by
      apply div_pos
      exact pi_pos
      simp only [Nat.cast_pos]
      omega
    obtain ⟨a, hA⟩ := h3 (π / n) hpi
    obtain ⟨a2, ha2⟩ := hf (1/2) (one_half_pos)
    use max a a2
    intro b hb
    rw [arg_pow_aux n (1 + f b) ?_]
    apply hA b
    exact le_of_max_le_left hb
    have ha2 := ha2 b (le_of_max_le_right hb)
    simp only [ne_eq]
    apply one_add_abs_half_ne_zero ha2
  simp only [one_mem_slitPlane]


lemma clog_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  have h := arg_pow n f hf
  simp at *
  simp_rw [Complex.log]
  obtain ⟨a, ha⟩ := h
  use a
  intro b hb
  have h2 := ha b hb
  rw [h2]
  simp only [AbsoluteValue.map_pow, log_pow, ofReal_mul, ofReal_natCast]
  ring

lemma log_summable_pow (f : ℕ → ℂ)  (hf : Summable f)  (m : ℕ) :
    Summable (fun n => Complex.log ((1 + f n)^m)) := by
  have hfl := log_of_summable hf
  have := (Summable.mul_left m (f := (fun n => Complex.log (1 + f n))) hfl).norm
  apply Summable.of_norm_bounded_eventually_nat _ this
  have hft := hf.tendsto_atTop_zero
  have H := clog_pow m f hft
  simp at *
  obtain ⟨a, ha⟩ := H
  use a
  intro b hb
  apply le_of_eq
  rw [ha b hb]
  simp only [AbsoluteValue.map_mul, abs_natCast]


lemma Discriminant_zeroAtImInfty (γ : SL(2, ℤ)): IsZeroAtImInfty
    (Discriminant_SIF ∣[(12 : ℤ)] γ) := by
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have := Discriminant_SIF.slash_action_eq' γ (by  sorry)
  simp at *
  rw [this]
  simp [Discriminant_SIF]
  unfold Δ
  rw [show (0 : ℂ) =  0 * 1 by ring]
  apply Tendsto.mul
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_eq_abs, Complex.abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat,
      ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im,
      mul_one, sub_self, coe_re, coe_im, zero_sub, tendsto_exp_comp_nhds_zero,
      tendsto_neg_atBot_iff]
    rw [Filter.tendsto_const_mul_atTop_iff_pos ]

    sorry
    rw [atImInfty]


    sorry

  have := Complex.cexp_tsum_eq_tprod (fun n : ℕ => fun x : ℍ => (1 - (cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x))) ^ 24 ) ?_ ?_
  --have hxx := congrFun this x

  conv =>
    enter [1]
    rw [← this]
  apply Tendsto.comp (y := (𝓝 0))
  refine Continuous.tendsto' ?_ 0 1 ?_
  exact Complex.continuous_exp
  exact Complex.exp_zero
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (g := fun (x : ℕ) => (0 : ℂ))
      (f := (fun x : ℍ ↦ fun (n : ℕ) => Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * (x : ℂ))) ^ 24)))
      (bound := fun x => 1)
  simp at this
  apply this
  sorry
  sorry
  sorry
  sorry
  intro x
  simp
  have := log_summable_pow (fun n => -cexp (2 * ↑π * Complex.I * (↑n + 1) * x)) ?_ 24
  apply this.congr
  intro b
  rw [sub_eq_add_neg]
  simp
/-   conv =>
    enter [1]
    ext n
    conv =>
      enter [1]
      rw [sub_eq_add_neg]

    rw [Complex.log]
  simp -/
  --apply Complex.log_of_summable

/-   have := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (g := fun (x : ℍ) => (1 : ℂ))
      (f := (fun x : ℍ ↦ (∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * (x : ℂ))) ^ 24)))
      (bound := fun x => 1)   -/
  sorry

def CuspForm_div_Discriminant (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
  ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
    toFun := f  / Δ
    slash_action_eq' := sorry
    holo' := sorry --need to use the q-expansion to see that its still holo
    bdd_at_infty' := sorry


/-this is done in the modformdims repo, soon to be in mathlib.-/
lemma weigth_zero_rank_eq_one : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 0) = 1 :=
  by sorry

/-this is done in the modformdims repo, soon to be in mathlib.-/
lemma neg_weight_rank_zero (k : ℤ) (hk : k < 0) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by sorry

def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) := sorry

theorem DiscriminantProductFormula (z : UpperHalfPlane) : Δ z = ((E₄ z) ^ 3 - (E₆ z) ^ 2) / 1728 := sorry
--enough to check its a cuspform, since if it is, then divining by Δ gives a modular form of weight 0.

lemma weight_two_empty (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := sorry
/- cant be a cuspform from the above, so let a be its constant term, then f^2 = a^2 E₄ and
f^3 = a^3 E₆, but now this would mean that Δ = 0 or a = 0, which is a contradiction. -/

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℤ) (hk : 2 < k):
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := sorry

lemma dim_modforms_lvl_one (k : ℤ) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = if 12 ∣ k - 2 then
    Nat.floor (k / 12) else Nat.floor (k / 12) + 1 := sorry

lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry
--use the norm to turn it into a level one question.


end Product_Formula

#min_imports

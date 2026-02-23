module
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded

public import SpherePacking.ModularForms.Delta


/-!
# `q`-expansion for Eisenstein series

This file defines the normalized level-one Eisenstein series `E k` (for `k >= 3`) and proves a
`q`-expansion formula compatible with the conventions used in this repository.

## Main definitions
* `standardcongruencecondition`
* `E`

## Main statement
* `E_k_q_expansion`
-/
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

noncomputable section Definitions

/-- The standard congruence condition used to define Eisenstein series at level one. -/
@[expose] public def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

/-- The (normalized) Eisenstein series of weight `k` as a modular form on `Γ(1)`. -/
@[expose] public def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • ModularForm.eisensteinSeriesMF hk standardcongruencecondition -- normalization

open Pointwise

def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 1 0

private lemma one_lt_of_three_le (k : ℕ) (hk : 3 ≤ k) : 1 < k := by linarith

private lemma three_le_int_of_three_le (k : ℕ) (hk : 3 ≤ k) : (3 : ℤ) ≤ k := by
  exact_mod_cast hk

private lemma inv_zero_pow (k : ℕ) (hk : k ≠ 0) : ((0 : ℂ) ^ k)⁻¹ = 0 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨k, rfl⟩
  simp

private lemma inv_zero_pow_real (k : ℕ) (hk : k ≠ 0) : ((0 : ℝ) ^ k)⁻¹ = 0 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨k, rfl⟩
  simp

private lemma gammaSetN_exists (N : ℕ) (v : gammaSetN N) :
    ∃ w ∈ gammaSet 1 1 0, N • w = v.1 := by
  simpa [gammaSetN, singleton_smul, mem_smul_set] using v.2

def gammaSetN_map (N : ℕ) (v : gammaSetN N) : gammaSet 1 1 0 := by
  exact ⟨Classical.choose (gammaSetN_exists N v), (Classical.choose_spec (gammaSetN_exists N v)).1⟩

lemma gammaSet_top_mem (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  simpa using (EisensteinSeries.mem_gammaSet_one (v := v))

lemma gammaSetN_map_eq (N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetN_map N v := by
  simpa [gammaSetN_map] using (Classical.choose_spec (gammaSetN_exists N v)).2.symm

def gammaSetN_Equiv (N : ℕ) (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 1 0 where
  toFun v := gammaSetN_map N v
  invFun v := by
    use N • v
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    use v
    simp
  left_inv v := by
    simp_rw [← gammaSetN_map_eq N v]
  right_inv v := by
    let w : gammaSetN N := by
      refine ⟨N • v.1, ?_⟩
      simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
      exact ⟨v.1, v.2, rfl⟩
    ext i
    have hEq := congr_fun (gammaSetN_map_eq N w) i
    have : v.1 i = (gammaSetN_map N w).1 i := by
      simpa [Pi.smul_apply, nsmul_eq_mul, hN, w] using hEq
    simpa using this.symm

lemma gammaSetN_eisSummand (k : ℤ) (z : ℍ) (n : ℕ) (v : gammaSetN n) : eisSummand k v z =
  ((n : ℂ)^k)⁻¹ * eisSummand k (gammaSetN_map n v) z := by
  simp only [eisSummand, gammaSetN_map_eq n v, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, zpow_neg, ← mul_inv]
  congr
  rw [← mul_zpow]
  ring_nf

def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (Σn : ℕ, gammaSetN n) where
  toFun v := ⟨(v 0).gcd (v 1), ⟨(v 0).gcd (v 1) • ![(v 0)/(v 0).gcd (v 1), (v 1)/(v 0).gcd (v 1)],
    by
  by_cases hn : 0 < (v 0).gcd (v 1)
  · apply Set.smul_mem_smul
    · simp only [Fin.isValue, mem_singleton_iff]
    · rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
      apply Int.gcd_div_gcd_div_gcd hn
  simp only [Fin.isValue, not_lt, nonpos_iff_eq_zero] at hn
  rw [hn]
  simp only [singleton_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_smul, gammaSetN]
  use ![1,1]
  simp only [gammaSet_top_mem, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul,
    and_true]
  exact Int.isCoprime_iff_gcd_eq_one.mpr rfl ⟩⟩
  invFun v := v.2
  left_inv v := by
            ext i
            fin_cases i
            · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
            · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))
  right_inv v := by
    ext i
    · have hv2 := v.2.2
      simp only [gammaSetN, singleton_smul, mem_smul_set] at hv2
      obtain ⟨x, hx⟩ := hv2
      simp_rw [← hx.2]
      simp only [Fin.isValue, Pi.smul_apply, nsmul_eq_mul]
      have hg := hx.1.2
      rw [Int.gcd_mul_left, hg]
      omega
    · fin_cases i
      · refine Int.mul_ediv_cancel' ?_
        simp only [Fin.isValue]
        exact Int.gcd_dvd_left _ _
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one, Pi.smul_apply,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.nsmul_eq_mul]
        exact Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)


theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * (riemannZeta (k)) + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * (z : ℂ) + d) ^ k :=
  by
  have hkk : 1 < (k ) := by
    linarith
  have hkz : (3 : ℤ) ≤ k := three_le_int_of_three_le k hk
  have hSummableProd :
      Summable (fun x : ℤ × ℤ => 1 / ((x.1 : ℂ) * z + x.2) ^ k) := by
    rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    apply Summable.of_norm
    refine (EisensteinSeries.summable_norm_eisSummand hkz z).congr ?_
    intro v
    simp_rw [eisSummand]
    simp only [Fin.isValue, zpow_neg, zpow_natCast, norm_inv, norm_pow, one_div,
      piFinTwoEquiv_apply, comp_apply]
  rw [Summable.tsum_prod, sum_int_even]
  · simp only [Int.cast_zero, zero_mul, zero_add, one_div, Int.cast_natCast, add_left_inj]
    rw [sum_int_even]
    · have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hk)
      have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := inv_zero_pow k hk0
      have h00 : ((0 : ℝ) ^ k)⁻¹ = 0 := inv_zero_pow_real k hk0
      norm_cast at *
      rw [h0]
      simp only [PNat.pow_coe, Nat.cast_pow, zero_add, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
        or_false]
      norm_cast
      simp only [PNat.pow_coe, Nat.cast_pow]
      rw [zeta_nat_eq_tsum_of_gt_one hkk, ← tsum_pNat _ (by simp; omega)]
      simp only [one_div]
    · intro n
      simp only [Int.cast_neg, inv_inj]
      rw [Even.neg_pow hk2]
    have := (Complex.summable_one_div_nat_cpow (p := k)).mpr (by simp [hkk])
    simp only [one_div] at *
    norm_cast at *
    apply Summable.of_nat_of_neg_add_one
    · apply this.congr
      intro b
      simp
    rw [← summable_nat_add_iff 1] at this
    apply this.congr
    intro b
    congr
    rw [Even.neg_pow hk2]
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Int.cast_pow, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
  · intro n
    simp only [one_div, Int.cast_neg, neg_mul]
    apply symm
    rw [int_sum_neg]
    congr
    funext d
    simp only [Int.cast_neg, inv_inj]
    ring_nf
    have := Even.neg_pow hk2 (n* (z : ℂ) + d)
    rw [←this]
    ring
  · simpa using hSummableProd.prod
  · exact hSummableProd

lemma EQ0 (k : ℕ) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k := by
  rw [← (piFinTwoEquiv fun _ => ℤ).tsum_eq]
  apply tsum_congr
  intro x
  simp

lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
     ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by
  rw [EQ0, q_exp_iden_2 k (by linarith) hk2]
  simp only [one_div, neg_mul, add_right_inj]
  have h1 (c : ℕ+) := q_exp_iden k (by linarith) (c • z)
  simp only [natPosSMul_apply, one_div] at *
  conv =>
    enter [1,2,1]
    ext c
    rw [h1 c]
  rw [tsum_mul_left]
  rw [← mul_assoc]
  congr 1
  · ring_nf
  rw [Summable.tsum_comm]
  · rw [← tsum_sigma_eqn2]
    rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq]
    simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
    rw [Summable.tsum_prod (h := by
      simpa [Function.uncurry, mul_assoc, mul_left_comm, mul_comm] using (a4 k z))]
    refine tsum_congr fun b => ?_
    refine tsum_congr fun c => ?_
    congr 1
    ring_nf
  · simpa [Function.uncurry, mul_assoc, mul_left_comm, mul_comm] using (a4 k z)


lemma EQ22 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), eisSummand k x z =
    (riemannZeta (k)) * ∑' (c : gammaSet 1 1 0), eisSummand k c z := by
  rw [← GammaSet_one_Equiv.symm.tsum_eq]
  have hk1 : 1 < k := one_lt_of_three_le k (by exact_mod_cast hk)
  have hr := zeta_nat_eq_tsum_of_gt_one hk1
  rw [Summable.tsum_sigma, GammaSet_one_Equiv, hr, tsum_mul_tsum_of_summable_norm (by simp [hk1])
    (by apply(EisensteinSeries.summable_norm_eisSummand hk z).subtype) ]
  · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, Int.nsmul_eq_mul,
      Matrix.smul_empty, Equiv.coe_fn_symm_mk, one_div]
    rw [Summable.tsum_prod' ]
    · apply tsum_congr
      intro b
      by_cases hb : b = 0
      · rw [hb]
        simp only [CharP.cast_eq_zero]
        conv =>
          enter [2,1]
          ext c
          rw [show ((0 : ℂ)^ k)⁻¹ = 0 by simp; omega]
          simp
        conv =>
          enter [1,1]
          ext c
          rw [gammaSetN_eisSummand k z, show (((0 : ℕ) : ℂ)^ (k : ℤ))⁻¹ = 0 by simp; omega]
          simp
        simp
      conv =>
        enter [1,1]
        ext c
        rw [gammaSetN_eisSummand k z]
      have := (gammaSetN_Equiv b hb).tsum_eq (fun v => eisSummand k v z)
      simp_rw [tsum_mul_left]
      simp only [zpow_natCast, mul_eq_mul_left_iff, inv_eq_zero, pow_eq_zero_iff', Nat.cast_eq_zero,
        ne_eq]
      left
      exact this
    · apply summable_mul_of_summable_norm (f := fun (n : ℕ) => ((n : ℂ)^k)⁻¹)
        (g := fun (v : (gammaSet 1 1 0) ) => eisSummand k v z)
      · simp only [norm_inv, norm_pow, norm_natCast, Real.summable_nat_pow_inv, hk1]
      apply (EisensteinSeries.summable_norm_eisSummand hk z).subtype
    intro b
    simp only
    apply Summable.mul_left
    apply Summable.of_norm
    apply (EisensteinSeries.summable_norm_eisSummand hk z).subtype
  have := (GammaSet_one_Equiv.symm.summable_iff ( f := fun v => eisSummand k v z)).mpr ?_
  · apply this.congr
    intro b
    simp
  exact (EisensteinSeries.summable_norm_eisSummand hk z).of_norm

lemma EQ2 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) : ∑' x : Fin 2 → ℤ,
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = riemannZeta k * ∑' c : gammaSet 1 1 0,
    1 / ((c.1 0) * (z : ℂ) + (c.1 1)) ^ k := by
  simpa [eisSummand, zpow_neg, zpow_natCast, one_div] using (EQ22 k hk z)


/-- `q`-expansion formula for `E k`, specialized to the conventions used in this repository. -/
public lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [E]
  rw [ModularForm.IsGLPos.smul_apply]
  have : (ModularForm.eisensteinSeriesMF hk standardcongruencecondition) z =
    (eisensteinSeriesSIF standardcongruencecondition k) z := rfl
  rw [this]
  rw [eisensteinSeriesSIF_apply]
  rw [eisensteinSeries, standardcongruencecondition]
  simp only [one_div, PNat.val_ofNat, smul_eq_mul, neg_mul]
  simp_rw [eisSummand]
  have inv_pow_eq_zpow_neg (a : ℂ) : (a ^ k)⁻¹ = a ^ (- (k : ℤ)) := by
    have hk' : a ^ k = a ^ (k : ℤ) := (zpow_natCast a k).symm
    calc
      (a ^ k)⁻¹ = (a ^ (k : ℤ))⁻¹ := congrArg (fun t => t⁻¹) hk'
      _ = a ^ (- (k : ℤ)) := (zpow_neg a (k : ℤ)).symm
  have HE1' := EQ1 k hk hk2 z
  simp only [one_div, inv_pow_eq_zpow_neg] at HE1'
  have HE2' := EQ2 k hk z
  have z2 : (riemannZeta (k)) ≠ 0 := by
    have hk1 : (1 : ℝ) < (k : ℂ).re := by
      simpa using (one_lt_of_three_le k (by exact_mod_cast hk))
    exact riemannZeta_ne_zero_of_one_lt_re hk1
  rw [← inv_mul_eq_iff_eq_mul₀ z2 ] at HE2'
  simp only [one_div, inv_pow_eq_zpow_neg] at HE2'
  conv =>
    enter [1,2]
    rw [← HE2']
  simp_rw [← mul_assoc]
  rw [HE1', mul_add]
  have : 2⁻¹ * (riemannZeta (k))⁻¹ * (2 * riemannZeta (k)) = 1 := by
    field_simp
  rw [this]
  ring

end Definitions

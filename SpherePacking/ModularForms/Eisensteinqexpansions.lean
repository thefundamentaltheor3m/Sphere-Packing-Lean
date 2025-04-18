import Mathlib
import SpherePacking.ModularForms.summable_lems
import SpherePacking.ModularForms.Delta

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

open Pointwise

def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 0

def gammaSetN_map (N : ℕ) (v : gammaSetN N) : gammaSet 1 0 := by
  have hv2 := v.2
  simp [gammaSetN] at hv2
  rw [@mem_smul_set] at hv2
  use hv2.choose
  exact hv2.choose_spec.1

lemma gammaSet_top_mem (v : Fin 2 → ℤ)  : v ∈ gammaSet 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet]
  simp only [Fin.isValue, mem_setOf_eq, and_iff_right_iff_imp]
  intro h
  exact Subsingleton.eq_zero (Int.cast ∘ v)

lemma gammaSetN_map_eq (N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetN_map N v := by
  have hv2 := v.2
  simp [gammaSetN] at hv2
  rw [@mem_smul_set] at hv2
  have h1 := hv2.choose_spec.2
  exact h1.symm

def gammaSetN_Equiv (N : ℕ) (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 0 where
  toFun v := gammaSetN_map N v
  invFun v := by
    use N • v
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    use v
    simp
  left_inv v := by
    simp_rw [← gammaSetN_map_eq N v]
  right_inv v := by
    simp
    have H : N • v.1 ∈ gammaSetN N := by
      simp [gammaSetN]
      rw [@mem_smul_set]
      use v.1
      simp
    rw [gammaSetN]  at H
    simp at H
    rw [@mem_smul_set] at H
    simp at H
    let x := H.choose
    have hx := H.choose_spec
    have hxv : ⟨x, hx.1⟩   = v := by
      ext i
      have hhxi := congr_fun hx.2 i
      simp [hN] at hhxi
      exact hhxi
    simp_rw [← hxv]
    rw [gammaSetN_map]
    simp_all only [ne_eq, nsmul_eq_mul, x]

lemma gammaSetN_eisSummand (k : ℤ) (z : ℍ) (n : ℕ) (v : gammaSetN n) : eisSummand k v z =
  ((n : ℂ)^k)⁻¹ * eisSummand k (gammaSetN_map n v) z := by
  simp only [eisSummand, gammaSetN_map_eq n v, Fin.isValue, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, zpow_neg, ← mul_inv]
  congr
  rw [← mul_zpow]
  ring_nf

def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (Σn : ℕ, gammaSetN n) where
  toFun v := ⟨(v 0).gcd (v 1), ⟨(v 0).gcd (v 1) • ![(v 0)/(v 0).gcd (v 1), (v 1)/(v 0).gcd (v 1)], by
  by_cases hn : 0 < (v 0).gcd (v 1)
  apply Set.smul_mem_smul
  simp only [Fin.isValue, mem_singleton_iff]
  rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
  apply Int.gcd_div_gcd_div_gcd hn
  simp only [Fin.isValue, not_lt, nonpos_iff_eq_zero] at hn
  rw [hn]
  simp only [singleton_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_smul, gammaSetN]
  use ![1,1]
  simp only [gammaSet_top_mem, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, zero_smul, and_true]
  exact Int.isCoprime_iff_gcd_eq_one.mpr rfl ⟩⟩
  invFun v := v.2
  left_inv v := by
            ext i
            fin_cases i
            refine Int.mul_ediv_cancel' Int.gcd_dvd_left
            refine Int.mul_ediv_cancel' Int.gcd_dvd_right
  right_inv v := by
           ext i
           have hv2 := v.2.2
           simp only [gammaSetN, singleton_smul, mem_smul_set] at hv2
           obtain ⟨x, hx⟩ := hv2
           simp_rw [← hx.2]
           simp only [Fin.isValue, Pi.smul_apply, nsmul_eq_mul]
           have hg := hx.1.2
           rw [@Int.isCoprime_iff_gcd_eq_one] at hg
           rw [Int.gcd_mul_left, hg]
           omega
           fin_cases i
           refine Int.mul_ediv_cancel'  Int.gcd_dvd_left
           refine Int.mul_ediv_cancel' Int.gcd_dvd_right


theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * (riemannZeta (k)) + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * (z : ℂ) + d) ^ k :=
  by
  have hkk : 1 < (k ) := by
    linarith
  rw [tsum_prod, sum_int_even]
  · simp only [Int.cast_zero, zero_mul, zero_add, one_div, Int.cast_natCast, add_left_inj]
    rw [sum_int_even]
    simp  [algebraMap.coe_zero, Int.cast_ofNat, one_div]
    have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := by simp; omega
    have h00 : ((0 ^ k : ℕ) : ℝ)⁻¹ = 0 := by simp; omega
    norm_cast at *
    rw [h0]
    simp  [zero_add, mul_eq_mul_left_iff,  one_ne_zero]
    norm_cast
    simp only [PNat.pow_coe, Nat.cast_pow]
    rw [zeta_nat_eq_tsum_of_gt_one hkk, ← tsum_pnat_eq_tsum_succ4]
    simp only [CharP.cast_eq_zero, one_div, right_eq_add, inv_eq_zero, pow_eq_zero_iff', ne_eq,
      true_and]
    exact Nat.ne_zero_of_lt hk
    intro n
    simp only [Int.cast_neg, inv_inj]
    rw [Even.neg_pow hk2]
    have := (Complex.summable_one_div_nat_cpow  (p := k)).mpr (by simp [hkk])
    simp only [cpow_ofNat, one_div, re_ofNat, Nat.one_lt_ofNat, iff_true] at *
    norm_cast at *
    apply  Summable.of_nat_of_neg_add_one
    apply this.congr
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
    have := Even.neg_pow hk2 (n* (z : ℂ)  + d)
    rw [←this]
    ring
  · have hkz : 3 ≤ (k : ℤ) := by linarith
    have:= Summable.prod  (f := fun x : ℤ × ℤ => 1 / ((x.1 : ℂ) * z + x.2) ^ k) ?_
    apply this
    rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    apply Summable.of_norm
    apply (EisensteinSeries.summable_norm_eisSummand hkz z).congr
    intro v
    simp_rw [eisSummand]
    simp only [Fin.isValue, zpow_neg, zpow_natCast, norm_inv, norm_pow, UpperHalfPlane.coe, one_div,
      piFinTwoEquiv_apply, comp_apply]
  · have hkz : 3 ≤ (k : ℤ) := by linarith
    rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    apply Summable.of_norm
    apply (EisensteinSeries.summable_norm_eisSummand hkz z).congr
    intro v
    simp_rw [eisSummand]
    simp only [Fin.isValue, zpow_neg, zpow_natCast, norm_inv, norm_pow, UpperHalfPlane.coe, one_div,
      piFinTwoEquiv_apply, comp_apply]

lemma EQ0 (k : ℕ) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k := by
  rw [← (piFinTwoEquiv fun _ => ℤ).tsum_eq]
  apply tsum_congr
  intro x
  simp


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

lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
     ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by
  rw [EQ0,  q_exp_iden_2 k (by linarith) hk2]
  simp
  have h1 (c : ℕ+) := q_exp_iden k (by linarith) (c • z)
  simp [natPosSMul_apply] at *
  conv =>
    enter [1,2,1]
    ext c
    rw [h1 c]
  rw [tsum_mul_left]
  rw [← mul_assoc]
  congr 1
  rw [tsum_comm]
  rw [← tsum_sigma_eqn2]
  rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq]
  rw [tsum_prod']
  simp
  congr
  ext i
  congr
  ext j
  ring_nf
  simp
  rw [← sigmaAntidiagonalEquivProd.summable_iff]
  simp [sigmaAntidiagonalEquivProd]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp [mapdiv]
  simp
  intro b
  have A3 := a1 k b z
  exact A3
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp [sigmaAntidiagonalEquivProd, mapdiv]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp
  left
  ring_nf


lemma EQ22 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), eisSummand k x z =
    (riemannZeta (k)) * ∑' (c : gammaSet 1 0), eisSummand k c z := by
  rw [← GammaSet_one_Equiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  have hr := zeta_nat_eq_tsum_of_gt_one hk1
  rw [tsum_sigma, GammaSet_one_Equiv, hr, tsum_mul_tsum_of_summable_norm (by simp [hk1])
    (by apply(EisensteinSeries.summable_norm_eisSummand hk z).subtype)  ]
  simp
  rw [tsum_prod' ]
  apply tsum_congr
  intro b
  by_cases hb : b = 0
  rw [hb]
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
  have := summable_mul_of_summable_norm (f:= fun (n : ℕ)=> ((n : ℂ)^k)⁻¹ )
    (g := fun (v : (gammaSet 1 0) ) => eisSummand k v z)
  apply this
  simp only [norm_inv, norm_pow, norm_natCast, Real.summable_nat_pow_inv, hk1]
  apply (EisensteinSeries.summable_norm_eisSummand hk z).subtype
  intro b
  simp only
  apply Summable.mul_left
  apply Summable.of_norm
  apply  (EisensteinSeries.summable_norm_eisSummand hk z).subtype
  have := (GammaSet_one_Equiv.symm.summable_iff ( f := fun v => eisSummand k v z)).mpr ?_
  apply this.congr
  intro b
  simp
  apply (EisensteinSeries.summable_norm_eisSummand hk z).of_norm

lemma EQ2 (k : ℕ) (hk : 3 ≤ (k : ℤ))  (z : ℍ) : ∑' (x : Fin 2 → ℤ),
  1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = (riemannZeta (k)) * ∑' (c : gammaSet 1 0), 1 / ((c.1 0) * (z : ℂ) + (c.1 1)) ^ k := by
  have := EQ22 k hk z
  simp_rw [eisSummand] at this
  simp [ UpperHalfPlane.coe] at *
  convert this


/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [E]
  rw [ModularForm.smul_apply]
  have : (eisensteinSeries_MF hk standardcongruencecondition) z =
    (eisensteinSeries_SIF standardcongruencecondition k) z := rfl
  rw [this]
  have := eisensteinSeries_SIF_apply standardcongruencecondition k z
  rw [this, eisensteinSeries, standardcongruencecondition]
  simp
  simp_rw [eisSummand]
  have HE1 := EQ1 k hk hk2 z
  have HE2 := EQ2 k hk z
  have z2 : (riemannZeta (k)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp
    omega
  rw [← inv_mul_eq_iff_eq_mul₀ z2 ] at HE2
  simp [UpperHalfPlane.coe] at *
  conv =>
    enter [1,2]
    rw [← HE2]
  simp_rw [← mul_assoc]
  rw [HE1, mul_add]
  have : 2⁻¹ * (riemannZeta (k))⁻¹ * (2 * riemannZeta (k)) = 1 := by
    field_simp
  rw [this]
  ring

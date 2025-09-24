import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import SpherePacking.ModularForms.Cauchylems
import SpherePacking.ModularForms.limunder_lems
import SpherePacking.ModularForms.tendstolems


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups Matrix.SpecialLinearGroup

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Matrix.SpecialLinearGroup


open ArithmeticFunction

noncomputable section Definitions


/- Maybe this is the definition we want as I cant see how to easily show the other outer sum is
absolutely convergent. -/
def G₂ : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

def G₂_a : ℍ → ℂ := fun z => limUnder (atTop)
    (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, (∑' (n : ℤ), (1 / ((m : ℂ) * z + n) ^ 2)))

def E₂ : ℍ → ℂ := (1 / (2 * riemannZeta 2)) • G₂

@[coe]
abbrev coe2 (g : SL(2, ℤ)) : (GL (Fin 2) ℝ) :=
  Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)

instance : Coe SL(2, ℤ) (GL (Fin 2) ℝ) :=
  ⟨coe2⟩

lemma coe2_mul (A B : SL(2, ℤ)) :
     coe2 (A * B) = (coe2 A) * (coe2 B) := by
  simp_rw [coe2]
  simp only [map_mul]

def D₂ (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma D₂_apply (γ : SL(2, ℤ)) (z : ℍ) :
    D₂ γ z = (2 * π * Complex.I * γ 1 0) / (γ 1 0 * z + γ 1 1) :=
  by rfl

lemma extracted_77 (z : ℍ) (n : ℤ) : Summable fun b : ℤ ↦ (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  have := (
      G2_summable_aux (-n) ⟨-1 /z, by simpa using pnat_div_upper 1 z⟩ 2 (by norm_num)
    ).mul_left ((z : ℂ)^2)⁻¹
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

theorem extracted_66 (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Ico (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp
  rw [@Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left]
    rw [int_sum_neg]
    congr
    ext d
    have hz := ne_zero z
    rw [← mul_inv]
    congr 1
    rw [show ((d : ℂ) * ↑z + ↑n) ^ 2 = (-↑d * ↑z - ↑n) ^ 2 by ring, ← mul_pow]
    congr
    simp only [UpperHalfPlane.coe] at *
    rw [mul_add]
    field_simp
    ring
  · intro i hi
    exact extracted_77 z i

lemma G2_S_act (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) = limUnder (atTop)
    fun N : ℕ => ((∑' (n : ℤ), ∑ m ∈ Finset.Ico (-N : ℤ) N, (1 / ((n : ℂ) * z + m) ^ 2))) := by
  rw [ modular_S_smul]
  simp [G₂]
  rw [ limUnder_mul_const]
  · congr
    simpa using extracted_66 z
  · apply CauchySeq_Icc_iff_CauchySeq_Ico
    · intro d
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



/-This is from the modforms repo, so no need to prove it. -/
theorem series_eql' (z : ℍ) :
    ↑π * Complex.I - 2 * ↑π * Complex.I * ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * z * n) =
      1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
    have := EisensteinSeries_Identity z
    rw [this]
    congr
    ext n
    rw [← Complex.exp_nat_mul]
    ring_nf

theorem extracted_summable (z : ℍ) (n : ℕ+) : Summable fun m : ℕ ↦
    cexp (2 * ↑π * Complex.I * (-↑↑n / ↑z) * ↑m) := by
  have A1 := a1 1 1 ⟨ -n / z , pnat_div_upper n z⟩
  simp at A1
  apply A1

theorem tsum_exp_tendsto_zero (z : ℍ) :
    Tendsto (fun x : ℕ+ ↦ 2 / ↑z * 2 * ↑π * Complex.I *
    ∑' (n : ℕ), cexp (2 * ↑π * Complex.I * (-↑↑x / ↑z) * ↑n)) atTop (𝓝 (4 * ↑π * Complex.I / ↑z))
    := by
  rw [show 4 * ↑π * Complex.I / ↑z = 2 / ↑z * 2 * ↑π * Complex.I + 0 by ring]
  conv =>
    enter [1]
    ext n
    rw [← tsum_pnat_eq_tsum_succ4 _ (by apply extracted_summable z n), mul_add]
  simp only [CharP.cast_eq_zero, mul_zero, exp_zero, mul_one, add_zero]
  nth_rw 3 [
      show 2 / ↑z * 2 * ↑π * Complex.I =
        2 / ↑z * 2 * ↑π * Complex.I + 2 / ↑z * 2 * ↑π * Complex.I * 0 by ring
    ]
  apply Tendsto.add
  · simp only [tendsto_const_nhds_iff]
  apply Tendsto.mul
  · simp
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun (n : ℕ+) => (0 : ℂ))
    (f := fun d : ℕ+ => fun n : ℕ+ => cexp (2 * ↑π * Complex.I * (-↑↑d / ↑z) * n) )
    (bound := fun n : ℕ+ => (‖(cexp (2 * ↑π * Complex.I * (-1 / ↑z)))^ (Subtype.val n)‖))
  simp only [tsum_zero] at this
  apply this
  · have hs : Summable fun n : ℕ ↦ ‖cexp (2 * ↑π * Complex.I * (-1 / ↑z)) ^ n‖ := by
      simpa [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs] using
      (exp_upperHalfPlane_lt_one ⟨-1 / z, by simpa using (pnat_div_upper 1 z)⟩)
    apply Summable.subtype hs
  · intro k
    have : (fun x : ℕ+ ↦ cexp (2 * ↑π * Complex.I * (-↑↑(x : ℂ) / ↑z) * ↑k)) =
    (fun x : ℕ+ ↦ (cexp (2 * ↑π * Complex.I * (-↑↑(k : ℂ) / ↑z))) ^ (x : ℕ)) := by
      ext n
      rw [← exp_nsmul]
      congr
      simp only [nsmul_eq_mul]
      ring
    rw [this]
    have ht : Tendsto (fun x : ℕ ↦ cexp (2 * ↑π * Complex.I * (-↑k / ↑z)) ^ ↑x) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_pow, tendsto_pow_atTop_nhds_zero_iff, abs_norm]
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
    simp only [norm_pow, ge_iff_le]
    rw [← pow_mul]

    apply Bound.pow_le_pow_right_of_le_one_or_one_le ?_
    right
    constructor
    · apply norm_nonneg
    · have := exp_upperHalfPlane_lt_one ⟨- 1 / z, by simpa using (pnat_div_upper 1 z)⟩
      constructor
      · apply this.le
      exact Nat.le_mul_of_pos_right k hb


theorem extracted_12 (z : ℍ) :
    Tendsto (fun n : ℕ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))
    := by
  have : Tendsto (fun n : ℕ+ => (2 / (z : ℂ) * ∑' (m : ℕ+),
    (1 / (-(n : ℂ) / ↑z - ↑↑m) + 1 / (-↑↑n / ↑z + ↑↑m)))) atTop (𝓝 (-2 * ↑π * Complex.I / ↑z))
    := by
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
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-N / z) * n) - z / -N))) =
        (fun N : ℕ+ => ((2 / (z : ℂ)) * ↑π * Complex.I - ((2 / z) * 2 * ↑π * Complex.I *
          ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * (-N / z) * n)) - 2 / -N)) := by
        funext N
        have hz : 2 / -(N : ℂ) = (2 / z) * (z / -N) := by
          have : (z : ℂ) ≠ 0 := ne_zero z
          field_simp
        rw [hz]
        ring
    rw [h3]
    rw [show -2 * ↑π * Complex.I / ↑z = 2 * ↑π * Complex.I / ↑z - 4 * ↑π * Complex.I / ↑z - 0 by
      ring]
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
  · simp only [PNat.mk_coe, gt_iff_lt] at *
    exact HNN
  norm_cast

theorem PS3tn22 (z : ℍ) :
  Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N,
    ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1))) atTop
    (𝓝 (-2 * ↑π * Complex.I / ↑z)) := by
  have : (fun N : ℕ+ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) =
    (fun N : ℕ+ =>
    ∑' m : ℤ , ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)), (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)))
      := by
    ext n
    rw [Summable.tsum_finsetSum]
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
  · have : Tendsto (fun x : ℕ ↦ -2 / (x : ℂ)) atTop (𝓝 0) := by
        have := Filter.Tendsto.const_div_atTop (g := fun n : ℕ => ‖(n : ℂ)‖) (r := 2) (l := atTop)
          ?_
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
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    ∑' m : ℤ , (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = -2 * π * Complex.I / z := by
  apply Filter.Tendsto.limUnder_eq
  apply pnat_tendsto_nat
  apply PS3tn22


theorem poly_id (z : ℍ) (b n : ℤ) :
  ((b : ℂ) * ↑z + ↑n + 1)⁻¹ * (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ + (δ b n) +
    (((b : ℂ) * ↑z + ↑n)⁻¹ - ((b : ℂ) * ↑z + ↑n + 1)⁻¹) =
    (((b : ℂ) * ↑z + ↑n) ^ 2)⁻¹ := by
  by_cases h : b = 0 ∧ n = 0
  · rw [h.1, h.2]
    simp
  simp at h
  by_cases hb : b = 0
  · by_cases hn : n = -1
    · simp [hb, hn]
      ring
    have hj := h hb
    have hd : δ 0 n = 0 := by
      simp [δ, hj, hn]
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
    have := linear_ne_zero (cd := ![b, n + 1]) z h
    simp at this
    norm_cast at this
    rw [@AddSemigroup.add_assoc]
    aesop
  have h1 : ((b : ℂ) * ↑z + ↑n) ≠ 0 := by
    have := linear_ne_zero (cd := ![b, n]) z hh
    simpa using this
  field_simp [h0, h1]
  ring

theorem extracted_66c (z : ℍ) :
  (fun _ => ((z : ℂ) ^ 2)⁻¹) *
    (fun N : ℕ ↦ ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, ∑' (n : ℤ), (((x : ℂ) * (-↑z)⁻¹ + ↑n) ^ 2)⁻¹) =
  fun N : ℕ ↦
    ∑' (n : ℤ), ∑ x ∈ Finset.Icc (-↑N : ℤ) ↑N, (((n : ℂ) * ↑z + ↑x) ^ 2)⁻¹ := by
  ext N
  simp
  rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · congr
    ext n
    rw [← tsum_mul_left]
    rw [int_sum_neg]
    congr
    ext d
    have hz := ne_zero z
    rw [← mul_inv]
    congr 1
    rw [show ((d : ℂ) * ↑z + ↑n) ^ 2 = (-↑d * ↑z - ↑n) ^ 2 by ring, ← mul_pow]
    congr
    field_simp
    simp only [UpperHalfPlane.coe]
    ring
  · intro i hi
    exact extracted_77 z i

theorem extracted_6 (z : ℍ) : CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-(N : ℤ)) ↑N,
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) := by
  have := PS3tn22 z
  apply Filter.Tendsto.cauchySeq
  · apply pnat_tendsto_nat
    apply this

lemma G2_inde_lhs (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  rw [G2_S_act, ← PS3 z, tsum_limUnder_atTop, limUnder_sub]
  · congr
    ext N
    simp only [one_div, Pi.sub_apply, mul_inv_rev]
    rw [Summable.tsum_finsetSum, ← Finset.sum_sub_distrib ]
    · congr
      ext n
      rw [← Summable.tsum_sub]
      · congr
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
      rw [Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    apply CauchySeq_Icc_iff_CauchySeq_Ico
    · intro n
      nth_rw 2 [int_sum_neg]
      congr
      ext m
      simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
      ring
    conv =>
      enter [1]
      ext N
      rw [← Summable.tsum_finsetSum (by intro i hi; simp only [one_div]; exact extracted_77 z i)]
    have := G2_cauchy ⟨-1 / z, by simpa using pnat_div_upper 1 z⟩
    have hC := cauchy_seq_mul_const _ ((z : ℂ) ^ 2)⁻¹ (by simp [ne_zero z]) this
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
      swap_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
      Matrix.cons_val_zero, one_div, mul_inv_rev] at *
    exact ht

lemma PS1 (z : ℍ) (m : ℤ) : limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) = 0 := by
  apply Filter.Tendsto.limUnder_eq
  have : (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1))) =
    (fun N : ℕ => (1 / ((m : ℂ) * z - N) - 1 / (m * z + N))) := by
    funext N
    rw [telescope_aux]
  rw [this]
  have h0 := tendstozero_inv_linear z m
  have h1 := tendstozero_inv_linear_neg z m
  have h2 := Filter.Tendsto.sub h1 h0
  simpa using h2


lemma PS2 (z : ℍ) : ∑' m : ℤ, (limUnder atTop
  (fun N : ℕ => ∑ n ∈ (Finset.Ico (-(N : ℤ)) (N : ℤ)),
    (1 / ((m : ℂ) * z + n) - 1 / (m * z + n + 1)))) = 0 := by
    convert tsum_zero
    next m =>
    apply PS1

lemma auxr (z : ℍ) (b : ℤ) :
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
  apply poly_id z b n


--this sum is now abs convergent. Idea is to subtract PS1 from the G₂ defn.
lemma G2_alt_eq (z : ℍ) : G₂ z = ∑' m : ℤ, ∑' n : ℤ,
    (1 / (((m : ℂ) * z + n) ^ 2 * (m * z + n + 1)) + δ m n) := by
  rw [G₂]
  have := PS2 z
  set t := ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ) * z + n) ^ 2 * (m * z + n + 1)) + δ m n)
  rw [show t = t + 0 by ring, ← this]
  simp only [t]
  rw [← Summable.tsum_add]
  · rw [tsum_limUnder_atTop]
    · congr
      ext n
      congr
      ext m
      rw [tsum_limUnder_atTop, tsum_limUnder_atTop, auxr z m]
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
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · have HS : Summable fun m : ℤ => (0 : ℂ) := by apply summable_zero
    apply HS.congr
    intro b
    symm
    apply PS1 z b


lemma G2_transf_aux (z : ℍ) : (z.1 ^ 2)⁻¹ * G₂ (ModularGroup.S • z) - -2 * π * Complex.I / z =
  G₂ z := by
  rw [G2_inde_lhs, G2_alt_eq z , ← G2_alt_indexing2_δ , G2_alt_indexing_δ]

lemma ModularGroup.coe_mul (A B : SL(2, ℤ)) :
    (ModularGroup.coe A) * B = ModularGroup.coe (A * B) := by
  have : Matrix.SpecialLinearGroup.toGLPos ∘ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) =
    ModularGroup.coe := by
    funext A
    rfl
  let C := MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ))
  have hC : C = ModularGroup.coe := by
    rw [← this]
    rfl
  have := C.map_mul A B
  rw [hC] at this
  exact this.symm

lemma denom_diff (A B : SL(2, ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
  (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  simp_rw [← map_mul]
  simp_rw [ModularGroup.denom_apply]
  have h0 := Matrix.two_mul_expl A.1 B.1
  have h1 := Matrix.det_fin_two B.1
  simp [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul,
    h1, Int.cast_sub, h0.2.2.2]
  ring


@[simp]
lemma denom_sim (A : SL(2, ℤ)) (z : ℍ) :
    denom (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)) z = denom (coe2 A) z := by
      rfl

@[simp]
lemma coe2_smul (A : SL(2, ℤ)) (z : ℍ) :
  (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) A)) • z = (coe2 A) • z := by rfl

lemma D2_mul (A B : SL(2, ℤ)) : D₂ (A * B) = ((D₂ A) ∣[(2 : ℤ)] B) + (D₂ B):= by
  ext z
  have := denom_cocycle A B z.im_ne_zero
  simp_rw [SL_slash_def]
  simp_rw [denom_sim]
  simp only [D₂, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Int.reduceNeg, zpow_neg,
    Pi.add_apply]
  simp_rw [coe2_mul]
  simp_rw [← mul_div, mul_assoc, ← mul_add]
  congr
  simp
  have hde : denom B z ≠ 0 := by exact denom_ne_zero (↑B) z
  field_simp [hde]
  have hd := denom_diff A B z
  rw [ ← sub_eq_iff_eq_add] at hd
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.det_coe,
    Int.cast_one, mul_one] at hd
  simp only [Fin.isValue, ← hd, this, zpow_two]
  rw [sub_mul, sub_div, ← mul_assoc, ← mul_assoc]
  simp_rw [mul_div_mul_right _ _ hde ]
  have : denom (↑A) (num ↑B ↑z / denom ↑B ↑z) = denom ↑A ↑(↑B • z) := by
    congr 1
    simp [UpperHalfPlane.specialLinearGroup_apply]
    congr
  rw [this]
  simp
  rw [ mul_div_cancel_right₀]
  · ring
  exact denom_ne_zero (↑A) (↑B • z)



lemma D2_one : D₂ 1 = 0 := by
  ext z
  simp only [D₂, Fin.isValue, Matrix.SpecialLinearGroup.coe_one, ne_eq, one_ne_zero,
    not_false_eq_true, Matrix.one_apply_ne, Int.cast_zero, mul_zero, zero_div, Pi.zero_apply]

lemma D2_inv (A : SL(2, ℤ)) : (D₂ A)∣[(2 : ℤ)] A⁻¹ = - D₂ (A⁻¹) := by
  have := D2_mul A A⁻¹
  simp only [mul_inv_cancel, SL_slash] at this
  rw [D2_one] at this
  apply eq_neg_of_add_eq_zero_left (_root_.id (Eq.symm this))


lemma D2_T : D₂ ModularGroup.T = 0 := by
  ext z
  simp [D₂, ModularGroup.T]

lemma D2_S (z : ℍ) : D₂ ModularGroup.S z = 2 * (π : ℂ) * Complex.I / z := by
  simp [D₂, ModularGroup.S, ModularGroup.denom_apply]

/-This is being PRd-/
lemma SL2_gens : Subgroup.closure {ModularGroup.S, ModularGroup.T} = ⊤ := by
  exact SpecialLinearGroup.SL2Z_generators


variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)
theorem modular_slash_S_apply :
    (f ∣[k] ModularGroup.S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]
  simp [ModularGroup.S]



theorem modular_slash_T_apply : (f ∣[k] ModularGroup.T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul]
  simp [ModularGroup.T]



lemma G₂_eq_G₂_a (z : ℍ) : G₂ z = G₂_a z := by
  rw [G₂]
  rw [G₂_a]
  rw [Filter.Tendsto.limUnder_eq]
  have := CauchySeq.tendsto_limUnder (G2_cauchy z)
  apply rest _ _ _ this
  have h0 := cc _ (G2_cauchy z) ?_
  conv =>
    enter [1]
    ext N
    simp
    rw [sum_Icc_eq_sum_Ico_succ _ (by omega)]
    simp
  · have := Filter.Tendsto.neg h0
    simp only [one_div, neg_zero] at this
    have := int_tendsto_nat this
    apply this
  · intro n
    nth_rw 2 [int_sum_neg]
    congr
    ext m
    simp only [one_div, Int.cast_neg, neg_mul, inv_inj]
    ring

lemma G2_q_exp (z : ℍ) : G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
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

lemma G2_periodic : (G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂ := by
  ext z
  simp only [ SL_slash_def, Int.reduceNeg, zpow_neg]
  have := UpperHalfPlane.modular_T_smul z
  rw [this, ModularGroup.denom_apply]
  simp only [G2_q_exp, coe_vadd, ofReal_one, ModularGroup.T, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Int.cast_zero, zero_mul,
    Int.cast_one, zero_add, one_zpow, inv_one, mul_one, sub_right_inj, mul_eq_mul_left_iff,
    mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero,
    false_or]
  left
  congr
  ext n
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
  left
  apply exp_periodo

/-This is the annoying exercise. -/
lemma G₂_transform (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ) := by
  have := Subgroup.closure_induction (G := SL(2, ℤ)) (p := fun γ _ ↦ G₂ ∣[(2 : ℤ)] γ = G₂ - (D₂ γ))
    (k := ({ModularGroup.S, ModularGroup.T})) ?_ ?_
  · apply this
    · intro a b ha hb HA HB
      rw [D2_mul, SlashAction.slash_mul, HA, sub_eq_add_neg, SlashAction.add_slash, HB]
      ext z
      simp only [SlashAction.neg_slash, SL_slash, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
    · intro g hg hg2
      have H1 : (G₂ ∣[(2 : ℤ)] g) ∣[(2 : ℤ)] g⁻¹ = (G₂ - D₂ g)∣[(2 : ℤ)] g⁻¹ := by
        rw [hg2]
      rw [← SlashAction.slash_mul, sub_eq_add_neg, SlashAction.add_slash] at H1
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
      · simp only [UpperHalfPlane.coe, inv_pow, inv_inj]
        norm_cast
      simp only [UpperHalfPlane.coe]
      ring
    · simpa only [h2, D2_T, sub_zero] using G2_periodic
  · simp only [SlashAction.slash_one, D2_one, sub_zero]


/-Should be easy from the above.-/
lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
  E₂ z + 6 / ( π * Complex.I * z) := by
  rw [E₂]
  have := G₂_transform (ModularGroup.S)
  have hsm := ModularForm.SL_smul_slash (2 : ℤ) ModularGroup.S G₂ (1 / (2 * riemannZeta 2))
  rw [hsm]
  simp only [SL_slash, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul] at *
  rw [this]
  simp only [Pi.sub_apply]
  rw [D2_S]
  ring_nf
  rw [sub_eq_add_neg]
  congr
  rw [riemannZeta_two]
  have hpi : (π : ℂ) ≠ 0 := by simp
  ring_nf
  simp only [inv_pow, inv_I, mul_neg, neg_mul, neg_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero,
    or_false]
  rw [← inv_pow, pow_two, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  ring



lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ, (n + 1) *
    cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π * Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  have := fun m : ℕ => tsum_choose_mul_geometric_of_norm_lt_one (r := (cexp (2 * ↑π * Complex.I *
    ↑z))^(m+1)) 0 (by rw [← exp_aux]; simpa using exp_upperHalfPlane_lt_one_nat z m)
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
  rw [Summable.tsum_prod' ]
  · congr
    ext n
    congr
    ext m
    simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    ring
  · have := a4 2 z
    apply this.congr
    intro b
    simp only [uncurry, Nat.add_one_sub_one, pow_one, UpperHalfPlane.coe, mul_eq_mul_left_iff,
      Nat.cast_eq_zero, PNat.ne_zero, or_false]
    ring_nf
  · intro e
    have := a1 2 e z
    simp at *
    apply this.subtype

/- This we should get from the modular forms repo stuff. Will port these things soon. -/
lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+),
    ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E₂]
  simp
  rw [G2_q_exp]
  rw [mul_sub]
  congr 1
  · rw [riemannZeta_two]
    have hpi : (π : ℂ) ≠ 0 := by simp
    field_simp
    ring
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]
      have hpi : (π : ℂ) ≠ 0 := by simp
      norm_cast
      field_simp
      ring
    · have hl := tsum_pnat_eq_tsum_succ3 (fun n => sigma 1 n * cexp (2 * π * Complex.I * n * z))
      have hr := tsum_pnat_eq_tsum_succ3 (fun n => n * cexp (2 * π * Complex.I * n * z) / (1 - cexp
        (2 * π * Complex.I * n * z)))
      rw [hl, hr]
      have ht := tsum_eq_tsum_sigma z
      simp at *
      rw [ht]

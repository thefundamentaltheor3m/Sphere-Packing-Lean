import Mathlib
import SpherePacking.ModularForms.summable_lems

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

abbrev ℍ' := {z : ℂ | 0 < z.im}

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

/-this is in a PR-/
theorem cot_series_rep (z : ℍ) :
    ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by sorry


lemma EisensteinSeries_Identity (z : ℍ) :
    1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n := by
  have h1 := cot_series_rep z
  rw [pi_mul_cot_pi_q_exp z ] at h1
  rw [← h1]
  ring



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
/-

theorem hasDerivAt_tsum_fun {α : Type*} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ (K) (_ : K ⊆ s), IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(deriv (f n) k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, deriv (fun z => f n z) x) x :=
  by
  have A :
    ∀ x : ℂ,
      x ∈ s →
        Tendsto (fun t : Finset α => ∑ n in t, (fun z => f n z) x) atTop
          (𝓝 (∑' n : α, (fun z => f n z) x)) :=
    by
    intro y hy
    apply Summable.hasSum
    simp
    apply hf y hy
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  use fun n : Finset α => fun a => ∑ i in n, deriv (fun z => f i z) a
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
  intro q _
  rw [hasDerivAt_deriv_iff]
  apply hf2 q ⟨r, hr⟩

theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖ (deriv (f n) k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, deriv (fun z => f n z) x) s x := by
  apply (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt

theorem hasDerivWithinAt_tsum_fun' {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖ (deriv (f n) k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
  by
  have := hasDerivWithinAt_tsum_fun f hs x hx hf hu hf2
  have Hd : (∑' (n : α), deriv (fun z => f n z) x) = (∑' n : α, derivWithin (fun z => f n z) s x) :=
    by
    apply tsum_congr
    intro n
    apply symm
    apply DifferentiableAt.derivWithin
    apply hf2 n ⟨x, hx⟩
    apply IsOpen.uniqueDiffWithinAt hs hx
  rw [Hd] at this
  convert this

theorem deriv_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ (K) (_ : K ⊆ s),
        IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖ (deriv (f n) k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply
    HasDerivWithinAt.derivWithin (hasDerivWithinAt_tsum_fun' f hs x hx hf hu hf2)
      (IsOpen.uniqueDiffWithinAt hs hx) -/

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
        Tendsto (fun t : Finset α => ∑ n in t, (fun z => f n z) x) atTop
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


example (a : ℂ) (n : ℕ) : (a ^ n)⁻¹ = a ^ (-n : ℤ) := by
  simp only [zpow_neg, zpow_natCast]

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


/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x := by
  apply (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt


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


def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)

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

lemma upper_half_plane_isOpen :
    IsOpen ℍ' := by
  apply isOpen_lt (by fun_prop) (by fun_prop)


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

theorem uexp_contDiffOn (k n : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => Complex.exp (2 * ↑π * Complex.I * n * z)) ℍ' :=
  by
  apply ContDiff.contDiffOn
  apply ContDiff.cexp
  apply ContDiff.mul
  apply contDiff_const
  apply contDiff_id



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

theorem pos_sum_eq (k : ℕ) (hk : 0 < k) :
    (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * x)) =
      fun x : ℂ =>
      -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * n * x) := by
  ext1 x
  simp
  left
  apply symm
  rw [← tsum_pnat_eq_tsum_succ4]
  simp
  exact Nat.ne_zero_of_lt hk

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

theorem sigma_eq_sum_div' (k n : ℕ) : sigma k n = ∑ d : ℕ in Nat.divisors n, (n / d) ^ k :=
  by
  simp [sigma]
  rw [← Nat.sum_div_divisors]

theorem aux_inequality_two (z : ℍ) (k : ℕ) (n : Σ x : ℕ+, Nat.divisorsAntidiagonal x) :
    ‖(n.2.1.1 : ℂ) ^ k * Complex.exp (2 * ↑π * Complex.I * z * n.2.1.1 * n.2.1.2)‖ ≤
      Complex.abs (2 * n.1 ^ (k + 1) * Complex.exp (2 * ↑π * Complex.I * z * n.1)) :=
  by
  sorry
/-   simp
  have hn := n.2.2
  simp [Nat.mem_divisorsAntidiagonal,  PNat.ne_zero, not_false_iff] at *
  norm_cast
  simp_rw [← hn]
  have gt : ∀ a b : ℕ, ((a * b : ℕ) : ℂ) = (a : ℂ) * (b : ℂ) := Nat.cast_mul
  rw [gt]
  rw [← mul_assoc]
  simp  [Nat.cast_pow, ofReal_mul, PNat.pow_coe, Nat.cast_mul, algebraMap.coe_one]
  rw [mul_le_mul_right _]
  have J := Nat.fst_mem_divisors_of_mem_antidiagonal n.2.2
  simp only [Nat.mem_divisors, Ne.def, PNat.ne_zero, not_false_iff,
    and_true_iff] at J
  have J2 := Nat.le_of_dvd ?_ J
  norm_cast
  apply aux_inequality_one
  apply n.1.2
  exact J2
  apply n.1.2
  simp only [AbsoluteValue.pos_iff, Ne.def]
  apply Complex.exp_ne_zero -/

theorem summable1 {k : ℕ} (z : ℍ) :
    Summable fun p : Σ b : ℕ+, ↥(Nat.divisorsAntidiagonal b) =>
      ((sigmaAntidiagonalEquivProd p).fst : ℂ) ^ k *
        exp
          (2 * ↑π * Complex.I * ↑z * (sigmaAntidiagonalEquivProd p).fst *
            (sigmaAntidiagonalEquivProd p).snd) :=
  by
  sorry
/-   have := Summable.of_norm_bounded _ ?_ (aux_inequality_two z k)
  apply this
  rw [summable_sigma_of_nonneg]
  constructor
  apply fun n => (hasSum_fintype _).summable
  simp only [ AbsoluteValue.map_mul, Complex.abs_two, Complex.abs_pow, abs_natCast]
  apply Summable.of_nonneg_of_le _ _ (@summable_pow_mul_exp (k + 2) z)
  intro x
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
  norm_cast
  apply mul_nonneg
  exact (Nat.divisorsAntidiagonal x).card.cast_nonneg
  apply mul_nonneg
  simp [Nat.cast_mul, algebraMap.coe_one, mul_nonneg_iff_of_pos_right, Nat.cast_pos,
    PNat.pos, zero_le_bit0, zero_le_one]
  apply Complex.abs.nonneg
  intro b
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul,
    AbsoluteValue.map_mul, Complex.abs_two, Complex.abs_pow, abs_natCast]
  have hk :
    2 * (b : ℝ) ^ (k + 2 + 1) * Complex.abs (exp (2 * ↑π * I * ↑z * b)) =
      b ^ 2 * (2 * b ^ (k + 1) * Complex.abs (exp (2 * ↑π * I * ↑z * b))) :=
    by
    norm_cast
    simp
    ring
  norm_cast at *
  simp at *
  rw [hk]
  have ht := anti_diag_card_le b
  refine' mul_le_mul _ _ _ _
  norm_cast
  simp
  simp
  nlinarith
  intro x
  apply Complex.abs.nonneg -/

theorem sum_sigma_fn_eq {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c.1 * c.2) =
      ∑' e : ℕ+,
        ∑ x : Nat.divisorsAntidiagonal e,
          x.1.1 ^ k * Complex.exp (2 * ↑π * Complex.I * z * x.1.1 * x.1.2) :=
  by
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [tsum_sigma']
  congr
  funext
  rw [tsum_fintype]
  congr
  apply fun n => (hasSum_fintype _).summable
  apply summable1

theorem tsum_sigma_eqn2 {k : ℕ} (z : ℍ) :
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

  sorry
/-   simp_rw [sigma_eq_sum_div',sum_sigma_fn_eq z]
  apply tsum_congr
  intro n
  have :=
    @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
      (x : ℂ) ^ (k : ℕ) * Complex.exp (2 * ↑π * I * z * x * y)) n
  simp only [Finset.univ_eq_attach, cpow_nat_cast, EisensteinSeries.uhc, Nat.cast_sum, Nat.cast_pow,
    Nat.isUnit_iff] at *
  simp_rw [mul_assoc] at *
  norm_cast at *
  simp at *
  have dma := div_mul_aux k z n
  simp only [Nat.isUnit_iff, cpow_nat_cast, EisensteinSeries.uhc] at dma
  rw [dma] at this
  have hr :
    (∑ x : ℕ in (n : ℕ).divisors, ↑(↑n / x) ^ k) * exp (2 * (↑π * (I * (↑z * ↑n)))) =
      ∑ x : ℕ in (n : ℕ).divisors, ↑(↑n / x) ^ k * exp (2 * (↑π * (I * (↑z * (n : ℕ))))) :=
    by
    simp
    apply Finset.sum_mul
  simp at *
  rw [hr, ← this, ←(sumaux _)]
  simp only [Finset.univ_eq_attach] -/

lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
     ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by

    sorry

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

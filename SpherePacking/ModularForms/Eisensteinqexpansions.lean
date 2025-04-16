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

example (a b c : ℂ) : a + b = c ↔ b = c - a := by exact Iff.symm eq_sub_iff_add_eq'

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
          ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖ derivWithin (f n) s k‖ ≤ u n)
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
  · have := summable_hammerTime_nat (fun n : ℕ => (((z : ℂ) - n) ^ (k + 1))) (k+1) (by sorry) ?_
    apply this.subtype
    norm_cast
    simp_rw [← inv_pow]
    have : (fun (n : ℕ) ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) = fun (n : ℕ) ↦ (↑(n : ℝ)⁻¹)  ^ (k + 1) := by sorry
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
  · have := summable_hammerTime_nat (fun n : ℕ => (((z : ℂ) + n) ^ (k + 1))) (k+1) (by sorry) ?_
    apply this.subtype
    norm_cast
    simp_rw [← inv_pow]
    have : (fun (n : ℕ) ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) = fun (n : ℕ) ↦ (↑(n : ℝ)⁻¹)  ^ (k + 1) := by sorry
    conv =>
      enter [3]
      rw [this]
    apply Asymptotics.IsBigO.pow
    have hl := linear_bigO_nat 1 z
    apply Asymptotics.IsBigO.of_abs_right
    simp only [Nat.cast_pow, inv_pow, Int.cast_one, one_mul, Nat.abs_cast,
      Asymptotics.isBigO_abs_right] at *
    exact hl
  simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
    Nat.cast_eq_zero, false_or]
  exact Nat.factorial_ne_zero k
  simp only [not_le, Nat.lt_one_iff] at hk
  simp_rw [hk]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one, one_mul]
  simpa using lhs_summable z


theorem aut_bound_on_comp (K : Set ℍ) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
          Complex.abs
              (deriv
                (fun z : ℂ =>
                  iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) {z : ℂ | 0 < z.im} z)
                s) ≤
            u n :=
  by
  by_cases h1 : Set.Nonempty K
  have H := UpperHalfPlane.subset_verticalStrip_of_isCompact hk2
  obtain ⟨A, B, hB, hAB⟩ := H
  refine'
    ⟨fun a : ℕ+ => 2 * Complex.abs ((k + 1)! / rfunct (lbpoint A B hB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹,
      _, _⟩
  exact upper_bnd_summable A B hB k
  intro n s
  have hr := der_of_iter_der ⟨s.1, hk s.2⟩ k n
  simp  at *
  rw [hr]
  apply le_trans (Complex.abs.add_le _ _)
  simp_rw [mul_assoc]
  rw [two_mul]
  apply add_le_add
  have he1 := sub_bound ⟨s.1, hk s.2⟩ A B hB ?_ k n
  simp_rw [div_eq_mul_inv] at *
  simp at *
  norm_cast at *
  simp at *
  apply hAB
  simp
  have he1 := add_bound ⟨s.1, hk s.2⟩ A B hB ?_ k n
  simp_rw [div_eq_mul_inv] at *
  simp  at *
  norm_cast at *

  apply hAB
  simp  at *
  refine' ⟨fun _ => 0, _, _⟩
  apply summable_zero
  intro n
  rw [not_nonempty_iff_eq_empty] at h1
  intro r
  exfalso
  have hr := r.2
  simp_rw [h1] at hr
  simp at hr


theorem aut_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ) :
    iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im}  x =
      ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im}  x :=
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
  sorry
  sorry

/-   apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen x.2
  exact upper_half_plane_isOpen
  exact x.2
  intro y hy
  simpa using summable_iter_aut k ⟨y, hy⟩
  intro K hK hK2
  apply aut_bound_on_comp K hK hK2 k
  intro n r
  apply diff_at_aux r k n
  apply IsOpen.uniqueDiffWithinAt upper_half_plane_isOpen
  exact x.2 -/

theorem aux_iter_der_tsum (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
    iteratedDerivWithin k
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ (k + 1 : ℕ) :=
  by
  rw [iteratedDerivWithin_add ?_ ?_]

  · have h1 := aut_iter_deriv 0 k x.2
    simp [UpperHalfPlane.coe] at *
    rw [h1]

    have := aut_series_ite_deriv_uexp2 k x
    simp at *
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
      rw [summable_mul_left_iff]
      · have hk2 : 2 ≤ k + 1 := by linarith
        simpa using lhs_summable_2 x (k + 1) hk2
      · simp only [Nat.factorial_ne_zero, Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero,
          not_false_iff]
      · rw [summable_mul_left_iff]
        · have hk2 : 2 ≤ k + 1 := by linarith
          simpa using lhs_summable_2' x (k + 1) hk2
        · simp only [Nat.factorial_ne_zero, Ne.def, neg_one_pow_mul_eq_zero_iff, Nat.cast_eq_zero,
            not_false_iff]
    · have hk3 : 2 ≤ (k + 1 : ℤ) := by linarith
      have := summable_factor (-1 : ℤ) x (k + 1) hk3
      simpa using this
  · have := aut_contDiffOn 0 k
    simpa using this
  · apply tsum_aexp_contDiffOn k


lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
     ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by sorry

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

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Cases

open UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


lemma arg_pow_aux (n : ℕ) (x : ℂ) (hx : x ≠ 0) (hna : |arg x| < π / n) :
  Complex.arg (x ^ n) = n * Complex.arg x := by
  induction n with
  | zero => simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul]
  | succ n hn2 =>
    by_cases hn0 : n = 0
    · simp only [hn0, zero_add, pow_one, Nat.cast_one, one_mul]
    · rw [pow_succ, arg_mul, hn2, Nat.cast_add]
      · ring
      · apply lt_trans hna
        gcongr
        exact (lt_add_one n)
      · apply pow_ne_zero n hx
      · exact hx
      simp only [mem_Ioc]
      rw [hn2]
      · rw [abs_lt] at hna
        constructor
        · have hnal := hna.1
          rw [← neg_div] at hnal
          rw [div_lt_iff₀' ] at hnal
          · rw [Nat.cast_add, add_mul] at hnal
            simpa only [gt_iff_lt, Nat.cast_one, one_mul] using hnal
          · norm_cast
            omega
        · have hnal := hna.2
          rw [lt_div_iff₀', Nat.cast_add] at hnal
          · rw [add_mul] at hnal
            simpa only [ge_iff_le, Nat.cast_one, one_mul] using hnal.le
          · norm_cast
            omega
      apply lt_trans hna
      gcongr
      exact (lt_add_one n)

lemma one_add_abs_half_ne_zero {x : ℂ} (hb : ‖x‖ < 1 / 2) : 1 + x ≠ 0 := by
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
  · rw [ContinuousAt] at *
    have h3 := h2.comp hf1
    simp only [arg_one] at h3
    rw [Metric.tendsto_nhds] at *
    simp only [gt_iff_lt, dist_zero_right, eventually_atTop, ge_iff_le,
      dist_self_add_left, arg_one, Real.norm_eq_abs, comp_apply] at *
    by_cases hn0 : n = 0
    · rw [hn0]
      simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul, implies_true, exists_const]
    · have hpi : 0 < π / n := by
        apply div_pos
        · exact Real.pi_pos
        simp only [Nat.cast_pos]
        omega
      obtain ⟨a, hA⟩ := h3 (π / n) hpi
      obtain ⟨a2, ha2⟩ := hf (1/2) (one_half_pos)
      use max a a2
      intro b hb
      rw [arg_pow_aux n (1 + f b) ?_]
      · apply hA b
        exact le_of_max_le_left hb
      have ha2 := ha2 b (le_of_max_le_right hb)
      simp only [ne_eq]
      apply one_add_abs_half_ne_zero ha2
  simp only [one_mem_slitPlane]

lemma arg_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty,
    Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  rw [Filter.eventually_iff_exists_mem ]
  have hf1 := hf.const_add 1
  simp only [add_zero] at hf1
  have h2 := (Complex.continuousAt_arg (x := 1) ?_)
  · rw [ContinuousAt] at *
    have h3 := h2.comp hf1
    simp only [arg_one] at h3
    rw [Metric.tendsto_nhds] at *
    simp only [gt_iff_lt, dist_zero_right, dist_self_add_left, arg_one, Real.norm_eq_abs,
      comp_apply] at *
    by_cases hn0 : n = 0
    · simp_rw [hn0]
      simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul, implies_true, and_true]
      rw [atImInfty]
      simp only [mem_comap, mem_atTop_sets, ge_iff_le]
      use {n | 1 ≤ n.im}
      use {r : ℝ | 1 ≤ r}
      refine ⟨?_, ?_⟩
      · use 1
        intro b hb
        aesop
      simp only [preimage_setOf_eq, subset_refl]
    · have hpi : 0 < π / n := by
        apply div_pos
        · exact Real.pi_pos
        simp only [Nat.cast_pos]
        omega
      have hA1 := h3 (π / n) hpi
      have hA2 := hf (1/2) (one_half_pos)
      rw [Filter.eventually_iff_exists_mem ] at hA1 hA2
      obtain ⟨a, ha1, hA1⟩ := hA1
      obtain ⟨a2, ha2, hA2⟩ := hA2
      use min a a2
      refine ⟨by rw [atImInfty] at *; simp at *; refine ⟨ha1, ha2⟩, ?_⟩
      intro b hb
      rw [arg_pow_aux n (1 + f b) ?_]
      · apply hA1 b
        exact mem_of_mem_inter_left hb
      have ha2 := hA2 b ( mem_of_mem_inter_right hb)
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
  simp only [norm_pow, Real.log_pow, ofReal_mul, ofReal_natCast]
  ring

lemma clog_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  have h := arg_pow2 n f hf
  simp at *
  simp_rw [Complex.log]
  obtain ⟨a, ha0, ha⟩ := h
  use a
  refine ⟨ha0, ?_⟩
  intro b hb
  have h2 := ha hb
  simp only [mem_atTop_sets, ge_iff_le, mem_preimage, mem_setOf_eq] at *
  rw [h2]
  simp only [norm_pow, Real.log_pow, ofReal_mul, ofReal_natCast]
  ring



lemma log_summable_pow (f : ℕ → ℂ) (hf : Summable f) (m : ℕ) :
    Summable (fun n => Complex.log ((1 + f n)^m)) := by
  have hfl := Complex.summable_log_one_add_of_summable hf
  have := (Summable.mul_left m (f := (fun n => Complex.log (1 + f n))) hfl).norm
  apply Summable.of_norm_bounded_eventually_nat this
  have hft := hf.tendsto_atTop_zero
  have H := clog_pow m f hft
  simp only [norm_mul, Complex.norm_natCast, eventually_atTop, ge_iff_le] at *
  obtain ⟨a, ha⟩ := H
  use a
  intro b hb
  apply le_of_eq
  rw [ha b hb]
  simp only [Complex.norm_mul, norm_natCast]

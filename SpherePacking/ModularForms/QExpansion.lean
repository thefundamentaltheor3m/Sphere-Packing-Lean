import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ForMathlib.AtImInfty

/-!
# Limits at infinity

In this file we establishes basic results about q-expansions. The results are put under the `QExp`
namespace.

TODO:
* Are any of these results in Mathlib, perhaps phrased in some other way?
-/

open scoped Real
open UpperHalfPlane hiding I
open Complex Asymptotics Topology Filter

namespace QExp

lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-2 * π * n)) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  convert tendsto_tsum_of_dominated_convergence (f := fun z n ↦ a n * cexp (2 * π * I * z * n))
    (𝓕 := atImInfty) (g := Set.indicator {0} (fun _ ↦ a 0)) ha ?_ ?_
  · rw [← tsum_subtype]
    convert (Finset.tsum_subtype {0} (fun _ ↦ a 0)).symm with x
    · rw [Finset.sum_const, Finset.card_singleton, one_smul]
    · -- Why did this get so complicated all of a sudden
      ext n
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hn
        rw [hn]
        exact Finset.singleton_subset_set_iff.mp fun ⦃a⦄ a ↦ a
      · intro hn
        exact Finset.mem_zero.mp hn
  · intro k
    rcases eq_or_ne k 0 with (rfl | hk)
    · simp
    · simp only [Set.mem_singleton_iff, hk, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
      rw [← mul_zero ‖a k‖]
      refine Tendsto.const_mul ‖a k‖ <| (Real.tendsto_exp_atBot).comp ?_
      simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
        coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, zero_add, tendsto_neg_atBot_iff]
      rw [tendsto_mul_const_atTop_of_pos, tendsto_const_mul_atTop_of_pos] <;> try positivity
      exact tendsto_im_atImInfty
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I, mul_right_comm]
    simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, neg_mul]
    nth_rw 4 [← mul_one k]
    rw [Nat.cast_mul, Nat.cast_one, ← mul_assoc]
    gcongr

lemma tendsto_int (a : ℤ → ℂ) (ha : Summable fun n : ℤ ↦ ‖a n‖ * rexp (-2 * π * n))
    (ha' : ∀ n, n < 0 → a n = 0) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  -- ∑' (n : ℕ), f ↑n + ∑' (n : ℕ), f (-(↑n + 1))
  have : Tendsto
    (fun z : ℍ ↦ (∑' n : ℕ, (a n * cexp (2 * π * I * z * n)
      + a (-(n + 1 : ℤ)) * cexp (2 * π * I * z * (-(n + 1) : ℤ))))) atImInfty (𝓝 (a 0)) := by
    have := tendsto_nat (fun n ↦ a n) ?_
    apply this.congr
    · exact fun _ ↦ tsum_congr (by simpa using fun _ ↦ ha' _ (by omega))
    · exact (summable_int_iff_summable_nat_and_neg.mp ha).left
  apply this.congr'
  rw [EventuallyEq, eventually_atImInfty]
  use 1, fun z hz ↦ ?_
  rw [← tsum_nat_add_neg_add_one]
  · rfl
  rw [← summable_norm_iff]
  convert_to Summable fun n ↦ ‖a n‖ * rexp (z.im * -2 * π * n)
  · ext n
    rw [norm_mul, mul_right_comm _ I, mul_right_comm _ I, norm_exp_mul_I]
    simp
    ring_nf
    simp
  · apply ha.of_nonneg_of_le (fun _ ↦ by positivity) fun b ↦ ?_
    by_cases hb : 0 ≤ b
    · have : z.im * -2 * π * b ≤ -2 * π * b := by
        gcongr
        simp [hz]
      gcongr
    · norm_num at hb
      simp [ha' _ hb]

end QExp

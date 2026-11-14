module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import SpherePacking.ModularForms.JacobiTheta.Basic
public import SpherePacking.ForMathlib.AtImInfty

/-!
# Limits at infinity

In this file we establishes basic results about q-expansions. The results are put under the `QExp`
namespace.

TODO:
* Are any of these results in Mathlib, perhaps phrased in some other way?
-/

@[expose] public section

open scoped Real
open UpperHalfPlane hiding I
open Complex Asymptotics Topology Filter

namespace QExp

lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-2 * π * n)) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  convert tendsto_tsum_of_dominated_convergence (f := fun z n ↦ a n * cexp (2 * π * I * z * n))
    (𝓕 := atImInfty) (g := Set.indicator {0} (fun _ ↦ a 0)) ha ?_ ?_
  · simp
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
    gcongr
    have hz2 : (2 : ℝ) ≤ 2 * z.im := by nlinarith [hz]
    have hbase : 2 * π ≤ 2 * z.im * π := by
      exact mul_le_mul_of_nonneg_right hz2 (by positivity)
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hmul : 2 * π * (k : ℝ) ≤ (2 * z.im * π) * (k : ℝ) := by
      exact mul_le_mul_of_nonneg_right hbase hk
    simpa [mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm] using hmul

end QExp

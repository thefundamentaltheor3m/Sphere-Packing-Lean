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

lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-π * n)) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (π * I * n * z)) atImInfty (𝓝 (a 0)) := by
  convert tendsto_tsum_of_dominated_convergence (f := fun z n ↦ a n * cexp (π * I * n * z))
    (𝓕 := atImInfty) (g := Set.indicator {0} (fun _ ↦ a 0)) ha ?_ ?_
  · rw [← tsum_subtype]
    convert (Finset.tsum_subtype {0} (fun _ ↦ a 0)).symm with x
    · rw [Finset.sum_const, Finset.card_singleton, one_smul]
    · exact Finset.mem_singleton.symm
  · intro k
    rcases eq_or_ne k 0 with (rfl | hk)
    · simpa using tendsto_const_nhds
    · simp only [Set.mem_singleton_iff, hk, not_false_eq_true, Set.indicator_of_not_mem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
      rw [← mul_zero ‖a k‖]
      refine Tendsto.const_mul ‖a k‖ <| (Real.tendsto_exp_atBot).comp ?_
      simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
        coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, zero_add, tendsto_neg_atBot_iff,
        mul_assoc]
      rw [tendsto_const_mul_atTop_of_pos, tendsto_const_mul_atTop_of_pos] <;> try positivity
      exact tendsto_im_atImInfty
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
    simp only [norm_eq_abs, mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, zero_add, neg_mul]
    nth_rw 4 [← mul_one k]
    rw [Nat.cast_mul, Nat.cast_one, ← mul_assoc]
    gcongr

lemma tsum_int_ite {f : ℕ → ℂ} :
    (∑' n, f n) = (∑' n : ℤ, if hn : 0 ≤ n then f n.toNat else 0) := by
  sorry

lemma tendsto_int (a : ℤ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-π * n))
    (ha' : ∀ n, n < 0 → a n = 0) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (π * I * n * z)) atImInfty (𝓝 (a 0)) := by
  let a' : ℕ → ℂ := fun n ↦ a n
  convert tendsto_nat a' ?_ with z
  · rw [tsum_int_ite]
    apply tsum_congr fun n ↦ ?_
    split_ifs with hn
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      simp
    · simp [ha' n (lt_of_not_le hn)]
  · exact ha

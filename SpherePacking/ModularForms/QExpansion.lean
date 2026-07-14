module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import SpherePacking.ModularForms.JacobiTheta.Basic
public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.Tactic.PushReIm

@[expose] public section

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
  · simp
  · intro k
    rcases eq_or_ne k 0 with (rfl | hk)
    · simp
    · simp only [Set.mem_singleton_iff, hk, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
      rw [← mul_zero ‖a k‖]
      refine Tendsto.const_mul ‖a k‖ <| (Real.tendsto_exp_atBot).comp ?_
      push_re_im [tendsto_neg_atBot_iff]
      exact ((tendsto_im_atImInfty.const_mul_atTop Real.pi_pos).atTop_mul_const
        (mod_cast Nat.pos_of_ne_zero hk)).atTop_mul_const two_pos
  · eventually_im_infty 1
    intro z hz k
    simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I, mul_right_comm]
    push_re_im
    gcongr
    exact le_mul_of_one_le_left Real.pi_pos.le hz

lemma tendsto_int (a : ℤ → ℂ) (ha : Summable fun n : ℤ ↦ ‖a n‖ * rexp (-2 * π * n))
    (ha' : ∀ n, n < 0 → a n = 0) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  -- ∑' (n : ℕ), f ↑n + ∑' (n : ℕ), f (-(↑n + 1))
  have : Tendsto
    (fun z : ℍ ↦ (∑' n : ℕ, (a n * cexp (2 * π * I * z * n)
      + a (-(n + 1 : ℤ)) * cexp (2 * π * I * z * (-(n + 1) : ℤ))))) atImInfty (𝓝 (a 0)) := by
    have := tendsto_nat (fun n ↦ a n) ?_
    · apply this.congr
      exact fun _ ↦ tsum_congr (by simpa using fun _ ↦ ha' _ (by omega))
    · exact (summable_int_iff_summable_nat_and_neg.mp ha).left
  apply this.congr'
  rw [EventuallyEq]
  eventually_im_infty 1 with z hz
  rw [← tsum_nat_add_neg_add_one]
  · rfl
  rw [← summable_norm_iff]
  convert_to Summable fun n ↦ ‖a n‖ * rexp (z.im * -2 * π * n)
  · ext n
    norm_exp_simp
  · apply ha.of_nonneg_of_le (fun _ ↦ by positivity) fun b ↦ ?_
    by_cases hb : 0 ≤ b
    · have : z.im * -2 * π * b ≤ -2 * π * b := by
        gcongr
        simp [hz]
      gcongr
    · norm_num at hb
      simp [ha' _ hb]

end QExp

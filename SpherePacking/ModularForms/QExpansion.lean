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

section 𝕢_lemmas

variable (n : ℝ) (z : ℂ)

noncomputable abbrev 𝕢 := cexp (π * (2 * n) * z * I)

lemma 𝕢_zero_left : 𝕢 0 z = 1 := by simp [𝕢]

lemma 𝕢_zero_right : 𝕢 n 0 = 1 := by simp [𝕢]

lemma 𝕢_int_eq_𝕢_one_pow (n : ℤ) (z : ℂ) : 𝕢 n z = 𝕢 1 z ^ n := by
  simp [𝕢, ← exp_int_mul]
  ring_nf

lemma 𝕢_eq_one_pow_nat (n : ℕ) (z : ℂ) : 𝕢 n z = 𝕢 1 z ^ n := by
  simp [𝕢, ← exp_nat_mul]
  ring_nf

lemma 𝕢_tendsto_atImInfty : Tendsto (fun z : ℍ ↦ 𝕢 n z) atImInfty (𝓝 0) := by
  sorry

lemma norm_𝕢 : ‖𝕢 n z‖ = rexp (π * (-2 * n) * z.im) := by
  rw [𝕢, norm_exp_mul_I]
  simp

lemma norm_𝕢_le_of_one_le_im (hn : 0 ≤ n) (hz : 1 ≤ z.im) :
    ‖𝕢 n z‖ ≤ rexp (π * (-2 * n)) := by
  rw [norm_𝕢, neg_mul, mul_neg, neg_mul, Real.exp_le_exp, neg_le_neg_iff]
  exact le_mul_of_one_le_right (by positivity) hz

lemma norm_𝕢_le_one (hn : 0 ≤ n) (hz : 0 ≤ z.im) : ‖𝕢 n z‖ ≤ 1 := by
  rw [norm_𝕢]
  simpa using by positivity

lemma norm_𝕢_lt_one (hn : 0 < n) (hz : 0 < z.im) : ‖𝕢 n z‖ < 1 := by
  rw [norm_𝕢]
  simpa using by positivity

end 𝕢_lemmas

/-- This lemma allows one to group any q-expansions into the "canonical" form of
`∑' n, a n * cexp (π * n * z * I)`. -/
lemma tsum_qexp_fiberwise {ι : Type*} (f : ι → ℝ) (z : ℂ) :
    (∑' i, 𝕢 (f i) z) = (∑' n : ℝ, Nat.card (f ⁻¹' {n}) • 𝕢 n z) := by
  sorry

lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (π * (-2 * n))) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * 𝕢 n z) atImInfty (𝓝 (a 0)) := by
  convert tendsto_tsum_of_dominated_convergence (f := fun z n ↦ a n * 𝕢 n z)
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
    · simp [𝕢, tendsto_const_nhds]
    · simp only [Set.mem_singleton_iff, hk, not_false_eq_true, Set.indicator_of_not_mem]
      rw [← mul_zero (a k)]
      apply Tendsto.const_mul
      exact 𝕢_tendsto_atImInfty _
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I, mul_right_comm]
    simp only [mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, coe_re, zero_mul, add_zero, coe_im, natCast_im, natCast_re, zero_add, neg_mul]
    nth_rw 4 [← mul_one k]
    rw [Nat.cast_mul, Nat.cast_one, ← mul_assoc]
    gcongr

lemma tendsto_int (a : ℤ → ℂ) (ha : Summable fun n : ℤ ↦ ‖a n‖ * rexp (-2 * π * n))
    (ha' : ∀ n, n < 0 → a n = 0) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * 𝕢 n z) atImInfty (𝓝 (a 0)) := by
  let a' : ℕ → ℂ := fun n ↦ a n
  convert tendsto_nat a' ?_ with z
  · rw [tsum_int_ite]
    apply tsum_congr fun n ↦ ?_
    split_ifs with hn
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      simp
    · simp [ha' n (lt_of_not_le hn)]
  · exact ha

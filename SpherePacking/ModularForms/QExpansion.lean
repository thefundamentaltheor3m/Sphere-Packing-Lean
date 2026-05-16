module
public import Mathlib.Analysis.Normed.Group.Tannery
public import SpherePacking.ModularForms.JacobiTheta
public import SpherePacking.ForMathlib.ModularFormsHelpers

/-!
# Limits at infinity

In this file we establish basic results about q-expansions. The results are put under the `QExp`
namespace.
-/

namespace QExp

open scoped Real

open UpperHalfPlane hiding I
open Complex Asymptotics Topology Filter

private lemma norm_term_nat (a : ℕ → ℂ) (z : ℍ) (n : ℕ) :
    ‖a n * cexp (2 * π * I * z * n)‖ = ‖a n‖ * rexp (z.im * (-2 * π * n)) := by
  simp_rw [norm_mul, mul_right_comm _ I, norm_exp_mul_I]
  simp [mul_assoc, mul_left_comm, mul_comm]

private lemma tendsto_term_nat_of_ne_zero (a : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun z : ℍ ↦ a k * cexp (2 * π * I * z * k)) atImInfty (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simp_rw [norm_term_nat (a := a) (n := k)]
  have hkneg : (-2 * π * (k : ℝ)) < 0 := by
    nlinarith [Real.pi_pos, (show (0 : ℝ) < (k : ℝ) by exact_mod_cast Nat.pos_of_ne_zero hk)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (tendsto_const_nhds.mul <| (Real.tendsto_exp_atBot).comp
      ((tendsto_mul_const_atBot_of_neg hkneg).2 tendsto_im_atImInfty))

private lemma norm_term_bound_nat (a : ℕ → ℂ) {z : ℍ} (hz : (1 : ℝ) ≤ z.im) (k : ℕ) :
    ‖a k * cexp (2 * π * I * z * k)‖ ≤ ‖a k‖ * rexp (-2 * π * k) := by
  simp_rw [norm_term_nat (a := a) (z := z) (n := k)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (a k))
  have ht : (-2 * π * (k : ℝ)) ≤ 0 := by
    nlinarith [Real.pi_pos, (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hz ht)

/-- A dominated-convergence lemma for `ℕ`-indexed `q`-expansions at the cusp `∞`. -/
public lemma tendsto_nat (a : ℕ → ℂ) (ha : Summable fun n : ℕ ↦ ‖a n‖ * rexp (-2 * π * n)) :
    Tendsto (fun z : ℍ ↦ ∑' n, a n * cexp (2 * π * I * z * n)) atImInfty (𝓝 (a 0)) := by
  simpa using
    (tendsto_tsum_of_dominated_convergence
      (f := fun z n ↦ a n * cexp (2 * π * I * z * n))
      (𝓕 := atImInfty)
      (g := Set.indicator ({0} : Set ℕ) (fun _ ↦ a 0))
      ha
      (by
        intro k
        rcases eq_or_ne k 0 with (rfl | hk)
        · simp
        · simpa [hk] using tendsto_term_nat_of_ne_zero (a := a) hk)
      (by
        rw [eventually_atImInfty]
        refine ⟨1, fun z hz k ↦ ?_⟩
        simpa using norm_term_bound_nat (a := a) (z := z) hz k))

end QExp

import Mathlib
import SpherePacking.ModularForms.exp_lems
import SpherePacking.ModularForms.summable_lems

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction


/-this is being PRd-/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n ≠ 0) : Multipliable (fun n : ℕ => 1 + f n) := by
    apply Complex.multipliable_of_summable_log
    apply hff
    apply Complex.summable_log_one_add_of_summable hf


theorem term_ne_zero (z : ℍ) (n : ℕ) : 1 -cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [@sub_ne_zero]
  intro h
  have :=  exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp only [AbsoluteValue.map_one, lt_self_iff_false] at *

lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ) := by
  have := Complex.summable_nat_multipliable_one_add (fun (n : ℕ) => (-cexp (2 * π * Complex.I * (n + 1) * z)) ) ?_ ?_
  simp at this
  apply this.congr
  intro n
  ring
  rw [←summable_norm_iff]
  simpa using summable_exp_pow z
  intro n
  simp
  apply term_ne_zero


lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))) := by
  conv =>
    enter [1]
    ext n
    rw [sub_eq_add_neg]
  let g := (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * n * z)) )
  have := MultipliableEtaProductExpansion z
  conv at this =>
    enter [1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  rw [ ← pnat_multipliable_iff_multipliable_succ (f := g)] at this
  apply this.congr
  intro b
  rfl



lemma tprod_ne_zero (x : ℍ) (f : ℕ → ℍ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : ℍ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0 := by
  have := Complex.cexp_tsum_eq_tprod (fun n => 1 + f n x) ?_ ?_
  simp
  rw [← this]
  simp only [comp_apply, exp_ne_zero, not_false_eq_true]
  intro n
  simp
  apply hf
  simp
  apply Complex.summable_log_one_add_of_summable
  apply hu x



lemma Multipliable_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) :
     Multipliable (fun i => f i ^ n) := by
  induction' n with n hn
  · simp
    apply multipliable_one
  · conv =>
      enter [1]
      intro u
      rw [pow_succ]
    apply Multipliable.mul hn hf


lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) : (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ), (f i) ^ n := by
  induction' n with n hn
  · simp
  · rw [pow_succ]
    rw [hn]
    rw [← tprod_mul]
    congr
    apply Multipliable_pow f hf n
    exact hf

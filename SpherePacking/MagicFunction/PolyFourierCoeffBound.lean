/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

import SpherePacking.ForMathlib.Fourier
import SpherePacking.ForMathlib.SpecificLimits
import SpherePacking.ForMathlib.tprod
import SpherePacking.ModularForms.Eisenstein


/-

This file contains the proof of Lemma 7.4 in the blueprint, which gives an upper-bound on the ratio
between any function whose Fourier coefficients are O(n^k) and its discriminant.

# TODO:
The only `sorry`s are in the section `calc_aux`, which consists of auxiliary lemmas that are used in
various `calc_steps` lemmas, which in turn make up the proof of the main theorem. Below, we give a
comprehensive list of things to be done, including but not limited to the `sorry`s in this file.
- [ ] `aux_5`: prove `fun i ↦ (1 - cexp (2 * ↑π * I * ↑↑i * z)) ^ 24` is Multipliable
- [ ] `step_10`, `step_12`: prove `tprod_le_tprod` in SpherePacking.ForMathlib.tprod
- [ ] `step_11`: prove `summable_real_norm_mul_geometric_of_norm_lt_one` in
      SpherePacking.ForMathlib.SpecificLimits
-/

open Filter Complex Real BigOperators Asymptotics
open scoped UpperHalfPlane
open scoped ArithmeticFunction.sigma

namespace MagicFunction.PolyFourierCoeffBound

private noncomputable def fouterm (coeff : ℤ → ℂ) (x : ℂ) (i : ℤ) : ℂ :=
  (coeff i) * cexp (π * I * i * x)

variable (z : ℍ) (hz : 1 / 2 < z.im)
variable (c : ℤ → ℂ) (n₀ : ℤ) (hcn₀ : c n₀ ≠ 0) -- (hn₀ : ∀ (n : ℤ), n < n₀ → c n = 0)
variable (hcsum : Summable fun (i : ℕ) ↦ (fouterm c z (i + n₀)))
variable (k : ℕ) (hpoly : c =O[atTop] (fun n ↦ (n ^ k : ℝ)))
-- Change to just `c n` is polynomial. Should work!
variable (f : ℍ → ℂ) (hf : ∀ x : ℍ, f x = ∑' (n : ℕ), (fouterm c x (n + n₀)))

noncomputable def DivDiscBound : ℝ :=
  (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24)

section hpoly_aux

include hpoly in
theorem hpoly' : (fun (n : ℕ) ↦ c (n + n₀)) =O[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  have h_shift : (fun n : ℕ => c (n + n₀)) =O[atTop] (fun n : ℕ => (n + n₀ : ℂ) ^ k) := by
    simp only [isBigO_iff, eventually_atTop] at hpoly ⊢
    obtain ⟨C, m, hCa⟩ := hpoly
    use C
    simp only [norm_pow, norm_eq_abs] at hCa ⊢
    refine ⟨(m - n₀).toNat, fun n hn ↦ ?_⟩
    exact_mod_cast hCa (n + n₀) (by grind)
  refine h_shift.trans ?_
  simp only [isBigO_iff, eventually_atTop]
  use 2 ^ k
  simp only [norm_pow, RCLike.norm_natCast]
  refine ⟨n₀.natAbs, fun n hn => ?_⟩
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  norm_cast
  cases abs_cases (n + n₀ : ℤ) <;> grind

end hpoly_aux

section calc_aux

-- These could even go in Mathlib... they look useful (if a bit random)

private lemma aux_1 (x : ℂ) : norm (cexp (I * x)) = rexp (-x.im) := by
  have h₁ : I * (↑x.im * I) = -x.im := by rw [mul_comm, mul_assoc, Complex.I_mul_I, mul_neg_one]
  rw [← x.re_add_im, mul_add, h₁, Complex.norm_exp]
  simp

-- Below was written by Bhavik
private lemma aux_2 (x : ℂ) : 1 - Real.exp x.re ≤ norm (1 - cexp x) := calc
  norm (1 - cexp x) ≥ |‖(1 : ℂ)‖ - norm (cexp x)| := abs_norm_sub_norm_le 1 (cexp x)
  _ = |1 - rexp x.re| := by simp [Complex.norm_exp]
  _ ≥ _ := le_abs_self _

include hcsum in
private lemma aux_3 : Summable fun (i : ℕ) ↦ ‖c (i + n₀) * cexp (↑π * I * i * z)‖ := by
  rw [summable_norm_iff]
  have h₁ := Summable.mul_right (cexp (↑π * I * ↑n₀ * z))⁻¹ hcsum
  simp [fouterm, mul_add, add_mul, Complex.exp_add] at h₁
  have h₂ : ∀ (i : ℕ), c (↑i + n₀) * (cexp (↑π * I * ↑i * z) * cexp (↑π * I * ↑n₀ * z)) *
      (cexp (↑π * I * ↑n₀ * z))⁻¹ = c (↑i + n₀) * cexp (↑π * I * ↑i * z) := by
    intro i; field_simp
  simp only [h₂] at h₁
  exact h₁

include hcsum in
private lemma aux_4 : Summable fun (i : ℕ) ↦ norm (c (i + n₀)) *
    norm (cexp (↑π * I * ↑i * z)) := by
  simp_rw [← norm_mul]; exact aux_3 z c n₀ hcsum

lemma aux_5 (z : ℍ) : norm (∏' (n : ℕ+), (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24) =
  ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  simp only [← norm_pow]
  apply Multipliable.norm_tprod -- ℕ+ (fun n => (1 - cexp (2 * ↑π * I * n * z)) ^ 24)
  apply MultipliableDeltaProductExpansion_pnat z


lemma aux_6 (z : ℍ) : 0 ≤ ∏' (n : ℕ+), norm (1 - cexp (2 * ↑π * I * ↑↑n * z)) ^ 24 := by
  rw [← aux_5 z]
  exact norm_nonneg _

lemma aux_7 (a : ℤ) :
    norm (cexp (↑π * I * a * z)) ≤ rexp (-π * a * z.im) := by
  rw [mul_comm (π : ℂ) I, mul_assoc, mul_assoc, aux_1 (↑π * (a * z))]
  refine exp_le_exp.2 ?_
  simp; linarith

lemma aux_8 : 0 < ∏' (n : ℕ+), (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod]
  · apply Real.exp_pos
  · intro i
    apply pow_pos
    simp [pi_pos, UpperHalfPlane.im_pos]
  · simp only [log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    apply Summable.const_smul
    simp_rw [sub_eq_add_neg]
    apply Real.summable_log_one_add_of_summable
    apply Summable.neg
    simp_rw [smul_eq_mul]
    conv =>
      lhs
      equals (fun (b : ℕ) => Real.exp (-2 * π * b * z.im)) ∘ (PNat.val) => rfl
    apply Summable.subtype
    simp_rw [mul_comm, mul_assoc, Real.summable_exp_nat_mul_iff]
    simp [pi_pos, UpperHalfPlane.im_pos]

lemma aux_ring (i : ℕ) : (I * ↑π * ↑i * z) = I * ((↑π * ↑i) * z) := by ring

lemma aux_9 (i : ℕ) :
    ‖c (i + n₀) * cexp (↑π * I * ↑i * z)‖ = ‖c (i + n₀)‖ * rexp (-π * ↑i * z.im) := by
  rw [norm_mul, mul_comm (↑π) (I)]
  rw [aux_ring, aux_1]
  congr; simp

include hcsum in
lemma aux_10 : Summable fun (n : ℕ) ↦ norm (c (n + n₀)) * rexp (-π * ↑n * z.im) := by
  simp only [← aux_9]
  exact aux_3 z c n₀ hcsum

lemma aux_11 : 0 < ∏' (n : ℕ+), (1 - rexp (-π * ↑↑n)) ^ 24 := by
  rw [← Real.rexp_tsum_eq_tprod]
  · apply Real.exp_pos
  · intro i
    apply pow_pos
    simp [pi_pos]
  · simp only [log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    apply Summable.const_smul
    simp_rw [sub_eq_add_neg]
    apply Real.summable_log_one_add_of_summable
    apply Summable.neg
    simp_rw [smul_eq_mul]
    conv =>
      lhs
      equals (fun (b : ℕ) => Real.exp (-π * b)) ∘ (PNat.val) => rfl
    apply Summable.subtype
    simp_rw [mul_comm, Real.summable_exp_nat_mul_iff]
    simp [pi_pos]

lemma aux_misc (x : ℍ) : norm (cexp (I * x)) ≤ rexp (x.im) := by
  rw [aux_1 x]
  refine exp_le_exp.2 ?_
  rw [UpperHalfPlane.coe_im, neg_le_self_iff]
  exact le_of_lt x.2

end calc_aux

section calc_steps

include hf in
private lemma step_1 :
    norm ((f z) / (Δ z)) = norm (
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)
    ) := by simp [DiscriminantProductFormula, hf, fouterm, UpperHalfPlane.coe];

private lemma step_2 :
    norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  congr
  rw [← tsum_mul_left]
  congr
  ext n; ring_nf
  rw [mul_assoc (c (n + n₀)) (cexp _), ← Complex.exp_add]
  congr 2
  ring

private lemma step_3 :
    norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by field_simp

private lemma step_4 :
    norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := by
  rw [mul_sub, sub_mul, ← Complex.exp_sub]
  congr 6
  ac_rfl

private lemma step_5 :
    norm ((cexp (π * I * (n₀ - 2) * z)) *
    (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) =
    norm (cexp (π * I * (n₀ - 2) * z)) *
    norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  simp only [norm_div, norm_mul]

private lemma step_6 :
    norm (cexp (π * I * (n₀ - 2) * z)) *
    norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) =
    norm (cexp (π * I * (n₀ - 2) * z)) *
    norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := by congr; exact aux_5 z

private lemma step_7 :
    norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · norm_cast
    exact aux_7 z (n₀ - 2)

include hcsum in
private lemma step_8 :
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · calc
    _ ≤ ∑' (n : ℕ), norm ((c (n + n₀)) * (cexp (↑π * I * ↑n * z))) := by
      refine norm_tsum_le_tsum_norm ?_
      exact aux_3 z c n₀ hcsum
    _ = ∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (↑π * I * ↑n * z)) :=
      by simp only [norm_mul]

include hcsum in
private lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · exact (aux_4 z c n₀ hcsum)
  · exact aux_10 z c n₀ hcsum
  · next j =>
    rw [Complex.norm_exp]
    simp

private lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) :=
by
  have hpow : ∀ {ι} (f : ι → ℝ), Multipliable f → ∀ n, Multipliable (fun i => f i ^ n) := by
    intro ι f hf n
    induction n with
    | zero => simpa using (multipliable_one : Multipliable (fun _ : ι => (1 : ℝ)))
    | succ n hn => simpa [pow_succ] using (hn.mul hf)
  gcongr
  · exact aux_8 z
  · apply tprod_le_of_nonneg_of_multipliable
    · intro n; simp
      have : (1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 24 =
          ((1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 12) ^ 2 := by ring_nf
      rw [this]; exact sq_nonneg _
    · intro n; simp only [neg_mul]; gcongr
      · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]; positivity
      · have hre : -(2 * π * n * z.im) = (2 * π * I * n * z).re := by simp
        rw [hre]; exact aux_2 (2 * π * I * n * z)
    · have h_base : Multipliable (fun b : ℕ+ => 1 - rexp (-2 * π * ↑↑b * z.im)) := by
        apply Real.multipliable_of_summable_log
        · intro i; simp [pi_pos, UpperHalfPlane.im_pos]
        · simp_rw [sub_eq_add_neg]
          apply Real.summable_log_one_add_of_summable
          apply Summable.neg
          conv => lhs; equals (fun (b : ℕ) => Real.exp (-2 * π * b * z.im)) ∘ (PNat.val) => rfl
          apply Summable.subtype
          simp_rw [mul_comm, mul_assoc, Real.summable_exp_nat_mul_iff]
          simp [pi_pos, UpperHalfPlane.im_pos]
      exact hpow _ h_base 24
    · exact hpow _ (MultipliableEtaProductExpansion_pnat z).norm 24

include hz hcsum hpoly in
private lemma step_11 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact le_of_lt (aux_8 z)
  · exact aux_10 z c n₀ hcsum
  · simp only [div_eq_mul_inv]
    -- **This is where we use the fact that c is eventually polynomial in n.**
    have hnorm : ‖(rexp (-π * 2⁻¹) : ℂ)‖ < 1 := by
      rw [Complex.norm_real]
      simp; positivity
    have h₁ : ∀ (n : ℕ), rexp (-π * n * 2⁻¹) = (rexp (-π * 2⁻¹)) ^ n := by
      intro n; symm
      calc (rexp (-π * 2⁻¹)) ^ n
      _ = rexp ((-π * 2⁻¹) * n) := by
        have := (Real.exp_mul (-π * 2⁻¹) n).symm
        norm_cast at this
      _ = rexp (-π * ↑n * 2⁻¹) := by congr 1; ring
    have h₂ : ∀ (n : ℕ), ‖c (↑n + n₀)‖ * rexp (-π * 2⁻¹) ^ n =
        ‖c (↑n + n₀) * rexp (-π * 2⁻¹) ^ n‖ := fun n => by
      rw [norm_mul, neg_mul, norm_pow, Complex.norm_real]
      simp
    simp only [h₁, h₂]
    have := hpoly' c n₀ k hpoly
    norm_cast at this
    exact summable_real_norm_mul_geometric_of_norm_lt_one hnorm this
  · next j =>
    have : -π * ↑j / 2 = -π * ↑j * (1 / 2) := by rw [mul_one_div]
    rw [this]
    simp only [neg_mul]
    gcongr

-- Summability on N implies summability on N+
private lemma natplus_summable_of_nat_summable {a : ℕ → ℝ} (h : Summable a)
  : Summable (fun (n : ℕ+) => a n) := by
  rw [← Equiv.pnatEquivNat.symm.summable_iff, Equiv.pnatEquivNat_symm_apply]
  exact (summable_nat_add_iff 1).mpr h

private lemma step_12a {r : ℝ} (cpos : r > 0)
    : Multipliable fun (b : ℕ+) ↦ (1 - rexp (-r * ↑↑b)) ^ 24 := by
-- Convert goal of Multipliablity to question of Summablility
  conv_lhs =>
    intro b
    rw [← add_sub_cancel 1 ((1 - rexp (-r * ↑↑b)) ^ 24)]
  apply Real.multipliable_one_add_of_summable
-- Establish geometric lower bound for the target series
  have h_lower_bound : ∀ x > 0 , - 24 * rexp (-r * x) ≤ (1 - rexp (-r * x)) ^ 24 - 1 := by
    intro x hx
    apply le_of_add_le_add_left (a := 1)
    rw [neg_mul_comm, sub_eq_add_neg, add_comm _ (-1), ←add_assoc 1 (-1), add_neg_cancel, zero_add]
    apply one_add_mul_le_pow _ 24
    rw [le_neg, neg_neg]
    trans 1
    · apply exp_le_one_iff.mpr
      apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg (le_of_lt cpos)) (le_of_lt hx)
    norm_num
-- Establish upper bound of 0 for target series
  have h_upper_bound : ∀ x ≥ 0 , (1 - rexp (-r * x)) ^ 24 - 1 ≤ 0 := by
    intro x hx
    apply sub_nonpos_of_le
    apply pow_le_one₀ (n := 24)
    · rw [sub_nonneg, exp_le_one_iff]
      apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg (le_of_lt cpos)) hx
    · rw [sub_le_comm, sub_self]
      exact exp_nonneg (-r * x)
-- Combine to show norm of target series is bounded by geometric series
  have h_bounded : ∀ i : ℕ+, ‖(1 - rexp (-r * i)) ^ 24 - 1‖ ≤ 24 * rexp (-r * i) := by
    intro i
    apply abs_sub_le_iff.mpr
    constructor
    · trans 0
      · apply h_upper_bound i (Nat.cast_nonneg i)
      apply mul_nonneg (by norm_num) (le_of_lt (exp_pos _))
    · simp_all only [le_of_neg_le_neg, neg_mul, neg_sub, Nat.cast_pos, PNat.pos]
-- Show that the bound is itself summable
  have h_bound_summable : Summable fun (i : ℕ) ↦ 24 * rexp (-r * i) := by
    rw [summable_mul_left_iff (a := 24) (by norm_num)]
    conv_lhs =>
      intro i
      rw [mul_comm]
    exact Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos cpos)
-- Series bounded in norm by a summable series is itself summable
  exact Summable.of_norm_bounded (natplus_summable_of_nat_summable h_bound_summable) h_bounded

include hz in
private lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  gcongr
  · -- This allows us to get rid of the numerators
    exact aux_11
  · apply tprod_le_of_nonneg_of_multipliable
    · intro n; simp
      have : (1 - rexp (-(π * ↑↑n))) ^ 24 = ((1 - rexp (-(π * ↑↑n))) ^ 12) ^ 2 := by ring
      rw [this]
      exact sq_nonneg ((1 - rexp (-(π * ↑↑n))) ^ 12)
    · intro n; simp
      suffices : 1 - rexp (-(π * ↑↑n)) < 1 - rexp (-2 * π * ↑↑n * z.im)
      · apply le_of_lt
        have h₁ : 0 ≤ 1 - rexp (-(π * ↑↑n)) := by norm_num; positivity
        have h₂ : 0 ≤ 1 - rexp (-2 * π * ↑↑n * z.im) := by linarith
        have h₃ : 24 ≠ 0 := by positivity
        have h₄ : (1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 24 = (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 :=
          by ring_nf
        rw [h₄]
        exact (pow_lt_pow_iff_left₀ h₁ h₂ h₃).mpr this
      gcongr; simp; ring_nf
      calc π * ↑↑n
      _ ≤ π * ↑↑n * 1 := by rw [mul_one]
      _ < π * ↑↑n * z.im * 2 := by
        rw [mul_assoc (π * ↑↑n), mul_lt_mul_iff_right₀ (by positivity)]
        linarith
    · exact step_12a pi_pos
    · conv_lhs =>
        intro b
        rw [mul_assoc, mul_comm _ z.im, ←mul_assoc, neg_mul, neg_mul]
      apply step_12a (mul_pos two_pi_pos (UpperHalfPlane.im_pos z))

private lemma step_13 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) =
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
  rw [DivDiscBound, mul_div_assoc, mul_comm]

end calc_steps

section main_theorem

/-
This section contains the proof of the main result of this file.
-/

include f hf z hz c n₀ hcsum k hpoly in
theorem DivDiscBoundOfPolyFourierCoeff : norm ((f z) / (Δ z)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_1 z c n₀ f hf
  _ = norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_2 z c n₀
  _ = norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_3 z c n₀
  _ = norm ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_4 z c n₀
  _ = norm (cexp (π * I * (n₀ - 2) * z)) *
      norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := step_5 z c n₀
  _ = norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := step_6 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_7 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_8 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_9 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_10 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z hz c n₀
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := step_13 z c n₀

-- #check DivDiscBoundOfPolyFourierCoeff

end main_theorem

section positivity

-- Note that this proof does NOT use our custom `summable_norm_pow_mul_geometric_of_norm_lt_one`
-- for functions with real inputs (see SpherePacking.ForMathlib.SpecificLimits).
include hpoly hcn₀ in
theorem DivDiscBound_pos : 0 < DivDiscBound c n₀ := by
  rw [DivDiscBound]
  apply div_pos
  · refine Summable.tsum_pos ?_ ?_ 0 ?_
    · have h₁ (n : ℕ) : norm (c (↑n + n₀)) * rexp (-π * ↑n / 2) =
          ‖(c (↑n + n₀)) * rexp (-π * ↑n / 2)‖ := by
        rw [norm_mul]
        norm_cast
        simp
      simp only [h₁, summable_norm_iff]
      have h₂ : (fun (n : ℕ) ↦ c (↑n + n₀) * rexp (-π * ↑n / 2)) =O[atTop]
          (fun (n : ℕ) ↦ (n ^ k) * rexp (-π * ↑n / 2)) := by
        refine IsBigO.mul (hpoly' c n₀ k hpoly) ?_
        norm_cast
        exact isBigO_refl _ atTop
      refine summable_of_isBigO_nat ?_ h₂
      have h₃ (n : ℕ) : rexp (-π * ↑n / 2) = (rexp (-π / 2)) ^ n := by
        symm; calc (rexp (-π / 2)) ^ n
        _ = rexp ((-π / 2) * n) := by
          rw [(Real.exp_mul (-π / 2) n)]
          norm_cast
        _ = rexp (-π * ↑n / 2) := by ring_nf
      simp only [h₃]
      rw [← summable_norm_iff]
      refine summable_norm_pow_mul_geometric_of_norm_lt_one k ?_
      simp [neg_div, pi_pos]
    · intro i
      positivity
    · simp [hcn₀]
  · exact aux_11

end positivity

open ArithmeticFunction Nat

section sigma

/-
Recall that σₖ(n) = ∑ {d | n}, d ^ k. In this section, we prove that for all n,
σₖ(n) = O(n ^ (k + 1)).
-/

theorem ArithmeticFunction.sigma_asymptotic (k : ℕ) :
    (fun n ↦ (σ k n : ℝ)) =O[atTop] (fun n ↦ (n ^ (k + 1) : ℝ)) := by
  rw [isBigO_iff]
  use 1
  simp only [Real.norm_natCast, norm_pow, one_mul, eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  rw [sigma_apply]
  norm_cast
  calc ∑ d ∈ n.divisors, d ^ k
  _ ≤ ∑ d ∈ n.divisors, n ^ k := by
      apply Finset.sum_le_sum
      intro d hd
      refine pow_le_pow ?_ hn le_rfl
      exact Nat.divisor_le hd
  _ ≤ n * n ^ k := by
      rw [Finset.sum_const, smul_eq_mul]
      gcongr
      exact Nat.card_divisors_le_self n
  _ = n ^ (k + 1) := by ring

theorem ArithmeticFunction.sigma_asymptotic' (k : ℕ) :
    (fun n ↦ (σ k n : ℂ)) =O[atTop] (fun n ↦ (n ^ (k + 1) : ℂ)) := by
  have (n : ℕ) : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  simp only [this]
  rw [isBigO_ofReal_left]
  norm_cast
  simp only [Nat.cast_pow]
  exact ArithmeticFunction.sigma_asymptotic k

end sigma

section Corollaries

/- The coefficients of `E₂ E₄ - E₆`. -/
noncomputable def coeff_g (n : ℕ) : ℂ := 720 * (n : ℂ) * (sigma 3 n : ℂ)

/- The coefficients of `E₂ E₄ - E₆` are `O(n^5)`. -/
lemma coeff_g_bound : coeff_g =O[atTop] (fun n ↦ (n : ℝ) ^ 5) := by
  have h_sigma3 : (fun n ↦ (sigma 3 n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) ^ 4) :=
    ArithmeticFunction.sigma_asymptotic 3
  have h_const : (fun n ↦ 720 * n * (sigma 3 n : ℝ)) =O[atTop]
      (fun n ↦ n * (n : ℝ) ^ 4) := by
    rw [isBigO_iff] at *
    obtain ⟨c, hc⟩ := h_sigma3
    use 720 * c
    filter_upwards [hc] with n hn
    simp only [mul_comm, mul_assoc, norm_mul, RCLike.norm_natCast, Real.norm_ofNat, norm_pow,
      mul_left_comm] at *
    nlinarith
  convert h_const using 2
  · ext
    norm_num [coeff_g, isBigO_iff]
  · ring

/- The coefficients of `(E₂ E₄ - E₆) ^ 2`, defined as the convolution of `coeff_g`. -/
noncomputable def coeff_sq (n : ℕ) : ℂ := ∑ k ∈ Finset.range (n + 1), coeff_g k * coeff_g (n - k)

/- The coefficients of `(E₂ E₄ - E₆) ^ 2` are `O(n^{11})`. -/
lemma coeff_sq_bound : coeff_sq =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 11) := by
  rw [Asymptotics.isBigO_iff]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, ∀ n, ‖coeff_g n‖ ≤ c₁ * n ^ 5 := by
    obtain ⟨c, hc⟩ : ∃ c, ∀ n, ‖(sigma 3 n : ℂ)‖ ≤ c * n ^ 4 := by
      norm_num [sigma]
      refine ⟨1, fun n ↦ mod_cast (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
        (n.recOn (by norm_num) fun n ih ↦ ?_)⟩
      norm_num [Finset.sum_Ico_succ_top]
      nlinarith [sq n]
    refine ⟨720 * c, fun n ↦ ?_⟩
    rw [coeff_g]
    convert mul_le_mul_of_nonneg_left (hc n) (by positivity : (0 : ℝ) ≤ 720 * n) |>.trans ?_
    · simp
    · grind
  have h_sum_bound : ∀ n, ‖coeff_sq n‖ ≤ (n + 1) * c₁ ^ 2 * n ^ 10 := by
    refine fun n ↦ (norm_sum_le _ _).trans ?_
    have h_term_bound : ∀ k, k ≤ n → ‖coeff_g k * coeff_g (n - k)‖ ≤ c₁ ^ 2 * n ^ 10 := by
      intros k hk
      have h_term_bound : ‖coeff_g k * coeff_g (n - k)‖ ≤ c₁ ^ 2 * k ^ 5 * (n - k) ^ 5 := by
        have h_norm_prod : ‖coeff_g k * coeff_g (n - k)‖ = ‖coeff_g k‖ * ‖coeff_g (n - k)‖ :=
          norm_mul _ _
        convert mul_le_mul (hc₁ k) (hc₁ (n - k)) (norm_nonneg _) ((norm_nonneg _).trans (hc₁ k))
          using 1
        rw [Nat.cast_sub hk]
        ring
      have h_max : ∀ k : ℕ, k ≤ n → k ^ 5 * (n - k) ^ 5 ≤ (n : ℝ) ^ 10 := by
        intros k hk
        have h_max : k ^ 5 ≤ (n : ℝ) ^ 5 ∧ (n - k) ^ 5 ≤ (n : ℝ) ^ 5 :=
          ⟨by gcongr, pow_le_pow_left₀ (sub_nonneg.mpr <| Nat.cast_le.mpr hk)
            (sub_le_self _ <| Nat.cast_nonneg _) _⟩
        refine (mul_le_mul h_max.1 h_max.2 (pow_nonneg (sub_nonneg.2 <| Nat.cast_le.2 hk) _)
          <| by positivity).trans ?_
        ring_nf
        exact le_rfl
      refine h_term_bound.trans ?_
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (h_max k hk) (sq_nonneg c₁)
    refine (Finset.sum_le_sum fun i hi ↦ h_term_bound i (Finset.mem_range_succ_iff.mp hi)).trans ?_
    norm_num
    nlinarith
  refine ⟨2 * c₁ ^ 2, ?_⟩
  filter_upwards [eventually_gt_atTop 1] with n hn
  refine (h_sum_bound n).trans ?_
  rw [norm_of_nonneg (by positivity)]
  nlinarith [show 0 ≤ (n : ℝ) ^ 10 by positivity,
    mul_le_mul_of_nonneg_left (show 2 ≤ (n : ℝ) by exact_mod_cast hn)
    (show 0 ≤ (c₁ ^ 2 : ℝ) by positivity)]

/- `(E₂ E₄ - E₆) ^ 2` is equal to the series with coefficients `coeff_sq`. -/
lemma E2E4mE6_sq_eq_sum (z : ℍ) :
  ((E₂ z) * (E₄ z) - (E₆ z)) ^ 2 = ∑' n : ℕ, coeff_sq n * cexp (2 * π * I * n * z) := by
    have h_conv : (E₂ z * E₄ z - E₆ z) ^ 2 = (∑' n, coeff_g n * cexp (2 * π * .I * n * z)) ^ 2 := by
      rw [E₂_mul_E₄_sub_E₆, ← tsum_mul_left, Eq.comm, tsum_eq_tsum_of_ne_zero_bij]
      use fun x ↦ x.val
      · exact fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by simpa using h
      · intro n hn
        have : n ≠ 0 := fun h ↦ by norm_num [coeff_g, h] at hn
        exact ⟨⟨⟨n, pos_of_ne_zero this⟩, by simp [this]⟩, rfl⟩
      · grind [coeff_g]
    have h_summable₀ : Summable (fun n : ℕ ↦ n ^ 5 * (rexp (-2 * π * z.im)) ^ n) := by
      refine summable_of_ratio_norm_eventually_le (r := (1 + rexp (-2 * π * z.im)) / 2) ?_ ?_
      · linarith [exp_lt_one_iff.mpr (show -2 * π * z.im < 0 by nlinarith [pi_pos, z.im_pos])]
      · have h_exp_lt_one : rexp (-2 * π * z.im) < 1 :=
          Real.exp_lt_one_iff.mpr (by nlinarith [pi_pos, z.im_pos])
        have h_lim : Tendsto (fun n : ℕ ↦ (1 + 1 / n) ^ 5 * rexp (-2 * π * z.im)) atTop
            (nhds (.exp (-2 * π * z.im))) := by
          convert ((tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat)).pow 5 ).mul
            tendsto_const_nhds using 2
          norm_num
        have ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ≥ M,
            (1 + 1 / n) ^ 5 * rexp (-2 * π * z.im) ≤ (1 + rexp (-2 * π * z.im)) / 2 :=
          eventually_atTop.mp (h_lim.eventually (ge_mem_nhds <| by linarith))
        have ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N,
            (n + 1) ^ 5 * rexp (-2 * π * z.im) ≤ (1 + rexp (-2 * π * z.im)) / 2 * n ^ 5 := by
          refine ⟨M + 1, fun n hn ↦ ?_⟩
          have := hM n (le_of_succ_le hn)
          rw [one_add_div (by norm_cast; omega), div_pow, div_mul_eq_mul_div,
            div_le_iff₀ (by exact mod_cast pow_pos (by omega) _)] at this
          omega
        norm_num
        refine ⟨N, fun n hn ↦ ?_⟩
        rw [abs_of_nonneg (by positivity)]
        convert mul_le_mul_of_nonneg_right (hN n hn)
          (pow_nonneg (exp_nonneg (-(2 * π * z.im))) n) using 1 <;> ring_nf
    have h_summable₁ : Summable (fun n : ℕ ↦ n ^ 5 * rexp (-2 * π * n * z.im)) := by
      convert h_summable₀ using 3
      simp [← Real.exp_nat_mul, mul_assoc, mul_comm, mul_left_comm]
    have h_summable₂ : Summable (fun n ↦ (720 * n * sigma 3 n) * rexp (-2 * π * n * z.im)) := by
      refine .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) (h_summable₁.mul_left 720)
      have h_sigma_bound : sigma 3 n ≤ (n : ℝ) ^ 4 := by
        norm_cast
        rcases n.eq_zero_or_pos with hn | hn
        · norm_num [hn, ArithmeticFunction.map_zero]
        refine (Finset.sum_le_sum_of_subset (fun x hx ↦ Finset.mem_Icc.mpr
          ⟨pos_of_mem_divisors hx, le_of_dvd hn (dvd_of_mem_divisors hx)⟩)).trans ?_
        refine (Finset.sum_le_sum fun i hi ↦ Nat.pow_le_pow_left
          (Finset.mem_Icc.mp hi).2 3).trans ?_
        simp [Nat.pow_succ _ 3, mul_comm]
      grw [h_sigma_bound, mul_assoc 720, mul_assoc]
      grind
    have h_summable₃ : Summable (fun n ↦ norm (coeff_g n) * rexp (-2 * π * n * z.im)) := by
      convert h_summable₂
      simp [coeff_g]
    have h_summable : Summable (fun n ↦ coeff_g n * cexp (2 * π * .I * n * z)) := by
      refine Summable.of_norm ?_
      convert h_summable₃
      norm_num [norm_exp]
    have h_summable' : Summable (fun n ↦ ‖coeff_g n * cexp (2 * π * .I * n * z)‖) := by
      convert h_summable₂ using 2
      simp [coeff_g, norm_exp]
    rw [h_conv, sq, Summable.tsum_mul_tsum_eq_tsum_sum_range h_summable h_summable ?_]
    · congr with n
      simp_rw [coeff_sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rw [Nat.cast_sub (Finset.mem_range_succ_iff.mp hx), mul_mul_mul_comm, ← Complex.exp_add]
      ring_nf
    · refine Summable.of_norm ?_
      convert h_summable'.norm.mul_norm h_summable'.norm
      simp [mul_assoc, mul_comm, mul_left_comm]

/- Auxiliary coefficients for the bound on `φ₀`. -/
noncomputable def c_aux (n : ℤ) : ℂ :=
  if n < 0 then 0 else
  if n.toNat % 2 = 0 then coeff_sq (n.toNat / 2) else 0

/- `c_aux` is polynomially bounded by `n^{11}`. -/
lemma c_aux_bound : c_aux =O[atTop] (fun n : ℤ ↦ (n : ℝ)^11) := by
  have h_coeff_sq_bound : coeff_sq =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 11) := coeff_sq_bound
  rw [Asymptotics.isBigO_iff] at *
  obtain ⟨c, hc⟩ := h_coeff_sq_bound
  norm_num at *
  obtain ⟨a, ha⟩ := hc
  refine ⟨c, a * 2, fun b hb ↦ ?_⟩
  rcases b with (_ | _ | b) <;> norm_num [c_aux]
  · simp_all only [Int.ofNat_eq_coe]
    split_ifs with h h'
    · linarith
    · simp_all only [not_lt, cast_nonneg]
      rename_i a_1
      refine (ha _ <| by linarith [Nat.mod_add_div a_1 2]).trans <| mul_le_mul_of_nonneg_left
        (mod_cast Nat.pow_le_pow_left (Nat.div_le_self _ _) _) (le_of_not_gt fun hc ↦ ?_)
      have := ha (a + 1) (a.le_add_right 1)
      norm_num at *
      nlinarith [norm_nonneg (coeff_sq (a + 1)), pow_pos (cast_add_one_pos (α := ℝ) a) 11]
    · simp_all only [not_lt, cast_nonneg]
      rw [norm_zero]
      exact (norm_nonneg _).trans ((ha _ (by linarith)).trans <| by norm_num)
  · linarith [Int.negSucc_lt_zero 0]
  · linarith [Int.negSucc_lt_zero (b + 1)]

/- The square of `E₂ E₄ - E₆` is given by the shifted series of `c_aux`. -/
lemma E2E4mE6_sq_eq_sum_shifted_c_aux (z : ℍ) :
    ((E₂ z) * (E₄ z) - (E₆ z)) ^ 2 = ∑' n : ℕ, c_aux (n + 4) * cexp (π * I * (n + 4) * z) := by
  have := E2E4mE6_sq_eq_sum z
  unfold c_aux
  simp only [ite_mul, zero_mul, this]
  refine tsum_eq_tsum_of_ne_zero_bij (fun x ↦ 2 * x.val - 4) ?_ ?_ ?_ |>.symm
  · intro ⟨x, hx⟩ ⟨y, hy⟩ a
    simp only [Subtype.mk.injEq] at a ⊢
    have h_eq : 2 * x = 2 * y := by
      unfold coeff_sq at hx hy
      congr
      simp only [coeff_g, Finset.sum_range_succ', tsub_zero, Function.mem_support] at hx hy
      rcases x with (_ | _ | x)
      · norm_num at hx
      · norm_num at hx
      rcases y with (_ | _ | y)
      · norm_num at hy
      · norm_num at hy
      · omega
    exact mul_left_cancel₀ two_ne_zero h_eq
  · refine fun x hx ↦ ⟨⟨(x + 4) / 2, ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq, ite_eq_left_iff, ite_eq_right_iff,
        Classical.not_imp] at hx
      simpa using hx.2.2
    norm_num
    simp_all only [Function.mem_support, ne_eq, ite_eq_left_iff, not_lt, ite_eq_right_iff,
      _root_.mul_eq_zero, Complex.exp_ne_zero, or_false, Classical.not_imp]
    exact Nat.sub_eq_of_eq_add <| Nat.mul_div_cancel' (by omega)
  · intro ⟨val, property⟩
    split_ifs with h h
    · grind
    · have : 4 ≤ 2 * val := by
        rcases val with (_ | _ | val)
        · exact (property <| by norm_num [coeff_sq, coeff_g]).elim
        · simp only [coeff_g, coeff_sq, zero_add, Function.mem_support, ne_eq,
            Finset.sum_range_succ] at property
          norm_num at property
        · omega
      rw [Nat.cast_sub this, Nat.cast_sub this]
      grind
    · simp_all only [not_lt, mod_two_not_eq_zero, zero_eq_mul, Complex.exp_ne_zero]
      omega

/- The series for `c_aux` is summable. -/
lemma c_aux_summable (z : ℍ) : Summable fun n : ℕ ↦ c_aux (n + 4) * cexp (π * I * (n + 4) * z) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ n : ℕ, n ≥ 4 → ‖c_aux n‖ ≤ C * n ^ 11 := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ n : ℕ, ‖coeff_sq n‖ ≤ C * n ^ 11 := by
      have := coeff_sq_bound
      simp only [Asymptotics.isBigO_iff, norm_pow, RCLike.norm_natCast, eventually_atTop] at this
      obtain ⟨w, w', h⟩ := this
      refine ⟨w ⊔ (∑ n ∈ Finset.range w', ‖coeff_sq n‖ / n ^ 11), fun n ↦ ?_⟩
      by_cases hn : n < w'
      · by_cases hn : n = 0
        · simp [hn, mul_comm, coeff_sq, coeff_g]
        · have := Finset.single_le_sum (fun a _ ↦ div_nonneg (norm_nonneg (coeff_sq a))
            (pow_nonneg (cast_nonneg a) 11)) (Finset.mem_range.mpr ‹_›)
          rw [div_le_iff₀ (by positivity)] at this
          nlinarith [le_max_right w (∑ n ∈ Finset.range w', ‖coeff_sq n‖ / n ^ 11),
            pow_pos (by positivity : 0 < (n : ℝ)) 11]
      · exact (h n (le_of_not_gt hn)).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine ⟨C, fun n hn ↦ ?_⟩
    simp only [c_aux]
    split_ifs
    · grind
    · have hC_nonneg : 0 ≤ C := by
        specialize hC 1
        norm_num at hC
        exact (norm_nonneg _).trans hC
      exact (hC _).trans
        (mul_le_mul_of_nonneg_left (mod_cast Nat.pow_le_pow_left (div_le_self _ _) _) hC_nonneg)
    · simp_all only [not_lt, cast_nonneg, mod_two_not_eq_zero, norm_zero]
      exact le_trans (norm_nonneg _) (hC n) |> le_trans <| by norm_num
  have h_factor : Summable (fun n : ℕ ↦ (n + 4) ^ 11 * rexp (-π * (n + 4) * z.im)) := by
    have h_exp : rexp (-π * z.im) < 1 :=
      Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) z.im_pos)
    have h_ratio_test :
        Tendsto (fun n : ℕ ↦ ((n + 1 + 4) ^ 11 * rexp (-π * (n + 1 + 4) * z.im)) /
            ((n + 4) ^ 11 * rexp (-π * (n + 4) * z.im)))
          atTop (nhds (.exp (-π * z.im))) := by
      suffices h_simplify : Tendsto (fun n : ℕ ↦ ((n + 5) / (n + 4)) ^ 11 * rexp (-π * z.im))
          atTop (nhds (.exp (-π * z.im))) by
        convert h_simplify using 2
        field_simp
        ring_nf
        simp only [mul_assoc, ← Real.exp_add]
        ring_nf
      suffices h_simplify : Tendsto (fun n : ℕ ↦ (1 + 1 / (n + 4)) ^ 11 * rexp (-π * z.im))
          atTop (nhds (.exp (-π * z.im))) by
        refine h_simplify.congr fun n ↦ ?_
        rw [one_add_div (by positivity)]
        ring
      exact (((tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <|
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ).pow _ ).mul
        tendsto_const_nhds).trans <| by norm_num
    refine summable_of_ratio_norm_eventually_le
      (r := (rexp (-π * z.im) + 1) / 2) (by linarith) ?_
    have : rexp (-π * z.im) < (.exp (-π * z.im) + 1) / 2 := by linarith
    have := h_ratio_test.eventually (gt_mem_nhds this)
    simp_all only [ge_iff_le, neg_mul, exp_lt_one_iff, Left.neg_neg_iff, eventually_atTop,
      cast_add, cast_one, norm_mul, norm_pow, norm_eq_abs, abs_exp]
    obtain ⟨w, h⟩ := this
    refine ⟨w, fun n hn ↦ ?_⟩
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have := h n hn
    rw [div_lt_iff₀ (by positivity)] at this
    grind
  have h_factor : Summable (fun n : ℕ ↦ C * (n + 4) ^ 11 * rexp (-π * (n + 4) * z.im)) := by
    simpa only [mul_assoc] using h_factor.mul_left C
  have h_norm (n : ℕ) : ‖c_aux (n + 4) * cexp (π * .I * (n + 4) * z)‖ ≤
      C * (n + 4) ^ 11 * rexp (-π * (n + 4) * z.im) := by
    specialize hC (n + 4) (by norm_num)
    norm_cast at *
    simp_all only [cast_pow, cast_add, cast_ofNat, neg_mul, Complex.norm_mul]
    gcongr
    · exact (norm_nonneg _).trans hC
    · simp [Complex.norm_exp]
  exact (h_factor.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_norm).of_norm

theorem norm_φ₀_le : ∃ C₀ > 0, ∀ z, 1 / 2 < z.im → norm (φ₀ z) ≤ C₀ * rexp (-2 * π * z.im) := by
  unfold φ₀
  refine ⟨(DivDiscBound c_aux 4) ⊔ 1, by norm_num, fun z hz ↦ ?_⟩
  have := DivDiscBoundOfPolyFourierCoeff z hz c_aux 4 (mod_cast c_aux_summable z) 11
    c_aux_bound _ (fun x ↦ mod_cast E2E4mE6_sq_eq_sum_shifted_c_aux x)
  ring_nf at *
  exact (mul_comm (rexp _) _ ▸ this).trans <|
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

end Corollaries

section Scratch

open MeasureTheory
open scoped MeasureTheory.Measure

example {m n : ℕ} {f : (EuclideanSpace ℝ (Fin m)) × (EuclideanSpace ℝ (Fin n)) → ℝ}
  (h₁ : ∀ x : EuclideanSpace ℝ (Fin m), Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦ f (x, y)))
  (h₂ : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
    ∫ x : EuclideanSpace ℝ (Fin m), f (x, y) ∂volume) volume) :
    Integrable f (volume.prod volume) := by

  sorry

end Scratch

end PolyFourierCoeffBound

end MagicFunction
